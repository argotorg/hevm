{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE StaticPointers #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-} -- It's OK to crash in tests if the pattern does not match

module EVM.Expr.ExprTests (tests) where

import Prelude hiding (LT, GT)
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding (Failure, Success)

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT)
import Data.Bits (shiftL)
import Data.ByteString qualified as BS (drop, length, pack, replicate, take)
import Data.Containers.ListUtils (nubOrd)
import Data.List qualified as List (nub, sort, tails)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Typeable
import Numeric.Natural (Natural)

import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Expr.Generator
import EVM.Expr.RewriteFuzz (genShapedWord, genShapedProp, shrinkWord, shrinkProp)
import EVM.Expr.Probe (probes, contract)
import EVM.HashCons qualified as HC
import EVM.Format (hexText)
import EVM.SMT (AbstractQuery(..), SMT2(..), SMTScript(..), assertPropsAbstract)
import EVM.Solvers hiding (checkSat)
import EVM.Solvers qualified as Solvers (checkSat)
import EVM.SymExec (subModel)
import EVM.Traversals (foldExpr, foldProp, mapExpr, mapExprM, mapProp)
import EVM.Types hiding (Env)


tests :: TestTree
tests = testGroup "Expr"
  [unitTests, fuzzTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ simplificationTests
  , constantPropagationTests
  , boundPropagationTests
  , comparisonTests
  , signExtendTests
  , concretizationTests
  , traversalTests
  , rewriteRuleTests
  ]

rewriteRuleTests :: TestTree
rewriteRuleTests = testGroup "Rewrite rules"
  [ testCase "mod-div-power-of-two" $ do
      let x = Var "x"
      assertEqual "mod" (And (Lit 0xff) x) (Expr.simplify (Mod x (Lit 0x100)))
      assertEqual "div" (SHR (Lit 8) x) (Expr.simplify (Div x (Lit 0x100)))
      assertEqual "not a power of two" (Mod x (Lit 6)) (Expr.simplify (Mod x (Lit 6)))
      assertEqual "byte offset exponentiation still becomes a shift"
        (SHL (Mul (Lit 8) (And (Lit 31) x)) (Lit 1)) (Expr.simplify (Exp (Lit 0x100) (Mod x (Lit 32))))
  ]

traversalTests :: TestTree
traversalTests = testCase "every-field-is-traversed" $ assertBool (unlines missed) (null missed)
  where
    cases = $(probes [| SomeExpr |] ['GVar] ''Expr)
      <> [ (SomeExpr (Failure [] mempty e), ms) | (e, ms) <- $(probes [| id |] [] ''EvmError) ]
      <> [ (SomeExpr (Partial [] mempty p), ms) | (p, ms) <- $(probes [| id |] [] ''PartialExec) ]
      <> [ (SomeExpr (contract c), ms) | (c, ms) <- $(probes [| id |] [] ''ContractCode) ]
      <> [ (SomeExpr (Failure [p] mempty StackUnderrun), ms) | (p, ms) <- $(probes [| id |] [] ''Prop) ]
    missed =
      [ name <> " misses a field of " <> show e
      | (SomeExpr e, ms) <- cases
      , let renamed = List.sort (fmap (<> "'") ms)
      , (name, ok) <-
          [ ("foldExpr", List.sort (foldExpr probeName ["acc"] e) == List.sort ("acc" : ms))
          , ("mapExpr", names (mapExpr renameProbe e) == renamed)
          , ("memoFixTraverse", names (HC.memoFixTraverse (static (HC.Rewrite renameProbe)) e) == renamed)
          ]
      , not ok ]
    names :: Expr a -> [Text]
    names = List.sort . foldExpr probeName []
    probeName :: Expr a -> [Text]
    probeName = \case
      Var n -> [n]; AbstractBuf n -> [n]; SymAddr n -> [n]; Gas n _ -> [n]
      -- the address is part of this leaf, not a child
      AbstractStore (SymAddr n) _ -> [n]
      _ -> []

renameProbe :: Expr a -> Expr a
renameProbe = \case
  Var n -> Var (n <> "'")
  AbstractBuf n -> AbstractBuf (n <> "'")
  SymAddr n -> SymAddr (n <> "'")
  Gas n i -> Gas (n <> "'") i
  AbstractStore (SymAddr n) w -> AbstractStore (SymAddr (n <> "'")) w
  e -> e

simplificationTests :: TestTree
simplificationTests = testGroup "Expr-rewriting"
  [ storageTests
  , copySliceTests
  , memoryTests
  , basicSimplificationTests
  , propSimplificationTests
  , wrappingTests
  ]

storageTests :: TestTree
storageTests = testGroup "Storage tests"
  [
    testCase "read-from-sstore" $ assertEqual errorMsg
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x0) (Lit 0xab) (AbstractStore (LitAddr 0x0) Nothing)))
    , testCase "read-from-concrete" $ assertEqual errorMsg
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, 0xab)]))
    , testCase "read-past-write" $ assertEqual errorMsg
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x1) (Var "b") (ConcreteStore $ Map.fromList [(0x0, 0xab)])))
    -- #1082: an empty ConcreteStore is total, so a symbolic slot reads 0
    , testCase "read-symbolic-slot-empty-concrete-store" $ assertEqual errorMsg
        (Lit 0)
        (Expr.readStorage' (Var "x") (ConcreteStore mempty))
    -- accessStorage relies on Nothing here to drive lazy RPC slot fetching;
    -- the empty-store => 0 rule lives in readStorage' only
    , testCase "readStorage-keeps-nothing-on-concrete-miss" $ assertEqual errorMsg
        Nothing
        (Expr.readStorage (Lit 0x5) (ConcreteStore mempty))
    -- a concrete-valued write would instead be folded into the store
    , testCase "read-symbolic-slot-stripped-to-empty-concrete-store" $ assertEqual errorMsg
        (Lit 0)
        (Expr.readStorage' (mappingRead 1 "k") (SStore (Lit 0x5) (Var "b") (ConcreteStore mempty)))
    , testCase "filter-store-drops-other-mapping-entries" $ assertEqual errorMsg
        (ConcreteStore $ Map.fromList [(0x5, 0x222)])
        (Expr.filterStoreByReadSlot preImgs (mappingRead 1 "k")
          (ConcreteStore $ Map.fromList [(preImgHash, 0x111), (0x5, 0x222)]))
    , testCase "filter-store-keeps-same-mapping-entries" $ assertEqual errorMsg
        (ConcreteStore $ Map.fromList [(preImgHash, 0x111), (0x5, 0x222)])
        (Expr.filterStoreByReadSlot preImgs (mappingRead 0 "k")
          (ConcreteStore $ Map.fromList [(preImgHash, 0x111), (0x5, 0x222)]))
    , testCase "filter-store-ignores-non-mapping-reads" $ assertEqual errorMsg
        (ConcreteStore $ Map.fromList [(preImgHash, 0x111)])
        (Expr.filterStoreByReadSlot preImgs (Var "x")
          (ConcreteStore $ Map.fromList [(preImgHash, 0x111)]))
    , testCase "read-unrelated-mapping-filters-to-zero" $ assertEqual errorMsg
        (Lit 0)
        (Expr.readStorage' (mappingRead 1 "k")
          (Expr.filterStoreByReadSlot preImgs (mappingRead 1 "k")
            (ConcreteStore $ Map.fromList [(preImgHash, 0x111)])))
    , testCase "simplify-storage-wordToAddr" $ do
       let a = "0x000000000000000000000000d95322745865822719164b1fc167930754c248de000000000000000000000000000000000000000000000000000000000000004a"
           store = ConcreteStore (Map.fromList[(W256 0xebd33f63ba5dda53a45af725baed5628cdad261db5319da5f5d921521fe1161d,W256 0x5842cf)])
           expr = SLoad (Keccak (ConcreteBuf (hexText a))) store
           simpExpr = Expr.wordToAddr expr
           simpExpr2 = Expr.concKeccakSimpExpr expr
       assertEqual "Expression should simplify to value." simpExpr (Just $ LitAddr 0x5842cf)
       assertEqual "Expression should simplify to value." simpExpr2 (Lit 0x5842cf)
    , testCase "simplify-storage-wordToAddr-complex" $ do
       let a = "0x000000000000000000000000d95322745865822719164b1fc167930754c248de000000000000000000000000000000000000000000000000000000000000004a"
           store = ConcreteStore (Map.fromList[(W256 0xebd33f63ba5dda53a45af725baed5628cdad261db5319da5f5d921521fe1161d,W256 0x5842cf)])
           expr = SLoad (Keccak (ConcreteBuf (hexText a))) store
           writeWChain = WriteWord (Lit 0x32) (Lit 0x72) (WriteWord (Lit 0x0) expr (ConcreteBuf ""))
           kecc = Keccak (CopySlice (Lit 0x0) (Lit 0x0) (Lit 0x20) (WriteWord (Lit 0x0) expr (writeWChain)) (ConcreteBuf ""))
           keccAnd =  (And (Lit 1461501637330902918203684832716283019655932542975) kecc)
           outer = And (Lit 1461501637330902918203684832716283019655932542975) (SLoad (keccAnd) (ConcreteStore (Map.fromList[(W256 1184450375068808042203882151692185743185288360635, W256 0xacab)])))
           simp = Expr.concKeccakSimpExpr outer
       assertEqual "Expression should simplify to value." simp (Lit 0xacab)
    -- A concrete mapping preimage is key || slot, just like MappingSlot.
    -- Use distinct keys and slots so reversing them cannot pass unnoticed.
    , testCase "decompose-concrete-mapping-read-selects-slot" $ assertEqual errorMsg
        (Just $ SLoad (Lit 1) (AbstractStore (LitAddr 0) (Just 0)))
        (Expr.decomposeStorage $ SLoad (mappingConcrete 0 1) (AbstractStore (LitAddr 0) Nothing))
    , testCase "decompose-symbolic-mapping-read-keeps-concrete-write" $ assertEqual errorMsg
        (Just $ SLoad (Var "k") (SStore (Lit 1) (Lit 3) emptyStore))
        (Expr.decomposeStorage $ SLoad (mappingRead 0 "k")
          (SStore (mappingConcrete 0 1) (Lit 3) emptyStore))
    , testCase "decompose-symbolic-mapping-read-drops-other-concrete-write" $ assertEqual errorMsg
        (Just $ SLoad (Var "k") emptyStore)
        (Expr.decomposeStorage $ SLoad (mappingRead 1 "k")
          (SStore (mappingConcrete 0 1) (Lit 3) emptyStore))
    , testCase "decompose-concrete-mapping-read-keeps-symbolic-write" $ assertEqual errorMsg
        (Just $ SLoad (Lit 1) (SStore (Var "k") (Lit 3) emptyStore))
        (Expr.decomposeStorage $ SLoad (mappingConcrete 0 1)
          (SStore (mappingRead 0 "k") (Lit 3) emptyStore))
    , testCase "decompose-concrete-mapping-read-drops-other-symbolic-write" $ assertEqual errorMsg
        (Just $ SLoad (Lit 0) emptyStore)
        (Expr.decomposeStorage $ SLoad (mappingConcrete 1 0)
          (SStore (mappingRead 0 "k") (Lit 3) emptyStore))
    -- an array and a mapping on one slot would end up in the same logical store
    , testCase "decompose-props-declines-array-and-mapping-on-one-slot" $ assertEqual errorMsg
        Nothing
        (Expr.decomposeStorageProps
          [PEq (Lit 0) (SLoad (mappingRead 2 "k") (SStore (arrElem 2 (Var "i")) (Lit 3) emptyStore))])
    , testCase "decompose-props-declines-clash-across-props" $ assertEqual errorMsg
        Nothing
        (Expr.decomposeStorageProps
          [ PEq (Lit 0) (SLoad (mappingRead 2 "k") emptyStore)
          , PEq (Lit 0) (SLoad (arrElem 2 (Var "i")) emptyStore) ])
    , testCase "decompose-props-mixes-array-and-mapping-on-different-slots" $ assertEqual errorMsg
        (Just [PEq (Lit 0) (SLoad (Var "k") emptyStore)])
        (Expr.decomposeStorageProps
          [PEq (Lit 0) (SLoad (mappingRead 1 "k") (SStore (arrElem 2 (Var "i")) (Lit 3) emptyStore))])
    , testCase "decompose-props-declines-unrecognized-key" $ assertEqual errorMsg
        Nothing
        (Expr.decomposeStorageProps
          [ PEq (Lit 0) (SLoad (mappingRead 1 "k") emptyStore)
          , PEq (Lit 0) (SLoad (Var "x") emptyStore) ])
    -- decomposition: keys of the read array become offsets, writes to other stores are dropped
    , testCase "decompose-array-read-rebases-keys" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") (SStore (Lit 0) (Lit 1) emptyStore))
        (Expr.decomposeStorage $ SLoad (arrElem 2 (Var "i"))
          (SStore (arrZero 2) (Lit 1) emptyStore))
    , testCase "decompose-array-read-drops-small-slot-write" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") emptyStore)
        (Expr.decomposeStorage $ SLoad (arrElem 2 (Var "i"))
          (SStore (Lit 0) (Var "a") emptyStore))
    , testCase "decompose-array-read-drops-other-array-write" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") emptyStore)
        (Expr.decomposeStorage $ SLoad (arrElem 2 (Var "i"))
          (SStore (arrZero 1) (Lit 5) emptyStore))
    , testCase "decompose-small-slot-read-drops-array-write" $ assertEqual errorMsg
        (Just $ SLoad (Lit 0) (SStore (Lit 0) (Var "a") emptyStore))
        (Expr.decomposeStorage $ SLoad (Lit 0)
          (SStore (arrZero 2) (Lit 1) (SStore (Lit 0) (Var "a") emptyStore)))
    , testCase "decompose-small-slot-read-keeps-concrete-base" $ assertEqual errorMsg
        (Just $ SLoad (Lit 3) (ConcreteStore $ Map.fromList [(3, 7)]))
        (Expr.decomposeStorage $ SLoad (Lit 3)
          (SStore (arrElem 1 (Var "i")) (Var "v") (ConcreteStore $ Map.fromList [(3, 7)])))
    , testCase "decompose-array-read-empties-small-slot-base" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") emptyStore)
        (Expr.decomposeStorage $ SLoad (arrElem 1 (Var "i")) (ConcreteStore $ Map.fromList [(3, 7)]))
    -- #1086: a skipped write must not cause the already-rebased writes below it to be rebased again
    , testCase "decompose-keeps-array-write-below-other-array-write" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") (SStore (Lit 0) (Lit 1) emptyStore))
        (Expr.decomposeStorage $ SLoad (arrElem 2 (Var "i"))
          (SStore (arrZero 1) (Lit 5) (SStore (arrZero 2) (Lit 1) emptyStore)))
    , testCase "decompose-keeps-symbolic-array-write-below-small-slot" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") (SStore (Var "j") (Lit 1) emptyStore))
        (Expr.decomposeStorage $ SLoad (arrElem 2 (Var "i"))
          (SStore (Lit 0) (Var "a") (SStore (arrElem 2 (Var "j")) (Lit 1) emptyStore)))
    , testCase "decompose-keeps-array-write-below-small-slot" $ assertEqual errorMsg
        (Just $ SLoad (Var "i") (SStore (Lit 0) (Lit 1) emptyStore))
        (Expr.decomposeStorage $ SLoad (arrElem 2 (Var "i"))
          (SStore (Lit 0) (Var "a") (SStore (arrZero 2) (Lit 1) emptyStore)))
  ]
  where
    errorMsg = "Storage read expression not simplified correctly"
    emptyStore = ConcreteStore mempty
    -- element `off` of the dynamic array at storage slot n: keccak(n) + off
    arrElem n off = Expr.ArraySlotWithOffs (arrId n) off
    arrZero n = Expr.ArraySlotZero (arrId n)
    arrId n = BS.pack (replicate 31 0 ++ [n])
    -- a symbolic read of the mapping at storage slot n: keccak(key . n)
    mappingRead n key = Keccak (WriteWord (Lit 0) (Var key) (ConcreteBuf (mapSlotBuf n)))
    mappingConcrete n key = Keccak (ConcreteBuf (BS.pack (replicate 31 0 ++ [key] ++ replicate 31 0 ++ [n])))
    mapSlotBuf n = BS.pack (replicate 63 0 ++ [n])
    -- recorded preimage of a write to the mapping at slot 0 with key 0xaa
    preImgBytes = BS.pack (replicate 31 0 ++ [0xaa] ++ replicate 32 0)
    preImgHash = keccak' preImgBytes
    preImgs = Map.fromList [(preImgHash, preImgBytes)]

copySliceTests :: TestTree
copySliceTests = testGroup "CopySlice tests"
  [ testCase "copyslice-simps" $ do
        let e a b =  CopySlice (Lit 0) (Lit 0) (BufLength (AbstractBuf "buff")) (CopySlice (Lit 0) (Lit 0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf a)) (ConcreteBuf b)
            expr1 = e "" ""
            expr2 = e "" "aasdfasdf"
            expr3 = e "9832478932" ""
            expr4 = e "9832478932" "aasdfasdf"
        assertEqual "Not full simp" (Expr.simplify expr1) (AbstractBuf "buff")
        assertEqual "Not full simp" (Expr.simplify expr2) $ CopySlice (Lit 0x0) (Lit 0x0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf "aasdfasdf")
        assertEqual "Not full simp" (Expr.simplify expr3) (AbstractBuf "buff")
        assertEqual "Not full simp" (Expr.simplify expr4) $ CopySlice (Lit 0x0) (Lit 0x0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf "aasdfasdf")
  , testCase "copyslice-difficult-concretization" $ do
        let commonOffset = (Var "x")
        let concreteVal = (Lit 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)
        let src = WriteWord commonOffset concreteVal (AbstractBuf "buff")
        let dst = ConcreteBuf ""
        let e = CopySlice commonOffset (Lit 1) (Lit 3) src dst
        let simpl = Expr.simplify e
        let expected = ConcreteBuf $ BS.pack [0x00, 0xff, 0x00, 0xff]
        assertEqual "" expected simpl
  , testCase "copyslice-single-byte-concretizes" $ do
        -- Regression for issue #1066. A size-1 CopySlice whose read range is
        -- fully covered by a concrete WriteWord must concretize, even when an
        -- unrelated (out-of-range) symbolic write sits underneath it.
        let w = Lit 0xabcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789
            src = WriteWord (Lit 0x20) w (WriteWord (Lit 0x80) (Var "x") (ConcreteBuf ""))
            e = CopySlice (Lit 0x20) (Lit 0x0) (Lit 0x1) src (ConcreteBuf "")
        assertEqual "size-1 copy must concretize to the 1st byte, dropping the out-of-range symbolic write"
          (ConcreteBuf (BS.pack [0xab])) (Expr.simplify e)
  , testCase "copyslice-single-byte-value" $ do
        -- Same as above, but no symbolic write this time
        let w = Lit 0xabcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789
            src = WriteWord (Lit 0x20) w (ConcreteBuf "")
            e = CopySlice (Lit 0x3f) (Lit 0x0) (Lit 0x1) src (ConcreteBuf "")
        assertEqual "size-1 copy must read the correct (last) byte"
          (ConcreteBuf (BS.pack [0x89])) (Expr.simplify e)
  , testCase "copyslice-window-trim-canonicalizes-mapping-keys" $ do
      let key rest = Expr.simplify $ Keccak (CopySlice (Lit 0) (Lit 0) (Lit 64)
                       (WriteWord (Lit 0) (Var "acc") (WriteWord (Lit 32) (Lit 7) rest)) (ConcreteBuf ""))
          k1 = key (WriteWord (Lit 192) (Var "x") (ConcreteBuf (BS.pack [9, 9, 9])))
          k2 = key (WriteWord (Lit 64) (Var "y") (WriteWord (Lit 320) (Lit 5) (ConcreteBuf "")))
          k3 = Expr.simplify $ Keccak (CopySlice (Lit 0) (Lit 0) (Lit 64)
                 (WriteWord (Lit 0) (Var "acc") (WriteWord (Lit 32) (Lit 8) (ConcreteBuf ""))) (ConcreteBuf ""))
      assertEqual "same first 64 bytes give the same key" k1 k2
      assertBool "a different second word gives a different key" (k1 /= k3)
      assertEqual "the equivalent key resolves a storage read" (Var "value")
        (Expr.readStorage' k2 (SStore k1 (Var "value") (AbstractStore (SymAddr "c") Nothing)))
  , testCase "copyslice-window-trim-preserves-zero-mapping-slot" $ do
      let src = WriteWord (Lit 0) (Var "acc") (WriteWord (Lit 32) (Lit 0)
                  (WriteWord (Lit 192) (Var "scratch") (ConcreteBuf "")))
          key = Expr.simplify $ Keccak (CopySlice (Lit 0) (Lit 0) (Lit 64) src (ConcreteBuf ""))
      assertEqual "retains the 64-byte mapping preimage"
        (Expr.MappingSlot (BS.pack (replicate 64 0)) (Var "acc")) key
      assertEqual "slot zero still decomposes"
        (Just $ SLoad (Var "acc") (AbstractStore (SymAddr "c") (Just 0)))
        (Expr.decomposeStorage $ SLoad key (AbstractStore (SymAddr "c") Nothing))
  , localOption (mkTimeout 5_000_000) $ testCase "copyslice-window-trim-short-copy" $ do
      let src = WriteWord (Lit 192) (Var "other") (WriteWord (Lit 16) (Var "value") (ConcreteBuf ""))
          dst = AbstractBuf "dst"
          expected = CopySlice (Lit 0) (Lit 5) (Lit 3) (WriteWord (Lit 0) (Var "value") (ConcreteBuf "")) dst
      assertEqual "short copies reach a stable result" expected (Expr.copySlice (Lit 16) (Lit 5) (Lit 3) src dst)
  , testCase "copyslice-window-trim-unsupported" $ do
      let base = ConcreteBuf ""
          src = WriteWord (Lit 0) (Var "value") base
          check (off, size, buf) =
            assertEqual "unsupported windows and writes stay intact"
              (CopySlice (Lit off) (Lit 0) (Lit size) buf (AbstractBuf "dst"))
              (Expr.copySlice (Lit off) (Lit 0) (Lit size) buf (AbstractBuf "dst"))
      mapM_ check
        [ (0, 64, WriteWord (Var "offset") (Var "value") base)
        , (0, 64, WriteWord (Lit (maxBound - 15)) (Var "value") base)
        , (0, 64, WriteWord (Lit 0) (Var "value") (AbstractBuf "src"))
        , (maxBound - 15, 64, src)
        , (0, Expr.maxBytes, src)
        ]
  , testCase "copyslice-smt-dst-named-src" $ do
      -- outside the copied window the byte is dst's, and dst may be any buffer, even one called src
      let e = ReadByte (Lit 1) (CopySlice (Lit 0xc) (Lit 0x31) (Lit 0x32) (ConcreteBuf "") (AbstractBuf "src"))
      res <- checkSat (PEq e (LitByte 128))
      assertBool ("the byte can be 128: " <> show res) (isSat res)
  , testCase "exp-literal-exponent-smt" $ do
      let x = Var "x"
          x13 = foldr1 Mul (replicate 13 x)
      res <- checkSat (PNeg (PEq (Exp x (Lit 13)) x13))
      assertBool ("x^13 is 13 multiplications: " <> show res) (isQed res)
      res2 <- checkSat (PEq (Exp x (Lit (2 ^ (255 :: Int) + 1))) (Lit 3) .&& PEq x (Lit 3))
      assertBool ("3^(2^255+1) is 3 mod 2^256: " <> show res2) (isSat res2)
  , testCase "copyslice-window-trim-in-simplify" $ do
      let src = WriteWord (Lit 262) (Var "a") (WriteWord (Lit 196) (Lit 0xba) (ConcreteBuf ""))
          dst = ConcreteBuf (BS.pack [1..100])
          e = CopySlice (Lit 145) (Lit 45) (Lit 82) src dst
      assertEqual "a write past the window does not survive simplification"
        (ConcreteBuf (BS.pack [1..45] <> BS.replicate 82 0)) (Expr.simplify e)
  , adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 200 else n)) $
    testProperty "copyslice-window-trim-equivalence" $ forAll genTrimCase $ \c ->
      forAll (frequency [(4, fromIntegral <$> choose (0 :: Int, 64)), (1, elements [Expr.maxBytes, maxBound - 15])]) $ \dOff ->
      forAll (elements [ConcreteBuf "", AbstractBuf "dst", ConcreteBuf (BS.pack [1..100])]) $ \dst -> ioProperty $ do
        let lit = Lit . fromIntegral
            full = CopySlice (lit c.tcOff) (Lit dOff) (lit c.tcSize) (tcSrc c) dst
            simp = Expr.copySlice (lit c.tcOff) (Lit dOff) (lit c.tcSize) (tcSrc c) dst
            simpAll = Expr.simplify full
            differ a = (full ./= a) .|| (Expr.bufLength full ./= Expr.bufLength a)
        res <- checkSatWith equivConfig (differ simp .|| differ simpAll)
        let result = case simp of
              _ | simp == full -> "unchanged"
              ConcreteBuf _ -> "concrete"
              CopySlice _ _ _ s _ | s /= tcSrc c -> "source trimmed"
              _ -> "other"
        pure $ foldr (uncurry tabulate) (counterexample (show (c, simp, simpAll, res)) $ isUnsatOrUnknown res)
          (("result", [result]) : ("solver", [takeWhile (/= ' ') (show res)]) : trimCaseLabels c)
  ]

memoryTests :: TestTree
memoryTests = testGroup "Memory tests"
  [ testCase "read-write-same-byte" $ assertEqual ""
      (LitByte 0x12)
      (Expr.readByte (Lit 0x20) (WriteByte (Lit 0x20) (LitByte 0x12) mempty))
  , testCase "read-write-same-word" $ assertEqual ""
      (Lit 0x12)
      (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
  , testCase "read-byte-write-word" $ assertEqual ""
      -- reading at byte 31 a word that's been written should return LSB
      (LitByte 0x12)
      (Expr.readByte (Lit 0x1f) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
  , testCase "read-byte-write-word2" $ assertEqual ""
      -- Same as above, but offset not 0
      (LitByte 0x12)
      (Expr.readByte (Lit 0x20) (WriteWord (Lit 0x1) (Lit 0x12) mempty))
  , testCase "read-write-with-offset" $ assertEqual ""
      -- 0x3F = 63 decimal, 0x20 = 32. 0x12 = 18
      --    We write 128bits (32 Bytes), representing 18 at offset 32.
      --    Hence, when reading out the 63rd byte, we should read out the LSB 8 bits
      --           which is 0x12
      (LitByte 0x12)
      (Expr.readByte (Lit 0x3F) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
  , testCase "read-write-with-offset2" $ assertEqual ""
      --  0x20 = 32, 0x3D = 61
      --  we write 128 bits (32 Bytes) representing 0x10012, at offset 32.
      --  we then read out a byte at offset 61.
      --  So, at 63 we'd read 0x12, at 62 we'd read 0x00, at 61 we should read 0x1
      (LitByte 0x1)
      (Expr.readByte (Lit 0x3D) (WriteWord (Lit 0x20) (Lit 0x10012) mempty))
  , testCase "read-write-with-extension-to-zero" $ assertEqual ""
      -- write word and read it at the same place (i.e. 0 offset)
      (Lit 0x12)
      (Expr.readWord (Lit 0x0) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
  , testCase "read-write-with-extension-to-zero-with-offset" $ assertEqual ""
      -- write word and read it at the same offset of 4
      (Lit 0x12)
      (Expr.readWord (Lit 0x4) (WriteWord (Lit 0x4) (Lit 0x12) mempty))
  , testCase "read-write-with-extension-to-zero-with-offset2" $ assertEqual ""
      -- write word and read it at the same offset of 16
      (Lit 0x12)
      (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
  , testCase "read-word-over-write-byte" $ assertEqual ""
      (ReadWord (Lit 0x4) (AbstractBuf "abs"))
      (Expr.readWord (Lit 0x4) (WriteByte (Lit 0x1) (LitByte 0x12) (AbstractBuf "abs")))
  , testCase "read-word-copySlice-overlap" $ assertEqual ""
      -- we should not recurse into a copySlice if the read index + 32 overlaps the sliced region
      (ReadWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
      (Expr.readWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
  , testCase "read-word-copySlice-after-slice" $ assertEqual "Read word simplification missing!"
      (ReadWord (Lit 100) (AbstractBuf "dst"))
      (Expr.readWord (Lit 100) (CopySlice (Var "srcOff") (Lit 12) (Lit 60) (AbstractBuf "src") (AbstractBuf "dst")))
  , testCase "indexword-MSB" $ assertEqual ""
      -- 31st is the LSB byte (of 32)
      (LitByte 0x78)
      (Expr.indexWord (Lit 31) (Lit 0x12345678))
  , testCase "indexword-LSB" $ assertEqual ""
      -- 0th is the MSB byte (of 32), Lit 0xff22bb... is exactly 32 Bytes.
      (LitByte 0xff)
      (Expr.indexWord (Lit 0) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
  , testCase "indexword-LSB2" $ assertEqual ""
      -- same as above, but with offset 2
      (LitByte 0xbb)
      (Expr.indexWord (Lit 2) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
  , testCase "indexword-oob-sym" $ assertEqual ""
      -- indexWord should return 0 for oob access
      (LitByte 0x0)
      (Expr.indexWord (Lit 100) (JoinBytes
        (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
        (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
        (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
        (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)))
  , testCase "stripbytes-concrete-bug" $ assertEqual ""
      (Expr.simplifyReads (ReadByte (Lit 0) (ConcreteBuf "5")))
      (LitByte 53)

  -- Interval-bounds disjointness for readWord over WriteWord (Add (Lit c) X).

  , testCase "readWord-skip-write-above-and-bounded" $ assertEqual
      "write at Add (Lit 100) (And (Lit 0xff) X) must be skipped when reading at 0"
      (Lit 0)
      (Expr.readWord (Lit 0)
        (WriteWord (Add (Lit 100) (And (Lit 0xff) (Var "x")))
                   (Lit 0x42)
                   mempty))

  , testCase "readWord-skip-write-above-mul-and-bounded" $ assertEqual
      "write at Add (Lit 100) (Mul 32 (And 0xff X)) must be skipped when reading at 0"
      (Lit 0)
      (Expr.readWord (Lit 0)
        (WriteWord (Add (Lit 100) (Mul (Lit 32) (And (Lit 0xff) (Var "x"))))
                   (Lit 0x42)
                   mempty))

  , testCase "readWord-no-skip-write-above-unbounded" $ do
      -- Unbounded X: rule must NOT fire.
      let r = Expr.readWord (Lit 0)
                (WriteWord (Add (Lit 100) (Var "x")) (Lit 0x42) mempty)
      assertBool ("rule fired on unbounded X (unsound): " <> show r)
                 (r /= Lit 0)

  , testCase "readWord-no-skip-write-wrap-risk" $ do
      -- c near maxBound: write region can wrap, so rule must NOT fire.
      let bigC = (maxBound :: W256) - 50
          r = Expr.readWord (Lit 0)
                (WriteWord (Add (Lit bigC) (And (Lit 0xff) (Var "x")))
                           (Lit 0x42)
                           mempty)
      assertBool ("rule fired on wrap-risk write (unsound): " <> show r)
                 (r /= Lit 0)

  , testCase "readWord-no-skip-write-possible-overlap" $ do
      -- Read [80,111] vs write [100,355] overlap; rule must NOT fire.
      let r = Expr.readWord (Lit 80)
                (WriteWord (Add (Lit 100) (And (Lit 0xff) (Var "x")))
                           (Lit 0x42)
                           mempty)
      assertBool ("rule fired on possibly-overlapping write (unsound): " <> show r)
                 (r /= Lit 0)
  ]

basicSimplificationTests :: TestTree
basicSimplificationTests = testGroup "Basic simplification tests"
  [ testCase "simp-readByte1" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (ReadWord (Lit 0x1) (AbstractBuf "stuff2"))
          src = (AbstractBuf "stuff2")
          e = ReadByte (Lit 0x0) (CopySlice srcOffset (Lit 0x10) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqual "" simp (ReadByte (Lit 0x0) (AbstractBuf "dst"))
  , testCase "simp-readByte2" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (Lit 0x1)
          src = (AbstractBuf "stuff2")
          e = ReadByte (Lit 0x0) (CopySlice srcOffset (Lit 0x10) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqual "" (ReadByte (Lit 0x0) (AbstractBuf "dst")) simp
  , testCase "simp-readWord1" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (ReadWord (Lit 0x1) (AbstractBuf "stuff2"))
          src = (AbstractBuf "stuff2")
          e = ReadWord (Lit 0x1) (CopySlice srcOffset (Lit 0x40) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqual "" simp (ReadWord (Lit 0x1) (AbstractBuf "dst"))
  , testCase "simp-readWord2" $ do
    let srcOffset = (ReadWord (Lit 0x12) (AbstractBuf "stuff1"))
        size = (Lit 0x1)
        src = (AbstractBuf "stuff2")
        e = ReadWord (Lit 0x12) (CopySlice srcOffset (Lit 0x50) size src (AbstractBuf "dst"))
        simp = Expr.simplify e
    assertEqual "readWord simplification" (ReadWord (Lit 0x12) (AbstractBuf "dst")) simp
  , testCase "simp-max-buflength" $ do
      let simp = Expr.simplify $ Max (Lit 0) (BufLength (AbstractBuf "txdata"))
      assertEqual "max-buflength rules" simp $ BufLength (AbstractBuf "txdata")
  , testCase "simp-PLT-max" $ do
      let simp = Expr.simplifyProp $ PLT (Max (Lit 5) (BufLength (AbstractBuf "txdata"))) (Lit 99)
      assertEqual "max-buflength rules" simp $ PLT (BufLength (AbstractBuf "txdata")) (Lit 99)
  , testCase "simp-assoc-add1" $ do
      let simp = Expr.simplify $ Add (Add (Var "c") (Var "a")) (Var "b")
      assertEqual "assoc rules" simp $ Add (Var "a") (Add (Var "b") (Var "c"))
  , testCase "simp-assoc-add2" $ do
      let simp = Expr.simplify $ Add (Add (Lit 1) (Var "c")) (Var "b")
      assertEqual "assoc rules" simp $ Add (Lit 1) (Add (Var "b") (Var "c"))
  , testCase "simp-assoc-add3" $ do
      let simp = Expr.simplify $ Add (Lit 1) (Add (Lit 2) (Var "c"))
      assertEqual "assoc rules" simp $ Add (Lit 3) (Var "c")
  , testCase "simp-assoc-add4" $ do
      let simp = Expr.simplify $ Add (Lit 1) (Add (Var "b") (Lit 2))
      assertEqual "assoc rules" simp $ Add (Lit 3) (Var "b")
  , testCase "simp-assoc-add5" $ do
      let simp = Expr.simplify $ Add (Var "a") (Add (Lit 1) (Lit 2))
      assertEqual "assoc rules" simp $ Add (Lit 3) (Var "a")
  , testCase "simp-assoc-add6" $ do
      let simp = Expr.simplify $ Add (Lit 7) (Add (Lit 1) (Lit 2))
      assertEqual "assoc rules" simp $ Lit 10
  , testCase "simp-assoc-add-7" $ do
      let simp = Expr.simplify $ Add (Var "a") (Add (Var "b") (Lit 2))
      assertEqual "assoc rules" simp $ Add (Lit 2) (Add (Var "a") (Var "b"))
  , testCase "simp-assoc-add8" $ do
      let simp = Expr.simplify $ Add (Add (Var "a") (Add (Lit 0x2) (Var "b"))) (Add (Var "c") (Add (Lit 0x2) (Var "d")))
      assertEqual "assoc rules" simp $ Add (Lit 4) (Add (Var "a") (Add (Var "b") (Add (Var "c") (Var "d"))))
  , testCase "simp-assoc-mul1" $ do
      let simp = Expr.simplify $ Mul (Mul (Var "b") (Var "a")) (Var "c")
      assertEqual "assoc rules" simp $ Mul (Var "a") (Mul (Var "b") (Var "c"))
  , testCase "simp-assoc-mul2" $ do
      let simp = Expr.simplify $ Mul (Lit 2) (Mul (Var "a") (Lit 3))
      assertEqual "assoc rules" simp $ Mul (Lit 6) (Var "a")
  , testCase "simp-assoc-xor1" $ do
      let simp = Expr.simplify $ Xor (Lit 2) (Xor (Var "a") (Lit 3))
      assertEqual "assoc rules" simp $ Xor (Lit 1) (Var "a")
  , testCase "simp-assoc-xor2" $ do
      let simp = Expr.simplify $ Xor (Lit 2) (Xor (Var "b") (Xor (Var "a") (Lit 3)))
      assertEqual "assoc rules" simp $ Xor (Lit 1) (Xor (Var "a") (Var "b"))
  , testCase "sign-extend-conc-1" $ do
      let p = Expr.sex (Lit 0) (Lit 0xff)
      assertEqual "" p (Lit Expr.maxLit)
      let p2 = Expr.sex (Lit 30) (Lit 0xff)
      assertEqual "" p2 (Lit 0xff)
      let p3 = Expr.sex (Lit 1) (Lit 0xff)
      assertEqual "" p3 (Lit 0xff)
      let p4 = Expr.sex (Lit 0) (Lit 0x1)
      assertEqual "" p4 (Lit 0x1)
      let p5 = Expr.sex (Lit 0) (Lit 0x0)
      assertEqual "" p5 (Lit 0x0)
  , testCase "writeWord-overflow" $ do
      let simp = Expr.simplify $ ReadByte (Lit 0x0) (WriteWord (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd) (Lit 0x0) (ConcreteBuf "\255\255\255\255"))
      assertEqual "writeWord overflow incorrect" (LitByte 0) simp
  , testCase "buffer-length-copy-slice-beyond-source1" $ do
      let simp = Expr.simplify $ BufLength (CopySlice (Lit 0x2) (Lit 0x2) (Lit 0x1) (ConcreteBuf "a") (ConcreteBuf ""))
      assertEqual "" (Lit 3) simp
  , testCase "copy-slice of size 0 is noop" $ do
        let simp = Expr.simplify $ BufLength $ CopySlice (Lit 0) (Lit 0x10) (Lit 0) (AbstractBuf "buffer") (ConcreteBuf "bimm")
        assertEqual "" (Lit 0x4) simp
  , testCase "length of concrete buffer is concrete" $ do
      let simp = Expr.simplify $ BufLength (ConcreteBuf "ab")
      assertEqual "" (Lit 2) simp
  , testCase "simplify read over write byte" $ do
      let simp = Expr.simplify $ ReadByte (Lit 0xf0000000000000000000000000000000000000000000000000000000000000) (WriteByte (And (Keccak (ConcreteBuf "")) (Lit 0x1)) (LitByte 0) (ConcreteBuf ""))
      assertEqual "" (LitByte 0) simp
  , testCase "storage-slot-single" $ do
      -- this tests that "" and "0"x32 is not equivalent in Keccak
      let x = SLoad (Add (Keccak (ConcreteBuf "")) (Lit 1)) (SStore (Keccak (ConcreteBuf "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")) (Lit 0) (AbstractStore (SymAddr "stuff") Nothing))
      let simplified = Expr.simplify x
      let expected = SLoad (Add (Lit 1) (Keccak (ConcreteBuf ""))) (AbstractStore (SymAddr "stuff") Nothing)
      assertEqual "" expected simplified
  , testCase "word-eq-bug" $ do
      -- This test is actually OK because the simplified takes into account that it's impossible to find a
      -- near-collision in the keccak hash
      let x = (SLoad (Keccak (AbstractBuf "es")) (SStore (Add (Keccak (ConcreteBuf "")) (Lit 0x1)) (Lit 0xacab) (ConcreteStore (Map.empty))))
      let simplified = Expr.simplify x
      -- the write is stripped and the residual read over an empty ConcreteStore is 0 (#1082)
      let expected = Lit 0
      assertEqual "Must be equal, given keccak distance axiom" expected simplified
  , testCase "expr-simp-and-commut-assoc" $ do
      let
        a = And (Lit 4) (And (Lit 5) (Var "a"))
        b = Expr.simplify a
      assertEqual "Must reorder and perform And" (And (Lit 4) (Var "a")) b
  , testCase "expr-simp-order-eqbyte" $ do
      let
        a = EqByte (ReadByte (Lit 1) (AbstractBuf "b")) (ReadByte (Lit 1) (AbstractBuf "a"))
        b = Expr.simplify a
      assertEqual "Must order eqbyte params" b (EqByte (ReadByte (Lit 1) (AbstractBuf "a")) (ReadByte (Lit 1) (AbstractBuf "b")))
  , testCase "prop-simp-expr" $ do
      let
        successPath props = Success props mempty (ConcreteBuf "") mempty
        a = successPath [PEq (Add (Lit 1) (Lit 2)) (Sub (Lit 4) (Lit 1))]
        b = Expr.simplify a
      assertEqual "Must simplify down" (successPath []) b
  , testCase "simp-mul-neg1" $ do
      let simp = Expr.simplify $ Mul (Lit Expr.maxLit) (Var "x")
      assertEqual "mul by -1 is negation" (Sub (Lit 0) (Var "x")) simp
  , testCase "simp-not-plus1" $ do
      let simp = Expr.simplify $ Add (Lit 1) (Not (Var "x"))
      assertEqual "~x + 1 is negation" (Sub (Lit 0) (Var "x")) simp
  , testCase "simp-xor-maxlit-plus1" $ do
      let simp = Expr.simplify $ Add (Lit 1) (Xor (Lit Expr.maxLit) (Var "x"))
      assertEqual "xor(maxLit, x) + 1 is negation" (Sub (Lit 0) (Var "x")) simp
  , testCase "simp-double-not" $ do
      let simp = Expr.simplify $ Not (Not (Var "a"))
      assertEqual "Not should be concretized" (Var "a") simp
  ]

propSimplificationTests :: TestTree
propSimplificationTests = testGroup "prop-simplifications"
  [ testCase "simpProp-concrete-trues" $ do
      let
        t = [PBool True, PBool True]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [] simplified
  , testCase "simpProp-concrete-false1" $ do
      let
        t = [PBool True, PBool False]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , testCase "simpProp-concrete-false2" $ do
      let
        t = [PBool False, PBool False]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , testCase "simpProp-concrete-or-1" $ do
      let
        -- a = 5 && (a=4 || a=3)  -> False
        t = [PEq (Lit 5) (Var "a"), POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 3))]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , ignoreTest $ testCase "simpProp-concrete-or-2" $ do
      let
        -- Currently does not work, because we don't do simplification inside
        --   POr/PAnd using canBeSat
        -- a = 5 && (a=4 || a=5)  -> a=5
        t = [PEq (Lit 5) (Var "a"), POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 5))]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [] simplified
  , testCase "simpProp-concrete-and-1" $ do
      let
        -- a = 5 && (a=4 && a=3)  -> False
        t = [PEq (Lit 5) (Var "a"), PAnd (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 3))]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , testCase "simpProp-concrete-or-of-or" $ do
      let
        -- a = 5 && ((a=4 || a=6) || a=3)  -> False
        t = [PEq (Lit 5) (Var "a"), POr (POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 6))) (PEq (Var "a") (Lit 3))]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , testCase "simpProp-inner-expr-simp" $ do
      let
        -- 5+1 = 6
        t = [PEq (Add (Lit 5) (Lit 1)) (Var "a")]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PEq (Lit 6) (Var "a")] simplified
  , testCase "simpProp-inner-expr-simp-with-canBeSat" $ do
      let
        -- 5+1 = 6, 6 != 7
        t = [PAnd (PEq (Add (Lit 5) (Lit 1)) (Var "a")) (PEq (Var "a") (Lit 7))]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , testCase "simpProp-inner-expr-bitwise-and" $ do
      let
        -- 1 & 2 != 2
        t = [PEq (And (Lit 1) (Lit 2)) (Lit 2)]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PBool False] simplified
  , testCase "simpProp-inner-expr-bitwise-or" $ do
      let
        -- 2 | 4 == 6
        t = [PEq (Or (Lit 2) (Lit 4)) (Lit 6)]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [] simplified
  , testCase "simpProp-constpropagate-1" $ do
      let
        -- 5+1 = 6
        t = [PEq (Add (Lit 5) (Lit 1)) (Var "a"), PEq (Var "b") (Var "a")]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PEq (Lit 6) (Var "a"), PEq (Lit 6) (Var "b")] simplified
  , testCase "simpProp-constpropagate-2" $ do
      let
        -- 5+1 = 6
        t = [PEq (Add (Lit 5) (Lit 1)) (Var "a"), PEq (Var "b") (Var "a"), PEq (Var "c") (Sub (Var "b") (Lit 1))]
        simplified = Expr.simplifyProps t
      assertEqual "Must be equal" [PEq (Lit 6) (Var "a"), PEq (Lit 6) (Var "b"), PEq (Lit 5) (Var "c")] simplified
  , testCase "simpProp-constpropagate-3" $ do
      let
        t = [ PEq (Add (Lit 5) (Lit 1)) (Var "a") -- a = 6
            , PEq (Var "b") (Var "a")             -- b = 6
            , PEq (Var "c") (Sub (Var "b") (Lit 1)) -- c = 5
            , PEq (Var "d") (Sub (Var "b") (Var "c"))] -- d = 1
        simplified = Expr.simplifyProps t
      assertEqual "Must  know d == 1" ((PEq (Lit 1) (Var "d")) `elem` simplified) True
  , testCase "PEq-and-PNot-PEq-1" $ do
      let a = [PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1"))]
      assertEqual "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
  , testCase "PEq-and-PNot-PEq-2" $ do
      let a = [PEq (Var "arg1") (Lit 0x539),PNeg (PEq (Lit 0x539) (Var "arg1"))]
      assertEqual "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
  , testCase "PEq-and-PNot-PEq-3" $ do
      let a = [PEq (Var "arg1") (Lit 0x539),PNeg (PEq (Var "arg1") (Lit 0x539))]
      assertEqual "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
  , testCase "propSimp-no-duplicate1" $ do
      let a = [PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)), PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x63) (Var "arg2"),PEq (Lit 0x539) (Var "arg1"),PEq TxValue (Lit 0x0),PEq (IsZero (Eq (Lit 0x63) (Var "arg2"))) (Lit 0x0)]
      let simp = Expr.simplifyProps a
      assertEqual "must not duplicate" simp (nubOrd simp)
  , testCase "propSimp-no-duplicate2" $ do
      let a = [PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1")),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0)),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqual "must not duplicate" simp (nubOrd simp)
  , testCase "full-order-prop1" $ do
      let a =[PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x63) (Var "arg2"),PEq (Lit 0x539) (Var "arg1"),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x63) (Var "arg2"))) (Lit 0x0),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqual "must not duplicate" simp (nubOrd simp)
  , testCase "dont simplify abstract buffer of size 0" $ do
      let
        p = Expr.peq (BufLength (AbstractBuf "b")) (Lit 0x0)
        simp = Expr.simplifyProp p
      assertEqual "peq does not normalize arguments" (PEq (Lit (0x0)) (BufLength (AbstractBuf "b"))) p
      assertBool "" (p == simp)
  , testCase "simplify comparison GEq" $ do
      let simp = Expr.simplifyProp $ PEq (Lit 0x1) (GEq (Var "v") (Lit 0x2))
      assertEqual "" (PLEq (Lit 0x2) (Var "v")) simp
  , testCase "prop-simp-bool1" $ do
      let
        a = [PAnd (PBool True) (PBool False)]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [PBool False] b
  , testCase "prop-simp-bool2" $ do
      let
        a = [POr (PBool True) (PBool False)]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [] b
  , testCase "prop-simp-LT" $ do
      let
        a = [PLT (Lit 1) (Lit 2)]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [] b
  , testCase "prop-simp-GEq" $ do
      let
        a = [PGEq (Lit 1) (Lit 2)]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [PBool False] b
  , testCase "prop-simp-liteq-false" $ do
      let
        a = [PEq (LitByte 10) (LitByte 12)]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [PBool False] b
  , testCase "prop-simp-concbuf-false" $ do
      let
        a = [PEq (ConcreteBuf "a") (ConcreteBuf "ab")]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [PBool False] b
  , testCase "prop-simp-sort-eq-arguments" $ do
      let
        a = [PEq (Var "a") (Var "b"), PEq (Var "b") (Var "a")]
        b = Expr.simplifyProps a
      assertEqual "Must reorder and nubOrd" (length b) 1
  , testCase "prop-simp-demorgan-pneg-pand" $ do
      let
        a = [PNeg (PAnd (PEq (Lit 4) (Var "a")) (PEq (Lit 5) (Var "b")))]
        b = Expr.simplifyProps a
      assertEqual "Must apply demorgan" b [POr (PNeg (PEq (Lit 4) (Var "a"))) (PNeg (PEq (Lit 5) (Var "b")))]
  , testCase "prop-simp-demorgan-pneg-por" $ do
    let
      a = [PNeg (POr (PEq (Lit 4) (Var "a")) (PEq (Lit 5) (Var "b")))]
      b = Expr.simplifyProps a
    assertEqual "Must apply demorgan" [PNeg (PEq (Lit 4) (Var "a")), PNeg (PEq (Lit 5) (Var "b"))] b
  , testCase "prop-simp-lit0-or-both-0" $ do
    let
      a = [PEq (Lit 0) (Or (Var "a") (Var "b"))]
      b = Expr.simplifyProps a
    assertEqual "Must apply demorgan" [PEq (Lit 0) (Var "a"), PEq (Lit 0) (Var "b")] b
  , testCase "prop-simp-impl" $ do
      let
        a = [PImpl (PBool False) (PEq (Var "abc") (Var "bcd"))]
        b = Expr.simplifyProps a
      assertEqual "Must simplify down" [] b
  ]

constantPropagationTests :: TestTree
constantPropagationTests = testGroup "isUnsat-concrete-tests"
  [
    testCase "disjunction-left-false" $
    let
      t = [PEq (Var "x") (Lit 1), POr (PEq (Var "x") (Lit 0)) (PEq (Var "y") (Lit 1)), PEq (Var "y") (Lit 2)]
      propagated = Expr.constPropagate t
    in
    mustContainFalse propagated
  , testCase "disjunction-right-false" $
      let
        t = [PEq (Var "x") (Lit 1), POr (PEq (Var "y") (Lit 1)) (PEq (Var "x") (Lit 0)), PEq (Var "y") (Lit 2)]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  , testCase "disjunction-both-false" $
      let
        t = [PEq (Var "x") (Lit 1), POr (PEq (Var "x") (Lit 2)) (PEq (Var "x") (Lit 0)), PEq (Var "y") (Lit 2)]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  , ignoreTest $ testCase "disequality-and-equality" $
      let
        t = [PNeg (PEq (Lit 1) (Var "arg1")), PEq (Lit 1) (Var "arg1")]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  , testCase "equality-and-disequality" $
      let
        t = [PEq (Lit 1) (Var "arg1"), PNeg (PEq (Lit 1) (Var "arg1"))]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  ]
  where
    mustContainFalse props = assertBool "Expression must simplify to False" $ (PBool False) `elem` props

boundPropagationTests :: TestTree
boundPropagationTests =  testGroup "inequality-propagation-tests" [
  testCase "PLT-detects-impossible-constraint" $
  let
    -- x < 0 is impossible for unsigned integers
    t = [PLT (Var "x") (Lit 0)]
    propagated = Expr.constPropagate t
  in
    mustContainFalse propagated
  , testCase "PLT-overflow-check" $
      let
        -- maxLit < y is impossible
        t = [PLT (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Var "y")]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "PGT-detects-impossible-constraint" $
      let
        -- x > maxLit is impossible
        t = [PGT (Var "x") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "PGT-overflow-check" $
      let
        -- 0 > y is impossible
        t = [PGT (Lit 0) (Var "y")]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-conflict-detection-narrow" $
      let
        -- x < 2 && x > 5 is impossible
        t = [PLT (Var "x") (Lit 2), PGT (Var "x") (Lit 5)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-conflict-detection-wide" $
      let
        -- x < 5 && x > 10 is impossible
        t = [PLT (Var "x") (Lit 5), PGT (Var "x") (Lit 10)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-tight-bounds-satisfied" $
      let
        -- x >= 5 && x <= 5 and x == 5 should be consistent
        t = [PGEq (Var "x") (Lit 5), PLEq (Var "x") (Lit 5), PEq (Var "x") (Lit 5)]
        propagated = Expr.constPropagate t
      in
        mustNotContainFalse propagated
  , testCase "inequality-tight-bounds-violated" $
      let
        -- x >= 5 && x <= 5 and x != 5 should be inconsistent
        t = [PGEq (Var "x") (Lit 5), PLEq (Var "x") (Lit 5), PNeg (PEq (Var "x") (Lit 5))]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-with-existing-equality-consistent" $
      let
        -- x == 5 && x < 10 is consistent
        t = [PEq (Var "x") (Lit 5), PLT (Var "x") (Lit 10)]
        propagated = Expr.constPropagate t
      in
        mustNotContainFalse propagated
  , testCase "inequality-with-existing-equality-inconsistent" $
      let
        -- x == 5 && x < 5 is inconsistent
        t = [PEq (Var "x") (Lit 5), PLT (Var "x") (Lit 5)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
    ]
  where
    mustContainFalse props = assertBool "Expression must simplify to False" $ (PBool False) `elem` props
    mustNotContainFalse props = assertBool "Expression must NOT simplify to False" $ (PBool False) `notElem` props

comparisonTests :: TestTree
comparisonTests = testGroup "Prop comparison tests"
  [
    testCase "nubOrd-Prop-PLT" $ do
        let a = [ PLT (Lit 0x0) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))
                , PLT (Lit 0x1) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))
                , PLT (Lit 0x2) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))
                , PLT (Lit 0x0) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))]
        let simp = nubOrd a
            simp2 = List.nub a
        assertEqual "Must be 3-length" 3 (length simp)
        assertEqual "Must be 3-length" 3 (length simp2)
    , testCase "nubOrd-Prop-PEq" $ do
        let a = [ PEq (Lit 0x0) (ReadWord (Lit 0x0) (AbstractBuf "txdata"))
                , PEq (Lit 0x0) (ReadWord (Lit 0x1) (AbstractBuf "txdata"))
                , PEq (Lit 0x0) (ReadWord (Lit 0x2) (AbstractBuf "txdata"))
                , PEq (Lit 0x0) (ReadWord (Lit 0x0) (AbstractBuf "txdata"))]
        let simp = nubOrd a
            simp2 = List.nub a
        assertEqual "Must be 3-length" 3 (length simp)
        assertEqual "Must be 3-length" 3 (length simp2)
  ]

signExtendTests :: TestTree
signExtendTests = testGroup "SEx tests"
  [
    -- these should run without simplification to test the SMT solver's ability to handle sign extension
    testCase "sign-extend-1" $ do
        let p = (PEq (Lit 1) (SLT (Lit 1774544) (SEx (Lit 2) (Lit 1774567))))
        let simp = Expr.simplifyProps [p]
        assertEqual "Must simplify to PBool True" simp []
        res <- checkSat p
        assertBool "Must be satisfiable!" $ isSat res
  , testCase "sign-extend-2" $ do
      let p = (PEq (Lit 1) (SLT (SEx (Lit 2) (Var "arg1")) (Lit 0)))
      res <- checkSat p
      assertBool "Must be satisfiable!" $ isSat res
  , testCase "sign-extend-3" $ do
      let p = PAnd
              (PEq (Lit 1) (SLT (SEx (Lit 2) (Var "arg1")) (Lit 115792089237316195423570985008687907853269984665640564039457584007913128752664)))
              (PEq (Var "arg1") (SEx (Lit 2) (Var "arg1")))
      res <- checkSat p
      assertBool "Must be satisfiable!" $ isSat res
  , testProperty "sign-extend-vs-smt" $ withMaxSuccess 30 $ \(a :: W256, b :: W256) -> ioProperty $ do
      let p = (PEq (Var "arg1") (SEx (Lit (a `mod` 50)) (Lit b)))
      Cex cex <- checkSat p
      let Right (Lit v1) = subModel cex (Var "arg1")
      let [PEq (Lit v2) (Var "arg1")] = Expr.simplifyProps [p]
      pure $ v1 === v2
  ]

concretizationTests :: TestTree
concretizationTests = testGroup "Concretization tests"
  [ -- Arithmetic operations
    testCase "conc-add" $ do
      let simp = Expr.simplify $ Add (Lit 0x10) (Lit 0x20)
      assertEqual "Add should be concretized" (Lit 0x30) simp
  , testCase "conc-add-overflow" $ do
      let simp = Expr.simplify $ Add (Lit Expr.maxLit) (Lit 1)
      assertEqual "Add overflow should wrap" (Lit 0) simp
  , testCase "conc-sub" $ do
      let simp = Expr.simplify $ Sub (Lit 0x30) (Lit 0x10)
      assertEqual "Sub should be concretized" (Lit 0x20) simp
  , testCase "conc-sub-underflow" $ do
      let simp = Expr.simplify $ Sub (Lit 0) (Lit 1)
      assertEqual "Sub underflow should wrap" (Lit Expr.maxLit) simp
  , testCase "conc-mul" $ do
      let simp = Expr.simplify $ Mul (Lit 0x10) (Lit 0x20)
      assertEqual "Mul should be concretized" (Lit 0x200) simp
  , testCase "conc-mul-zero" $ do
      let simp = Expr.simplify $ Mul (Lit 0) (Lit 0x1234)
      assertEqual "Mul by zero" (Lit 0) simp
  , testCase "conc-div" $ do
      let simp = Expr.simplify $ Div (Lit 0x20) (Lit 0x10)
      assertEqual "Div should be concretized" (Lit 0x2) simp
  , testCase "conc-div-by-zero" $ do
      let simp = Expr.simplify $ Div (Lit 0x20) (Lit 0)
      assertEqual "Div by zero should be 0" (Lit 0) simp
  , testCase "conc-sdiv" $ do
      -- -6 / 3 = -2 in signed arithmetic
      -- -6 in W256 is maxLit - 5
      let neg6 = Expr.maxLit - 5
          neg2 = Expr.maxLit - 1
          simp = Expr.simplify $ SDiv (Lit neg6) (Lit 3)
      assertEqual "SDiv should handle signed division" (Lit neg2) simp
  , testCase "conc-sdiv-by-zero" $ do
      let simp = Expr.simplify $ SDiv (Lit 0x20) (Lit 0)
      assertEqual "SDiv by zero should be 0" (Lit 0) simp
  , testCase "conc-mod" $ do
      let simp = Expr.simplify $ Mod (Lit 0x25) (Lit 0x10)
      assertEqual "Mod should be concretized" (Lit 0x5) simp
  , testCase "conc-mod-by-zero" $ do
      let simp = Expr.simplify $ Mod (Lit 0x25) (Lit 0)
      assertEqual "Mod by zero should be 0" (Lit 0) simp
  , testCase "conc-smod" $ do
      -- -7 smod 3 = -1 in signed arithmetic
      let neg7 = Expr.maxLit - 6
          neg1 = Expr.maxLit
          simp = Expr.simplify $ SMod (Lit neg7) (Lit 3)
      assertEqual "SMod should handle signed mod" (Lit neg1) simp
  , testCase "conc-smod-by-zero" $ do
      let simp = Expr.simplify $ SMod (Lit 0x25) (Lit 0)
      assertEqual "SMod by zero should be 0" (Lit 0) simp
  , testCase "conc-addmod" $ do
      let simp = Expr.simplify $ AddMod (Lit 10) (Lit 10) (Lit 8)
      assertEqual "AddMod should be concretized" (Lit 4) simp
  , testCase "conc-addmod-by-zero" $ do
      let simp = Expr.simplify $ AddMod (Lit 10) (Lit 10) (Lit 0)
      assertEqual "AddMod by zero should be 0" (Lit 0) simp
  , testCase "conc-mulmod" $ do
      let simp = Expr.simplify $ MulMod (Lit 10) (Lit 10) (Lit 8)
      assertEqual "MulMod should be concretized" (Lit 4) simp
  , testCase "conc-mulmod-by-zero" $ do
      let simp = Expr.simplify $ MulMod (Lit 10) (Lit 10) (Lit 0)
      assertEqual "MulMod by zero should be 0" (Lit 0) simp
  , testCase "conc-exp" $ do
      let simp = Expr.simplify $ Exp (Lit 2) (Lit 10)
      assertEqual "Exp should be concretized" (Lit 1024) simp
  , testCase "conc-exp-zero" $ do
      let simp = Expr.simplify $ Exp (Lit 2) (Lit 0)
      assertEqual "x^0 should be 1" (Lit 1) simp
  , testCase "conc-sex" $ do
      -- sign-extend byte 0 of 0xff -> all 1s (since bit 7 is set)
      let simp = Expr.simplify $ SEx (Lit 0) (Lit 0xff)
      assertEqual "SEx should be concretized" (Lit Expr.maxLit) simp
  , testCase "conc-sex-no-extend" $ do
      -- sign-extend byte 30 of 0xff -> 0xff (bit 247 is not set)
      let simp = Expr.simplify $ SEx (Lit 30) (Lit 0xff)
      assertEqual "SEx should not extend" (Lit 0xff) simp

    -- Comparison operations
  , testCase "conc-lt-true" $ do
      let simp = Expr.simplify $ LT (Lit 1) (Lit 2)
      assertEqual "LT true" (Lit 1) simp
  , testCase "conc-lt-false" $ do
      let simp = Expr.simplify $ LT (Lit 2) (Lit 1)
      assertEqual "LT false" (Lit 0) simp
  , testCase "conc-gt-true" $ do
      let simp = Expr.simplify $ GT (Lit 2) (Lit 1)
      assertEqual "GT true" (Lit 1) simp
  , testCase "conc-gt-false" $ do
      let simp = Expr.simplify $ GT (Lit 1) (Lit 2)
      assertEqual "GT false" (Lit 0) simp
  , testCase "conc-leq-true" $ do
      let simp = Expr.simplify $ LEq (Lit 1) (Lit 1)
      assertEqual "LEq equal" (Lit 1) simp
  , testCase "conc-leq-false" $ do
      let simp = Expr.simplify $ LEq (Lit 2) (Lit 1)
      assertEqual "LEq false" (Lit 0) simp
  , testCase "conc-geq-true" $ do
      let simp = Expr.simplify $ GEq (Lit 2) (Lit 1)
      assertEqual "GEq true" (Lit 1) simp
  , testCase "conc-geq-false" $ do
      let simp = Expr.simplify $ GEq (Lit 1) (Lit 2)
      assertEqual "GEq false" (Lit 0) simp
  , testCase "conc-slt-true" $ do
      -- -1 < 0 in signed: maxLit < 0
      let simp = Expr.simplify $ SLT (Lit Expr.maxLit) (Lit 0)
      assertEqual "SLT true (negative < zero)" (Lit 1) simp
  , testCase "conc-slt-false" $ do
      let simp = Expr.simplify $ SLT (Lit 0) (Lit Expr.maxLit)
      assertEqual "SLT false (zero < negative)" (Lit 0) simp
  , testCase "conc-sgt-true" $ do
      let simp = Expr.simplify $ SGT (Lit 0) (Lit Expr.maxLit)
      assertEqual "SGT true (zero > negative)" (Lit 1) simp
  , testCase "conc-sgt-false" $ do
      let simp = Expr.simplify $ SGT (Lit Expr.maxLit) (Lit 0)
      assertEqual "SGT false (negative > zero)" (Lit 0) simp
  , testCase "conc-eq-true" $ do
      let simp = Expr.simplify $ Eq (Lit 42) (Lit 42)
      assertEqual "Eq true" (Lit 1) simp
  , testCase "conc-eq-false" $ do
      let simp = Expr.simplify $ Eq (Lit 42) (Lit 43)
      assertEqual "Eq false" (Lit 0) simp
  , testCase "conc-iszero-true" $ do
      let simp = Expr.simplify $ IsZero (Lit 0)
      assertEqual "IsZero of 0" (Lit 1) simp
  , testCase "conc-iszero-false" $ do
      let simp = Expr.simplify $ IsZero (Lit 42)
      assertEqual "IsZero of non-zero" (Lit 0) simp

    -- Bitwise operations
  , testCase "conc-and" $ do
      let simp = Expr.simplify $ And (Lit 0xff00) (Lit 0x0ff0)
      assertEqual "And should be concretized" (Lit 0x0f00) simp
  , testCase "conc-or" $ do
      let simp = Expr.simplify $ Or (Lit 0xff00) (Lit 0x00ff)
      assertEqual "Or should be concretized" (Lit 0xffff) simp
  , testCase "conc-xor" $ do
      let simp = Expr.simplify $ Xor (Lit 0xff00) (Lit 0x0ff0)
      assertEqual "Xor should be concretized" (Lit 0xf0f0) simp
  , testCase "conc-xor-same" $ do
      let simp = Expr.simplify $ Xor (Lit 0x1234) (Lit 0x1234)
      assertEqual "Xor of same values is 0" (Lit 0) simp
  , testCase "conc-xor-self" $ do
      let simp = Expr.simplify $ Xor (Var "x") (Var "x")
      assertEqual "x xor x = 0" (Lit 0) simp
  , testCase "conc-not" $ do
      let simp = Expr.simplify $ Not (Lit 0x55)
      assertEqual "Not should be concretized" (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaa) simp
  , testCase "conc-not-zero" $ do
      let simp = Expr.simplify $ Not (Lit 0)
      assertEqual "Not of 0 is maxLit" (Lit Expr.maxLit) simp
  , testCase "conc-shl" $ do
      let simp = Expr.simplify $ SHL (Lit 4) (Lit 0xff)
      assertEqual "SHL should be concretized" (Lit 0xff0) simp
  , testCase "conc-shl-overflow" $ do
      let simp = Expr.simplify $ SHL (Lit 256) (Lit 0xff)
      assertEqual "SHL by 256 should be 0" (Lit 0) simp
  , testCase "conc-shr" $ do
      let simp = Expr.simplify $ SHR (Lit 4) (Lit 0xff)
      assertEqual "SHR should be concretized" (Lit 0xf) simp
  , testCase "conc-shr-overflow" $ do
      let simp = Expr.simplify $ SHR (Lit 257) (Lit 0xff)
      assertEqual "SHR by >256 should be 0" (Lit 0) simp
  , testCase "conc-sar-positive" $ do
      let simp = Expr.simplify $ SAR (Lit 4) (Lit 0xff)
      assertEqual "SAR positive should be like SHR" (Lit 0xf) simp
  , testCase "conc-sar-negative" $ do
      -- SAR of a negative number (MSB set) should fill with 1s
      -- maxLit has MSB set, shifting right by 4 should fill top 4 bits with 1s
      let simp = Expr.simplify $ SAR (Lit 4) (Lit Expr.maxLit)
      assertEqual "SAR negative should fill with 1s" (Lit Expr.maxLit) simp
  , testCase "conc-sar-large-shift-negative" $ do
      -- SAR by >= 255 of negative number -> maxBound (all 1s)
      let simp = Expr.simplify $ SAR (Lit 255) (Lit Expr.maxLit)
      assertEqual "SAR large shift negative" (Lit Expr.maxLit) simp
  , testCase "conc-sar-large-shift-positive" $ do
      -- SAR by >= 255 of positive number -> 0
      let simp = Expr.simplify $ SAR (Lit 255) (Lit 1)
      assertEqual "SAR large shift positive" (Lit 0) simp
  , testCase "conc-clz-zero" $ do
      let simp = Expr.simplify $ CLZ (Lit 0)
      assertEqual "CLZ of 0 should be 256" (Lit 256) simp
  , testCase "conc-clz-one" $ do
      let simp = Expr.simplify $ CLZ (Lit 1)
      assertEqual "CLZ of 1 should be 255" (Lit 255) simp
  , testCase "conc-clz-max" $ do
      let simp = Expr.simplify $ CLZ (Lit Expr.maxLit)
      assertEqual "CLZ of maxLit should be 0" (Lit 0) simp

    -- Min/Max operations
  , testCase "conc-min" $ do
      let simp = Expr.simplify $ Min (Lit 5) (Lit 10)
      assertEqual "Min should be concretized" (Lit 5) simp
  , testCase "conc-max" $ do
      let simp = Expr.simplify $ Max (Lit 5) (Lit 10)
      assertEqual "Max should be concretized" (Lit 10) simp

    -- Byte-level operations
  , testCase "conc-eqbyte-true" $ do
      let simp = Expr.eqByte (LitByte 0x42) (LitByte 0x42)
      assertEqual "EqByte equal" (Lit 1) simp
  , testCase "conc-eqbyte-false" $ do
      let simp = Expr.eqByte (LitByte 0x42) (LitByte 0x43)
      assertEqual "EqByte not equal" (Lit 0) simp
  , testCase "conc-joinbytes" $ do
      let simp = Expr.joinBytes (replicate 31 (LitByte 0) ++ [LitByte 0x42])
      assertEqual "JoinBytes all concrete" (Lit 0x42) simp
  , testCase "conc-joinbytes-msb" $ do
      let simp = Expr.joinBytes (LitByte 0xff : replicate 31 (LitByte 0))
      assertEqual "JoinBytes MSB set" (Lit 0xff00000000000000000000000000000000000000000000000000000000000000) simp

  -- Keccak
  , testCase "conc-keccak" $ do
      let simp = Expr.concKeccakSimpExpr $ Keccak (ConcreteBuf "")
      assertEqual "Keccak of empty should be concretized" (Lit (keccak' "")) simp
  , testCase "conc-keccak-nonempty" $ do
      let simp = Expr.concKeccakSimpExpr $ Keccak (ConcreteBuf "hello")
      assertEqual "Keccak of hello should be concretized" (Lit (keccak' "hello")) simp

  -- PEq simplifyProp over Props
  , testCase "conc-peq-lit-true" $ do
      let simp = Expr.simplifyProp $ PEq (Lit 42) (Lit 42)
      assertEqual "PEq Lit equal" (PBool True) simp
  , testCase "conc-peq-lit-false" $ do
      let simp = Expr.simplifyProp $ PEq (Lit 42) (Lit 43)
      assertEqual "PEq Lit not equal" (PBool False) simp
  , testCase "conc-peq-litaddr-true" $ do
      let simp = Expr.simplifyProp $ PEq (LitAddr 0x1234) (LitAddr 0x1234)
      assertEqual "PEq LitAddr equal" (PBool True) simp
  , testCase "conc-peq-litaddr-false" $ do
      let simp = Expr.simplifyProp $ PEq (LitAddr 0x1234) (LitAddr 0x5678)
      assertEqual "PEq LitAddr not equal" (PBool False) simp
  , testCase "conc-peq-litbyte-true" $ do
      let simp = Expr.simplifyProp $ PEq (LitByte 0xab) (LitByte 0xab)
      assertEqual "PEq LitByte equal" (PBool True) simp
  , testCase "conc-peq-litbyte-false" $ do
      let simp = Expr.simplifyProp $ PEq (LitByte 0xab) (LitByte 0xcd)
      assertEqual "PEq LitByte not equal" (PBool False) simp
  , testCase "conc-peq-concretebuf-true" $ do
      let simp = Expr.simplifyProp $ PEq (ConcreteBuf "hello") (ConcreteBuf "hello")
      assertEqual "PEq ConcreteBuf equal" (PBool True) simp
  , testCase "conc-peq-concretebuf-false" $ do
      let simp = Expr.simplifyProp $ PEq (ConcreteBuf "hello") (ConcreteBuf "world")
      assertEqual "PEq ConcreteBuf not equal" (PBool False) simp
  , testCase "conc-peq-concretestore-true" $ do
      let simp = Expr.simplifyProp $ PEq (ConcreteStore (Map.fromList [(1, 2)])) (ConcreteStore (Map.fromList [(1, 2)]))
      assertEqual "PEq ConcreteStore equal" (PBool True) simp
  , testCase "conc-peq-concretestore-false" $ do
      let simp = Expr.simplifyProp $ PEq (ConcreteStore (Map.fromList [(1, 2)])) (ConcreteStore (Map.fromList [(1, 3)]))
      assertEqual "PEq ConcreteStore not equal" (PBool False) simp
  , testCase "conc-peq-var-self" $ do
      let simp = Expr.simplifyProp $ PEq (Var "x") (Var "x")
      assertEqual "PEq Var self-equal" (PBool True) simp
  , testCase "conc-peq-symaddr-self" $ do
      let simp = Expr.simplifyProp $ PEq (SymAddr "a") (SymAddr "a")
      assertEqual "PEq SymAddr self-equal" (PBool True) simp
  , testCase "conc-peq-abstractbuf-self" $ do
      let simp = Expr.simplifyProp $ PEq (AbstractBuf "b") (AbstractBuf "b")
      assertEqual "PEq AbstractBuf self-equal" (PBool True) simp
  , testCase "conc-peq-abstractstore-self" $ do
      let simp = Expr.simplifyProp $ PEq (AbstractStore (LitAddr 0x1) Nothing) (AbstractStore (LitAddr 0x1) Nothing)
      assertEqual "PEq AbstractStore self-equal" (PBool True) simp
  -- Other simplifications over Props
  , testCase "conc-plt-true" $ do
      let simp = Expr.simplifyProp $ PLT (Lit 1) (Lit 2)
      assertEqual "PLT true" (PBool True) simp
  , testCase "conc-plt-false" $ do
      let simp = Expr.simplifyProp $ PLT (Lit 2) (Lit 1)
      assertEqual "PLT false" (PBool False) simp
  , testCase "conc-plt-equal" $ do
      let simp = Expr.simplifyProp $ PLT (Lit 5) (Lit 5)
      assertEqual "PLT equal is false" (PBool False) simp
  , testCase "conc-pgt-true" $ do
      let simp = Expr.simplifyProp $ PGT (Lit 2) (Lit 1)
      -- PGT a b is simplified to PLT b a
      assertEqual "PGT true" (PBool True) simp
  , testCase "conc-pgt-false" $ do
      let simp = Expr.simplifyProp $ PGT (Lit 1) (Lit 2)
      assertEqual "PGT false" (PBool False) simp
  , testCase "conc-pgeq-true" $ do
      let simp = Expr.simplifyProp $ PGEq (Lit 2) (Lit 1)
      -- PGEq a b is simplified to PLEq b a
      assertEqual "PGEq true" (PBool True) simp
  , testCase "conc-pgeq-false" $ do
      let simp = Expr.simplifyProp $ PGEq (Lit 1) (Lit 2)
      assertEqual "PGEq false" (PBool False) simp
  , testCase "conc-pgeq-equal" $ do
      let simp = Expr.simplifyProp $ PGEq (Lit 5) (Lit 5)
      assertEqual "PGEq equal is true" (PBool True) simp
  , testCase "conc-prop-pleq-true" $ do
      let simp = Expr.simplifyProp $ PLEq (Lit 1) (Lit 2)
      assertEqual "PLEq true" (PBool True) simp
  , testCase "conc-prop-pleq-false" $ do
      let simp = Expr.simplifyProp $ PLEq (Lit 2) (Lit 1)
      assertEqual "PLEq false" (PBool False) simp
  , testCase "conc-pneg-true" $ do
      let simp = Expr.simplifyProp $ PNeg (PBool True)
      assertEqual "PNeg True" (PBool False) simp
  , testCase "conc-pneg-false" $ do
      let simp = Expr.simplifyProp $ PNeg (PBool False)
      assertEqual "PNeg False" (PBool True) simp
  , testCase "conc-pand-true" $ do
      let simp = Expr.simplifyProp $ PAnd (PBool True) (PBool True)
      assertEqual "PAnd True True" (PBool True) simp
  , testCase "conc-pand-false" $ do
      let simp = Expr.simplifyProp $ PAnd (PBool True) (PBool False)
      assertEqual "PAnd True False" (PBool False) simp
  , testCase "conc-por-true" $ do
      let simp = Expr.simplifyProp $ POr (PBool False) (PBool True)
      assertEqual "POr False True" (PBool True) simp
  , testCase "conc-por-false" $ do
      let simp = Expr.simplifyProp $ POr (PBool False) (PBool False)
      assertEqual "POr False False" (PBool False) simp
  , testCase "conc-pimpl-true-true" $ do
      let simp = Expr.simplifyProp $ PImpl (PBool True) (PBool True)
      assertEqual "PImpl True True" (PBool True) simp
  , testCase "conc-pimpl-true-false" $ do
      let simp = Expr.simplifyProp $ PImpl (PBool True) (PBool False)
      assertEqual "PImpl True False" (PBool False) simp
  , testCase "conc-pimpl-false-any" $ do
      let simp = Expr.simplifyProp $ PImpl (PBool False) (PBool False)
      assertEqual "PImpl False _ is True" (PBool True) simp

    -- WAddr concretization
  , testCase "conc-waddr" $ do
      let simp = Expr.simplify $ WAddr (LitAddr 0x1234)
      assertEqual "WAddr LitAddr should be concretized" (Lit 0x1234) simp

    -- BufLength concretization
  , testCase "conc-buflength-empty" $ do
      let simp = Expr.simplify $ BufLength (ConcreteBuf "")
      assertEqual "BufLength of empty" (Lit 0) simp
  , testCase "conc-buflength-nonempty" $ do
      let simp = Expr.simplify $ BufLength (ConcreteBuf "hello")
      assertEqual "BufLength of hello" (Lit 5) simp

    -- ITE with concrete condition
  , testCase "conc-ite-true" $ do
      let simp = Expr.simplify $ ITE (Lit 1) (Lit 42) (Lit 99)
      assertEqual "ITE true takes true branch" (Lit 42) simp
  , testCase "conc-ite-false" $ do
      let simp = Expr.simplify $ ITE (Lit 0) (Lit 42) (Lit 99)
      assertEqual "ITE false takes false branch" (Lit 99) simp
  , testCase "conc-ite-same-branches" $ do
      let simp = Expr.simplify $ ITE (Var "c") (Lit 42) (Lit 42)
      assertEqual "ITE with same branches" (Lit 42) simp

    -- Eq in simplifier (structural equality)
  , testCase "conc-eq-self" $ do
      let simp = Expr.simplify $ Eq (Var "x") (Var "x")
      assertEqual "Eq self" (Lit 1) simp

    -- GT/LT/SLT/SGT special cases
  , testCase "conc-lt-zero" $ do
      let simp = Expr.simplify $ LT (Var "x") (Lit 0)
      assertEqual "Nothing is < 0 unsigned" (Lit 0) simp
  , testCase "conc-lt-maxlit" $ do
      let simp = Expr.simplify $ LT (Lit Expr.maxLit) (Var "x")
      assertEqual "maxLit is never < anything" (Lit 0) simp
  , testCase "conc-gt-maxlit" $ do
      -- GT _ maxLit becomes lt maxLit _ which is 0
      let simp = Expr.simplify $ GT (Var "x") (Lit Expr.maxLit)
      assertEqual "Nothing is > maxLit" (Lit 0) simp
  , testCase "conc-gt-zero" $ do
      let simp = Expr.simplify $ GT (Lit 0) (Var "x")
      assertEqual "0 is not > anything unsigned" (Lit 0) simp
  , testCase "conc-slt-min-signed" $ do
      let simp = Expr.simplify $ SLT (Var "x") (Lit Expr.minLitSigned)
      assertEqual "Nothing is SLT minLitSigned" (Lit 0) simp
  , testCase "conc-slt-max-signed" $ do
      let simp = Expr.simplify $ SLT (Lit Expr.maxLitSigned) (Var "x")
      assertEqual "maxLitSigned is not SLT anything" (Lit 0) simp
  , testCase "conc-sgt-min-signed" $ do
      let simp = Expr.simplify $ SGT (Lit Expr.minLitSigned) (Var "x")
      assertEqual "minLitSigned is not SGT anything" (Lit 0) simp
  , testCase "conc-sgt-max-signed" $ do
      let simp = Expr.simplify $ SGT (Var "x") (Lit Expr.maxLitSigned)
      assertEqual "Nothing is SGT maxLitSigned" (Lit 0) simp

    -- Sub self
  , testCase "conc-sub-self" $ do
      let simp = Expr.simplify $ Sub (Var "x") (Var "x")
      assertEqual "x - x = 0" (Lit 0) simp

    -- Div/SDiv special cases
  , testCase "conc-div-zero-num" $ do
      let simp = Expr.simplify $ Div (Lit 0) (Var "x")
      assertEqual "0 / x = 0" (Lit 0) simp
  , testCase "conc-div-zero-denom" $ do
      let simp = Expr.simplify $ Div (Var "x") (Lit 0)
      assertEqual "x / 0 = 0" (Lit 0) simp
  , testCase "conc-div-by-one" $ do
      let simp = Expr.simplify $ Div (Var "x") (Lit 1)
      assertEqual "x / 1 = x" (Var "x") simp
  , testCase "conc-sdiv-zero-num" $ do
      let simp = Expr.simplify $ SDiv (Lit 0) (Var "x")
      assertEqual "0 sdiv x = 0" (Lit 0) simp
  , testCase "conc-sdiv-zero-denom" $ do
      let simp = Expr.simplify $ SDiv (Var "x") (Lit 0)
      assertEqual "x sdiv 0 = 0" (Lit 0) simp
  , testCase "conc-sdiv-by-one" $ do
      let simp = Expr.simplify $ SDiv (Var "x") (Lit 1)
      assertEqual "x sdiv 1 = x" (Var "x") simp

    -- Mod/SMod special cases
  , testCase "conc-mod-zero-denom" $ do
      let simp = Expr.simplify $ Mod (Var "x") (Lit 0)
      assertEqual "x mod 0 = 0" (Lit 0) simp
  , testCase "conc-mod-zero-num" $ do
      let simp = Expr.simplify $ Mod (Lit 0) (Var "x")
      assertEqual "0 mod x = 0" (Lit 0) simp
  , testCase "conc-mod-self" $ do
      let simp = Expr.simplify $ Mod (Var "x") (Var "x")
      assertEqual "x mod x = 0" (Lit 0) simp
  , testCase "conc-smod-zero-denom" $ do
      let simp = Expr.simplify $ SMod (Var "x") (Lit 0)
      assertEqual "x smod 0 = 0" (Lit 0) simp
  , testCase "conc-smod-zero-num" $ do
      let simp = Expr.simplify $ SMod (Lit 0) (Var "x")
      assertEqual "0 smod x = 0" (Lit 0) simp
  , testCase "conc-smod-self" $ do
      let simp = Expr.simplify $ SMod (Var "x") (Var "x")
      assertEqual "x smod x = 0" (Lit 0) simp
  , testCase "conc-mod-one" $ do
      let simp = Expr.simplify $ Mod (Var "x") (Lit 1)
      assertEqual "x mod 1 = 0" (Lit 0) simp
  , testCase "conc-smod-one" $ do
      let simp = Expr.simplify $ SMod (Var "x") (Lit 1)
      assertEqual "x smod 1 = 0" (Lit 0) simp

    -- MulMod/AddMod zero cases
  , testCase "conc-mulmod-zero-first" $ do
      let simp = Expr.simplify $ MulMod (Lit 0) (Var "y") (Var "z")
      assertEqual "0 * y mod z = 0" (Lit 0) simp
  , testCase "conc-mulmod-zero-second" $ do
      let simp = Expr.simplify $ MulMod (Var "x") (Lit 0) (Var "z")
      assertEqual "x * 0 mod z = 0" (Lit 0) simp
  , testCase "conc-mulmod-zero-mod" $ do
      let simp = Expr.simplify $ MulMod (Var "x") (Var "y") (Lit 0)
      assertEqual "x * y mod 0 = 0" (Lit 0) simp
  , testCase "conc-addmod-zero-mod" $ do
      let simp = Expr.simplify $ AddMod (Var "x") (Var "y") (Lit 0)
      assertEqual "x + y mod 0 = 0" (Lit 0) simp

    -- Exp special cases
  , testCase "conc-exp-zero-exp" $ do
      let simp = Expr.simplify $ Exp (Var "x") (Lit 0)
      assertEqual "x^0 = 1" (Lit 1) simp
  , testCase "conc-exp-one-exp" $ do
      let simp = Expr.simplify $ Exp (Var "x") (Lit 1)
      assertEqual "x^1 = x" (Var "x") simp
  , testCase "conc-exp-one-base" $ do
      let simp = Expr.simplify $ Exp (Lit 1) (Var "x")
      assertEqual "1^x = 1" (Lit 1) simp

    -- Mul special cases
  , testCase "conc-mul-zero-left" $ do
      let simp = Expr.simplify $ Mul (Lit 0) (Var "x")
      assertEqual "0 * x = 0" (Lit 0) simp
  , testCase "conc-mul-one" $ do
      let simp = Expr.simplify $ Mul (Lit 1) (Var "x")
      assertEqual "1 * x = x" (Var "x") simp

    -- And/Or special cases
  , testCase "conc-and-zero" $ do
      let simp = Expr.simplify $ And (Lit 0) (Var "x")
      assertEqual "0 & x = 0" (Lit 0) simp
  , testCase "conc-and-maxlit" $ do
      let simp = Expr.simplify $ And (Lit Expr.maxLit) (Var "x")
      assertEqual "maxLit & x = x" (Var "x") simp
  , testCase "conc-and-self" $ do
      let simp = Expr.simplify $ And (Var "x") (Var "x")
      assertEqual "x & x = x" (Var "x") simp
  , testCase "conc-and-complement" $ do
      let simp = Expr.simplify $ And (Not (Var "x")) (Var "x")
      assertEqual "~x & x = 0" (Lit 0) simp
  , testCase "conc-or-zero" $ do
      let simp = Expr.simplify $ Or (Lit 0) (Var "x")
      assertEqual "0 | x = x" (Var "x") simp
  , testCase "conc-or-self" $ do
      let simp = Expr.simplify $ Or (Var "x") (Var "x")
      assertEqual "x | x = x" (Var "x") simp
  , testCase "conc-or-maxlit-left" $ do
      let simp = Expr.simplify $ Or (Lit Expr.maxLit) (Var "x")
      assertEqual "maxLit | x = maxLit" (Lit Expr.maxLit) simp
  , testCase "conc-or-maxlit-right" $ do
      let simp = Expr.simplify $ Or (Var "x") (Lit Expr.maxLit)
      assertEqual "x | maxLit = maxLit" (Lit Expr.maxLit) simp

    -- SHL/SHR with zero
  , testCase "conc-shl-zero-amount" $ do
      let simp = Expr.simplify $ SHL (Lit 0) (Var "x")
      assertEqual "x << 0 = x" (Var "x") simp
  , testCase "conc-shl-zero-value" $ do
      let simp = Expr.simplify $ SHL (Var "n") (Lit 0)
      assertEqual "0 << n = 0" (Lit 0) simp
  , testCase "conc-shl-large-shift" $ do
      let simp = Expr.simplify $ SHL (Lit 256) (Var "x")
      assertEqual "x << 256 = 0" (Lit 0) simp
  , testCase "conc-shl-very-large-shift" $ do
      let simp = Expr.simplify $ SHL (Lit 1000) (Var "x")
      assertEqual "x << 1000 = 0" (Lit 0) simp
  , testCase "conc-shr-zero-amount" $ do
      let simp = Expr.simplify $ SHR (Lit 0) (Var "x")
      assertEqual "x >> 0 = x" (Var "x") simp
  , testCase "conc-shr-zero-value" $ do
      let simp = Expr.simplify $ SHR (Var "n") (Lit 0)
      assertEqual "0 >> n = 0" (Lit 0) simp
  , testCase "conc-shr-large-shift" $ do
      let simp = Expr.simplify $ SHR (Lit 256) (Var "x")
      assertEqual "x >> 256 = 0" (Lit 0) simp
  , testCase "conc-shr-very-large-shift" $ do
      let simp = Expr.simplify $ SHR (Lit 1000) (Var "x")
      assertEqual "x >> 1000 = 0" (Lit 0) simp

    -- ReadWord
  , testCase "conc-readword" $ do
      let simp = Expr.simplify $ ReadWord (Lit 0) (WriteWord (Lit 0) (Lit 0x42) (AbstractBuf "abc"))
      assertEqual "ReadWord from WriteWord" (Lit 0x42) simp

    -- WriteByte
  , testCase "conc-writebyte" $ do
      let simp = Expr.simplify $ ReadByte (Lit 0) (WriteByte (Lit 0) (LitByte 0xff) (AbstractBuf "abc"))
      assertEqual "WriteByte then ReadByte" (LitByte 0xff) simp

    -- WriteWord
  , testCase "conc-writeword" $ do
      let simp = Expr.simplify $ ReadWord (Lit 0) (WriteWord (Lit 0) (Lit 0xab) (AbstractBuf "abc"))
      assertEqual "WriteWord then ReadWord" (Lit 0xab) simp

    -- CopySlice of zero size should be a no-op
  , testCase "conc-copyslice-zero-size" $ do
      let simp = Expr.simplify $ CopySlice (Lit 0) (Lit 0) (Lit 0) (AbstractBuf "src") (AbstractBuf "dst")
      assertEqual "CopySlice size 0 is noop" (AbstractBuf "dst") simp

    -- IndexWord
  , testCase "conc-indexword" $ do
      let simp = Expr.simplify $ IndexWord (Lit 31) (Lit 0x42)
      assertEqual "IndexWord LSB" (LitByte 0x42) simp
  , testCase "conc-indexword-msb" $ do
      let simp = Expr.simplify $ IndexWord (Lit 0) (Lit 0xff00000000000000000000000000000000000000000000000000000000000000)
      assertEqual "IndexWord MSB" (LitByte 0xff) simp

    -- SEx special case
  , testCase "conc-sex-zero" $ do
      let simp = Expr.simplify $ SEx (Var "b") (Lit 0)
      assertEqual "SEx of 0 is 0" (Lit 0) simp

    -- Min with zero
  , testCase "conc-min-zero" $ do
      let simp = Expr.simplify $ Min (Lit 0) (Var "x")
      assertEqual "min(0, x) = 0" (Lit 0) simp
  ]

-- | Regression tests for W256 unsigned wrapping bugs in the expression simplifier.
-- Each test constructs an expression that triggers a specific wrapping edge case where
-- the simplifier previously produced a result that was not semantically equivalent to
-- the original expression. See commit c4d33256 for the fix.
wrappingTests :: TestTree
wrappingTests = testGroup "W256 wrapping edge cases"
  [ -- A1: readByte, CopySlice before-region, symbolic size
    -- dstOffset near maxBound makes dstOffset+size potentially wrap to low addresses.
    -- Old code only checked dstOffset > x, missing the wrapping case.
    testCase "readByte-copySlice-before-symSize-wrap" $ do
      let dstOff = maxBound - 5 :: W256
          x = 3 :: W256
          buf = CopySlice (Lit 0) (Lit dstOff) (Var "sz") (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadByte (Lit x) buf
          simplified = Expr.readByte (Lit x) buf
      result <- proveEquivExpr full simplified
      assertBool "readByte with near-maxBound dstOffset and symbolic size" result

  , -- A2: readByte, CopySlice before-region, concrete size, dstOffset+size wraps
    -- dstOffset + size wraps past zero, overwriting low addresses.
    testCase "readByte-copySlice-before-concSize-wrap" $ do
      let dstOff = maxBound - 30 :: W256
          size = 58 :: W256
          x = 10 :: W256
          buf = CopySlice (Lit 0) (Lit dstOff) (Lit size) (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadByte (Lit x) buf
          simplified = Expr.readByte (Lit x) buf
      result <- proveEquivExpr full simplified
      assertBool "readByte with wrapping dstOffset+size" result

  , -- B1: readWord, CopySlice before-region, symbolic size
    -- Same wrapping issue as A1 but for 32-byte reads.
    testCase "readWord-copySlice-before-symSize-wrap" $ do
      let dstOff = maxBound - 5 :: W256
          x = 3 :: W256
          buf = CopySlice (Lit 0) (Lit dstOff) (Var "sz") (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadWord (Lit x) buf
          simplified = Expr.readWord (Lit x) buf
      result <- proveEquivExpr full simplified
      assertBool "readWord with near-maxBound dstOffset and symbolic size" result

  , -- B2: readWord, CopySlice before-region, concrete size, wrapping
    -- Same as A2 but for word reads.
    testCase "readWord-copySlice-before-concSize-wrap" $ do
      let dstOff = maxBound - 30 :: W256
          size = 100 :: W256
          x = 3 :: W256
          buf = CopySlice (Lit 0) (Lit dstOff) (Lit size) (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadWord (Lit x) buf
          simplified = Expr.readWord (Lit x) buf
      result <- proveEquivExpr full simplified
      assertBool "readWord with wrapping dstOffset+size" result

  , -- C1: readWord, CopySlice before-region, x+32 wraps past maxBound
    -- When x is near maxBound, x+32 wraps to a small value, making
    -- dstOffset >= x+32 true even though the 32-byte read wraps into the CopySlice region.
    testCase "readWord-copySlice-before-x32-wrap" $ do
      let dstOff = maxBound - 100 :: W256
          x = maxBound - 10 :: W256  -- x+32 = 21, wraps!
          buf = CopySlice (Lit 0) (Lit dstOff) (Var "sz") (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadWord (Lit x) buf
          simplified = Expr.readWord (Lit x) buf
      result <- proveEquivExpr full simplified
      assertBool "readWord with x+32 wrapping" result

  , -- C2: readWord, CopySlice after-region, concrete size, dstOffset+size wraps
    -- x is inside the wrapped CopySlice region => the expression cannot be simplified
    testCase "readWord-copySlice-after-concSize-wrap" $ do
      let dstOff = maxBound - 100 :: W256
          size = 200 :: W256
          x = maxBound - 50 :: W256
          buf = CopySlice (Lit 0) (Lit dstOff) (Lit size) (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadWord (Lit x) buf
          simplified = Expr.readWord (Lit x) buf
      result <- proveEquivExpr full simplified
      assertBool "readWord after-region with wrapping dstOffset+size" result

  , -- D1: readWord, ConcreteBuf, idx+31 wraps
    -- readWord previously did not handle this case correctly due to overflow of idx+31
    testCase "readWord-concreteBuf-wrap" $ do
      let idx = maxBound - 19 :: W256
          buf = ConcreteBuf (BS.pack [1..50])
          full = ReadWord (Lit idx) buf
          simplified = Expr.readWord (Lit idx) buf
      result <- proveEquivExpr full simplified
      assertBool "readWord with idx+31 wrapping on ConcreteBuf" result

  , -- D2: readWord, non-concrete buf, idx+31 wraps
    -- Same wrapping issue as D1 but with a non-concrete buffer (WriteByte over ConcreteBuf).
    -- WriteByte at maxBound-5 is within the read range and won't be incorrectly skipped.
    testCase "readWord-abstractBuf-wrap" $ do
      let idx = maxBound - 10 :: W256
          buf = WriteByte (Lit (maxBound - 5)) (LitByte 0xAB) (ConcreteBuf (BS.pack [1..50]))
          full = ReadWord (Lit idx) buf
          simplified = Expr.readWord (Lit idx) buf
      result <- proveEquivExpr full simplified
      assertBool "readWord with idx+31 wrapping on abstract buf" result

  , -- E1: copySlice fully concrete, srcOffset near maxBound wraps
    -- When srcOffset is near maxBound, srcOffset > BS.length triggers zero-fill,
    -- but the wrapped indices actually read real source data.
    testCase "copySlice-concrete-srcOffset-wrap" $ do
      let srcOff = maxBound - 9 :: W256
          size = 20 :: W256
          srcBuf = ConcreteBuf (BS.pack [1..50])
          dstBuf = ConcreteBuf (BS.pack (replicate 50 0))
          full = CopySlice (Lit srcOff) (Lit 0) (Lit size) srcBuf dstBuf
          simplified = Expr.copySlice (Lit srcOff) (Lit 0) (Lit size) srcBuf dstBuf
      result <- proveEquivExpr full simplified
      assertBool "copySlice with wrapping srcOffset" result

  , testCase "writeWord-wrapping-write-stays-on-top" $ do
      let lower = WriteWord (Lit 0) (Var "x") (AbstractBuf "b")
          full = ReadWord (Lit 0) (WriteWord (Lit maxBound) (Var "v") lower)
          simplified = ReadWord (Lit 0) (Expr.writeWord (Lit maxBound) (Var "v") lower)
          nested = WriteWord (Lit maxBound) (Var "v") (WriteWord (Lit 0x2a) (Var "x") (AbstractBuf "b"))
      result <- proveEquivExpr full simplified
      assertBool "writeWord with a wrapping offset over a lower write" result
      assertEqual "simplify terminates" nested (Expr.simplify nested)

  , testCase "copySlice-short-from-writeWord-terminates" $ do
      let buf = CopySlice (Var "c") (Lit 0x26) (Lit 3) (WriteWord (Var "c") (Var "x") (AbstractBuf "b")) (AbstractBuf "b")
          expected = CopySlice (Lit 0) (Lit 0x26) (Lit 3) (WriteWord (Lit 0) (Var "x") (ConcreteBuf "")) (AbstractBuf "b")
      assertEqual "" expected (Expr.simplify buf)

  , testCase "bufLength-copySlice-symbolic-size-zero" $ do
      let len = Expr.bufLength (CopySlice (Lit 0x30) (Lit 0x4b) (Var "s") (AbstractBuf "b") (ConcreteBuf ""))
          at :: W256 -> Expr EWord
          at v = Expr.simplify (mapExpr (\case { Var "s" -> Lit v; e -> e }) len)
      assertEqual "a copy of zero bytes does not grow the buffer" (Lit 0) (at 0)
      assertEqual "" (Lit 0x50) (at 5)

  , testCase "readWord-wrap-over-low-writeByte" $ do
      let buf = WriteByte (Lit 5) (LitByte 0xAB) (ConcreteBuf (BS.pack [1..50]))
          full = ReadWord (Lit maxBound) buf
      result <- proveEquivExpr full (Expr.readWord (Lit maxBound) buf)
      assertBool "readWord wrapping onto a WriteByte at a low index" result

  , testCase "readWord-wrap-over-low-copySlice" $ do
      let buf = CopySlice (Lit 0) (Lit 0) (Lit 3) (AbstractBuf "src") (AbstractBuf "dst")
          full = ReadWord (Lit maxBound) buf
      result <- proveEquivExpr full (Expr.readWord (Lit maxBound) buf)
      assertBool "readWord wrapping onto a CopySlice at a low index" result

  , testCase "show-addr-leaves-rest-alone" $
      assertEqual "" "(0x0000000000000000000000000000000000001234,Just 1)" (show (Addr 0x1234, Just (1 :: Int)))
  ]

fuzzTests :: TestTree
fuzzTests = testGroup "ExprFuzzTests"
  [ halfQuickCheckTests $ testGroup "plain"
      [ equivalenceSanityChecks equivConfig
      , simplifierFuzzTests equivConfig
      ]
  , halfQuickCheckTests $ testGroup "abstract-arith"
      [ equivalenceSanityChecks abstractConfig
      , simplifierFuzzTests abstractConfig
      ]
  , abstractArithmeticFuzzTests
  , enumerateFuzzTests
  ]
  where
    halfQuickCheckTests = adjustOption $ \(Test.Tasty.QuickCheck.QuickCheckTests n) ->
      Test.Tasty.QuickCheck.QuickCheckTests (div n 2)

-- | Every model of the path conditions must take a value of the subterm that is enumerated,
-- and give the word the value enumerated with it: one left out drops a feasible path.
enumerateFuzzTests :: TestTree
enumerateFuzzTests = testGroup "enumerateViaSmallSubterm"
  [ testProperty "enumerate-small-subterm-complete" $ \(SmallRange limit props e) -> ioProperty $
      -- path conditions are stored simplified
      case Expr.enumerateViaSmallSubterm limit (Expr.simplifyProps props) e of
        Nothing -> pure $ label "nothing enumerated" True
        Just (atom, groups) -> do
          let ks = concatMap snd groups
              covered = foldr POr (PBool False) [PAnd (PEq atom (Lit k)) (PEq e (Lit v)) | (v, vks) <- groups, k <- vks]
          res <- checkSat $ foldr PAnd (PNeg covered) props
          pure $ label (if null groups then "enumerated as infeasible" else "enumerated")
               $ label (if isUnknown res then "solver gave up" else "solver answered")
               $ counterexample ("subterm: " <> show atom <> "\ngroups: " <> show groups <> "\nresult: " <> show res)
               $ length ks <= limit && length ks == length (nubOrd ks) && isUnsatOrUnknown res
  ]

equivalenceSanityChecks :: Config -> TestTree
equivalenceSanityChecks cfg = testGroup "Expr equivalence sanity checks"
  [ testCase "read-beyond-bound (negative-test)" $ do
      let
        e1 = CopySlice (Lit 1) (Lit 0) (Lit 2) (ConcreteBuf "a") (ConcreteBuf "")
        e2 = ConcreteBuf "Definitely not the same!"
      equal <- proveEquivExprWith cfg e1 e2
      assertBool "Should not be equivalent!" $ not equal
  , testProperty "expr equality is satisfiable" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readWord idx buf
            full = ReadWord idx buf
        res <- checkSatWith cfg (Expr.peq full simplified)
        pure $ isSatOrUnknown res
  ]

-- These tests fuzz the simplifier by generating a random expression,
-- applying some simplification rules, and then using the smt encoding to
-- check that the simplified version is semantically equivalent to the
-- unsimplified one
simplifierFuzzTests :: Config -> TestTree
simplifierFuzzTests cfg = testGroup "SimplifierPropertyTests"
    [ testProperty  "buffer-simplification" $ \(expr :: Expr Buf) -> ioProperty $ proveEquivExprWith cfg expr (Expr.simplify expr)
    , testProperty  "buffer-simplification-len" $ \(expr :: Expr Buf) -> ioProperty $ do
        let buflen = BufLength expr
        proveEquivExprWith cfg buflen (Expr.simplify buflen)
    , testProperty "shaped-word-simplification" $ forAllShrink (sized $ \n -> genShapedWord (min n 20)) shrinkWord $ \e' ->
        let e = litCopySizes e' in within 20_000_000 $ ioProperty $ proveEquivExprWith cfg e (Expr.simplify e)
    , testProperty "shaped-prop-simplification" $ forAllShrink (sized $ \n -> genShapedProp (min n 16)) shrinkProp $ \p' ->
        let p = mapProp litCopySizes p' in within 20_000_000 $ ioProperty $ proveEquivPropWith cfg p (Expr.simplifyProp p)
    , testProperty "store-simplification" $ \(expr :: Expr Storage) -> ioProperty $ proveEquivExprWith cfg expr (Expr.simplify expr)
    , testProperty "load-simplification" $ \(GenWriteStorageLoad expr) -> ioProperty $ proveEquivExprWith cfg expr (Expr.simplify expr)
    -- decomposition must not change the loaded value, given its assumption that keys of different
    -- stores never alias
    , testProperty "load-decompose" $ \(GenDecomposableLoad expr) -> ioProperty $
        case mapExprM Expr.decomposeStorage expr of
          Nothing -> pure $ counterexample "decomposition failed" False
          Just decomposed -> decomposeEquiv cfg (storeKeys expr) expr decomposed
    -- same, on the shapes the simplifier leaves behind. It may leave some that cannot be decomposed
    , testProperty "load-simplify-decompose" $ \(GenDecomposableLoad expr) -> ioProperty $ do
        let simp = Expr.simplify expr
        case mapExprM Expr.decomposeStorage simp of
          Nothing -> pure $ property Discard
          Just decomposed -> decomposeEquiv cfg (nubOrd $ storeKeys expr <> storeKeys simp) expr decomposed
    -- the entry point the solver pipeline uses: it backs off, or the props keep their meaning
    , testProperty "props-decompose" $ \(GenDecomposableProps props) -> ioProperty $
        case Expr.decomposeStorageProps props of
          Nothing -> pure $ label "declined" True
          Just decomposed -> label "decomposed" <$> decomposeEquivProps cfg props decomposed
    -- guards against the entry point backing off from what it is there for
    , testProperty "props-decompose-accepts" $ \(GenDecomposableLoad a) (GenDecomposableLoad b) ->
        isJust $ Expr.decomposeStorageProps [PEq a b]
    , testProperty "byte-simplification" $ \(expr :: Expr Byte) -> ioProperty $ proveEquivExprWith cfg expr (Expr.simplify expr)
    , askOption $ \(QuickCheckTests n) -> testProperty "word-simplification" $ withMaxSuccess (min n 20) $ \(ZeroDepthWord expr) ->
        ioProperty $ proveEquivExprWith cfg expr (Expr.simplify expr)
    , testProperty "readStorage-equivalance" $ \(store, slot) -> ioProperty $ do
        let simplified = Expr.readStorage' slot store
            full = SLoad slot store
        proveEquivExprWith cfg full simplified
    , testProperty "writeStorage-equivalance" $ \(val, GenWriteStorageExpr (slot, store)) -> ioProperty $ do
        let simplified = Expr.writeStorage slot val store
            full = SStore slot val store
        proveEquivExprWith cfg full simplified
    , testProperty "readWord-equivalance" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readWord idx buf
            full = ReadWord idx buf
        proveEquivExprWith cfg full simplified
    , testProperty "writeWord-equivalance" $ \(idx, val, WriteWordBuf buf) -> ioProperty $ do
        let simplified = Expr.writeWord idx val buf
            full = WriteWord idx val buf
        proveEquivExprWith cfg full simplified
    , testProperty "arith-simplification" $ \(_ :: Int) -> ioProperty $ do
        expr <- generate . sized $ genWordArith 15
        let simplified = Expr.simplify expr
        proveEquivExprWith cfg expr simplified
    , testProperty "readByte-equivalance" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readByte idx buf
            full = ReadByte idx buf
        proveEquivExprWith cfg full simplified
    -- we currently only simplify concrete writes over concrete buffers so that's what we test here
    , testProperty "writeByte-equivalance" $ \(LitOnly val, LitOnly buf, GenWriteByteIdx idx) -> ioProperty $ do
        let simplified = Expr.writeByte idx val buf
            full = WriteByte idx val buf
        proveEquivExprWith cfg full simplified
    , testProperty "copySlice-equivalance" $ \(GenCopySliceOff srcOff, GenCopySliceBuf src, GenCopySliceBuf dst, LitWord @300 size) -> ioProperty $ do
        -- we bias buffers to be concrete more often than not
        dstOff <- generate (maybeBoundedLit 100_000)
        let simplified = Expr.copySlice srcOff dstOff size src dst
            full = CopySlice srcOff dstOff size src dst
        proveEquivExprWith cfg full simplified
    , testProperty "indexWord-equivalence" $ \(src, LitWord @50 idx) -> ioProperty $ do
        let simplified = Expr.indexWord idx src
            full = IndexWord idx src
        proveEquivExprWith cfg full simplified
    , testProperty "pow-base2-simp" $ \(_ :: Int) -> ioProperty $ do
        expo <- generate . sized $ genWordArith 15
        let full = Exp (Lit 2) expo
            simplified = Expr.simplify full
        proveEquivExprWith cfg full simplified
    , testProperty "pow-low-exponent-simp" $ \(LitWord @100 expo) -> ioProperty $ do
        base <- generate . sized $ genWordArith 15
        let full = Exp base expo
            simplified = Expr.simplify full
        proveEquivExprWith cfg full simplified
    , testProperty "indexWord-mask-equivalence" $ \(src :: Expr EWord, LitWord @35 idx) -> ioProperty $ do
        mask <- generate $ do
          pow <- arbitrary :: Gen Int
          frequency
           [ (1, pure $ Lit $ (shiftL 1 (pow `mod` 256)) - 1)        -- potentially non byte aligned
           , (1, pure $ Lit $ (shiftL 1 ((pow * 8) `mod` 256)) - 1)  -- byte aligned
           ]
        let
          input = And mask src
          simplified = Expr.indexWord idx input
          full = IndexWord idx input
        proveEquivExprWith cfg full simplified
    , testProperty "toList-equivalance" $ \buf -> ioProperty $ do
        let
          -- transforms the input buffer to give it a known length
          fixLength :: Expr Buf -> Gen (Expr Buf)
          fixLength = mapExprM go
            where
              go :: Expr a -> Gen (Expr a)
              go = \case
                WriteWord _ val b -> WriteWord <$> idx <*> (pure val) <*> (pure b)
                WriteByte _ val b -> WriteByte <$> idx <*> (pure val) <*> (pure b)
                CopySlice so _ sz src dst -> CopySlice <$> (pure so) <*> idx <*> (pure sz) <*> (pure src) <*> (pure dst)
                AbstractBuf _ -> cbuf
                e -> pure e
              cbuf = do
                bs <- arbitrary
                pure $ ConcreteBuf bs
              idx = do
                w <- arbitrary
                -- we use 100_000 as an upper bound for indices to keep tests reasonably fast here
                pure $ Lit (w `mod` 100_000)

        input <- generate $ fixLength buf
        case Expr.toList input of
          Nothing -> do
            pure True -- ignore cases where the buf cannot be represented as a list
          Just asList -> do
            let asBuf = Expr.fromList asList
            proveEquivExprWith cfg asBuf input
    , testProperty "simplifyProp-equivalence-lit" $ \(LitProp p) -> ioProperty $ do
        let simplified = Expr.simplifyProps [p]
        case simplified of
          [] -> proveEquivPropWith cfg (PBool True) p
          [val@(PBool _)] -> proveEquivPropWith cfg val p
          _ -> assertFailure "must evaluate down to a literal bool"
    , testProperty "simplifyProp-equivalence-sym" $ \(p) -> ioProperty $ proveEquivPropWith cfg p (Expr.simplifyProp p)
    , testProperty "simplify-joinbytes" $ \(SymbolicJoinBytes exprList) -> ioProperty $ do
        let x = joinBytesFromList exprList
        let simplified = Expr.simplify x
        proveEquivExprWith cfg x simplified
    , testProperty "simpProp-equivalence-sym-Prop" $ withMaxSuccess 20 $ \(ps :: [Prop]) -> ioProperty $ do
        let simplified = pand (Expr.simplifyProps ps)
        proveEquivPropWith cfg (pand ps) simplified
    , testProperty "simpProp-equivalence-sym-LitProp" $ \(LitProp p) -> ioProperty $ do
        let simplified = pand (Expr.simplifyProps [p])
        proveEquivPropWith cfg p simplified
    , testProperty "storage-slot-simp-property" $ \(StorageExp s) -> ioProperty $ do
        -- we have to run `Expr.litToKeccak` on the unsimplified system, or
        -- we'd need some form of minimal simplifier for things to work out. As long as
        -- we trust the litToKeccak, this is fine, as that function is stand-alone,
        -- and quite minimal
        let s2 = Expr.litToKeccak s
        let simplified = Expr.simplify s2
        proveEquivExprWith cfg s2 simplified
    , testProperty "expr-ordering" $ \(p) -> ioProperty $ do
      let simp = Expr.simplifyProp p
      pure $ Expr.checkLHSConstProp simp
    ]
    {- NOTE: These tests were designed to test behaviour on reading from a buffer such that the indices overflow 2^256.
           However, such scenarios are impossible in the real world (the operation would run out of gas). The problem
           is that the behaviour of bytecode interpreters does not match the semantics of SMT. Intrepreters just
           return all zeroes for any read beyond buffer size, while in SMT reading multiple bytes may lead to overflow
           on indices and subsequently to reading from the beginning of the buffer (wrap-around semantics).
  , testGroup "concrete-buffer-simplification-large-index" [
      test "copy-slice-large-index-nooverflow" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x1) (ConcreteBuf "a") (ConcreteBuf "")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "copy-slice-overflow-back-into-source" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x2) (ConcreteBuf "a") (ConcreteBuf "")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "copy-slice-overflow-beyond-source" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x3) (ConcreteBuf "a") (ConcreteBuf "")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "copy-slice-overflow-beyond-source-into-nonempty" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x3) (ConcreteBuf "a") (ConcreteBuf "b")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "read-word-overflow-back-into-source" $ do
        let
          e = ReadWord (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (ConcreteBuf "kkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkk")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
  ]
  -}

abstractArithmeticFuzzTests :: TestTree
abstractArithmeticFuzzTests = testGroup "AbstractArithmeticPropertyTests"
  -- timeouts are discarded, but if over ~half the cases time out, QuickCheck gives up and the test fails
  -- several kinds of broken lemma only show after more than the default number of cases
  [ adjustOption (\(QuickCheckTests n) -> QuickCheckTests (2 * n)) $
    localOption (QuickCheckMaxRatio 1) $
    testProperty "targeted arithmetic shapes agree with concrete evaluation" $
      \(AbstractArithCase kind parts expr _ bindings) ->
        tabulate "arithmetic shape" [kind] $ tabulate "component shape" parts $ ioProperty $ do
          let expected = evalWithBindings bindings expr
              assignments = fmap (\(name, value) -> PEq (Var name) (Lit value)) bindings
              counterexampleQuery rhs = PNeg (PEq expr (Lit rhs)) : assignments
              nearbyQuery = counterexampleQuery (expected + 1)
          ((exactResult, exactPhase), (nearbyResult, nearbyPhase), families, lemmaResult) <-
            runAbstractArith abstractConfig 5 $ \solvers -> do
              exact <- checkSatWithPropsPhase solvers Nothing (counterexampleQuery expected)
              nearby <- checkSatWithPropsPhase solvers Nothing nearbyQuery
              (families, lemmaResult) <- checkLemmasAtPoint solvers nearbyQuery
              pure (exact, nearby, families, lemmaResult)
          pure $ tabulate "lemma family" (nubOrd families)
               $ tabulate "decided by" [show exactPhase, show nearbyPhase]
               $ counterexample (unlines
            [ "shape: " <> kind <> " " <> show parts
            , "expression: " <> show expr
            , "bindings: " <> show bindings
            , "concrete value: " <> show expected
            , "exact result: " <> show exactResult
            , "nearby result: " <> show nearbyResult
            , "lemmas over fully interpreted terms: " <> show lemmaResult
            ]) $ not (any isUnknown [exactResult, nearbyResult, lemmaResult]) ==>
              (isQed exactResult && isCex nearbyResult && isCex lemmaResult)
  , looselyConstrained "loosely constrained queries have a valid model" abstractConfig
  , looselyConstrained "loosely constrained queries have a valid model (simplified)" abstractConfig {simp = True}
  ]
  where
    -- the production pipeline: variables left free or ranged, arithmetic
    -- spread over several props, and a counterexample that has to check out
    looselyConstrained name cfg = localOption (QuickCheckMaxRatio 3) $ testProperty name $
      \c@(AbstractArithCase kind _ _ _ bindings) -> forAll (genLooseQuery c) $ \props ->
        tabulate "arithmetic shape" [kind] $ ioProperty $ do
          (result, phase) <- runAbstractArith cfg 1 $ \solvers -> checkSatWithPropsPhase solvers Nothing props
          let outcome = case result of
                Cex model | modelHolds bindings model props -> "valid model"
                Cex _ -> "invalid model"
                Qed -> "unsound Qed"
                _ -> "unknown"
          pure $ tabulate "decided by" [show phase] $ tabulate "outcome" [outcome]
               $ counterexample (unlines
            [ "props: " <> show props
            , "satisfying bindings: " <> show bindings
            , "result: " <> show result
            ]) $ outcome /= "unknown" ==> outcome == "valid model"

-- | Props that hold at the case's bindings, so the query is satisfiable: a
-- relation on the expression, relations on some of its components, and each
-- variable pinned, ranged around its binding, or left free.
genLooseQuery :: AbstractArithCase -> Gen [Prop]
genLooseQuery (AbstractArithCase _ _ expr components bindings) = do
  goal <- trueRelation expr
  sides <- sublistOf components >>= mapM trueRelation
  constraints <- concat <$> mapM constrain bindings
  pure (goal : sides <> constraints)
  where
    trueRelation e = do
      let v = evalWithBindings bindings e
      elements $ [PEq e (Lit v), PLEq e (Lit v), PGEq e (Lit v), PNeg (PEq e (Lit (v + 1)))]
        <> [PLT e (Lit (v + 1)) | v /= maxBound] <> [PGT e (Lit (v - 1)) | v /= 0]
    constrain (name, v) = frequency
      [ (2, pure [PEq (Var name) (Lit v)])
      , (2, do
          slack <- fromInteger <$> chooseInteger (0, 0xffff)
          pure $ [PLEq (Var name) (Lit (v + slack)) | v <= maxBound - slack]
              <> [PGEq (Var name) (Lit (v - slack)) | v >= slack])
      , (1, pure [])
      ]

-- | Whether the props hold under the model. A variable the simplifier removed
-- from the query is missing from the model; its binding is as good as any.
modelHolds :: [(Text, W256)] -> SMTCex -> [Prop] -> Bool
modelHolds bindings model = all holds
  where
    assignment = [(name, Map.findWithDefault v (Var name) model.vars) | (name, v) <- bindings]
    holds p = Expr.simplifyProp (mapProp (substituteBindings assignment) p) == PBool True

evalWithBindings :: [(Text, W256)] -> Expr EWord -> W256
evalWithBindings bindings expr =
  case Expr.simplify (mapExpr (substituteBindings bindings) expr) of
    Lit value -> value
    other -> internalError $ "targeted arithmetic expression did not concretize: " <> show other

substituteBindings :: [(Text, W256)] -> Expr a -> Expr a
substituteBindings bindings (Var name) = case lookup name bindings of
  Just value -> Lit value
  Nothing -> internalError $ "missing targeted arithmetic binding: " <> show name
substituteBindings _ other = other

runAbstractArith :: Config -> Natural -> (SolverGroup -> ReaderT Env IO a) -> IO a
runAbstractArith cfg timeout = runEnv (Env {config = cfg}) . withSolvers Bitwuzla 1 (Just timeout) defMemLimit

-- | The lemmas of the query with every abstract term they mention equated to
-- the native op. The props hold at a point, so a Qed means some lemma instance
-- is false there. The refinement cannot show this for a lemma about a
-- synthesized term, which it leaves uninterpreted.
checkLemmasAtPoint :: SolverGroup -> [Prop] -> ReaderT Env IO ([String], SMTResult)
checkLemmasAtPoint solvers props = case assertPropsAbstract abstractConfig props of
  Left e -> internalError $ "could not encode abstract query: " <> e
  Right q -> do
    res <- liftIO $ Solvers.checkSat solvers Nothing (Right (q.query <> SMT2 (SMTScript q.saturatedTruth) mempty mempty))
    pure (q.lemmaFamilies, res)


proveEquivPropWith :: Config -> Prop -> Prop -> IO Bool
proveEquivPropWith cfg a b
  | a == b = pure True
  | otherwise = do
      res <- checkSatWith cfg $ PNeg ((PImpl a b) .&& (PImpl b a))
      pure $ isUnsatOrUnknown res

proveEquivExpr :: Typeable a => Expr a -> Expr a -> IO Bool
proveEquivExpr = proveEquivExprWith equivConfig

proveEquivExprWith :: Typeable a => Config -> Expr a -> Expr a -> IO Bool
proveEquivExprWith cfg a b
  | a == b = pure True
  | otherwise = do
      res <- (checkSatWith cfg $ a ./= b)
      pure $ isUnsatOrUnknown res

checkSat :: Prop -> IO SMTResult
checkSat = checkSatWith equivConfig

checkSatWith :: Config -> Prop -> IO SMTResult
checkSatWith cfg p = runEnv (Env {config = cfg}) $
    withOneBitwuzla $ \solvers -> checkSatWithProps solvers [p]

equivConfig :: Config
equivConfig = defaultConfig {simp = False, dumpQueries = False}

abstractConfig :: Config
abstractConfig = equivConfig {abstractArith = True}

withOneBitwuzla :: App m => (SolverGroup -> m a) -> m a
withOneBitwuzla = withSolvers Bitwuzla 1 (Just 1) defMemLimit

-- keccak is uninterpreted in SMT, so the no-aliasing assumption has to be asserted. A decomposed
-- abstract base is a different SMT array per logical store, so tie each one to the original base
decomposeAssumes :: [Expr EWord] -> [Expr EAddr] -> [Prop]
decomposeAssumes keys addrs = noAlias <> link
  where
    noAlias = [PNeg (PEq a b) | (a:rest) <- List.tails keys, b <- rest, storeId a /= storeId b]
    link = [ PEq (SLoad k (AbstractStore a Nothing)) (SLoad logicalKey (AbstractStore a (Just idx)))
           | a <- addrs, k <- keys, Just (idx, logicalKey) <- [logicalLoc k] ]

-- differ must be unsatisfiable under the assumptions
checkDecomposed :: Show a => Config -> [Prop] -> Prop -> a -> IO Property
checkDecomposed cfg assumes differ decomposed = do
  res <- checkSatWith cfg $ foldr PAnd differ assumes
  -- a timeout proves nothing either way: discard it rather than count it as a pass
  pure $ counterexample ("decomposed: " <> show decomposed <> "\nresult: " <> show res) $
    not (isUnknown res) ==> isQed res

decomposeEquiv :: Config -> [Expr EWord] -> Expr EWord -> Expr EWord -> IO Property
decomposeEquiv cfg keys expr decomposed =
  checkDecomposed cfg (decomposeAssumes keys (nubOrd $ foldExpr abstractAddr [] expr)) (expr ./= decomposed) decomposed

decomposeEquivProps :: Config -> [Prop] -> [Prop] -> IO Property
decomposeEquivProps cfg props decomposed = checkDecomposed cfg (decomposeAssumes keys addrs) differ decomposed
  where
    keys = nubOrd $ concatMap (foldProp storeKey []) props
    addrs = nubOrd $ concatMap (foldProp abstractAddr []) props
    (a, b) = (foldr PAnd (PBool True) props, foldr PAnd (PBool True) decomposed)
    differ = POr (PAnd a (PNeg b)) (PAnd (PNeg a) b)

storeKeys :: Expr a -> [Expr EWord]
storeKeys = foldExpr storeKey []

storeKey :: Expr a -> [Expr EWord]
storeKey = \case
  SLoad k _ -> [k]
  SStore k _ _ -> [k]
  ConcreteStore m -> Lit <$> Map.keys m
  _ -> []

abstractAddr :: Expr a -> [Expr EAddr]
abstractAddr = \case
  AbstractStore a _ -> [a]
  _ -> []

-- the logical store a key belongs to: Nothing for small slots
storeId :: Expr EWord -> Maybe W256
storeId = fmap fst . logicalLoc

-- the logical store of a key and the key within it. Written independently of decomposeStorage
logicalLoc :: Expr EWord -> Maybe (W256, Expr EWord)
logicalLoc = \case
  Expr.MappingSlot idx key -> Just (word (BS.drop 32 idx), key)
  Keccak (ConcreteBuf k) | BS.length k == 64 -> Just (word (BS.drop 32 k), Lit (word (BS.take 32 k)))
  Expr.ArraySlotWithOffs idx offs -> Just (word idx, offs)
  Expr.ArraySlotWithOffs2 idx offs1 offs2 -> Just (word idx, Add (Lit offs1) offs2)
  Expr.ArraySlotZero idx -> Just (word idx, Lit 0)
  _ -> Nothing

-- | The SMT encoding only supports CopySlice with a literal size
litCopySizes :: Expr a -> Expr a
litCopySizes = mapExpr $ \case
  CopySlice a b sz src dst | not (isLit sz) -> CopySlice a b (Lit 7) src dst
  e -> e
  where
    isLit :: Expr EWord -> Bool
    isLit = \case Lit _ -> True; _ -> False

isSat :: SMTResult -> Bool
isSat = isCex

isSatOrUnknown :: SMTResult -> Bool
isSatOrUnknown res = isSat res || isUnknown res

isUnsatOrUnknown :: SMTResult -> Bool
isUnsatOrUnknown res = isQed res || isUnknown res

-- | A copy window over a word-write chain, biased towards writes and base ends on the window edges
data TrimCase = TrimCase
  { tcOff :: Int, tcSize :: Int, tcWrites :: [(Int, Expr EWord)], tcBase :: Expr Buf }
  deriving Show

tcSrc :: TrimCase -> Expr Buf
tcSrc c = foldr (\(i, v) acc -> WriteWord (Lit (fromIntegral i)) v acc) c.tcBase c.tcWrites

genTrimCase :: Gen TrimCase
genTrimCase = do
  off <- frequency [(3, choose (0, 160)), (1, elements [0, 32, 64])]
  -- size 32 is rewritten to a WriteWord before the trim is reached
  size <- frequency [(1, choose (1, 31)), (2, choose (33, 96))]
  let end = off + size
      edges = filter (>= 0) [off - 32, off - 31, off - 1, off, end - 32, end - 31, end - 1, end]
      genIdx prev = frequency $
        [(2, choose (0, end + 40)), (2, elements edges)]
        <> [(1, elements prev >>= \p -> (p +) <$> choose (-31, 31)) | not (null prev)]
      genWrites 0 _ = pure []
      genWrites k prev = do
        i <- max 0 <$> genIdx prev
        v <- oneof [Lit <$> arbitrary, Lit . fromIntegral <$> choose (0 :: Int, 255), elements [Var "a", Var "b", Var "c"]]
        ((i, v) :) <$> genWrites (k - 1 :: Int) (i : prev)
  writes <- choose (1, 6) >>= \n -> genWrites n []
  len <- frequency [(1, pure 0), (2, choose (0, 200)), (2, elements (filter (>= 0) [end - 1, end, end + 1]))]
  bytes <- BS.pack <$> vectorOf len (frequency [(1, pure 0), (3, choose (1, 255))])
  base <- frequency
    [ (8, pure $ ConcreteBuf bytes)
    , (1, pure $ AbstractBuf "src")
    , (1, pure $ WriteByte (Lit 3) (LitByte 1) (ConcreteBuf bytes))
    ]
  pure $ TrimCase off size writes base

-- | What a case exercises, by the window semantics rather than by the implementation
trimCaseLabels :: TrimCase -> [(String, [String])]
trimCaseLabels c =
  [ ("write vs window", go [] c.tcWrites)
  , ("base", [baseKind])
  , ("size", [if c.tcSize < 32 then "<32" else ">32"])
  ]
  where
    off = c.tcOff
    end = off + c.tcSize
    hits i = i < end && i + 32 > off
    go _ [] = []
    go later ((i, _) : rest) = tag : go (i : later) rest
      where
        tag | i + 32 == off || i == end = "edge, outside"
            | i + 31 == off || i + 1 == end = "edge, inside"
            | not (hits i) = "outside"
            | any (\j -> j < i + 32 && i < j + 32) later = "overlaps a later write"
            | i < off || i + 32 > end = "straddles"
            | otherwise = "inside"
    baseKind = case c.tcBase of
      ConcreteBuf bs
        | BS.length bs < off -> "concrete, ends before window"
        | BS.length bs < end -> "concrete, ends in window"
        | otherwise -> "concrete, covers window"
      AbstractBuf _ -> "abstract"
      _ -> "WriteByte"
