module EVM.Expr.ExprTests (tests) where

import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.HUnit

import Data.Containers.ListUtils (nubOrd)
import Data.Map.Strict qualified as Map

import EVM.Expr qualified as Expr
import EVM.Types

tests :: TestTree
tests = testGroup "Expr"
  [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ simplificationTests
  , constantPropagationTests
  , boundPropagationTests
  ]

simplificationTests :: TestTree
simplificationTests = testGroup "Expr-rewriting"
  [ storageTests
  , copySliceTests
  , memoryTests
  , basicSimplificationTests
  , propSimplificationTests
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
  ]
  where errorMsg = "Storage read expression not simplified correctly"

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
  ]

memoryTests :: TestTree
memoryTests = testGroup "Memory tests"
  [ testCase "read-write-same-byte"  $ assertEqual ""
      (LitByte 0x12)
      (Expr.readByte (Lit 0x20) (WriteByte (Lit 0x20) (LitByte 0x12) mempty))
  , testCase "read-write-same-word"  $ assertEqual ""
      (Lit 0x12)
      (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
  , testCase "read-byte-write-word"  $ assertEqual ""
      -- reading at byte 31 a word that's been written should return LSB
      (LitByte 0x12)
      (Expr.readByte (Lit 0x1f) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
  , testCase "read-byte-write-word2"  $ assertEqual ""
      -- Same as above, but offset not 0
      (LitByte 0x12)
      (Expr.readByte (Lit 0x20) (WriteWord (Lit 0x1) (Lit 0x12) mempty))
  ,testCase "read-write-with-offset"  $ assertEqual ""
      -- 0x3F = 63 decimal, 0x20 = 32. 0x12 = 18
      --    We write 128bits (32 Bytes), representing 18 at offset 32.
      --    Hence, when reading out the 63rd byte, we should read out the LSB 8 bits
      --           which is 0x12
      (LitByte 0x12)
      (Expr.readByte (Lit 0x3F) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
  ,testCase "read-write-with-offset2"  $ assertEqual ""
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
  ]

basicSimplificationTests :: TestTree
basicSimplificationTests = testGroup "Basic simplification tests"
  [ testCase "simp-readByte1" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (ReadWord (Lit 0x1) (AbstractBuf "stuff2"))
          src = (AbstractBuf "stuff2")
          e = ReadByte (Lit 0x0) (CopySlice srcOffset (Lit 0x10) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqual "readByte simplification" simp (ReadByte (Lit 0x0) (AbstractBuf "dst"))
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