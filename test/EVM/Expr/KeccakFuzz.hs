-- | Storage slots of Solidity layouts written and read back through different keccak
-- representations (symbolic hashes, concrete buffers, copies, compiler-folded literals).
module EVM.Expr.KeccakFuzz (tests) where

import Data.ByteString qualified as BS
import Data.List (nub, nubBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, QuickCheckTests(..))

import EVM.Effects (Env(..), Config(..), defaultConfig, runEnv)
import EVM.Expr qualified as Expr
import EVM.Expr.Generator ()
import EVM.Solvers (Solver(..), withSolvers, checkSatWithProps, defMemLimit)
import EVM.Types hiding (Env, Case)

data Key = KLit W256 | KVar Text
  deriving (Show, Eq)

data Slot
  = Plain W256
  | Mapping Key Slot W256 -- ^ keccak(key . parent) + field offset
  | Array Slot W256       -- ^ keccak(parent) + index
  deriving (Show, Eq)

data Case = Case
  { writes :: [(Slot, Expr EWord, W256)] -- ^ newest first, with the rendered slot
  , baseEntries :: [(Slot, W256)]        -- ^ concrete slots in the ConcreteStore base
  , abstractBase :: Bool
  , readSlot :: Slot
  , readExpr :: Expr EWord
  , canonRead :: Expr EWord
  }
  deriving Show

-- each case costs about a second of solver time; pass --quickcheck-tests to fuzz longer
tests :: TestTree
tests = adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10 else n)) $
  testGroup "keccak-slot-fuzz"
  [ testProperty "keccak-slot-no-spurious-cex" $ forAllShrink genCase shrinkCase $ \c -> forAll arbitrary $ \simp -> ioProperty $ do
      let p = loaded c ./= expected c
      res <- checkSat ((if simp then Expr.simplifyProp p else p) : keyWitnesses c)
      pure $ classify simp "simplified" $ case res of
        Cex cex -> counterexample ("spurious counterexample: " <> show cex.vars <> "\n" <> show c) False
        Qed -> property True
        Unknown _ -> label "unknown" True
        Error e -> counterexample e False
  , testProperty "keccak-equal-prefix-same-hash" $ forAll genPrefixCase $ \c -> forAll arbitrary $ \simp -> ioProperty $ do
      let p = PNeg (PEq (Keccak c.bufA) (Keccak c.bufB))
      -- bitwuzla answers unknown: it does not support equality over constant arrays
      res <- checkSatWith Z3 ((if simp then Expr.simplifyProp p else p) : c.lenProps <> c.extra)
      pure $ classify simp "simplified" $ case res of
        Cex cex -> counterexample ("spurious counterexample: " <> show cex.buffers <> "\n" <> show c) False
        Qed -> property True
        Unknown u -> label ("unknown: " <> take 80 (show u)) True
        Error e -> counterexample (e <> "\n" <> show c) False
  , testProperty "keccak-differing-input-may-differ" $ forAll genDifferingCase $ \c -> forAll arbitrary $ \simp -> ioProperty $ do
      let p = PNeg (PEq (Keccak c.bufA) (Keccak c.bufB))
      res <- checkSatWith Z3 ((if simp then Expr.simplifyProp p else p) : c.lenProps <> c.extra)
      pure $ classify simp "simplified" $ case res of
        Qed -> counterexample ("false proof that the hashes are equal\n" <> show c) False
        Error e -> counterexample (e <> "\n" <> show c) False
        _ -> property True
  , testProperty "keccak-slot-no-false-proof" $ forAllShrink genConcreteBaseCase shrinkCase $ \c -> forAll (genEnv c) $ \env -> ioProperty $ do
      let pins = [PEq (Var v) (Lit w) | (v, w) <- Map.toList env]
      res <- checkSat (PEq (loaded c) (Lit (refLoad env c)) : pins <> keyWitnesses c)
      pure $ case res of
        Qed -> counterexample ("false proof under " <> show env <> "\n" <> show c) False
        _ -> property True
  ]

checkSat :: [Prop] -> IO SMTResult
checkSat = checkSatWith Bitwuzla

checkSatWith :: Solver -> [Prop] -> IO SMTResult
checkSatWith solver ps = runEnv (Env {config = defaultConfig {simp = False}}) $
  withSolvers solver 1 (Just 5) defMemLimit $ \s -> checkSatWithProps s ps

-- | Recovering a folded slot needs its keys above 255 to occur in the query, as when the
-- program compares against them
keyWitnesses :: Case -> [Prop]
keyWitnesses c = [PEq (Var ("seen" <> T.pack (show i))) (Lit w) | (i, w) <- zip [0 :: Int ..] (nub bigKeys)]
  where
    slots = c.readSlot : [s | (s, _, _) <- c.writes] <> map fst c.baseEntries
    bigKeys = [w | KLit w <- concatMap slotKeys slots, w > 255]
    slotKeys = \case
      Plain _ -> []
      Mapping k p _ -> k : slotKeys p
      Array p _ -> slotKeys p

store :: Case -> Expr Storage
store c = foldr (\(_, e, v) s -> SStore e (Lit v) s) base c.writes
  where
    base
      | c.abstractBase = AbstractStore (SymAddr "c") Nothing
      | otherwise = ConcreteStore (Map.fromList [(refSlot mempty s, v) | (s, v) <- reverse c.baseEntries])

loaded :: Case -> Expr EWord
loaded c = SLoad c.readExpr (store c)

-- | The read value, assuming no hash collisions
expected :: Case -> Expr EWord
expected c = foldr hit fallback ([(s, v) | (s, _, v) <- c.writes] <> c.baseEntries)
  where
    hit (s, v) rest = ITE (sameSlot s c.readSlot) (Lit v) rest
    fallback
      | c.abstractBase = SLoad c.canonRead (AbstractStore (SymAddr "c") Nothing)
      | otherwise = Lit 0

sameSlot :: Slot -> Slot -> Expr EWord
sameSlot (Plain a) (Plain b) = boolLit (a == b)
sameSlot (Mapping k p o) (Mapping k' p' o')
  | o == o' = And (sameKey k k') (sameSlot p p')
sameSlot (Array p i) (Array p' i')
  | i == i' = sameSlot p p'
sameSlot _ _ = Lit 0

sameKey :: Key -> Key -> Expr EWord
sameKey (KLit a) (KLit b) = boolLit (a == b)
sameKey a b = Eq (keyExpr a) (keyExpr b)

boolLit :: Bool -> Expr EWord
boolLit b = Lit (if b then 1 else 0)

keyExpr :: Key -> Expr EWord
keyExpr (KLit w) = Lit w
keyExpr (KVar v) = Var v

refKey :: Map Text W256 -> Key -> W256
refKey _ (KLit w) = w
refKey env (KVar v) = fromMaybe 0 (Map.lookup v env)

refSlot :: Map Text W256 -> Slot -> W256
refSlot _ (Plain s) = s
refSlot env (Mapping k p o) = keccak' (word256Bytes (refKey env k) <> word256Bytes (refSlot env p)) + o
refSlot env (Array p i) = keccak' (word256Bytes (refSlot env p)) + i

refLoad :: Map Text W256 -> Case -> W256
refLoad env c = case [v | (s, _, v) <- c.writes, refSlot env s == r] of
  v : _ -> v
  [] -> fromMaybe 0 $ lookup r [(refSlot env s, v) | (s, v) <- reverse c.baseEntries]
  where r = refSlot env c.readSlot

-- | Whether recovery claims the preimages of the slot as a folded literal, which hides all
-- intermediate hashes: those must be in its shared tables
foldable :: Slot -> Bool
foldable = \case
  Plain _ -> True
  Mapping (KLit _) (Plain _) _ -> True
  Array (Plain _) _ -> True
  Array (Mapping (KLit k) (Plain _) 0) _ -> k < 256
  Mapping (KLit k) (Array (Plain _) 0) _ -> k < 256
  _ -> False

slotVars :: Slot -> [Text]
slotVars = \case
  Plain _ -> []
  Mapping k p _ -> [v | KVar v <- [k]] <> slotVars p
  Array p _ -> slotVars p

-- few names and values, so that layouts share slots
genKey :: Gen Key
genKey = frequency
  [ (3, KVar <$> elements ["k0", "k1"])
  , (3, KLit <$> elements [0, 1, 3])
  , (1, KLit <$> elements [0x5eed1234, maxBound])
  ]

genSlot :: Int -> Gen Slot
genSlot depth = frequency $
  [ (1, Plain <$> elements [0, 1, 2, 3]) ] <>
  [ (w, g) | depth > 0, (w, g) <-
    [ (4, Mapping <$> genKey <*> genSlot (depth - 1) <*> elements [0, 0, 1, 255])
    , (1, Array <$> genSlot (depth - 1) <*> elements [0, 1, 7])
    ] ]

-- | One of the forms in which the slot can reach storage
render :: Slot -> Gen (Expr EWord)
render s = frequency $ [(2, structural s)] <> [(1, pure (Lit (refSlot mempty s))) | foldable s]
  where
    structural = \case
      Plain w -> pure (Lit w)
      Mapping k p o -> do
        pe <- render p
        let ke = keyExpr k
            zeros = BS.replicate 32 0
        buf <- frequency $
          [ (2, pure $ WriteWord (Lit 0) ke (WriteWord (Lit 32) pe (ConcreteBuf "")))
          , (1, do
              junk <- BS.pack <$> vectorOf 320 arbitrary
              pure $ CopySlice (Lit 256) (Lit 0) (Lit 64)
                (WriteWord (Lit 256) ke (WriteWord (Lit 288) pe (ConcreteBuf junk))) (ConcreteBuf ""))
          ] <>
          [ (2, pure $ WriteWord (Lit 0) ke (ConcreteBuf (zeros <> word256Bytes pw))) | Lit pw <- [pe] ] <>
          [ (1, pure $ ConcreteBuf (word256Bytes kw <> word256Bytes pw)) | Lit kw <- [ke], Lit pw <- [pe] ]
        offset o (Keccak buf)
      Array p i -> do
        pe <- render p
        offset i $ Keccak $ case pe of
          Lit pw -> ConcreteBuf (word256Bytes pw)
          _ -> WriteWord (Lit 0) pe (ConcreteBuf "")
    offset 0 h = pure h
    offset o h = elements [Add (Lit o) h, Add h (Lit o)]

canonical :: Slot -> Expr EWord
canonical = \case
  Plain w -> Lit w
  Mapping k p o -> withOffset o $ Keccak (WriteWord (Lit 0) (keyExpr k) (WriteWord (Lit 32) (canonical p) (ConcreteBuf "")))
  Array p i -> withOffset i $ Keccak (WriteWord (Lit 0) (canonical p) (ConcreteBuf ""))
  where
    withOffset 0 h = h
    withOffset o h = Add (Lit o) h

genCaseWith :: Gen Bool -> Gen Case
genCaseWith genAbstract = do
  slots <- resize 4 $ listOf1 (genSlot 2)
  writes <- mapM (\(s, v) -> (s, , v) <$> render s) (zip slots [1 ..])
  concreteSlots <- resize 2 $ listOf (genSlot 2 `suchThat` foldable)
  let baseEntries = nubBy (\a b -> refSlot mempty (fst a) == refSlot mempty (fst b)) (zip concreteSlots [100 ..])
  abstractBase <- genAbstract
  -- mostly re-read a written slot, possibly with different keys
  readSlot <- frequency
    [ (3, elements slots)
    , (1, elements (slots <> map fst baseEntries) >>= rekey)
    , (1, genSlot 2)
    ]
  readExpr <- render readSlot
  pure Case
    { writes, abstractBase, readSlot, readExpr
    , baseEntries = if abstractBase then [] else baseEntries
    , canonRead = canonical readSlot
    }
  where
    rekey = \case
      Mapping _ p o -> Mapping <$> genKey <*> pure p <*> pure o
      s -> pure s

genCase :: Gen Case
genCase = genCaseWith arbitrary

genConcreteBaseCase :: Gen Case
genConcreteBaseCase = genCaseWith (pure False)

shrinkCase :: Case -> [Case]
shrinkCase c =
  [c {writes = w} | w <- dropOne c.writes]
  <> [c {baseEntries = b} | b <- dropOne c.baseEntries]
  <> [c {readExpr = c.canonRead} | c.readExpr /= c.canonRead]
  where dropOne xs = [take i xs <> drop (i + 1) xs | i <- [0 .. length xs - 1]]

-- values that hit the literal keys, so that aliasing happens
genEnv :: Case -> Gen (Map Text W256)
genEnv c = Map.fromList <$> mapM (\v -> (v,) <$> val) vars
  where
    vars = nub $ concatMap slotVars (c.readSlot : [s | (s, _, _) <- c.writes])
    val = frequency [(3, elements [0, 1, 3, 0x5eed1234, maxBound]), (1, arbitrary)]

-- | Two buffers with the same length and the same bytes up to it, built differently
data PrefixCase = PrefixCase
  { bufA :: Expr Buf
  , bufB :: Expr Buf
  , lenProps :: [Prop]
  , extra :: [Prop] -- ^ mentions another hash, which the pairwise assumptions must not upset
  }
  deriving Show

genPrefixCase :: Gen PrefixCase
genPrefixCase = do
  let a = AbstractBuf "a"
  -- concrete lengths only: the SMT encoding cannot copy a symbolically sized region
  n <- elements [0, 1, 4, 31, 32, 33, 64]
  let len = Lit n
      lenProps = [PEq (BufLength a) (Lit n)]
  junk <- BS.pack <$> (choose (0, 32) >>= flip vectorOf arbitrary)
  copy <- elements $
    [ CopySlice (Lit 0) (Lit 0) len a (ConcreteBuf "")
    -- staged in memory after a junk prefix, then copied back to the start
    , CopySlice (Lit 32) (Lit 0) len (CopySlice (Lit 0) (Lit 32) len a (ConcreteBuf junk)) (ConcreteBuf "")
    ] <>
    [ foldr (\i -> WriteWord (Lit i) (ReadWord (Lit i) a)) (ConcreteBuf "") [0, 32 .. n - 32]
    | n > 0, n `mod` 32 == 0 ] <>
    [ foldr (\i -> WriteByte (Lit i) (ReadByte (Lit i) a)) (ConcreteBuf "") [0 .. n - 1]
    | n > 0 ]
  swap <- arbitrary
  extra <- genExtraHash n
  pure $ if swap then PrefixCase copy a lenProps extra else PrefixCase a copy lenProps extra

-- | Another hash, sometimes pinning the first word of 'a' to it: that makes the
-- query define 'a''s copies through chains of buffer variables
genExtraHash :: W256 -> Gen [Prop]
genExtraHash n = elements $
  [ []
  , [PGT (Keccak (AbstractBuf "c")) (Lit 0)]
  , [PEq (BufLength (AbstractBuf "c")) (Lit 32), PGT (Keccak (AbstractBuf "c")) (Lit 0)]
  ] <> [ [PEq (ReadWord (Lit 0) (AbstractBuf "a")) (Keccak (ConcreteBuf "x"))] | n >= 32 ]

-- | A copy of the bytes hashed from 'a' with one byte changed, or one byte longer
genDifferingCase :: Gen PrefixCase
genDifferingCase = do
  c0 <- genPrefixCase
  -- a pinned byte of 'a' could equal the changed one
  let c = c0 { extra = filter (not . pinsA) c0.extra }
      pinsA = \case PEq (ReadWord _ (AbstractBuf "a")) _ -> True; _ -> False
      a = AbstractBuf "a"
      other = if c.bufA == a then c.bufB else c.bufA
      n = case c.lenProps of [PEq _ (Lit l)] -> l; _ -> 0
  i <- chooseBoundedIntegral (0, max 1 n - 1)
  v <- arbitrary
  longer <- if n == 0 then pure True else arbitrary
  pure $ if longer
    then c { bufA = a, bufB = WriteByte (Lit n) (LitByte 0) other }
    else c { bufA = a, bufB = WriteByte (Lit i) (LitByte v) other
           , lenProps = PNeg (PEq (ReadByte (Lit i) a) (LitByte v)) : c.lenProps }
