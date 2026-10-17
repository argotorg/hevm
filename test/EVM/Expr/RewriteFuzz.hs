{-# LANGUAGE DataKinds #-}

-- | Solver-free differential fuzzing of the simplifier: variables and abstract buffers get
-- random concrete values, and a reference evaluator compares the original and the simplified
-- expression.
module EVM.Expr.RewriteFuzz
  ( tests
  , genShapedWord
  , genShapedProp
  , shrinkWord
  , shrinkProp
  , evalWord
  , evalProp
  , FuzzEnv(..)
  ) where

import Prelude hiding (LT, GT)

import Data.Bits (shiftL, shiftR, testBit, (.&.), (.|.), xor, complement, countLeadingZeros)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Word (Word8)
import Data.Typeable (Typeable, eqT, (:~:)(..))
import Test.QuickCheck hiding ((.&.))
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, QuickCheckTests(..))

import EVM.Expr qualified as Expr
import EVM.Expr.Generator ()
import EVM.Traversals (foldExpr, mapExpr)
import EVM.Types

tests :: TestTree
tests = testGroup "Rewrite fuzzing"
  -- cheap, so many more cases than the solver-backed properties
  [ adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10000 else n)) $
      testProperty "rewrite-fuzz-word" prop_word
  , adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10000 else n)) $
      testProperty "rewrite-fuzz-prop" prop_prop
  -- guards the reference semantics: with everything concrete, the simplifier folds to the same value
  , adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10000 else n)) $
      testProperty "rewrite-fuzz-eval-matches-folding" prop_folding
  , adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10000 else n)) $
      testProperty "bounds-fuzz" prop_bounds
  ]

prop_word :: Property
prop_word = forAllShrink (sized $ \n -> genShapedWord (min n 40)) shrinkWord $ \e ->
  let s = Expr.simplify e
  in forAll (vectorOf 20 (genEnv e)) $ \envs -> within 5_000_000 $
    checkAll (s == e) [(env, evalWord env e, evalWord env s, show s) | env <- envs]

prop_prop :: Property
prop_prop = forAllShrink (sized $ \n -> genShapedProp (min n 30)) shrinkProp $ \p ->
  let s = Expr.simplifyProp p
      ss = Expr.simplifyProps [p]
      conj env = and <$> mapM (evalProp env) ss
  in forAll (vectorOf 20 (genEnvProp p)) $ \envs -> within 5_000_000 $
    checkAll (s == p) $ concat
      [ [(env, evalProp env p, evalProp env s, show s), (env, evalProp env p, conj env, show ss)] | env <- envs ]

prop_folding :: Property
prop_folding = forAll (sized $ \n -> genShapedWord (min n 40)) $ \e -> forAll (genEnv e) $ \env ->
  case (evalWord env e, Expr.simplify (substitute env e)) of
    (Just v, Lit v') -> counterexample ("env: " <> show env) $ v === v'
    (Just _, other) -> tabulate "folding" ["did not fold"] $ counterexample (show other) True
    (Nothing, _) -> tabulate "folding" ["not evaluable"] True

-- | The bounds that the simplifier derives are sound: under bound props that
-- hold in the environment, every subterm's value is within them
prop_bounds :: Property
prop_bounds = forAllShrink (sized $ \n -> genShapedWord (min n 40)) shrinkWord $ \e ->
  forAll (genEnv e) $ \env ->
    let vals = [(t, v) | t <- take 30 (nub (foldExpr (maybe [] pure . Expr.asWord) [] e)), Just v <- [evalWord env t]]
    in forAll (genFacts vals) $ \facts ->
      let bs = Expr.propBounds facts
          inBounds = [ counterexample ("propBounds: " <> show t <> " = " <> show v <> " outside " <> show (lb, ub, ex)) $
                         lb <= v && v <= ub && Prelude.not (v `elem` ex)
                     | (t, v) <- vals, Just (Expr.Bounds lb ub ex) <- [Map.lookup t bs] ]
          uppers = [ counterexample ("upperWithBounds: " <> show t <> " = " <> show v <> " > " <> show u) $ v <= u
                   | (t, v) <- vals, let u = Expr.upperWithBounds bs t ]
                <> [ counterexample ("upperBound: " <> show t <> " = " <> show v <> " > " <> show u) $ v <= u
                   | (t, v) <- vals, Just u <- [Expr.upperBound t] ]
                <> [ counterexample ("possibleOnes: " <> show t <> " = " <> show v) $ v .&. complement (Expr.possibleOnes t) == 0
                   | (t, v) <- vals ]
      in counterexample ("env: " <> show env <> "\nfacts: " <> show facts) $
           tabulate "bounded subterms" [show (length inBounds)] $
           conjoin (inBounds <> uppers)

-- | Props that hold for subterms with these values, in the shapes that bounds are read from
genFacts :: [(Expr EWord, W256)] -> Gen [Prop]
genFacts [] = pure []
genFacts vals = do
  k <- choose (0, 4)
  vectorOf k (elements vals >>= uncurry fact)
  where
    fact t v = frequency
      [ (3, PLEq t . Lit <$> above v)
      , (if v < maxBound then 2 else 0, (\u -> PLT t (Lit (u + 1))) <$> suchThat (above v) (< maxBound))
      , (3, PLEq <$> (Lit <$> below v) <*> pure t)
      , (if v > 0 then 2 else 0, (\l -> PLT (Lit (l - 1)) t) <$> suchThat (below v) (> 0))
      , (2, elements [PEq (Lit v) t, PEq t (Lit v), PEq (Lit 0) (Xor (Lit v) t), PEq (Lit 0) (Xor t (Lit v))])
      , (2, (\c f -> f c) <$> suchThat genSpecialLit (/= v)
              <*> elements [PNeg . (`PEq` t) . Lit, PNeg . PEq t . Lit, \c -> PNeg (PEq (Lit 0) (Xor (Lit c) t))])
      , (1, PAnd <$> fact t v <*> fact t v)
      ]
    above v = elements $ nub $ [v, maxBound, if v == 0 then 0 else maxBound `shiftR` countLeadingZeros v]
      <> [v + d | d <- [1, 2, 3], v + d > v]
    below v = elements $ nub $ [v, 0, if v == 0 then 0 else 1 `shiftL` (255 - countLeadingZeros v)]
      <> [v - d | d <- [1, 2, 3], v - d < v]

substitute :: FuzzEnv -> Expr a -> Expr a
substitute env = mapExpr $ \case
  Var n | Just v <- Map.lookup n env.vars -> Lit v
  AbstractBuf n | Just b <- Map.lookup n env.bufs -> ConcreteBuf b
  e -> e

checkAll :: (Eq a, Show a) => Bool -> [(FuzzEnv, Maybe a, Maybe a, String)] -> Property
checkAll unchanged cases =
  tabulate "simplified" [if unchanged then "unchanged" else "changed"] $
  tabulate "evaluation" (map status cases) $
  conjoin [ counterexample (unlines ["env: " <> show env, "simplified: " <> shown, "original value: " <> show a, "simplified value: " <> show b]) (a == b)
          | (env, Just a, Just b, shown) <- cases ]
  where
    status (_, Just _, Just _, _) = "compared"
    status (_, Just _, Nothing, _) = "simplified not evaluable"
    status _ = "original not evaluable"

-- * Reference semantics

data FuzzEnv = FuzzEnv { vars :: Map Text W256, bufs :: Map Text ByteString }
  deriving Show

-- | Writes and copies past this are not materialized, the expression is then not evaluated
bufBound :: Integer
bufBound = 1_000_000

modulus :: Integer
modulus = 2 ^ (256 :: Int)

toW :: Integer -> W256
toW i = fromInteger (i `mod` modulus)

toI :: W256 -> Integer
toI = toInteger

toS :: W256 -> Integer
toS x = let i = toI x in if testBit i 255 then i - modulus else i

boolW :: Bool -> W256
boolW b = if b then 1 else 0

evalWord :: FuzzEnv -> Expr EWord -> Maybe W256
evalWord env = go
  where
    go :: Expr EWord -> Maybe W256
    go = \case
      Lit x -> Just x
      Var n -> Map.lookup n env.vars
      WAddr (LitAddr a) -> Just (fromIntegral a)
      Add a b -> int2 (+) a b
      Sub a b -> int2 (-) a b
      Mul a b -> int2 (*) a b
      Div a b -> int2 (\x y -> if y == 0 then 0 else x `div` y) a b
      Mod a b -> int2 (\x y -> if y == 0 then 0 else x `mod` y) a b
      SDiv a b -> sint2 (\x y -> if y == 0 then 0 else x `quot` y) a b
      SMod a b -> sint2 (\x y -> if y == 0 then 0 else x `rem` y) a b
      AddMod a b c -> int3 (\x y z -> if z == 0 then 0 else (x + y) `mod` z) a b c
      MulMod a b c -> int3 (\x y z -> if z == 0 then 0 else (x * y) `mod` z) a b c
      Exp a b -> int2 powMod a b
      SEx a b -> do
        n <- toI <$> go a
        x <- toI <$> go b
        pure $ if n >= 31 then toW x
          else let bitN = fromInteger (8 * n + 7)
                   low = x .&. ((1 `shiftL` (bitN + 1)) - 1)
               in toW $ if testBit x bitN then low - (1 `shiftL` (bitN + 1)) else low
      Min a b -> int2 min a b
      Max a b -> int2 max a b
      LT a b -> cmp (<) a b
      GT a b -> cmp (>) a b
      LEq a b -> cmp (<=) a b
      GEq a b -> cmp (>=) a b
      SLT a b -> scmp (<) a b
      SGT a b -> scmp (>) a b
      Eq a b -> cmp (==) a b
      IsZero a -> boolW . (== 0) <$> go a
      ITE c t f -> go c >>= \cv -> if cv /= 0 then go t else go f
      And a b -> int2 (.&.) a b
      Or a b -> int2 (.|.) a b
      Xor a b -> int2 xor a b
      Not a -> toW . (\x -> complement x .&. (modulus - 1)) . toI <$> go a
      SHL s x -> shift2 (\v k -> v `shiftL` k) s x
      SHR s x -> shift2 (\v k -> v `shiftR` k) s x
      SAR s x -> do
        k <- toI <$> go s
        v <- toS <$> go x
        pure $ toW (v `shiftR` fromInteger (min 256 k))
      CLZ a -> (\x -> toW (256 - bitLen (toI x))) <$> go a
      EqByte a b -> (\x y -> boolW (x == y)) <$> evalByte env a <*> evalByte env b
      JoinBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 -> do
        bs <- mapM (evalByte env)
          [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
           b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]
        pure $ toW (foldl (\acc b -> acc * 256 + toInteger b) 0 bs)
      ReadWord i buf -> do
        idx <- toI <$> go i
        bs <- evalBuf env buf
        if idx + 31 >= modulus then Nothing
        else pure $ toW (foldl (\acc j -> acc * 256 + toInteger (byteAt bs (idx + j))) 0 [0 .. 31])
      BufLength buf -> toW . toInteger . BS.length <$> evalBuf env buf
      _ -> Nothing
    int2 f a b = (\x y -> toW (f (toI x) (toI y))) <$> go a <*> go b
    int3 f a b c = (\x y z -> toW (f (toI x) (toI y) (toI z))) <$> go a <*> go b <*> go c
    sint2 f a b = (\x y -> toW (f (toS x) (toS y))) <$> go a <*> go b
    cmp f a b = (\x y -> boolW (f (toI x) (toI y))) <$> go a <*> go b
    scmp f a b = (\x y -> boolW (f (toS x) (toS y))) <$> go a <*> go b
    shift2 f s x = do
      k <- toI <$> go s
      v <- toI <$> go x
      pure $ if k >= 256 then 0 else toW (f v (fromInteger k))
    powMod b e = goPow (b `mod` modulus) e 1
      where goPow _ 0 acc = acc
            goPow x k acc = goPow (x * x `mod` modulus) (k `div` 2) (if odd k then acc * x `mod` modulus else acc)
    bitLen :: Integer -> Integer
    bitLen 0 = 0
    bitLen x = 1 + bitLen (x `shiftR` 1)

evalByte :: FuzzEnv -> Expr Byte -> Maybe Integer
evalByte env = \case
  LitByte b -> Just (toInteger b)
  IndexWord i w -> do
    idx <- toI <$> evalWord env i
    v <- toI <$> evalWord env w
    pure $ if idx >= 32 then 0 else (v `shiftR` fromInteger (8 * (31 - idx))) .&. 0xff
  ReadByte i buf -> do
    idx <- toI <$> evalWord env i
    bs <- evalBuf env buf
    pure $ toInteger (byteAt bs idx)
  _ -> Nothing

byteAt :: ByteString -> Integer -> Word8
byteAt bs i = if i < toInteger (BS.length bs) then BS.index bs (fromInteger i) else 0

-- | A buffer as its materialized bytes: its length is the buffer length, bytes past it are 0
evalBuf :: FuzzEnv -> Expr Buf -> Maybe ByteString
evalBuf env = \case
  ConcreteBuf bs -> Just bs
  AbstractBuf n -> Map.lookup n env.bufs
  WriteWord i v b -> do
    idx <- toI <$> evalWord env i
    val <- evalWord env v
    bs <- evalBuf env b
    if idx + 32 > bufBound then Nothing else pure $ splice idx (word256Bytes val) bs
  WriteByte i v b -> do
    idx <- toI <$> evalWord env i
    val <- evalByte env v
    bs <- evalBuf env b
    if idx + 1 > bufBound then Nothing else pure $ splice idx (BS.singleton (fromInteger val)) bs
  CopySlice so d sz src dst -> do
    srcOff <- toI <$> evalWord env so
    dstOff <- toI <$> evalWord env d
    size <- toI <$> evalWord env sz
    s <- evalBuf env src
    t <- evalBuf env dst
    if size == 0 then pure t
    else if dstOff + size > bufBound || srcOff + size > modulus then Nothing
    else pure $ splice dstOff (BS.pack [byteAt s (srcOff + j) | j <- [0 .. size - 1]]) t
  _ -> Nothing
  where
    splice off new bs =
      let o = fromInteger off
          padded = bs <> BS.replicate (o + BS.length new - BS.length bs) 0
      in BS.take o padded <> new <> BS.drop (o + BS.length new) padded

evalProp :: FuzzEnv -> Prop -> Maybe Bool
evalProp env = \case
  PBool b -> Just b
  PEq a b -> peq a b
  PLT a b -> (<) <$> w a <*> w b
  PGT a b -> (>) <$> w a <*> w b
  PLEq a b -> (<=) <$> w a <*> w b
  PGEq a b -> (>=) <$> w a <*> w b
  PNeg a -> not <$> evalProp env a
  PAnd a b -> (&&) <$> evalProp env a <*> evalProp env b
  POr a b -> (||) <$> evalProp env a <*> evalProp env b
  PImpl a b -> (\x y -> not x || y) <$> evalProp env a <*> evalProp env b
  _ -> Nothing
  where
    w = fmap toI . evalWord env
    peq :: forall t. Typeable t => Expr t -> Expr t -> Maybe Bool
    peq a b = case eqT @t @EWord of
      Just Refl -> (==) <$> w a <*> w b
      Nothing -> case eqT @t @Byte of
        Just Refl -> (==) <$> evalByte env a <*> evalByte env b
        Nothing -> Nothing

-- * Generators

-- | Replace a node by one of its word children, or shrink a child
shrinkWord :: Expr EWord -> [Expr EWord]
shrinkWord e = case e of
  Lit x -> Lit <$> filter (< x) [0, 1, x `div` 2]
  Var _ -> [Lit 0]
  ReadWord i b -> [ReadWord i b' | b' <- shrinkBuf b] <> [ReadWord i' b | i' <- shrinkWord i]
  BufLength b -> Lit 0 : [BufLength b' | b' <- shrinkBuf b]
  _ -> case wordChildren e of
    Nothing -> []
    Just (cs, rebuild) -> cs <> [rebuild (pre <> [c'] <> post) | (pre, c, post) <- splits cs, c' <- shrinkWord c]
  where
    splits xs = [(take i xs, xs !! i, drop (i + 1) xs) | i <- [0 .. length xs - 1]]

wordChildren :: Expr EWord -> Maybe ([Expr EWord], [Expr EWord] -> Expr EWord)
wordChildren = \case
  Add a b -> two Add a b; Sub a b -> two Sub a b; Mul a b -> two Mul a b; Div a b -> two Div a b
  Mod a b -> two Mod a b; SDiv a b -> two SDiv a b; SMod a b -> two SMod a b; Exp a b -> two Exp a b
  SEx a b -> two SEx a b; Min a b -> two Min a b; Max a b -> two Max a b
  LT a b -> two LT a b; GT a b -> two GT a b; LEq a b -> two LEq a b; GEq a b -> two GEq a b
  SLT a b -> two SLT a b; SGT a b -> two SGT a b; Eq a b -> two Eq a b
  And a b -> two And a b; Or a b -> two Or a b; Xor a b -> two Xor a b
  SHL a b -> two SHL a b; SHR a b -> two SHR a b; SAR a b -> two SAR a b
  AddMod a b c -> three AddMod a b c; MulMod a b c -> three MulMod a b c; ITE a b c -> three ITE a b c
  IsZero a -> one IsZero a; Not a -> one Not a; CLZ a -> one CLZ a
  ReadWord i b -> Just ([i], \case [x] -> ReadWord x b; _ -> ReadWord i b)
  _ -> Nothing
  where
    one f a = Just ([a], \case [x] -> f x; _ -> f a)
    two f a b = Just ([a, b], \case [x, y] -> f x y; _ -> f a b)
    three f a b c = Just ([a, b, c], \case [x, y, z] -> f x y z; _ -> f a b c)

shrinkBuf :: Expr Buf -> [Expr Buf]
shrinkBuf = \case
  ConcreteBuf bs -> [ConcreteBuf "" | bs /= ""] <> [ConcreteBuf (BS.take (BS.length bs `div` 2) bs) | BS.length bs > 1]
  AbstractBuf _ -> [ConcreteBuf ""]
  WriteWord i v b -> b : [WriteWord i v b' | b' <- shrinkBuf b] <> [WriteWord i' v b | i' <- shrinkWord i] <> [WriteWord i v' b | v' <- shrinkWord v]
  WriteByte i v b -> b : [WriteByte i v b' | b' <- shrinkBuf b] <> [WriteByte i' v b | i' <- shrinkWord i]
  CopySlice so d sz src dst -> [src, dst]
    <> [CopySlice so d sz src' dst | src' <- shrinkBuf src] <> [CopySlice so d sz src dst' | dst' <- shrinkBuf dst]
    <> [CopySlice so' d sz src dst | so' <- shrinkWord so] <> [CopySlice so d' sz src dst | d' <- shrinkWord d]
    <> [CopySlice so d sz' src dst | sz' <- shrinkWord sz]
  _ -> []

shrinkProp :: Prop -> [Prop]
shrinkProp = \case
  PEq (a :: Expr t) b | Just Refl <- eqT @t @EWord -> wordPair PEq a b
  PLT a b -> wordPair PLT a b
  PGT a b -> wordPair PGT a b
  PLEq a b -> wordPair PLEq a b
  PGEq a b -> wordPair PGEq a b
  PNeg a -> a : (PNeg <$> shrinkProp a)
  PAnd a b -> [a, b] <> [PAnd a' b | a' <- shrinkProp a] <> [PAnd a b' | b' <- shrinkProp b]
  POr a b -> [a, b] <> [POr a' b | a' <- shrinkProp a] <> [POr a b' | b' <- shrinkProp b]
  PImpl a b -> [a, b] <> [PImpl a' b | a' <- shrinkProp a] <> [PImpl a b' | b' <- shrinkProp b]
  _ -> []
  where
    wordPair :: (Expr EWord -> Expr EWord -> Prop) -> Expr EWord -> Expr EWord -> [Prop]
    wordPair f a b = [f a' b | a' <- shrinkWord a] <> [f a b' | b' <- shrinkWord b]

varNames :: [Text]
varNames = ["a", "b", "c", "d"]

genSpecialLit :: Gen W256
genSpecialLit = frequency
  [ (3, fromIntegral <$> choose (0 :: Int, 40))
  , (2, elements [0, 1, 2, 31, 32, 0xff, Expr.maxLit, Expr.maxLitSigned, Expr.minLitSigned, 2 ^ (160 :: Int) - 1])
  , (2, (2 ^) <$> choose (0 :: Int, 255))
  , (2, (\k -> 2 ^ k - 1) <$> choose (0 :: Int, 256))
  , (1, (\k j -> (2 ^ k - 1) `shiftL` j) <$> choose (0 :: Int, 256) <*> choose (0, 255))
  , (1, arbitrary)
  ]

genLeaf :: Gen (Expr EWord)
genLeaf = frequency [(3, Var <$> elements varNames), (3, Lit <$> genSpecialLit)]

genShapedWord :: Int -> Gen (Expr EWord)
genShapedWord 0 = genLeaf
genShapedWord n = frequency
  [ (3, genLeaf)
  , (4, genTemplate s shiftAmt)
  , (2, Add <$> s <*> s), (2, Sub <$> s <*> s), (1, Mul <$> s <*> s)
  , (1, Div <$> s <*> s), (1, Mod <$> s <*> s), (1, SDiv <$> s <*> s), (1, SMod <$> s <*> s)
  , (1, AddMod <$> s <*> s <*> s), (1, MulMod <$> s <*> s <*> s)
  , (1, Exp <$> s <*> (Lit . fromIntegral <$> choose (0 :: Int, 300)))
  , (1, SEx <$> (Lit . fromIntegral <$> choose (0 :: Int, 33)) <*> s)
  , (1, Min <$> s <*> s), (1, Max <$> s <*> s)
  , (1, LT <$> s <*> s), (1, GT <$> s <*> s), (1, LEq <$> s <*> s), (1, GEq <$> s <*> s)
  , (1, SLT <$> s <*> s), (1, SGT <$> s <*> s), (2, Eq <$> s <*> s), (2, IsZero <$> s)
  , (2, ITE <$> s <*> s <*> s)
  , (2, And <$> s <*> s), (2, Or <$> s <*> s), (1, Xor <$> s <*> s), (1, Not <$> s)
  , (2, SHL <$> shiftAmt <*> s), (2, SHR <$> shiftAmt <*> s), (1, SAR <$> shiftAmt <*> s)
  , (1, CLZ <$> s)
  , (1, ReadWord <$> smallIdx <*> genShapedBuf (n `div` 2))
  , (1, BufLength <$> genShapedBuf (n `div` 2))
  , (1, EqByte <$> genShapedByte (n `div` 2) <*> genShapedByte (n `div` 2))
  ]
  where
    s = genShapedWord (n `div` 2)
    -- mostly from a small palette, so that the amounts of nested shifts often coincide
    shiftAmt = frequency
      [ (4, Lit <$> elements [0, 1, 8, 16, 32, 64, 96, 128, 160, 224, 248, 255, 256])
      , (2, Lit . fromIntegral <$> choose (0 :: Int, 260))
      , (1, s)
      ]
    smallIdx = smallIdxWith s

-- | A buffer offset or size. Kept bounded when concrete: the simplifier materializes concrete
-- buffers up to 'Expr.maxBytes', and huge ones exhaust memory.
-- | The shapes that rewrite rules match, built directly: random composition rarely puts a
-- literal exactly where a rule needs it
genTemplate :: Gen (Expr EWord) -> Gen (Expr EWord) -> Gen (Expr EWord)
genTemplate s shiftAmt = oneof
  [ Eq <$> lit <*> (litOp <*> lit <*> s)
  , Eq <$> (Add <$> lit <*> s) <*> (Add <$> lit <*> s)
  , Eq <$> lit <*> (Not <$> s)
  , IsZero <$> (litOp <*> lit <*> s)
  , And <$> lit <*> (shiftOp <*> shiftAmt <*> s)
  , shiftOp <*> shiftAmt <*> (shiftOp <*> shiftAmt <*> s)
  , SAR <$> shiftAmt <*> (SAR <$> shiftAmt <*> s)
  , Mod <$> s <*> pow2, Div <$> s <*> pow2
  , LT <$> (And <$> lit <*> s) <*> lit
  , LT <$> lit <*> (And <$> lit <*> s)
  , litOp' <*> lit <*> ite, litOp' <*> ite <*> lit, litOp' <*> ite <*> ite
  , IsZero <$> ite, Not <$> ite
  , ITE <$> (IsZero <$> s) <*> s <*> s
  , ITE <$> s <*> elements [Lit 0, Lit 1] <*> elements [Lit 0, Lit 1]
  , shared
  , Not <$> (elements [Add, Sub, Xor] <*> lit <*> s)
  , Mul <$> lit <*> (Add <$> lit <*> s)
  ]
  where
    -- one operand twice, as cancellations need
    shared = do
      x <- s
      y <- s
      elements
        [ Add x (Sub y x), Add (Sub y x) x, Sub x (Add x y), Sub x (Add y x), Sub x (Sub x y)
        , Xor x (Xor x y), Xor (Xor y x) x, Or x (Or x y), And x (And y x)
        , Or x (Not x), Xor (Not x) x, Add x (Not x), Max x x, Min x x, Eq x (Add x y), Eq x (Sub x y)
        , LT x (Add y x), LT (Add y x) x, LT x (Sub x y), LT (Sub x y) x, GT x (Add y x), LEq x (Sub x y) ]
    -- literal branches, sharing a condition from a small set so that ITEs pair up
    ite = ITE <$> elements [Var "a", LT (Var "a") (Var "b"), IsZero (Var "c")] <*> lit <*> lit
    litOp' = elements [Add, Sub, Mul, Div, Mod, And, Or, Xor, Eq, LT, SLT, SHL, SHR, SAR]
    lit = Lit <$> genSpecialLit
    pow2 = Lit . (2 ^) <$> choose (0 :: Int, 255)
    litOp = elements [Add, Sub, Xor, Mul]
    shiftOp = elements [SHL, SHR]

ptrOff :: Gen Int
ptrOff = frequency
  [ (1, choose (0, 96))
  , (2, (\k e -> 32 * k + e) <$> choose (0, 2) <*> elements [-1, 0, 1, 31])
  ]

ptr :: Int -> Expr EWord
ptr o | o < 0 = Sub (Var "p") (Lit (fromIntegral (negate o)))
ptr 0 = Var "p"
ptr o = Add (Lit (fromIntegral o)) (Var "p")

smallIdxWith :: Gen (Expr EWord) -> Gen (Expr EWord)
smallIdxWith s = frequency
  [ (8, Lit . fromIntegral <$> choose (0 :: Int, 100))
  , (3, ptr <$> ptrOff)
  , (1, Var <$> elements varNames)
  , (1, Add <$> (Lit . fromIntegral <$> choose (0 :: Int, 64)) <*> (Var <$> elements varNames))
  , (1, And (Lit 0x3f) <$> s)
  ]

genShapedByte :: Int -> Gen (Expr Byte)
genShapedByte n = frequency
  [ (1, LitByte <$> arbitrary)
  , (2, IndexWord <$> (Lit . fromIntegral <$> choose (0 :: Int, 33)) <*> genShapedWord n)
  , (2, ReadByte <$> smallIdxWith (genShapedWord n) <*> genShapedBuf n)
  ]

genShapedBuf :: Int -> Gen (Expr Buf)
genShapedBuf 0 = oneof
  [ ConcreteBuf <$> genBytes
  , AbstractBuf <$> elements ["src", "buf"]
  , ConcreteBuf . flip BS.replicate 0 <$> choose (0, 80)
  ]
genShapedBuf n = frequency
  [ (2, genShapedBuf 0)
  , (2, overwrite)
  , (2, pointerWrites)
  , (2, WriteWord <$> idx <*> w <*> sub)
  , (1, WriteByte <$> idx <*> genShapedByte (n `div` 2) <*> sub)
  , (2, CopySlice <$> idx <*> idx <*> size <*> sub <*> sub)
  ]
  where
    w = genShapedWord (n `div` 2)
    idx = smallIdxWith w
    sub = genShapedBuf (n `div` 2)
    -- writes at offsets from a symbolic pointer, as reads from it need
    pointerWrites = do
      k <- choose (1, 4 :: Int)
      offs <- vectorOf k ptrOff
      foldr (\o acc -> oneof [WriteWord (ptr o) <$> w <*> acc, WriteByte (ptr o) <$> genShapedByte 0 <*> acc]) sub offs
    -- a copy over writes in and around its window
    overwrite = do
      d <- choose (0, 64 :: Int)
      sz <- choose (1, 80)
      k <- choose (1, 4 :: Int)
      offs <- vectorOf k $ frequency
        [(3, choose (d, d + sz)), (1, choose (Prelude.max 0 (d - 32), d + sz + 32)), (1, elements [d, d + sz - 32, d + sz - 31, d + sz - 1])]
      dst <- foldr (\o acc -> oneof [WriteWord (Lit (fromIntegral (Prelude.max 0 o))) <$> w <*> acc, WriteByte (Lit (fromIntegral (Prelude.max 0 o))) <$> genShapedByte 0 <*> acc]) sub offs
      CopySlice <$> idx <*> pure (Lit (fromIntegral d)) <*> pure (Lit (fromIntegral sz)) <*> sub <*> pure dst
    size = frequency [(4, Lit . fromIntegral <$> choose (0 :: Int, 80)), (1, smallIdxWith w)]

genBytes :: Gen ByteString
genBytes = do
  len <- frequency [(1, pure 0), (3, choose (1, 100))]
  BS.pack <$> vectorOf len (frequency [(2, pure 0), (3, arbitrary)])

genShapedProp :: Int -> Gen Prop
genShapedProp 0 = PBool <$> arbitrary
genShapedProp n = frequency
  [ (3, PEq <$> w <*> w), (2, PLT <$> w <*> w), (1, PGT <$> w <*> w)
  , (2, PLEq <$> w <*> w), (1, PGEq <$> w <*> w)
  , (2, PNeg <$> p), (2, PAnd <$> p <*> p), (2, POr <$> p <*> p), (1, PImpl <$> p <*> p)
  , (2, overflowCheck)
  , (2, mulOverflowCheck)
  , (2, PEq <$> lit <*> ite), (1, PLT <$> lit <*> ite), (1, PLT <$> ite <*> lit)
  , (1, PLEq <$> lit <*> ite), (1, PLEq <$> ite <*> lit)
  ]
  where
    lit = Lit <$> genSpecialLit
    ite = ITE <$> w <*> lit <*> lit
    overflowCheck = do
      x <- w
      c <- lit
      op <- elements [PLT, PLEq, PGT, PGEq]
      e <- elements [Add c x, Sub x c]
      elements [op x e, op e x]
    -- Solidity's checked multiplication under bounds, around where the product overflows
    mulOverflowCheck = do
      let var = Var <$> elements varNames
          scaled = Div <$> (Mul <$> var <*> (Mod <$> var <*> lit)) <*> lit
      x <- frequency [(2, var), (1, w), (1, scaled), (1, Add <$> lit <*> scaled)]
      d <- frequency [(2, var), (1, w), (1, lit)]
      bx <- frequency [(3, Lit . (\k -> 2 ^ k - 1) <$> choose (0 :: Int, 256)), (1, lit)]
      bd <- case bx of
        Lit c | c > 0 -> frequency [(3, (\o -> Lit (Expr.maxLit `div` c + o)) <$> elements [-1, 0, 1]), (1, lit)]
        _ -> lit
      -- bounds on the variables, which bound compound x and d through their structure
      va <- var
      ba <- frequency [(3, Lit . (\k -> 2 ^ k - 1) <$> choose (0 :: Int, 256)), (1, lit)]
      prod <- elements [Mul x d, Mul d x]
      eq <- elements [PEq x (Div prod d), PEq (Div prod d) x]
      let z = PEq (Lit 0) d
          guardW = Or (Eq x (Div prod d)) (IsZero d)
      g <- elements [POr eq z, POr z eq, eq, PNeg eq, PEq (Lit 0) guardW, PNeg (PEq (Lit 0) guardW)]
      pure $ PAnd (PLEq va ba) (PAnd (PLEq x bx) (PAnd (PLEq d bd) g))
    w = genShapedWord (n `div` 2)
    p = genShapedProp (n `div` 2)

-- | Variable values biased towards the literals of the expression and their neighbours,
-- where equalities and comparisons flip
genEnvFrom :: [W256] -> [Text] -> Gen FuzzEnv
genEnvFrom lits names = do
  let near = nub $ concat [[l - 1, l, l + 1] | l <- lits]
      -- values that solve equalities like c = d + x or c = k * x
      few = take 8 lits
      solving = nub $ [f a b | a <- few, b <- few, f <- [(+), (-), xor]]
        <> [a * Expr.oddInverse b | a <- few, b <- few, odd b] <> map complement few
      val = frequency $ [(3, elements near) | Prelude.not (null near)]
        <> [(2, elements solving) | Prelude.not (null solving)] <> [(2, genSpecialLit), (1, arbitrary)]
  vs <- mapM (\v -> (v,) <$> val) varNames
  p <- frequency [(3, fromIntegral <$> choose (0 :: Int, 200)), (1, val)]
  bs <- mapM (\b -> (b,) <$> genBytes) names
  pure $ FuzzEnv (Map.fromList (("p", p) : vs)) (Map.fromList bs)

genEnv :: Expr a -> Gen FuzzEnv
genEnv e = genEnvFrom (litsOf e) ["src", "buf"]

genEnvProp :: Prop -> Gen FuzzEnv
genEnvProp p = genEnvFrom (propLits p) ["src", "buf"]

litsOf :: Expr a -> [W256]
litsOf = take 30 . nub . foldExpr (\case Lit x -> [x]; _ -> []) []

propLits :: Prop -> [W256]
propLits = \case
  PEq a b -> litsOf a <> litsOf b
  PLT a b -> litsOf a <> litsOf b
  PGT a b -> litsOf a <> litsOf b
  PLEq a b -> litsOf a <> litsOf b
  PGEq a b -> litsOf a <> litsOf b
  PNeg a -> propLits a
  PAnd a b -> propLits a <> propLits b
  POr a b -> propLits a <> propLits b
  PImpl a b -> propLits a <> propLits b
  _ -> []
