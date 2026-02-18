{- | Abstract div/mobsolud encoding for two-phase SMT solving. -}
module EVM.SMT.DivModEncoding
  ( divModGroundTruth
  , divModEncoding
  , divModAbstractDecls
  ) where

import Data.Bits ((.&.), countTrailingZeros)
import Data.Containers.ListUtils (nubOrd)
import Data.List (groupBy, sortBy)
import Data.Ord (comparing)
import Data.Text.Lazy.Builder
import qualified Data.Text.Lazy.Builder.Int
import EVM.SMT.Types
import EVM.Traversals
import EVM.Types (Prop(..), EType(EWord), Err, W256, Expr, Expr(Lit), Expr(SHL))
import EVM.Types qualified as T

-- | Uninterpreted function declarations for abstract div/mod.
divModAbstractDecls :: [SMTEntry]
divModAbstractDecls =
  [ SMTComment "abstract division/modulo (uninterpreted functions)"
  , SMTCommand "(declare-fun abst_evm_bvsdiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvsrem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

-- | Local helper for trivial SMT constructs
sp :: Builder -> Builder -> Builder
a `sp` b = a <> " " <> b

zero :: Builder
zero = "(_ bv0 256)"

wordAsBV :: forall a. Integral a => a -> Builder
wordAsBV w = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal w <> " 256)"

data DivModKind = IsDiv | IsMod
  deriving (Eq, Ord)

type DivModOp = (DivModKind, Expr EWord, Expr EWord)

data AbstractKey = AbstractKey (Expr EWord) (Expr EWord) DivModKind
  deriving (Eq, Ord)

isDiv :: DivModKind -> Bool
isDiv IsDiv = True
isDiv _     = False

-- | Collect all div/mod operations from an expression.
collectDivMods :: Expr a -> [DivModOp]
collectDivMods = \case
  T.SDiv a b -> [(IsDiv, a, b)]
  T.SMod a b -> [(IsMod, a, b)]
  _          -> []

abstractKey :: DivModOp -> AbstractKey
abstractKey (kind, a, b) = AbstractKey a b kind

-- | Declare abs_a, abs_b, and unsigned result variables for a signed group.
declareAbsolute :: (Expr EWord -> Err Builder) -> Int -> Expr EWord -> Expr EWord -> Builder -> Err ([SMTEntry], (Builder, Builder))
declareAbsolute enc groupIdx firstA firstB unsignedResult = do
  aenc <- enc firstA
  benc <- enc firstB
  let absAEnc = smtAbsolute aenc
      absBEnc = smtAbsolute benc
      absoluteAName = fromString $ "absolute_a" <> show groupIdx
      absoluteBName = fromString $ "absolute_b" <> show groupIdx
  let decls = [ SMTCommand $ "(declare-const" `sp` absoluteAName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` absoluteBName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` unsignedResult `sp` "(_ BitVec 256))"
              , SMTCommand $ "(assert (=" `sp` absoluteAName `sp` absAEnc <> "))"
              , SMTCommand $ "(assert (=" `sp` absoluteBName `sp` absBEnc <> "))"
              ]
  pure (decls, (absoluteAName, absoluteBName))

-- | Assert abstract(a,b) = signed result derived from unsigned result.
assertSignedEqualsUnsignedDerived :: (Expr EWord -> Err Builder) -> Builder -> DivModOp -> Err SMTEntry
assertSignedEqualsUnsignedDerived enc unsignedResult (kind, a, b) = do
  aenc <- enc a
  benc <- enc b
  let fname = if isDiv kind then "abst_evm_bvsdiv" else "abst_evm_bvsrem"
      abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
      concrete = if isDiv kind
                 then signedFromUnsignedDiv aenc benc unsignedResult
                 else signedFromUnsignedMod aenc benc unsignedResult
  pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Ground-truth axioms: for each sdiv/smod op, assert that the abstract
-- uninterpreted function equals the real bvsdiv/bvsrem.
-- e.g. (assert (= (abst_evm_bvsdiv a b) (bvsdiv a b)))
divModGroundTruth :: (Expr EWord -> Err Builder) -> [Prop] -> Err [SMTEntry]
divModGroundTruth enc props = do
  let allDivMods = nubOrd $ concatMap (foldProp collectDivMods []) props
  if null allDivMods then pure []
  else do
    axioms <- mapM mkGroundTruthAxiom allDivMods
    pure $ (SMTComment "division/modulo ground-truth refinement") : axioms
  where
    mkGroundTruthAxiom :: DivModOp -> Err SMTEntry
    mkGroundTruthAxiom (kind, a, b) = do
      aenc <- enc a
      benc <- enc b
      let (abstFn, concFn) = if isDiv kind
            then ("abst_evm_bvsdiv", "bvsdiv")
            else ("abst_evm_bvsrem", "bvsrem")
      pure $ SMTCommand $ "(assert (=" `sp`
        "(" <> abstFn `sp` aenc `sp` benc <> ")" `sp`
        "(" <> concFn `sp` aenc `sp` benc <> ")))"

-- | Encode div/mod operations using abs values, shift-bounds, and congruence (no bvudiv).
divModEncoding :: (Expr EWord -> Err Builder) -> [Prop] -> Err [SMTEntry]
divModEncoding enc props = do
  let allDivMods = nubOrd $ concatMap (foldProp collectDivMods []) props
  if null allDivMods then pure []
  else do
    let groups = groupBy (\a b -> abstractKey a == abstractKey b) $ sortBy (comparing abstractKey) allDivMods
        indexedGroups = zip [0..] groups
    let links = mkCongruenceLinks indexedGroups
    entries <- concat <$> mapM (uncurry mkGroupEncoding) indexedGroups
    pure $ (SMTComment "division/modulo encoding (abs + shift-bounds + congruence, no bvudiv)") : entries <> links
  where
    knownPow2Bound :: Expr EWord -> Maybe W256
    knownPow2Bound (SHL (Lit k) _) = Just k
    knownPow2Bound (Lit n) | n > 0 = Just (fromIntegral $ countTrailingZeros n)
    knownPow2Bound _ = Nothing

    mkGroupEncoding :: Int -> [DivModOp] -> Err [SMTEntry]
    mkGroupEncoding _ [] = pure []
    mkGroupEncoding groupIdx ops@((firstKind, firstA, firstB) : _) = do
      let isDiv' = isDiv firstKind
          prefix = if isDiv' then "udiv" else "urem"
          unsignedResult = fromString $ prefix <> "_" <> show groupIdx
      (decls, (absoluteA, absoluteB)) <- declareAbsolute enc groupIdx firstA firstB unsignedResult

      -- When the dividend is a left-shift (a = x << k, i.e. a = x * 2^k),
      -- we can bound the unsigned division result using cheap bitshift
      -- operations instead of the expensive bvudiv SMT theory.
      -- The pivot point is |a| >> k (= |a| / 2^k):
      --   - If |b| >= 2^k: result <= |a| >> k  (upper bound)
      --   - If |b| <  2^k and b != 0: result >= |a| >> k  (lower bound)
      let shiftBounds = case (isDiv', knownPow2Bound firstA) of
            (True, Just k) ->
              let kLit = wordAsBV k
                  -- twoPowK = 2^k
                  twoPowK = "(bvshl (_ bv1 256) " <> kLit <> ")"
                  -- shifted = |a| >> k = |a| / 2^k
                  shifted = "(bvlshr" `sp` absoluteA `sp` kLit <> ")"
              in  -- |b| >= 2^k  =>  |a|/|b| <= |a|/2^k
                 [ SMTCommand $ "(assert (=> (bvuge" `sp` absoluteB `sp` twoPowK <> ") (bvule" `sp` unsignedResult `sp` shifted <> ")))"
                  -- |b| < 2^k and |b| != 0  =>  |a|/|b| >= |a|/2^k
                 , SMTCommand $ "(assert (=> "
                   <> "(and (bvult" `sp` absoluteB `sp` twoPowK <> ") (distinct " `sp` absoluteB `sp` zero <> "))"
                   <> "(bvuge" `sp` unsignedResult `sp` shifted <> ")))"
                 ]
            _ -> []
      axioms <- mapM (assertSignedEqualsUnsignedDerived enc unsignedResult) ops
      pure $ decls <> shiftBounds <> axioms

-- | Congruence: if two signed groups have equal absolute inputs, their results are equal.
mkCongruenceLinks :: [(Int, [DivModOp])] -> [SMTEntry]
mkCongruenceLinks indexedGroups =
  let signedDivGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == IsDiv]
      signedModGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == IsMod]
  in    concatMap (mkPairLinks "udiv") (allPairs signedDivGroups)
     <> concatMap (mkPairLinks "urem") (allPairs signedModGroups)
  where
    allPairs xs = [(a, b) | a <- xs, b <- xs, fst a < fst b]
    mkPairLinks prefix' ((i, _), (j, _)) =
      let absoluteAi = fromString $ "absolute_a" <> show i
          abosluteBi = fromString $ "absolute_b" <> show i
          absoluteAj = fromString $ "absolute_a" <> show j
          absoluteBj = fromString $ "absolute_b" <> show j
          absoluteResI = fromString $ prefix' <> "_" <> show i
          absoluteRedJ = fromString $ prefix' <> "_" <> show j
      in [ SMTCommand $ "(assert (=> "
            <> "(and (=" `sp` absoluteAi `sp` absoluteAj <> ") (=" `sp` abosluteBi `sp` absoluteBj <> "))"
            <> "(=" `sp` absoluteResI `sp` absoluteRedJ <> ")))" ]

-- | (ite (= divisor 0) 0 result)
smtZeroGuard :: Builder -> Builder -> Builder
smtZeroGuard divisor nonZeroResult =
  "(ite (=" `sp` divisor `sp` zero <> ")" `sp` zero `sp` nonZeroResult <> ")"

-- | |x| as SMT: ite(x >= 0, x, 0 - x).
smtAbsolute :: Builder -> Builder
smtAbsolute x = "(ite (bvsge" `sp` x `sp` zero <> ")" `sp` x `sp` "(bvsub" `sp` zero `sp` x <> "))"

-- | -x as SMT.
smtNeg :: Builder -> Builder
smtNeg x = "(bvsub" `sp` zero `sp` x <> ")"

-- | True if a and b have the same sign
smtSameSign :: Builder -> Builder -> Builder
smtSameSign a b = "(=" `sp` "(bvslt" `sp` a `sp` zero <> ")" `sp` "(bvslt" `sp` b `sp` zero <> "))"

-- | x >= 0.
smtIsNonNeg :: Builder -> Builder
smtIsNonNeg x = "(bvsge" `sp` x `sp` zero <> ")"

-- | sdiv(a,b) from udiv(|a|,|b|): negate result if signs differ
signedFromUnsignedDiv :: Builder -> Builder -> Builder -> Builder
signedFromUnsignedDiv aenc benc udivResult =
  smtZeroGuard benc $
  "(ite" `sp` (smtSameSign aenc benc) `sp`
    udivResult `sp` (smtNeg udivResult) <> ")"

-- | smod(a,b) from urem(|a|,|b|): result sign matches dividend.
signedFromUnsignedMod :: Builder -> Builder -> Builder -> Builder
signedFromUnsignedMod aenc benc uremResult =
  smtZeroGuard benc $
  "(ite" `sp` (smtIsNonNeg aenc) `sp`
    uremResult `sp` (smtNeg uremResult) <> ")"
