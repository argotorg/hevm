{- | Abstract div/mod encoding for two-phase SMT solving. -}
module EVM.SMT.DivEncoding
  ( assertProps
  , assertPropsShiftBounds
  , divModGroundTruth
  ) where

import Data.Bits ((.&.), countTrailingZeros)
import Data.Containers.ListUtils (nubOrd)
import Data.List (groupBy, sortBy)
import Data.Ord (comparing)
import Data.Text.Lazy.Builder

import EVM.Effects
import EVM.SMT
import EVM.Traversals
import EVM.Types (Prop(..), EType(EWord), Err, W256, Expr, Expr(Lit), Expr(SHL))
import EVM.Types qualified as T

assertProps :: Config -> [Prop] -> Err SMT2
assertProps conf ps =
  if not conf.simp then assertPropsHelperWith ConcreteDivision False [] ps
  else assertPropsHelperWith ConcreteDivision True [] (decompose conf ps)

-- | Uninterpreted function declarations for abstract div/mod.
divModAbstractDecls :: [SMTEntry]
divModAbstractDecls =
  [ SMTComment "abstract division/modulo (uninterpreted functions)"
  , SMTCommand "(declare-fun abst_evm_bvsdiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvsrem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

exprToSMTAbst :: Expr a -> Err Builder
exprToSMTAbst = exprToSMTWith AbstractDivision

data DivModOp = IsDiv | IsMod
  deriving (Eq, Ord)

type DivOp = (DivModOp, Expr EWord, Expr EWord)

data AbsKey = AbsKey (Expr EWord) (Expr EWord) DivModOp
  deriving (Eq, Ord)

isDiv :: DivModOp -> Bool
isDiv IsDiv = True
isDiv _     = False

isMod :: DivModOp -> Bool
isMod = not . isDiv

-- | Collect all div/mod operations from an expression.
collectDivMods :: Expr a -> [DivOp]
collectDivMods = \case
  T.SDiv a b -> [(IsDiv, a, b)]
  T.SMod a b -> [(IsMod, a, b)]
  _          -> []

absKey :: DivOp -> AbsKey
absKey (kind, a, b) = AbsKey a b kind

-- | Declare abs_a, abs_b, and unsigned result variables for a signed group.
declareAbs :: Int -> Expr EWord -> Expr EWord -> Builder -> Err ([SMTEntry], (Builder, Builder))
declareAbs groupIdx firstA firstB unsignedResult = do
  aenc <- exprToSMTAbst firstA
  benc <- exprToSMTAbst firstB
  let absAEnc = smtAbsolute aenc
      absBEnc = smtAbsolute benc
      absAName = fromString $ "abs_a_" <> show groupIdx
      absBName = fromString $ "abs_b_" <> show groupIdx
  let decls = [ SMTCommand $ "(declare-const" `sp` absAName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` absBName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` unsignedResult `sp` "(_ BitVec 256))"
              , SMTCommand $ "(assert (=" `sp` absAName `sp` absAEnc <> "))"
              , SMTCommand $ "(assert (=" `sp` absBName `sp` absBEnc <> "))"
              ]
  pure (decls, (absAName, absBName))

-- | Assert abstract(a,b) = signed result derived from unsigned result.
mkSignedAxiom :: Builder -> DivOp -> Err SMTEntry
mkSignedAxiom unsignedResult (kind, a, b) = do
  aenc <- exprToSMTAbst a
  benc <- exprToSMTAbst b
  let fname = if isDiv kind then "abst_evm_bvsdiv" else "abst_evm_bvsrem"
      abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
      concrete = if isDiv kind
                 then smtSdivResult aenc benc unsignedResult
                 else smtSmodResult aenc benc unsignedResult
  pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Assert props using shift-based bounds to avoid bvudiv when possible.
assertPropsShiftBounds :: Config -> [Prop] -> Err SMT2
assertPropsShiftBounds conf ps = do
  let mkBase s = assertPropsHelperWith AbstractDivision s divModAbstractDecls
  base <- if not conf.simp then mkBase False ps
          else mkBase True (decompose conf ps)
  shiftBounds <- divModShiftBounds ps
  pure $ base
      -- <> SMT2 (SMTScript bounds) mempty mempty
      <> SMT2 (SMTScript shiftBounds) mempty mempty

-- | Ground-truth axioms: for each sdiv/smod op, assert that the abstract
-- uninterpreted function equals the real bvsdiv/bvsrem.
-- e.g. (assert (= (abst_evm_bvsdiv a b) (bvsdiv a b)))
divModGroundTruth :: [Prop] -> Err [SMTEntry]
divModGroundTruth props = do
  let allDivs = nubOrd $ concatMap (foldProp collectDivMods []) props
  if null allDivs then pure []
  else do
    axioms <- mapM mkGroundTruthAxiom allDivs
    pure $ (SMTComment "division/modulo ground-truth refinement") : axioms
  where
    mkGroundTruthAxiom :: DivOp -> Err SMTEntry
    mkGroundTruthAxiom (kind, a, b) = do
      aenc <- exprToSMTAbst a
      benc <- exprToSMTAbst b
      let (abstFn, concFn) = if isDiv kind
            then ("abst_evm_bvsdiv", "bvsdiv")
            else ("abst_evm_bvsrem", "bvsrem")
      pure $ SMTCommand $ "(assert (=" `sp`
        "(" <> abstFn `sp` aenc `sp` benc <> ")" `sp`
        "(" <> concFn `sp` aenc `sp` benc <> ")))"

-- | Shift-based bound axioms for div/mod with SHL dividends.
divModShiftBounds :: [Prop] -> Err [SMTEntry]
divModShiftBounds props = do
  let allDivs = nubOrd $ concatMap (foldProp collectDivMods []) props
  if null allDivs then pure []
  else do
    let groups = groupBy (\a b -> absKey a == absKey b)
               $ sortBy (comparing absKey) allDivs
        indexedGroups = zip [0..] groups
    let links = mkCongruenceLinks indexedGroups
    entries <- concat <$> mapM (uncurry mkGroupShiftAxioms) indexedGroups
    pure $ (SMTComment "division/modulo shift-bound axioms (no bvudiv)") : entries <> links
  where
    -- | Extract shift amount k from SHL(k, _) or power-of-2 literals.
    extractShift :: Expr EWord -> Maybe W256
    extractShift (SHL (Lit k) _) = Just k
    extractShift (Lit n) | n > 0, n .&. (n - 1) == 0 = Just (fromIntegral $ countTrailingZeros n)
    extractShift _ = Nothing

    mkGroupShiftAxioms :: Int -> [DivOp] -> Err [SMTEntry]
    mkGroupShiftAxioms _ [] = pure []
    mkGroupShiftAxioms groupIdx ops@((firstKind, firstA, firstB) : _) = do
      let isDiv' = isDiv firstKind
          prefix = if isDiv' then "udiv" else "urem"
          unsignedResult = fromString $ prefix <> "_" <> show groupIdx
      (decls, (absAName, absBName)) <- declareAbs groupIdx firstA firstB unsignedResult

      -- When the dividend is a left-shift (a = x << k, i.e. a = x * 2^k),
      -- we can bound the unsigned division result using cheap bitshift
      -- operations instead of the expensive bvudiv SMT theory.
      -- The pivot point is |a| >> k (= |a| / 2^k):
      --   - If |b| >= 2^k: result <= |a| >> k  (upper bound)
      --   - If |b| <  2^k and b != 0: result >= |a| >> k  (lower bound)
      let shiftBounds = case (isDiv', extractShift firstA) of
            (True, Just k) ->
              let kLit = wordAsBV k
                  -- threshold = 2^k
                  threshold = "(bvshl (_ bv1 256) " <> kLit <> ")"
                  -- shifted = |a| >> k = |a| / 2^k
                  shifted = "(bvlshr" `sp` absAName `sp` kLit <> ")"
              in  -- |b| >= 2^k  =>  |a|/|b| <= |a|/2^k
                  [ SMTCommand $ "(assert (=> (bvuge" `sp` absBName `sp` threshold <> ") (bvule" `sp` unsignedResult `sp` shifted <> ")))"
                  -- |b| < 2^k and b != 0  =>  |a|/|b| >= |a|/2^k
                 , SMTCommand $ "(assert (=> "
                   <> "(and (bvult" `sp` absBName `sp` threshold <> ") (distinct " `sp` absBName `sp` zero <> "))"
                   <> "(bvuge" `sp` unsignedResult `sp` shifted <> ")))"
                 ]
            _ -> []
      axioms <- mapM (mkSignedAxiom unsignedResult) ops
      pure $ decls <> shiftBounds <> axioms

-- | Congruence: if two signed groups have equal abs inputs, their results are equal.
mkCongruenceLinks :: [(Int, [DivOp])] -> [SMTEntry]
mkCongruenceLinks indexedGroups =
  let signedDivGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == IsDiv]
      signedModGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == IsMod]
  in    concatMap (mkPairLinks "udiv") (allPairs signedDivGroups)
     <> concatMap (mkPairLinks "urem") (allPairs signedModGroups)
  where
    allPairs xs = [(a, b) | a <- xs, b <- xs, fst a < fst b]
    mkPairLinks prefix' ((i, _), (j, _)) =
      let absAi = fromString $ "abs_a_" <> show i
          absBi = fromString $ "abs_b_" <> show i
          absAj = fromString $ "abs_a_" <> show j
          absBj = fromString $ "abs_b_" <> show j
          unsignedResultI = fromString $ prefix' <> "_" <> show i
          unsignedResultJ = fromString $ prefix' <> "_" <> show j
      in [ SMTCommand $ "(assert (=> "
            <> "(and (=" `sp` absAi `sp` absAj <> ") (=" `sp` absBi `sp` absBj <> "))"
            <> "(=" `sp` unsignedResultI `sp` unsignedResultJ <> ")))" ]

-- | (ite (= divisor 0) 0 result)
smtZeroGuard :: Builder -> Builder -> Builder
smtZeroGuard divisor nonZeroResult =
  "(ite (=" `sp` divisor `sp` zero <> ")" `sp` zero `sp` nonZeroResult <> ")"

-- | |x| as SMT.
-- Bug 3 (Minor): smtAbsolute doesn't handle MIN_INT (line 278-279)
-- smtAbsolute computes ite(x >= 0, x, 0 - x).
-- For the minimum signed 256-bit value (-2^255), 0 - (-2^255) overflows back to -2^255 in two's complement. So |MIN_INT| = MIN_INT (negative),
-- which could produce incorrect signed div/mod results for edge cases like sdiv(-2^255, -1) (which EVM defines as -2^255).
smtAbsolute :: Builder -> Builder
smtAbsolute x = "(ite (bvsge" `sp` x `sp` zero <> ")" `sp` x `sp` "(bvsub" `sp` zero `sp` x <> "))"

-- | -x as SMT.
smtNeg :: Builder -> Builder
smtNeg x = "(bvsub" `sp` zero `sp` x <> ")"

-- | True if a and b have the same sign.
smtSameSign :: Builder -> Builder -> Builder
smtSameSign a b = "(=" `sp` "(bvslt" `sp` a `sp` zero <> ")" `sp` "(bvslt" `sp` b `sp` zero <> "))"

-- | x >= 0.
smtIsNonNeg :: Builder -> Builder
smtIsNonNeg x = "(bvsge" `sp` x `sp` zero <> ")"

-- | sdiv(a,b) from udiv(|a|,|b|): negate result if signs differ.
smtSdivResult :: Builder -> Builder -> Builder -> Builder
smtSdivResult aenc benc udivResult =
  smtZeroGuard benc $
  "(ite" `sp` (smtSameSign aenc benc) `sp`
    udivResult `sp` (smtNeg udivResult) <> ")"

-- | smod(a,b) from urem(|a|,|b|): result sign matches dividend.
smtSmodResult :: Builder -> Builder -> Builder -> Builder
smtSmodResult aenc benc uremResult =
  smtZeroGuard benc $
  "(ite" `sp` (smtIsNonNeg aenc) `sp`
    uremResult `sp` (smtNeg uremResult) <> ")"
