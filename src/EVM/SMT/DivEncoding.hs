{- |
    Module: EVM.SMT.DivEncoding
    Description: Abstract division/modulo encoding for two-phase SMT solving (Halmos-style)
-}
module EVM.SMT.DivEncoding
  ( divModAbstractDecls
  , divModGroundAxioms
  , assertProps
  , assertPropsAbstract
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (groupBy, sortBy)
import Data.Ord (comparing)
import Data.Text.Lazy.Builder

import EVM.Effects
import EVM.SMT
import EVM.Traversals
import EVM.Types

-- | Phase 1: Encode props using uninterpreted functions for div/mod
assertPropsAbstract :: Config -> [Prop] -> Err SMT2
assertPropsAbstract conf ps = do
  let mkBase simp = assertPropsHelperWith AbstractDivision simp divModAbstractDecls
  base <- if not conf.simp then mkBase False ps
          else mkBase True (decompose conf ps)
  bounds <- divModBounds ps
  pure $ base <> SMT2 (SMTScript bounds) mempty mempty

-- | Phase 2: Add ground-instance axioms for div/mod operations
assertProps :: Config -> [Prop] -> Err SMT2
assertProps conf ps = do
  abst <- assertPropsAbstract conf ps
  refine <- divModGroundAxioms ps
  pure $ abst <> SMT2 (SMTScript refine) mempty mempty

-- | Uninterpreted function declarations for abstract div/mod encoding (Phase 1).
divModAbstractDecls :: [SMTEntry]
divModAbstractDecls =
  [ SMTComment "abstract division/modulo (uninterpreted functions)"
  , SMTCommand "(declare-fun abst_evm_div   ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_sdiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_mod  ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_smod ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

exprToSMTAbs :: Expr a -> Err Builder
exprToSMTAbs = exprToSMTWith AbstractDivision

-- | Generate bounds constraints for abstract div/mod operations.
-- These help the solver prune impossible models without full bitvector division reasoning.
divModBounds :: [Prop] -> Err [SMTEntry]
divModBounds props = do
  let allBounds = concatMap (foldProp collectBounds []) props
  if null allBounds then pure []
  else do
    assertions <- mapM mkAssertion allBounds
    pure $ (SMTComment "division/modulo bounds") : assertions
  where
    collectBounds :: Expr a -> [(Builder, Expr EWord, Expr EWord)]
    collectBounds = \case
      Div a b  -> [("abst_evm_div", a, b)]
      Mod a b  -> [("abst_evm_mod", a, b)]
      _        -> []

    mkAssertion :: (Builder, Expr EWord, Expr EWord) -> Err SMTEntry
    mkAssertion (fname, a, b) = do
      aenc <- exprToSMTAbs a
      benc <- exprToSMTAbs b
      let result = "(" <> fname `sp` aenc `sp` benc <> ")"
      pure $ SMTCommand $ "(assert (bvule " <> result `sp` aenc <> "))"

data DivModOp = IsDiv | IsMod
  deriving (Eq, Ord)

data DivOpKind = UDiv | USDiv | UMod | USMod
  deriving (Eq, Ord)

type DivOp = (DivOpKind, Expr EWord, Expr EWord)

data AbsKey
  = UnsignedAbsKey (Expr EWord) (Expr EWord) DivModOp  -- ^ (dividend, divisor, op) - raw operands
  | SignedAbsKey   (Expr EWord) (Expr EWord) DivModOp  -- ^ (dividend, divisor, op) - canonicalAbs normalized
  deriving (Eq, Ord)

-- | Normalize an expression for absolute value canonicalization.
-- |Sub(Lit 0, x)| = |x|, so we strip the negation wrapper.
canonicalAbs :: Expr EWord -> Expr EWord
canonicalAbs (Sub (Lit 0) x) = x
canonicalAbs x = x

isSigned :: DivOpKind -> Bool
isSigned USDiv = True
isSigned USMod = True
isSigned _     = False

isDiv :: DivOpKind -> Bool
isDiv UDiv  = True
isDiv USDiv = True
isDiv _     = False

divModOp :: DivOpKind -> DivModOp
divModOp k = if isDiv k then IsDiv else IsMod

absKey :: DivOp -> AbsKey
absKey (kind, a, b)
  | not (isSigned kind) = UnsignedAbsKey a b (divModOp kind)
  | otherwise           = SignedAbsKey (canonicalAbs a) (canonicalAbs b) (divModOp kind)

-- | Generate ground-instance axioms with CSE'd bvudiv/bvurem intermediates.
-- For each group of div/mod ops sharing the same (|a|, |b|), generates:
--   - declare-const for abs_a, abs_b, and the bvudiv/bvurem result
--   - axioms expressing each evm_bvXdiv call in terms of the shared result
divModGroundAxioms :: [Prop] -> Err [SMTEntry]
divModGroundAxioms props = do
  let allDivs = nubOrd $ concatMap (foldProp collect []) props
  if null allDivs then pure []
  else do
    let groups = groupBy (\a b -> absKey a == absKey b) $ sortBy (comparing absKey) allDivs
        indexedGroups = zip [0..] groups
    entries <- concat <$> mapM (uncurry mkGroupAxioms) indexedGroups
    let links = mkCongruenceLinks indexedGroups
    pure $ (SMTComment "division/modulo ground-instance axioms") : entries <> links
  where
    collect :: forall a . Expr a -> [DivOp]
    collect = \case
      Div a b  -> [(UDiv, a, b)]
      SDiv a b -> [(USDiv, a, b)]
      Mod a b  -> [(UMod, a, b)]
      SMod a b -> [(USMod, a, b)]
      _        -> []

    -- | Generate axioms for a group of ops sharing the same bvudiv/bvurem core.
    mkGroupAxioms :: Int -> [DivOp] -> Err [SMTEntry]
    mkGroupAxioms _ [] = pure []
    mkGroupAxioms groupIdx ops@((firstKind, firstA, firstB) : _) = do
      let isDiv' = isDiv firstKind
          prefix = if isDiv' then "udiv" else "urem"
          coreName = fromString $ prefix <> "_" <> show groupIdx

      if not (isSigned firstKind) then mapM (mkUnsignedAxiom coreName) ops
      else do
        let absAName = fromString $ "abs_a_" <> show groupIdx
            absBName = fromString $ "abs_b_" <> show groupIdx
        -- Use the canonical (non-negated) form for abs value encoding
        let canonA = stripNeg firstA
            canonB = stripNeg firstB
        canonAenc <- exprToSMTAbs canonA
        canonBenc <- exprToSMTAbs canonB
        let absAEnc = smtAbs canonAenc
            absBEnc = smtAbs canonBenc
            op = if isDiv' then "bvudiv" else "bvurem"
            coreEnc = smtZeroGuard absBName $ "(" <> op `sp` absAName `sp` absBName <> ")"
        let decls = [ SMTCommand $ "(declare-const" `sp` absAName `sp` "(_ BitVec 256))"
                    , SMTCommand $ "(declare-const" `sp` absBName `sp` "(_ BitVec 256))"
                    , SMTCommand $ "(declare-const" `sp` coreName `sp` "(_ BitVec 256))"
                    , SMTCommand $ "(assert (=" `sp` absAName `sp` absAEnc <> "))"
                    , SMTCommand $ "(assert (=" `sp` absBName `sp` absBEnc <> "))"
                    , SMTCommand $ "(assert (=" `sp` coreName `sp` coreEnc <> "))"
                    ]
        axioms <- mapM (mkSignedAxiom coreName) ops
        pure $ decls <> axioms

    stripNeg :: Expr EWord -> Expr EWord
    stripNeg (Sub (Lit 0) x) = x
    stripNeg x = x

    mkUnsignedAxiom :: Builder -> DivOp -> Err SMTEntry
    mkUnsignedAxiom _coreName (kind, a, b) = do
      aenc <- exprToSMTAbs a
      benc <- exprToSMTAbs b
      let fname = if kind == UDiv then "abst_evm_div" else "abst_evm_mod"
          abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
          op = if kind == UDiv then "bvudiv" else "bvurem"
          concrete = smtZeroGuard benc $ "(" <> op `sp` aenc `sp` benc <> ")"
      pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

    mkSignedAxiom :: Builder -> DivOp -> Err SMTEntry
    mkSignedAxiom coreName (kind, a, b) = do
      aenc <- exprToSMTAbs a
      benc <- exprToSMTAbs b
      let fname = if kind == USDiv then "abst_evm_sdiv" else "abst_evm_smod"
          abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
          concrete = if kind == USDiv
                     then smtSdivResult aenc benc coreName
                     else smtSmodResult aenc benc coreName
      pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | For each pair of signed groups with the same operation type (udiv/urem),
-- emit a congruence lemma: if abs inputs are equal, results are equal.
-- This is a sound tautology (function congruence for bvudiv/bvurem) that
-- helps solvers avoid independent reasoning about multiple bvudiv terms.
mkCongruenceLinks :: [(Int, [DivOp])] -> [SMTEntry]
mkCongruenceLinks indexedGroups =
  let signedDivGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == USDiv]  -- SDiv groups
      signedModGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == USMod]  -- SMod groups
  in    concatMap (mkPairLinks "udiv") (allPairs signedDivGroups)
     <> concatMap (mkPairLinks "urem") (allPairs signedModGroups)
  where
    allPairs xs = [(a, b) | a <- xs, b <- xs, fst a < fst b]
    mkPairLinks prefix' ((i, _), (j, _)) =
      let absAi = fromString $ "abs_a_" <> show i
          absBi = fromString $ "abs_b_" <> show i
          absAj = fromString $ "abs_a_" <> show j
          absBj = fromString $ "abs_b_" <> show j
          coreI = fromString $ prefix' <> "_" <> show i
          coreJ = fromString $ prefix' <> "_" <> show j
      in [ SMTCommand $ "(assert (=> "
            <> "(and (=" `sp` absAi `sp` absAj <> ") (=" `sp` absBi `sp` absBj <> "))"
            <> "(=" `sp` coreI `sp` coreJ <> ")))" ]
