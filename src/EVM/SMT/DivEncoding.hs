{- |
    Module: EVM.SMT.DivEncoding
    Description: Abstract division/modulo encoding for two-phase SMT solving (Halmos-style)
-}
module EVM.SMT.DivEncoding
  ( divModAbstractDecls
  , divModBounds
  , assertPropsAbstract
  , assertPropsRefined
  ) where

import Data.List (nubBy, groupBy, sortBy)
import Data.Ord (comparing)
import Data.Text.Lazy.Builder

import EVM.Effects
import EVM.SMT
import EVM.Traversals
import EVM.Types


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

-- | Encode props using uninterpreted functions for div/mod (Phase 1 of two-phase solving)
assertPropsAbstract :: Config -> [Prop] -> Err SMT2
assertPropsAbstract conf ps = do
  let mkBase s = assertPropsHelperWith AbstractDivision s divModAbstractDecls
  base <- if not conf.simp then mkBase False ps
          else mkBase True (decompose conf ps)
  bounds <- divModBounds ps
  pure $ base <> SMT2 (SMTScript bounds) mempty mempty

-- | Encode props using exact div/mod definitions (Phase 2 refinement).
-- Keeps declare-fun (uninterpreted) for sharing, but adds ground-instance
-- axioms with CSE'd bvudiv/bvurem intermediates. Signed division operations
-- that differ only in divisor sign share the same bvudiv result since
-- |x| = |-x|.
assertPropsRefined :: Config -> [Prop] -> Err SMT2
assertPropsRefined conf ps = do
  let mkBase s = assertPropsHelperWith AbstractDivision s divModAbstractDecls
  base <- if not conf.simp then mkBase False ps
          else mkBase True (decompose conf ps)
  bounds <- divModBounds ps
  axioms <- divModGroundAxioms ps
  pure $ base
      <> SMT2 (SMTScript bounds) mempty mempty
      <> SMT2 (SMTScript axioms) mempty mempty

-- | Kind of division/modulo operation
data DivOpKind = UDiv | USDiv | UMod | USMod
  deriving (Eq, Ord)

-- We track (kind, dividend, divisor)
type DivOp = (DivOpKind, Expr EWord, Expr EWord)

-- | Canonical key for grouping operations that share the same bvudiv/bvurem core.
-- For unsigned: (a, b, False, isMod)
-- For signed:   (canonicalAbs a, canonicalAbs b, True, isMod) where canonicalAbs normalizes negations
type AbsKey = (Expr EWord, Expr EWord, Bool, Bool)

-- | Normalize an expression for absolute value canonicalization.
-- |Sub(Lit 0, x)| = |x|, so we strip the negation wrapper.
canonicalAbs :: Expr EWord -> Expr EWord
canonicalAbs (Sub (Lit 0) x) = x
canonicalAbs x = x

isSigned :: DivOpKind -> Bool
isSigned USDiv = True
isSigned USMod = True
isSigned _     = False

isMod :: DivOpKind -> Bool
isMod UMod  = True
isMod USMod = True
isMod _     = False

absKey :: DivOp -> AbsKey
absKey (kind, a, b)
  | not (isSigned kind) = (a, b, False, isMod kind)         -- unsigned: exact operands
  | otherwise           = (canonicalAbs a, canonicalAbs b, True, isMod kind)  -- signed: normalize abs

-- | Generate ground-instance axioms with CSE'd bvudiv/bvurem intermediates.
-- For each group of div/mod ops sharing the same (|a|, |b|), generates:
--   - declare-const for abs_a, abs_b, and the bvudiv/bvurem result
--   - axioms expressing each evm_bvXdiv call in terms of the shared result
divModGroundAxioms :: [Prop] -> Err [SMTEntry]
divModGroundAxioms props = do
  let allDivs = nubBy eqDivOp $ concatMap (foldProp collectDivOps []) props
  if null allDivs then pure []
  else do
    let groups = groupBy (\a b -> absKey a == absKey b)
               $ sortBy (comparing absKey) allDivs
        indexedGroups = zip [0..] groups
    entries <- concat <$> mapM (uncurry mkGroupAxioms) indexedGroups
    let links = mkCongruenceLinks indexedGroups
    pure $ (SMTComment "division/modulo ground-instance axioms (CSE'd)") : entries <> links
  where
    collectDivOps :: forall a . Expr a -> [DivOp]
    collectDivOps = \case
      Div a b  -> [(UDiv, a, b)]
      SDiv a b -> [(USDiv, a, b)]
      Mod a b  -> [(UMod, a, b)]
      SMod a b -> [(USMod, a, b)]
      _        -> []

    eqDivOp :: DivOp -> DivOp -> Bool
    eqDivOp (k1, a1, b1) (k2, a2, b2) =
      k1 == k2 && a1 == a2 && b1 == b2

    -- | Generate axioms for a group of ops sharing the same bvudiv/bvurem core.
    mkGroupAxioms :: Int -> [DivOp] -> Err [SMTEntry]
    mkGroupAxioms _ [] = pure []
    mkGroupAxioms groupIdx ops@((firstKind, firstA, firstB) : _) = do
      let isDiv' = not (isMod firstKind)
          prefix = if isDiv' then "udiv" else "urem"
          coreName = fromString $ prefix <> "_" <> show groupIdx

      if not (isSigned firstKind) then do
        -- Unsigned: simple axioms, one bvudiv/bvurem per op (no abs-value needed)
        mapM (mkUnsignedAxiom coreName) ops
      else do
        -- Signed: create shared intermediates for abs values and bvudiv/bvurem result
        let absAName = fromString $ "abs_a_" <> show groupIdx
            absBName = fromString $ "abs_b_" <> show groupIdx
        -- Use the canonical (non-negated) form for abs value encoding
        let canonA = stripNeg firstA
            canonB = stripNeg firstB
        canonAenc <- exprToSMTAbs canonA
        canonBenc <- exprToSMTAbs canonB
        let absAEnc = "(ite (bvsge" `sp` canonAenc `sp` zero <> ")"
                   `sp` canonAenc `sp` "(bvsub" `sp` zero `sp` canonAenc <> "))"
            absBEnc = "(ite (bvsge" `sp` canonBenc `sp` zero <> ")"
                   `sp` canonBenc `sp` "(bvsub" `sp` zero `sp` canonBenc <> "))"
            coreEnc = if isDiv'
                      then "(ite (=" `sp` absBName `sp` zero <> ")" `sp` zero
                        `sp` "(bvudiv" `sp` absAName `sp` absBName <> "))"
                      else "(ite (=" `sp` absBName `sp` zero <> ")" `sp` zero
                        `sp` "(bvurem" `sp` absAName `sp` absBName <> "))"
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
          concrete = "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero
                  `sp` "(" <> op `sp` aenc `sp` benc <> "))"
      pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

    mkSignedAxiom :: Builder -> DivOp -> Err SMTEntry
    mkSignedAxiom coreName (kind, a, b) = do
      aenc <- exprToSMTAbs a
      benc <- exprToSMTAbs b
      let fname = if kind == USDiv then "abst_evm_sdiv" else "abst_evm_smod"
          abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
      if kind == USDiv then do
        -- SDiv: result sign depends on whether operand signs match
        let sameSign = "(=" `sp` "(bvslt" `sp` aenc `sp` zero <> ")"
                    `sp` "(bvslt" `sp` benc `sp` zero <> "))"
            concrete = "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero
                     `sp` "(ite" `sp` sameSign `sp` coreName
                     `sp` "(bvsub" `sp` zero `sp` coreName <> ")))"
        pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"
      else do
        -- SMod: result sign matches dividend
        let concrete = "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero
                     `sp` "(ite (bvsge" `sp` aenc `sp` zero <> ")"
                     `sp` coreName
                     `sp` "(bvsub" `sp` zero `sp` coreName <> ")))"
        pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | For each pair of signed groups with the same operation type (udiv/urem),
-- emit a congruence lemma: if abs inputs are equal, results are equal.
-- This is a sound tautology (function congruence for bvudiv/bvurem) that
-- helps bitwuzla avoid independent reasoning about multiple bvudiv terms.
mkCongruenceLinks :: [(Int, [DivOp])] -> [SMTEntry]
mkCongruenceLinks indexedGroups =
  let signedDivGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups
                        , k == USDiv]  -- SDiv groups
      signedModGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups
                        , k == USMod]  -- SMod groups
  in concatMap (mkPairLinks "udiv") (allPairs signedDivGroups)
     <> concatMap (mkPairLinks "urem") (allPairs signedModGroups)
  where
    allPairs xs = [(a, b) | a <- xs, b <- xs, fst a < fst b]
    mkPairLinks prefix' ((i, _), (j, _)) =
      let absAI = fromString $ "abs_a_" <> show i
          absBi = fromString $ "abs_b_" <> show i
          absAJ = fromString $ "abs_a_" <> show j
          absBJ = fromString $ "abs_b_" <> show j
          coreI = fromString $ prefix' <> "_" <> show i
          coreJ = fromString $ prefix' <> "_" <> show j
      in [ SMTCommand $ "(assert (=> (and (=" `sp` absAI `sp` absAJ <> ") (="
              `sp` absBi `sp` absBJ <> ")) (=" `sp` coreI `sp` coreJ <> ")))" ]
