{- |
    Module: EVM.SMT.DivEncoding
    Description: Abstract division/modulo encoding for two-phase SMT solving (Halmos-style)
-}
module EVM.SMT.DivEncoding
  ( divModAbstractDecls
  , divModRefinedDefs
  , divModBounds
  , assertPropsAbstract
  , assertPropsRefined
  ) where

import Data.Text.Lazy.Builder

import EVM.Effects
import EVM.SMT
import EVM.Traversals
import EVM.Types


-- | Uninterpreted function declarations for abstract div/mod encoding (Phase 1).
divModAbstractDecls :: [SMTEntry]
divModAbstractDecls =
  [ SMTComment "abstract division/modulo (uninterpreted functions)"
  , SMTCommand "(declare-fun evm_bvudiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun evm_bvsdiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun evm_bvurem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun evm_bvsrem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

-- | Exact function definitions for div/mod with EVM semantics (Phase 2 refinement).
-- These define-fun replace the declare-fun from Phase 1, giving concrete semantics:
-- division by zero returns zero (matching EVM behavior).
divModRefinedDefs :: [SMTEntry]
divModRefinedDefs =
  [ SMTComment "refined division/modulo (exact EVM semantics)"
  , SMTCommand "(define-fun evm_bvudiv ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256) (ite (= y (_ bv0 256)) (_ bv0 256) (bvudiv x y)))"
  , SMTCommand "(define-fun evm_bvsdiv ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256) (ite (= y (_ bv0 256)) (_ bv0 256) (bvsdiv x y)))"
  , SMTCommand "(define-fun evm_bvurem ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256) (ite (= y (_ bv0 256)) (_ bv0 256) (bvurem x y)))"
  , SMTCommand "(define-fun evm_bvsrem ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256) (ite (= y (_ bv0 256)) (_ bv0 256) (bvsrem x y)))"
  ]

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
      Div a b  -> [("evm_bvudiv", a, b)]
      Mod a b  -> [("evm_bvurem", a, b)]
      _        -> []

    mkAssertion :: (Builder, Expr EWord, Expr EWord) -> Err SMTEntry
    mkAssertion (fname, a, b) = do
      aenc <- exprToSMTWith AbstractDivision a
      benc <- exprToSMTWith AbstractDivision b
      let result = "(" <> fname `sp` aenc `sp` benc <> ")"
      if fname == "evm_bvudiv"
        -- (x / y) <= x
        then pure $ SMTCommand $ "(assert (bvule " <> result `sp` aenc <> "))"
        -- (x % y) <= y (ULE not ULT because y could be 0 and 0 % 0 = 0)
        else pure $ SMTCommand $ "(assert (bvule " <> result `sp` benc <> "))"

-- | Encode props using uninterpreted functions for div/mod (Phase 1 of two-phase solving)
assertPropsAbstract :: Config -> [Prop] -> Err SMT2
assertPropsAbstract conf ps = do
  base <- if not conf.simp then assertPropsHelperWith AbstractDivision False ps
          else assertPropsHelperWith AbstractDivision True (decompose conf ps)
  bounds <- divModBounds ps
  pure $ SMT2 (SMTScript divModAbstractDecls) mempty mempty
      <> base
      <> SMT2 (SMTScript bounds) mempty mempty

-- | Encode props using exact div/mod definitions (Phase 2 refinement)
assertPropsRefined :: Config -> [Prop] -> Err SMT2
assertPropsRefined conf ps = do
  base <- if not conf.simp then assertPropsHelperWith AbstractDivision False ps
          else assertPropsHelperWith AbstractDivision True (decompose conf ps)
  bounds <- divModBounds ps
  pure $ SMT2 (SMTScript divModRefinedDefs) mempty mempty
      <> base
      <> SMT2 (SMTScript bounds) mempty mempty
