{- | Abstract arithmetic encoding for two-phase SMT solving.

   Orchestration layer. The shared vocabulary (primitives, collectors,
   'saturate') lives in "EVM.SMT.AbstractBase"; the multiplication lemma
   catalogue lives in "EVM.SMT.AbstractLemmas". This module wires them together
   ('mulEncoding') and holds the /ground-truth/ encodings that equate the
   abstract functions with the native ops.
-}
module EVM.SMT.ArithEncoding
  ( divModGroundTruth
  , mulGroundTruth
  , divModEncoding
  , divModAbstractDecls
  , mulEncoding
  ) where

import Data.Bits (countTrailingZeros)
import Data.Text.Lazy.Builder (Builder, fromString)

import EVM.SMT.AbstractBase
import EVM.SMT.AbstractLemmas (collectLemmas, emitLemma)
import EVM.SMT.SMTLIB (sp, zero, wordAsBV)
import EVM.SMT.Types
import EVM.Types (Prop, EType(EWord), Err, W256, Expr, Expr(Lit), Expr(SHL))

-- | Lemmas for the initial abstract-multiplication phase. We add only the sound
-- algebraic facts catalogued in
-- "EVM.SMT.AbstractLemmas". 'saturate' closes the term set the lemmas range
-- over; 'collectLemmas' picks the instances; 'emitLemma' renders each to SMT.
mulEncoding :: Enc -> [Prop] -> Err [SMTEntry]
mulEncoding enc props = do
  lemmas <- concat <$> mapM (emitLemma enc) (collectLemmas (saturate props))
  pure $ if null lemmas then []
         else SMTComment "multiplication abstraction lemmas" : lemmas

-- | The variables an op introduces, named from its index. 'mkCongruenceLinks'
-- refers to the same ones, so both derive them here rather than agreeing by
-- accident.
absoluteAName, absoluteBName :: Int -> Builder
absoluteAName idx = fromString $ "absolute_a" <> show idx
absoluteBName idx = fromString $ "absolute_b" <> show idx

-- | The op's result as an unsigned quotient/remainder of the magnitudes.
resultName :: DivModKind -> Int -> Builder
resultName kind idx = fromString $ (if isDiv kind then "udiv" else "urem") <> "_" <> show idx

-- | Declare the magnitude variables and the unsigned result variable for an
-- op. For signed ops the magnitudes are the absolute values |a|, |b|; for
-- unsigned ops the operands are already non-negative, so the magnitude is the
-- operand itself (|x| = x).
declareAbsolute :: Enc -> Int -> DivModOp -> Err [SMTEntry]
declareAbsolute enc idx (kind, a, b) = do
  aenc <- enc a
  benc <- enc b
  let magnitude x = if isSigned kind then smtAbsolute x else x
      declareConst n = SMTCommand $ "(declare-const" `sp` n `sp` "(_ BitVec 256))"
  pure [ declareConst (absoluteAName idx)
       , declareConst (absoluteBName idx)
       , declareConst (resultName kind idx)
       , SMTCommand $ "(assert (=" `sp` absoluteAName idx `sp` magnitude aenc <> "))"
       , SMTCommand $ "(assert (=" `sp` absoluteBName idx `sp` magnitude benc <> "))"
       ]

-- | Assert "abstract div/mod(a,b)" = result derived from the unsigned result
-- variable. Signed ops reconstruct the sign from |a|/|b|; unsigned ops need
-- only the EVM divide-by-zero guard, since the unsigned result is the answer.
assertAbstEqResult :: Enc -> Builder -> DivModOp -> Err SMTEntry
assertAbstEqResult enc unsignedResult (kind, a, b) = do
  aenc <- enc a
  benc <- enc b
  let abstract = "(" <> abstFnName kind `sp` aenc `sp` benc <> ")"
      concrete = case kind of
        IsSDiv -> signedFromUnsignedDiv aenc benc unsignedResult
        IsSMod -> signedFromUnsignedMod aenc benc unsignedResult
        IsUDiv -> smtZeroGuard benc unsignedResult
        IsUMod -> smtZeroGuard benc unsignedResult
  pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Ground-truth axioms: for each sdiv/smod op, assert that the abstract
-- uninterpreted function equals the real bvsdiv/bvsrem.
-- e.g. (assert (= (abst_evm_bvsdiv a b) (bvsdiv a b)))
divModGroundTruth :: Enc -> [Prop] -> Err [SMTEntry]
divModGroundTruth enc props = do
  let allDivMods = collectFrom collectDivMods props
  if null allDivMods then pure []
  else do
    axioms <- mapM mkGroundTruthAxiom allDivMods
    pure $ (SMTComment "division/modulo ground-truth refinement") : axioms
  where
    mkGroundTruthAxiom :: DivModOp -> Err SMTEntry
    mkGroundTruthAxiom (kind, a, b) = do
      aenc <- enc a
      benc <- enc b
      let abstract = "(" <> abstFnName kind `sp` aenc `sp` benc <> ")"
          native   = "(" <> concFnName kind `sp` aenc `sp` benc <> ")"
          -- EVM defines every division/modulo by zero as zero, whereas the
          -- corresponding native SMT-LIB operations return other values.
          concrete = smtZeroGuard benc native
      pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Equate every abstract multiplication in the properties with native
-- bit-vector multiplication.
mulGroundTruth :: Enc -> [Prop] -> Err [SMTEntry]
mulGroundTruth enc props = do
  let allMuls = collectFrom collectMuls props
  if null allMuls then pure []
  else do
    axioms <- mapM mkGroundTruthAxiom allMuls
    pure $ SMTComment "multiplication ground-truth refinement" : axioms
  where
    mkGroundTruthAxiom :: (Expr EWord, Expr EWord) -> Err SMTEntry
    mkGroundTruthAxiom (a, b) = do
      aenc <- enc a
      benc <- enc b
      -- collectMuls only yields symbolic*symbolic, so this is the abstract one
      let abstract = mulSMT (a, aenc) (b, benc)
          concrete = "(bvmul" `sp` aenc `sp` benc <> ")"
      pure $ SMTCommand $ "(assert (= " <> abstract <> " " <> concrete <> "))"

-- | Encode div/mod operations using abs values, shift-bounds, and congruence.
-- This is all the first phase knows about division; the native ops only enter
-- when a satisfiable query is re-checked.
divModEncoding :: Enc -> [Prop] -> Err [SMTEntry]
divModEncoding enc props = do
  let allDivMods = collectFrom collectDivMods props
  if null allDivMods then pure []
  else do
    let indexedOps = zip [0..] allDivMods
    entries <- concat <$> mapM (uncurry mkOpEncoding) indexedOps
    let links = mkCongruenceLinks indexedOps
    pure $ (SMTComment "division/modulo encoding (abs + shift-bounds + congruence)") : entries <> links
  where
    knownPow2Bound :: Expr EWord -> Maybe W256
    knownPow2Bound (SHL (Lit k) _) = Just k
    knownPow2Bound (Lit n) | n > 0 = Just (fromIntegral $ countTrailingZeros n)
    knownPow2Bound _ = Nothing

    mkOpEncoding :: Int -> DivModOp -> Err [SMTEntry]
    mkOpEncoding idx op@(kind, a, _) = do
      decls <- declareAbsolute enc idx op
      let unsignedResult = resultName kind idx
          absoluteA = absoluteAName idx
          absoluteB = absoluteBName idx

      -- When the dividend is a left-shift (a = x << k, i.e. a = x * 2^k),
      -- we can bound the unsigned division result using cheap bitshift
      -- operations instead of the expensive bvudiv SMT theory.
      -- The pivot point is |a| >> k (= |a| / 2^k):
      --   - If |b| >= 2^k: result <= |a| >> k  (upper bound)
      --   - If |b| <  2^k and b != 0: result >= |a| >> k  (lower bound)
      let shiftBounds = case (isDiv kind, knownPow2Bound a) of
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
      axiom <- assertAbstEqResult enc unsignedResult op
      pure $ decls <> shiftBounds <> [axiom]

-- | Congruence: if two ops of the same kind have equal magnitude inputs,
-- their results are equal. Signed and unsigned ops are linked separately so
-- a signed op is never tied to an unsigned op (and vice versa).
mkCongruenceLinks :: [(Int, DivModOp)] -> [SMTEntry]
mkCongruenceLinks indexedOps = concatMap linkKind [minBound ..]
  where
    linkKind kind = concatMap (mkPairLinks kind) (allPairs (opsOfKind kind))
    opsOfKind want = [i | (i, (k, _, _)) <- indexedOps, k == want]
    allPairs xs = [(i, j) | i <- xs, j <- xs, i < j]
    mkPairLinks kind (i, j) =
      [ SMTCommand $ "(assert (=> "
          <> "(and (=" `sp` absoluteAName i `sp` absoluteAName j <> ") (="
             `sp` absoluteBName i `sp` absoluteBName j <> "))"
          <> "(=" `sp` resultName kind i `sp` resultName kind j <> ")))" ]
