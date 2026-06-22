{- | Abstract div/mod encoding for two-phase SMT solving.

   Orchestration layer. The shared vocabulary (primitives, collectors,
   'saturate') lives in "EVM.SMT.AbstractBase"; the multiplication lemma
   catalogue lives in "EVM.SMT.AbstractLemmas". This module wires them together
   ('mulEncoding') and holds the div/mod /ground-truth/ encoding — the phase that
   refines the abstract uninterpreted functions against real bvudiv/bvsdiv using
   absolute values, shift bounds, and congruence.
-}
module EVM.SMT.DivModEncoding
  ( divModGroundTruth
  , divModEncoding
  , divModAbstractDecls
  , mulEncoding
  , hasAbstractMul
  ) where

import Data.Bits (countTrailingZeros)
import Data.Containers.ListUtils (nubOrd)
import Data.List (groupBy, sortBy)
import Data.Ord (comparing)
import Data.Text.Lazy.Builder (Builder, fromString)

import EVM.SMT.AbstractBase
import EVM.SMT.AbstractLemmas (collectLemmas, emitLemma)
import EVM.SMT.Types
import EVM.Traversals (foldProp)
import EVM.Types (Prop, EType(EWord), Err, W256, Expr, Expr(Lit), Expr(SHL))

-- | Lemmas for abstract multiplication. Multiplication is kept fully
-- uninterpreted (no ground truth, so the solver never bit-blasts a symbolic
-- product); we add only the sound algebraic facts catalogued in
-- "EVM.SMT.AbstractLemmas". 'saturate' closes the term set the lemmas range
-- over; 'collectLemmas' picks the instances; 'emitLemma' renders each to SMT.
mulEncoding :: Enc -> [Prop] -> Err [SMTEntry]
mulEncoding enc props = do
  let ctx = saturate props
  if null ctx.acUDivs && null ctx.acMuls && null ctx.acConstMuls then pure []
  else do
    lemmas <- concat <$> mapM (emitLemma enc) (collectLemmas ctx)
    pure $ (SMTComment "multiplication abstraction lemmas") : lemmas

-- | Declare the magnitude variables and the unsigned result variable for a
-- group. For signed ops the magnitudes are the absolute values |a|, |b|; for
-- unsigned ops the operands are already non-negative, so the magnitude is the
-- operand itself (|x| = x).
declareAbsolute :: Enc -> DivModKind -> Int -> Expr EWord -> Expr EWord -> Builder -> Err ([SMTEntry], (Builder, Builder))
declareAbsolute enc kind groupIdx firstA firstB unsignedResult = do
  aenc <- enc firstA
  benc <- enc firstB
  let magnitude x = if isSigned kind then smtAbsolute x else x
      absoluteAEnc = magnitude aenc
      absoluteBEnc = magnitude benc
      absoluteAName = fromString $ "absolute_a" <> show groupIdx
      absoluteBName = fromString $ "absolute_b" <> show groupIdx
  let decls = [ SMTCommand $ "(declare-const" `sp` absoluteAName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` absoluteBName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` unsignedResult `sp` "(_ BitVec 256))"
              , SMTCommand $ "(assert (=" `sp` absoluteAName `sp` absoluteAEnc <> "))"
              , SMTCommand $ "(assert (=" `sp` absoluteBName `sp` absoluteBEnc <> "))"
              ]
  pure (decls, (absoluteAName, absoluteBName))

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
      let abstract = "(" <> abstFnName kind `sp` aenc `sp` benc <> ")"
          native   = "(" <> concFnName kind `sp` aenc `sp` benc <> ")"
          -- EVM defines x/0 = 0 and x%0 = 0, whereas SMT-LIB's native bvudiv/
          -- bvurem return non-zero on a zero divisor; guard the unsigned ops so
          -- the axiom matches op2CheckZero and the encoding's zero guard. (The
          -- signed reconstruction already applies the guard on its side.)
          concrete = if isSigned kind then native else smtZeroGuard benc native
      pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Encode div/mod operations using abs values, shift-bounds, and congruence (no bvudiv).
divModEncoding :: Enc -> [Prop] -> Err [SMTEntry]
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
    mkGroupEncoding groupIdx lhs@((firstKind, firstA, firstB) : _) = do
      let isDiv' = isDiv firstKind
          prefix = if isDiv' then "udiv" else "urem"
          unsignedResult = fromString $ prefix <> "_" <> show groupIdx
      (decls, (absoluteA, absoluteB)) <- declareAbsolute enc firstKind groupIdx firstA firstB unsignedResult

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
      axioms <- mapM (assertAbstEqResult enc unsignedResult) lhs
      pure $ decls <> shiftBounds <> axioms

-- | Congruence: if two groups of the same kind have equal magnitude inputs,
-- their results are equal. Signed and unsigned groups are linked separately so
-- a signed op is never tied to an unsigned op (and vice versa).
mkCongruenceLinks :: [(Int, [DivModOp])] -> [SMTEntry]
mkCongruenceLinks indexedGroups =
  let groupsOfKind want = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == want]
  in    concatMap (mkPairLinks "udiv") (allPairs (groupsOfKind IsSDiv))
     <> concatMap (mkPairLinks "urem") (allPairs (groupsOfKind IsSMod))
     <> concatMap (mkPairLinks "udiv") (allPairs (groupsOfKind IsUDiv))
     <> concatMap (mkPairLinks "urem") (allPairs (groupsOfKind IsUMod))
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
