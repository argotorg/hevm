{- | Abstract div/mobsolud encoding for two-phase SMT solving. -}
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
  , SMTCommand "(declare-fun abst_evm_bvudiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvurem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTComment "abstract multiplication (kept fully uninterpreted: no ground truth)"
  , SMTCommand "(declare-fun abst_evm_bvmul ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

-- | Local helper for trivial SMT constructs
sp :: Builder -> Builder -> Builder
a `sp` b = a <> " " <> b

zero :: Builder
zero = "(_ bv0 256)"

one :: Builder
one = "(_ bv1 256)"

-- | Maximum value representable in 128 unsigned bits (2^128 - 1).
maxU128 :: Builder
maxU128 = "(_ bv340282366920938463463374607431768211455 256)"

-- | A /sufficient/ condition for x*y not to overflow 256 bits: both operands
-- fit in 128 bits, so their product fits in 256 (since (2^128-1)^2 < 2^256).
--
-- We deliberately use this cheap sufficient condition rather than the exact
-- no-overflow predicate @extract 511 256 (bvmul (zext x) (zext y)) = 0@. The
-- exact form forces the solver to bit-blast a full 512-bit multiply for every
-- lemma instance, which is the dominant cost and makes queries with large
-- operands (~2^100) time out. Two comparisons against a constant are
-- essentially free by contrast.
--
-- This is the same width-budget idea Halmos uses. It is SOUND: when the guard
-- holds there is genuinely no overflow, so any lemma it gates remains valid.
-- The cost is completeness — a product of operands above 2^128 that happens not
-- to overflow will not receive the lemma. Callers bound operands (e.g. a
-- Solidity @require(x < 2**128)@) so the guard discharges cheaply.
mulNoOverflow :: Builder -> Builder -> Builder
mulNoOverflow x y =
  "(and (bvule " <> x <> " " <> maxU128 <> ") (bvule " <> y <> " " <> maxU128 <> "))"

wordAsBV :: forall a. Integral a => a -> Builder
wordAsBV w = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal w <> " 256)"

-- | The four EVM division/modulo operations. The @S@-variants are signed
-- (SDiv/SMod), the @U@-variants unsigned (Div/Mod). Signed and unsigned ops
-- are kept in separate groups so the signed absolute-value/sign-reconstruction
-- machinery is never applied to unsigned operands (and vice versa).
data DivModKind = IsSDiv | IsSMod | IsUDiv | IsUMod
  deriving (Eq, Ord)

type DivModOp = (DivModKind, Expr EWord, Expr EWord)

data AbstractKey = AbstractKey (Expr EWord) (Expr EWord) DivModKind
  deriving (Eq, Ord)

isDiv :: DivModKind -> Bool
isDiv IsSDiv = True
isDiv IsUDiv = True
isDiv _      = False

isSigned :: DivModKind -> Bool
isSigned IsSDiv = True
isSigned IsSMod = True
isSigned _      = False

-- | Name of the uninterpreted function standing in for this op.
abstFnName :: DivModKind -> Builder
abstFnName IsSDiv = "abst_evm_bvsdiv"
abstFnName IsSMod = "abst_evm_bvsrem"
abstFnName IsUDiv = "abst_evm_bvudiv"
abstFnName IsUMod = "abst_evm_bvurem"

-- | Name of the concrete SMT-LIB op refined against in phase two.
concFnName :: DivModKind -> Builder
concFnName IsSDiv = "bvsdiv"
concFnName IsSMod = "bvsrem"
concFnName IsUDiv = "bvudiv"
concFnName IsUMod = "bvurem"

-- | Collect all div/mod operations from an expression.
collectDivMods :: Expr a -> [DivModOp]
collectDivMods = \case
  T.SDiv a b -> [(IsSDiv, a, b)]
  T.SMod a b -> [(IsSMod, a, b)]
  T.Div  a b -> [(IsUDiv, a, b)]
  T.Mod  a b -> [(IsUMod, a, b)]
  _          -> []

abstractKey :: DivModOp -> AbstractKey
abstractKey (kind, a, b) = AbstractKey a b kind

-- | Declare the magnitude variables and the unsigned result variable for a
-- group. For signed ops the magnitudes are the absolute values |a|, |b|; for
-- unsigned ops the operands are already non-negative, so the magnitude is the
-- operand itself (|x| = x).
declareAbsolute :: (Expr EWord -> Err Builder) -> DivModKind -> Int -> Expr EWord -> Expr EWord -> Builder -> Err ([SMTEntry], (Builder, Builder))
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
assertAbstEqResult :: (Expr EWord -> Err Builder) -> Builder -> DivModOp -> Err SMTEntry
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
      let abstract = "(" <> abstFnName kind `sp` aenc `sp` benc <> ")"
          native   = "(" <> concFnName kind `sp` aenc `sp` benc <> ")"
          -- EVM defines x/0 = 0 and x%0 = 0, whereas SMT-LIB's native bvudiv/
          -- bvurem return non-zero on a zero divisor; guard the unsigned ops so
          -- the axiom matches op2CheckZero and the encoding's zero guard. (The
          -- signed reconstruction already applies the guard on its side.)
          concrete = if isSigned kind then native else smtZeroGuard benc native
      pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Collect symbolic*symbolic multiplications (neither operand a literal).
-- Concrete factors (incl. 0/1/power-of-two) are handled natively by the
-- simplifier, so only genuinely symbolic products are abstracted.
collectMuls :: Expr a -> [(Expr EWord, Expr EWord)]
collectMuls = \case
  T.Mul a b | notLit a, notLit b -> [(a, b)]
  _ -> []
  where
    notLit (Lit _) = False
    notLit _       = True

-- | Collect multiplications by a literal constant, @(c, x)@ for @c*x@ (either
-- operand order), excluding the trivial constants 0 and 1. These stay native
-- @bvmul@ (the value is concrete), but a symbolic operand times a large
-- constant is still costly to bit-blast and compare; const-mul monotonicity
-- (see 'mkConstMulMono') lets the solver order such products without doing so.
collectConstMuls :: Expr a -> [(W256, Expr EWord)]
collectConstMuls = \case
  T.Mul (Lit c) x | notLit x, c /= 0, c /= 1 -> [(c, x)]
  T.Mul x (Lit c) | notLit x, c /= 0, c /= 1 -> [(c, x)]
  _ -> []
  where
    notLit (Lit _) = False
    notLit _       = True

-- | True if any prop contains a symbolic*symbolic multiplication, i.e. the
-- multiplication abstraction is in play. Because abst_evm_bvmul is left
-- uninterpreted (no ground truth), a satisfying model may assign it values
-- inconsistent with real multiplication, so a counterexample cannot be
-- trusted; callers must downgrade SAT results to Unknown to stay SOUND.
hasAbstractMul :: [Prop] -> Bool
hasAbstractMul props = not $ null $ concatMap (foldProp collectMuls []) props

-- | Lemmas for abstract multiplication. Multiplication is kept fully
-- uninterpreted (no ground truth, so the solver never bit-blasts a symbolic
-- product); we add only sound algebraic facts. Commutativity is free because
-- the simplifier canonically orders Mul operands, so abst_evm_bvmul(a,b) and
-- abst_evm_bvmul(b,a) are the same term.
--
-- Step 1 lemma (sound unconditionally): quotient*divisor <= dividend, i.e.
--   abst_evm_bvmul(abst_evm_bvudiv(X,Y), Y) <= X
-- The product (X/Y)*Y <= X < 2^256 can never overflow, so no guard is needed.
-- This is what links the div and mul abstractions and chains nested divisions.
mulEncoding :: (Expr EWord -> Err Builder) -> [Prop] -> Err [SMTEntry]
mulEncoding enc props = do
  let udivs = [ (a, b) | (IsUDiv, a, b) <- nubOrd $ concatMap (foldProp collectDivMods []) props ]
      muls  = nubOrd $ concatMap (foldProp collectMuls []) props
      constMuls = nubOrd $ concatMap (foldProp collectConstMuls []) props
      -- Cancellation: when an abstract product a*b has a factor that is reused
      -- as a divisor elsewhere, synthesize the exact division (a*b)/factor.
      -- Adding it to the div set lets the existing lemmas bridge nested
      -- divisions: mulDiv-bound gives (a*b)/b <= a, and div-monotonicity carries
      -- that bound across a shared divisor. This is what proves cross-divisor
      -- round-trips like convertToAssetValue(convertToShares(x)) <= x (the
      -- stateless core of inflation-attack safety), which single-level lemmas
      -- cannot. The synthetic terms are exact EVM divisions, so this is SOUND.
      divisors  = nubOrd [ b | (_, b) <- udivs ]
      synthDivs = nubOrd $ [ (T.Mul a b, b) | (a, b) <- muls, b `elem` divisors ]
                        <> [ (T.Mul a b, a) | (a, b) <- muls, a `elem` divisors ]
      udivsAll  = nubOrd (udivs <> synthDivs)
      -- products the div-link lemma introduces, e.g. (a/b)*b
      linkMuls = [ (T.Div a b, b) | (a, b) <- udivsAll ]
      allMuls  = nubOrd (muls <> linkMuls)
      -- divisions whose dividend is an abstract product: (x*y)/z
      mulDivs = [ (a, x, y, b) | (a, b) <- udivsAll, Just (x, y) <- [asMul a] ]
      -- pairs of const-muls sharing the same constant: (c, x, y) for c*x, c*y
      constMulPairs = [ (c, x, y) | (c, x) <- constMuls, (c', y) <- constMuls, c == c', x /= y ]
      -- const cancellation: a product c1*x divided by a literal c2 that divides
      -- c1 collapses to (c1/c2)*x. (a, c1, c2, x): a is the dividend (c1*x). The
      -- same-constant case (c1==c2) gives just x; the general case (c2 | c1)
      -- covers lossless precision scaling like x*1e18/1e6 == x*1e12.
      constCancels = [ (a, c1, c2, x)
                     | (a, b) <- udivsAll, Just (c1, x) <- [asConstMul a]
                     , Lit c2 <- [b], c2 /= 0, c1 `mod` c2 == 0 ]
      -- nested-division collapse: (A/c1)/c2 == A/(c1*c2) for literals c1,c2 whose
      -- product fits in 256 bits. A floor identity (sound unconditionally). E.g.
      -- x*rate/1e9/1e18 == x*rate/1e27.
      nestedDivs = [ (innerA, c1, c2)
                   | (a, b) <- udivsAll, Lit c2 <- [b]
                   , T.Div innerA (Lit c1) <- [a]
                   , c1 /= 0, c2 /= 0, toInteger c1 * toInteger c2 < 2 ^ (256 :: Int) ]
  if null udivs && null muls && null constMuls then pure []
  else do
    comm    <- mapM mkComm allMuls
    links   <- mapM mkDivMulLink udivsAll
    zeroOne <- concat <$> mapM mkMulIdentities allMuls
    mulMono <- concat <$> mapM mkMulMono (sharedPairs (bothOrders allMuls))
    divMono <- concat <$> mapM mkDivMono (sharedPairs udivsAll)
    divDivisorMono <- concat <$> mapM mkDivisorMono (divisorPairs udivsAll)
    mulDivB <- concat <$> mapM mkMulDivBound mulDivs
    constMulMono <- mapM mkConstMulMono constMulPairs
    constCancel <- mapM mkConstCancel constCancels
    nestedDiv <- mapM mkNestedDiv nestedDivs
    pure $ (SMTComment "multiplication abstraction lemmas")
           : (comm <> zeroOne <> links <> mulMono <> divMono <> divDivisorMono <> mulDivB <> constMulMono <> constCancel <> nestedDiv)
  where
    -- commutativity: abst_evm_bvmul(a,b) = abst_evm_bvmul(b,a). Needed so that
    -- lemma terms match the props regardless of the simplifier's operand order.
    mkComm (a, b) = do
      aenc <- enc a; benc <- enc b
      let m1 = "(abst_evm_bvmul" `sp` aenc `sp` benc <> ")"
          m2 = "(abst_evm_bvmul" `sp` benc `sp` aenc <> ")"
      pure $ SMTCommand $ "(assert (=" `sp` m1 `sp` m2 <> "))"
    -- Include both operand orders of each product. Multiplication is
    -- commutative (and we assert that), but the simplifier/solc may order a
    -- product's operands either way; considering both ensures monotonicity is
    -- found regardless of ordering. Only used for the (commutative) mul lemmas,
    -- never for the order-sensitive division lemmas.
    bothOrders :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord)]
    bothOrders xs = nubOrd (xs <> [ (b, a) | (a, b) <- xs ])

    -- ordered pairs (x, y, z) where (x,z) and (y,z) both occur (shared 2nd operand)
    sharedPairs :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord, Expr EWord)]
    sharedPairs xs = [ (x, y, z) | (x, z) <- xs, (y, z') <- xs, z == z', x /= y ]

    -- ordered pairs (y1, y2, x) where (x,y1) and (x,y2) both occur (shared 1st
    -- operand): divisions of the same dividend by different divisors.
    divisorPairs :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord, Expr EWord)]
    divisorPairs xs = [ (y1, y2, x) | (x, y1) <- xs, (x', y2) <- xs, x == x', y1 /= y2 ]

    -- div anti-monotonicity in the divisor (sound for nonzero divisors): a
    -- bigger divisor yields a smaller-or-equal quotient.
    --   y1 <= y2 && y1 != 0  =>  x/y2 <= x/y1
    mkDivisorMono (y1, y2, x) = do
      y1e <- enc y1; y2e <- enc y2; xe <- enc x
      let dxy1 = "(abst_evm_bvudiv" `sp` xe `sp` y1e <> ")"
          dxy2 = "(abst_evm_bvudiv" `sp` xe `sp` y2e <> ")"
      pure [ SMTCommand $ "(assert (=> (and (distinct" `sp` y1e `sp` zero <> ")"
             <> " (bvule" `sp` y1e `sp` y2e <> ")) (bvule" `sp` dxy2 `sp` dxy1 <> ")))" ]

    -- mul monotonicity (guarded by no-overflow, hence sound): if neither x*z
    -- nor y*z overflows then x <= y  =>  x*z <= y*z. The guard is bound-free;
    -- bounding operands (e.g. a Solidity require) keeps it cheap to discharge.
    mkMulMono (x, y, z) = do
      xenc <- enc x; yenc <- enc y; zenc <- enc z
      let mxz = "(abst_evm_bvmul" `sp` xenc `sp` zenc <> ")"
          myz = "(abst_evm_bvmul" `sp` yenc `sp` zenc <> ")"
      -- forward: x <= y  =>  x*z <= y*z
      pure [ SMTCommand $ "(assert (=> (and" `sp` mulNoOverflow xenc zenc `sp` mulNoOverflow yenc zenc
             <> " (bvule" `sp` xenc `sp` yenc <> ")) (bvule" `sp` mxz `sp` myz <> ")))" ]

    -- const-mul monotonicity (sound, no-overflow guarded): for a fixed literal
    -- constant c, x <= y  =>  c*x <= c*y. Because c is concrete we compute the
    -- exact no-overflow bound floor((2^256-1)/c) at encode time, so the guard is
    -- a single comparison against a constant (cheap) rather than a 512-bit
    -- multiply. c*x stays a native bvmul; this lemma simply lets the solver
    -- order two such products without bit-blasting the multiply.
    mkConstMulMono (c, x, y) = do
      xe <- enc x; ye <- enc y
      let cbv  = wordAsBV c
          cx   = "(bvmul" `sp` cbv `sp` xe <> ")"
          cy   = "(bvmul" `sp` cbv `sp` ye <> ")"
          bnd  = wordAsBV ((maxBound :: W256) `div` c)  -- largest x with c*x < 2^256
      pure $ SMTCommand $ "(assert (=> (and (bvule" `sp` xe `sp` bnd <> ") (bvule" `sp` ye `sp` bnd <> ")"
             <> " (bvule" `sp` xe `sp` ye <> ")) (bvule" `sp` cx `sp` cy <> ")))"

    -- const cancellation (sound, no-overflow guarded): a product c1*x divided by
    -- a literal c2 that divides c1 collapses to (c1/c2)*x. The multiply by a
    -- constant stays a native bvmul but the divide is abstracted (uninterpreted),
    -- so without this the precision-scaling wrapper c1*x/c2 (e.g. amount*1e18/1e18
    -- in _getUsdsValue, or amount*1e18/1e6 in _getUsdcValue) is not provably its
    -- closed form. `a` is the dividend expr (c1*x) so the abst_evm_bvudiv term
    -- matches the prop exactly; c2 | c1 makes c1/c2 exact, and the no-overflow
    -- bound floor((2^256-1)/c1) is computed at encode time (one comparison).
    mkConstCancel (a, c1, c2, x) = do
      ae <- enc a; xe <- enc x
      let c2bv = wordAsBV c2
          k    = c1 `div` c2                 -- exact, since c2 | c1
          rhs  = if k == 1 then xe else "(bvmul" `sp` wordAsBV k `sp` xe <> ")"
          dv   = "(abst_evm_bvudiv" `sp` ae `sp` c2bv <> ")"
          bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
      pure $ SMTCommand $ "(assert (=> (bvule" `sp` xe `sp` bnd <> ") (=" `sp` dv `sp` rhs <> ")))"

    -- nested-division collapse (sound, floor identity): (A/c1)/c2 == A/(c1*c2) for
    -- literal c1,c2 with c1*c2 < 2^256. Lets the solver simplify chained constant
    -- divisions such as x*rate/1e9/1e18 to x*rate/1e27. No operand bound needed.
    mkNestedDiv (innerA, c1, c2) = do
      ae <- enc innerA
      let inner    = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c1 <> ")"
          outer    = "(abst_evm_bvudiv" `sp` inner `sp` wordAsBV c2 <> ")"
          collapsed = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV (c1 * c2) <> ")"
      pure $ SMTCommand $ "(assert (=" `sp` outer `sp` collapsed <> "))"

    -- recognise multiplication by a non-trivial literal constant: c*x or x*c.
    asConstMul :: Expr EWord -> Maybe (W256, Expr EWord)
    asConstMul (T.Mul (Lit c) x) | notLit x, c /= 0, c /= 1 = Just (c, x)
    asConstMul (T.Mul x (Lit c)) | notLit x, c /= 0, c /= 1 = Just (c, x)
    asConstMul _ = Nothing

    -- div monotonicity in the dividend (sound unconditionally): for a common
    -- divisor z, x <= y  =>  floor(x/z) <= floor(y/z).
    mkDivMono (x, y, z) = do
      xenc <- enc x; yenc <- enc y; zenc <- enc z
      let dxz = "(abst_evm_bvudiv" `sp` xenc `sp` zenc <> ")"
          dyz = "(abst_evm_bvudiv" `sp` yenc `sp` zenc <> ")"
      pure [ SMTCommand $ "(assert (=> (bvule" `sp` xenc `sp` yenc <> ") (bvule" `sp` dxz `sp` dyz <> ")))" ]
    -- recognise an abstract symbolic*symbolic product
    asMul :: Expr EWord -> Maybe (Expr EWord, Expr EWord)
    asMul (T.Mul x y) | notLit x, notLit y = Just (x, y)
    asMul _ = Nothing
    notLit (Lit _) = False
    notLit _       = True

    -- mulDiv bound (sound under no-overflow of x*z): if one factor is <= the
    -- divisor then dividing the product by it cannot exceed the other factor.
    --   y <= z  =>  (x*y)/z <= x       x <= z  =>  (x*y)/z <= y
    -- `a` is the original product expr, so the div term matches the prop exactly.
    mkMulDivBound (a, x, y, z) = do
      ae <- enc a; xe <- enc x; ye <- enc y; ze <- enc z
      let dv = "(abst_evm_bvudiv" `sp` ae `sp` ze <> ")"
      pure [ SMTCommand $ "(assert (=> (and (bvule" `sp` ye `sp` ze <> ")" `sp` mulNoOverflow xe ze
               <> ") (bvule" `sp` dv `sp` xe <> ")))"
           , SMTCommand $ "(assert (=> (and (bvule" `sp` xe `sp` ze <> ")" `sp` mulNoOverflow ye ze
               <> ") (bvule" `sp` dv `sp` ye <> ")))" ]
    -- quotient*divisor <= dividend
    mkDivMulLink (a, b) = do
      aenc <- enc a
      benc <- enc b
      let q  = "(abst_evm_bvudiv" `sp` aenc `sp` benc <> ")"
          qb = "(abst_evm_bvmul" `sp` q `sp` benc <> ")"
      pure $ SMTCommand $ "(assert (bvule" `sp` qb `sp` aenc <> "))"
    -- sound identities pinning the otherwise-free UF on 0/1 operands:
    --   x*0 = 0, 0*y = 0, x*1 = x, 1*y = y
    mkMulIdentities (a, b) = do
      aenc <- enc a
      benc <- enc b
      let m = "(abst_evm_bvmul" `sp` aenc `sp` benc <> ")"
      pure [ SMTCommand $ "(assert (=> (=" `sp` aenc `sp` zero <> ") (=" `sp` m `sp` zero  <> ")))"
           , SMTCommand $ "(assert (=> (=" `sp` benc `sp` zero <> ") (=" `sp` m `sp` zero  <> ")))"
           , SMTCommand $ "(assert (=> (=" `sp` aenc `sp` one  <> ") (=" `sp` m `sp` benc  <> ")))"
           , SMTCommand $ "(assert (=> (=" `sp` benc `sp` one  <> ") (=" `sp` m `sp` aenc  <> ")))"
           ]

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

-- | sdiv(a,b) = ITE(b = 0,              0,
--               ITE(sign(a) = sign(b),  udiv(|a|,|b|),
--                                      -udiv(|a|,|b|)))
signedFromUnsignedDiv :: Builder -> Builder -> Builder -> Builder
signedFromUnsignedDiv aenc benc udivResult =
  smtZeroGuard benc $
  "(ite" `sp` (smtSameSign aenc benc) `sp`
    udivResult `sp` (smtNeg udivResult) <> ")"

-- | smod(a,b) = ITE(b = 0,   0,
--               ITE(a ≥ 0,   urem(|a|,|b|),
--                           -urem(|a|,|b|)))
signedFromUnsignedMod :: Builder -> Builder -> Builder -> Builder
signedFromUnsignedMod aenc benc uremResult =
  smtZeroGuard benc $
  "(ite" `sp` (smtIsNonNeg aenc) `sp`
    uremResult `sp` (smtNeg uremResult) <> ")"
