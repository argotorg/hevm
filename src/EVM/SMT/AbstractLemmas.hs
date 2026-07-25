{- |
   Module: EVM.SMT.AbstractLemmas
   Description: The catalogue of sound algebraic lemmas for abstract arithmetic.

   Multiplication is kept fully uninterpreted (no ground truth, so the solver
   never bit-blasts a symbolic product); we add only /sound/ algebraic facts
   about @abst_evm_bvmul@/@abst_evm_bvudiv@. Each lemma is a 'LemmaInst'
   constructor, a 'collectLemmas' clause (its trigger) and an 'emitLemma'
   clause (the SMT it emits + why it is sound); GHC's exhaustiveness checker
   ties the three together. To audit soundness, read 'emitLemma': every
   emitted assertion is true of ordinary arithmetic, so anything derived from
   them holds for the real operations too.
-}
module EVM.SMT.AbstractLemmas
  ( LemmaInst(..)
  , collectLemmas
  , emitLemma
  ) where

import Data.Containers.ListUtils (nubOrd)

import EVM.SMT.AbstractBase
import EVM.SMT.SMTLIB (sp, zero, one, wordAsBV)
import EVM.SMT.Types (SMTEntry(..))
import EVM.Types (EType(EWord), Err, W256, Expr, Expr(Lit))
import EVM.Types qualified as T

-- | A single firing of a lemma family, carrying the sub-terms it matched.
data LemmaInst
  = Comm          (Expr EWord) (Expr EWord)                            -- ^ a*b = b*a
  | Identity      (Expr EWord) (Expr EWord)                            -- ^ x*0, 0*y, x*1, 1*y
  | DivMulLink    (Expr EWord) (Expr EWord)                            -- ^ (a/b)*b <= a
  | MulMono       (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ x<=y => x*z<=y*z
  | DivMono       (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ x<=y => x/z<=y/z
  | DivisorMono   (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ y1<=y2 => x/y2<=x/y1
  | MulDivBound   (Expr EWord) (Expr EWord) (Expr EWord) (Expr EWord)  -- ^ (x*y)/z <= x or y
  | MulDivExact   (Expr EWord) (Expr EWord) (Expr EWord) (Expr EWord)  -- ^ (x*y)/y == x (own-factor divisor)
  | DivModEuclid  (Expr EWord) (Expr EWord)                            -- ^ (a/b)*b + a%b == a
  | MulModCollapse (Expr EWord) (Expr EWord) (Expr EWord)              -- ^ mulmod(a,b,c) ground truth
  | RoundTrip     (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ ((x*A)/B * B)/A <= x
  | ConstMulMono  W256 (Expr EWord) (Expr EWord)                       -- ^ x<=y => c*x<=c*y
  | ConstCancel   (Expr EWord) W256 W256 (Expr EWord)                  -- ^ (c1*x)/c2 == (c1/c2)*x
  | NestedDiv     (Expr EWord) W256 W256                               -- ^ (A/c1)/c2 == A/(c1*c2)
  | FracReduce    (Expr EWord) W256 W256 (Expr EWord)                  -- ^ (c1*x)/c2 == x/(c2/c1)
  | CeilDivCancel (Expr EWord) W256 W256 (Expr EWord)                  -- ^ ceilDiv(c1*x,c2) inner divide
  | Telescope     (Expr EWord) (Expr EWord) W256 W256                  -- ^ (a*b)/c - (a*(b-k))/c == a*(k/c)
  deriving (Eq, Ord)

-- | Every lemma instance triggered by the saturated term set, in emission
-- order. One clause per family; see 'emitLemma' for the math.
collectLemmas :: AbstractCtx -> [LemmaInst]
collectLemmas ctx =
     -- commutativity + 0/1 identities over every product
     [ Comm a b            | (a, b) <- ctx.acMuls ]
  <> [ Identity a b        | (a, b) <- ctx.acMuls ]
     -- the div<->mul link, one per division
  <> [ DivMulLink a b      | (a, b) <- ctx.acUDivs ]
     -- monotonicities over shared-operand pairs
  <> [ MulMono x y z       | (x, y, z) <- sharedPairs (bothOrders (ctx.acMuls)) ]
  <> [ DivMono x y z       | (x, y, z) <- sharedPairs (ctx.acUDivs) ]
  <> [ DivisorMono y1 y2 x | (y1, y2, x) <- divisorPairs (ctx.acUDivs) ]
     -- product-over-divisor bound, for divisions whose dividend is a product
  <> [ MulDivBound a x y b | (a, b) <- ctx.acUDivs, Just (x, y) <- [asMul a] ]
     -- exact cancellation when the divisor is one of the product's own factors
  <> [ MulDivExact a x y b | (a, b) <- ctx.acUDivs, Just (x, y) <- [asMul a], y == b || x == b ]
     -- the Euclidean div/mod link, for (a,b) pairs carrying BOTH a division and
     -- a remainder (only then is it useful, and only then does it introduce
     -- terms already present)
  <> [ DivModEuclid a b | (a, b) <- ctx.acUDivs, (a', b') <- ctx.acUMods, a == a', b == b' ]
     -- mulmod ground truth, one per mulmod term
  <> [ MulModCollapse a b c | (a, b, c) <- ctx.acMulMods ]
     -- direct cross-divisor round trips matched on the nested shape
  <> [ RoundTrip outerNum aA x | (outerNum, aA, x) <- roundTrips ]
     -- const-mul monotonicity over const-products sharing the same constant
  <> [ ConstMulMono c x y  | (c, x) <- ctx.acConstMuls, (c', y) <- ctx.acConstMuls, c == c', x /= y ]
     -- constant cancellation / fraction reduction over constant divisions
  <> [ ConstCancel a c1 c2 x
     | (a, b) <- ctx.acUDivs, Just (c1, x) <- [asConstMul a]
     , Lit c2 <- [b], c2 /= 0, c1 `mod` c2 == 0 ]
  <> [ NestedDiv innerA c1 c2
     | (a, b) <- ctx.acUDivs, Lit c2 <- [b]
     , T.Div innerA (Lit c1) <- [a]
     , c1 /= 0, c2 /= 0, toInteger c1 * toInteger c2 < 2 ^ (256 :: Int) ]
  <> [ FracReduce a c1 c2 x
     | (a, b) <- ctx.acUDivs, Just (c1, x) <- [asConstMul a]
     , Lit c2 <- [b], c2 /= 0, c1 /= 0, c2 `mod` c1 == 0, c2 /= c1 ]
  <> [ CeilDivCancel a c1 c2 x
     | (a, b) <- ctx.acUDivs, T.Sub inner (Lit 1) <- [a]
     , Just (c1, x) <- [asConstMul inner]
     , Lit c2 <- [b], c2 /= 0, c1 `mod` c2 == 0 ]
     -- scaled-product telescoping (the only cross-product lemma)
  <> [ Telescope a b k c | (a, b, k, c) <- telescopes ]
  where
    telescopes = nubOrd
      [ (a, b, k, c)
      | (sd, Lit c) <- ctx.acUDivs, c /= 0
      , Just (f1, f2) <- [asMul sd]
      , (a, T.Sub b (Lit k)) <- [(f1, f2), (f2, f1)]
      , k /= 0, k `mod` c == 0
      , any (`elem` ctx.acUDivs) [ (T.Mul a b, Lit c), (T.Mul b a, Lit c) ] ]
    -- Direct cross-divisor round trip: ((x*A)/B)*B/A <= x. The multi-step chain
    -- (div-mul link -> div-monotonicity -> cancellation) only closes when every
    -- intermediate term happens to have been synthesized; matching the nested
    -- shape outright is robust to that. This is the shape BOTH the ERC4626
    -- inflation-attack round trip and the performance-fee core step reduce to.
    roundTrips = nubOrd
      [ (outerNum, aA, x)
      | (outerNum, aA) <- ctx.acUDivs
      , (q0, bB) <- mulPairs outerNum
      , q <- unIte q0
      , T.Div innerNum0 bB' <- [q], bB == bB'
      , innerNum <- unIte innerNum0
      , (x, aA') <- mulPairs innerNum, aA == aA' ]

-- | Emit the SMT assertion(s) for a single lemma instance. Each clause is the
-- sound fact, with its no-overflow / divisor guard where one is required.
emitLemma :: Enc -> LemmaInst -> Err [SMTEntry]

-- commutativity: abst_evm_bvmul(a,b) = abst_evm_bvmul(b,a), so lemma terms
-- match the props regardless of operand order.
emitLemma enc (Comm a b) = do
  aenc <- enc a; benc <- enc b
  let m1 = "(abst_evm_bvmul" `sp` aenc `sp` benc <> ")"
      m2 = "(abst_evm_bvmul" `sp` benc `sp` aenc <> ")"
  pure [ SMTCommand $ "(assert (=" `sp` m1 `sp` m2 <> "))" ]

-- 0/1 identities pinning the otherwise-free UF: x*0 = 0*y = 0, x*1 = x, 1*y = y
emitLemma enc (Identity a b) = do
  aenc <- enc a; benc <- enc b
  let m = "(abst_evm_bvmul" `sp` aenc `sp` benc <> ")"
  pure [ SMTCommand $ "(assert (=> (=" `sp` aenc `sp` zero <> ") (=" `sp` m `sp` zero  <> ")))"
       , SMTCommand $ "(assert (=> (=" `sp` benc `sp` zero <> ") (=" `sp` m `sp` zero  <> ")))"
       , SMTCommand $ "(assert (=> (=" `sp` aenc `sp` one  <> ") (=" `sp` m `sp` benc  <> ")))"
       , SMTCommand $ "(assert (=> (=" `sp` benc `sp` one  <> ") (=" `sp` m `sp` aenc  <> ")))"
       ]

-- div<->mul link (sound unconditionally, (a/b)*b <= a < 2^256 cannot
-- overflow): quotient*divisor <= dividend. Links the div and mul abstractions
-- and chains nested divisions.
emitLemma enc (DivMulLink a b) = do
  aenc <- enc a; benc <- enc b
  let q  = "(abst_evm_bvudiv" `sp` aenc `sp` benc <> ")"
      qb = "(abst_evm_bvmul" `sp` q `sp` benc <> ")"
  pure [ SMTCommand $ "(assert (bvule" `sp` qb `sp` aenc <> "))" ]

-- mul monotonicity (no-overflow guarded, hence sound):
--   x <= y => x*z <= y*z
emitLemma enc (MulMono x y z) = do
  xenc <- enc x; yenc <- enc y; zenc <- enc z
  let mxz = "(abst_evm_bvmul" `sp` xenc `sp` zenc <> ")"
      myz = "(abst_evm_bvmul" `sp` yenc `sp` zenc <> ")"
  pure [ SMTCommand $ "(assert (=> (and" `sp` mulNoOverflow xenc zenc `sp` mulNoOverflow yenc zenc
         <> " (bvule" `sp` xenc `sp` yenc <> ")) (bvule" `sp` mxz `sp` myz <> ")))" ]

-- div monotonicity in the dividend (sound unconditionally):
--   x <= y => floor(x/z) <= floor(y/z)
emitLemma enc (DivMono x y z) = do
  xenc <- enc x; yenc <- enc y; zenc <- enc z
  let dxz = "(abst_evm_bvudiv" `sp` xenc `sp` zenc <> ")"
      dyz = "(abst_evm_bvudiv" `sp` yenc `sp` zenc <> ")"
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xenc `sp` yenc <> ") (bvule" `sp` dxz `sp` dyz <> ")))" ]

-- div anti-monotonicity in the divisor (sound for nonzero divisors): a bigger
-- divisor yields a smaller-or-equal quotient.
--   y1 <= y2 && y1 != 0  =>  x/y2 <= x/y1
emitLemma enc (DivisorMono y1 y2 x) = do
  y1e <- enc y1; y2e <- enc y2; xe <- enc x
  let dxy1 = "(abst_evm_bvudiv" `sp` xe `sp` y1e <> ")"
      dxy2 = "(abst_evm_bvudiv" `sp` xe `sp` y2e <> ")"
  pure [ SMTCommand $ "(assert (=> (and (distinct" `sp` y1e `sp` zero <> ")"
         <> " (bvule" `sp` y1e `sp` y2e <> ")) (bvule" `sp` dxy2 `sp` dxy1 <> ")))" ]

-- mulDiv bound (sound under no-overflow of x*z): if one factor is <= the
-- divisor then dividing the product by it cannot exceed the other factor.
--   y <= z  =>  (x*y)/z <= x       x <= z  =>  (x*y)/z <= y
-- `a` is the original product expr, so the div term matches the prop exactly.
emitLemma enc (MulDivBound a x y z) = do
  ae <- enc a; xe <- enc x; ye <- enc y; ze <- enc z
  let dv = "(abst_evm_bvudiv" `sp` ae `sp` ze <> ")"
  pure [ SMTCommand $ "(assert (=> (and (bvule" `sp` ye `sp` ze <> ")" `sp` mulNoOverflow xe ze
           <> ") (bvule" `sp` dv `sp` xe <> ")))"
       , SMTCommand $ "(assert (=> (and (bvule" `sp` xe `sp` ze <> ")" `sp` mulNoOverflow ye ze
           <> ") (bvule" `sp` dv `sp` ye <> ")))" ]

-- exact mul-then-div cancellation (sound under no-overflow of the product):
-- dividing an abstract product by ONE OF ITS OWN FACTORS recovers the other
-- factor exactly. MulDivBound only supplies <=; the equality is what
-- round-trip properties (ERC4626 convert/preview, mulDiv) actually need --
-- without it (x*y)/y == x comes back `unknown` even with both operands
-- bounded below 2^128, because abst_evm_bvmul is deliberately ground-truth
-- free and nothing else pins the quotient from below.
--   z == y  /\  z != 0  /\  noOverflow(x,y)  =>  (x*y)/z == x
emitLemma enc (MulDivExact a x y z) = do
  ae <- enc a; xe <- enc x; ye <- enc y; ze <- enc z
  let dv = "(abst_evm_bvudiv" `sp` ae `sp` ze <> ")"
      nz = "(distinct" `sp` ze `sp` zero <> ")"
      lemma other = SMTCommand $ "(assert (=> (and" `sp` nz `sp` mulNoOverflow xe ye
                      <> ") (=" `sp` dv `sp` other <> ")))"
  pure $ [ lemma xe | y == z ] <> [ lemma ye | x == z ]

-- Euclidean div/mod link (sound unconditionally: the product (a/b)*b is
-- <= a < 2^256, so it can never overflow). This is the only lemma relating
-- the div and mod abstractions to each other; without it a remainder can be
-- discharged only by bit-blasting, and a == (a/b)*b + a%b stalls at `passed`.
--   b != 0  =>  (a/b)*b + (a%b) == a
emitLemma enc (DivModEuclid a b) = do
  ae <- enc a; be <- enc b
  let q  = "(abst_evm_bvudiv" `sp` ae `sp` be <> ")"
      qb = "(abst_evm_bvmul" `sp` q `sp` be <> ")"
      r  = "(abst_evm_bvurem" `sp` ae `sp` be <> ")"
  pure [ SMTCommand $ "(assert (=> (distinct" `sp` be `sp` zero <> ") (= (bvadd"
         `sp` qb `sp` r <> ")" `sp` ae <> ")))" ]

-- mulmod collapse. Both forms are sound:
--  * general: when a*b cannot exceed 256 bits, the full-precision product
--    equals the truncated one, so mulmod(a,b,c) == (a*b) % c.
--  * max-literal modulus: with c == 2^256-1 and a,b < 2^128 the product is at
--    most 2^256-2^129+1, strictly below the modulus, so the remainder IS the
--    product. OpenZeppelin's Math.mulDiv probes overflow with exactly
--    mulmod(x, y, not(0)), so this is the lemma that lets `prod1 == 0`
--    discharge -- pruning the 512-bit Newton-Raphson branch instead of
--    exploring it, which is what stalls every mulDiv-based property today.
emitLemma enc (MulModCollapse a b c) = do
  ae <- enc a; be <- enc b; ce <- enc c
  let mm   = "(abst_evm_mulmod" `sp` ae `sp` be `sp` ce <> ")"
      prod = "(abst_evm_bvmul" `sp` ae `sp` be <> ")"
      nzc  = "(distinct" `sp` ce `sp` zero <> ")"
      gen  = SMTCommand $ "(assert (=> (and" `sp` nzc `sp` mulNoOverflow ae be
               <> ") (=" `sp` mm `sp` "(abst_evm_bvurem" `sp` prod `sp` ce <> ")" <> ")))"
      big  = [ SMTCommand $ "(assert (=>" `sp` mulNoOverflow ae be
                 `sp` "(=" `sp` mm `sp` prod <> ")))"
             | Lit m <- [c], m == maxBound ]
      -- Fundamental remainder bound, unconditionally true. The exact 512-bit
      -- encoding gave this away for free (bvurem(X,c) < c is readable off the
      -- term); an uninterpreted mulmod does not, so without this lemma
      -- abstracting MULMOD REGRESSES anything relying on the bound, and
      -- leaves a remainder unpinned from above.
      bnd  = SMTCommand $ "(assert (=>" `sp` nzc `sp` "(bvult" `sp` mm `sp` ce <> ")))"
  pure (gen : bnd : big)

-- Cross-divisor round trip (sound): with q = floor(x*A/B) we have q <= x*A/B,
-- hence q*B <= x*A, hence floor(q*B/A) <= floor(x*A/A) = x. The final equality
-- needs x*A not to overflow, so the no-overflow guard is required; A != 0 is
-- kept for conservatism (EVM x/0 = 0 would satisfy the bound trivially anyway).
--   A != 0 /\ noOverflow(x,A)  =>  ((x*A)/B * B)/A <= x
emitLemma enc (RoundTrip outerNum aA x) = do
  oe <- enc outerNum; ae <- enc aA; xe <- enc x
  let dv = "(abst_evm_bvudiv" `sp` oe `sp` ae <> ")"
      nz = "(distinct" `sp` ae `sp` zero <> ")"
  pure [ SMTCommand $ "(assert (=> (and" `sp` nz `sp` mulNoOverflow xe ae
         <> ") (bvule" `sp` dv `sp` xe <> ")))" ]

-- const-mul monotonicity (sound, no-overflow guarded): x <= y => c*x <= c*y.
-- c is concrete, so the exact bound floor((2^256-1)/c) is computed at encode
-- time and the guard is one comparison. c*x stays a native bvmul; the lemma
-- lets the solver order two such products without bit-blasting the multiply.
emitLemma enc (ConstMulMono c x y) = do
  xe <- enc x; ye <- enc y
  let cbv  = wordAsBV c
      cx   = "(bvmul" `sp` cbv `sp` xe <> ")"
      cy   = "(bvmul" `sp` cbv `sp` ye <> ")"
      bnd  = wordAsBV ((maxBound :: W256) `div` c)  -- largest x with c*x < 2^256
  pure [ SMTCommand $ "(assert (=> (and (bvule" `sp` xe `sp` bnd <> ") (bvule" `sp` ye `sp` bnd <> ")"
         <> " (bvule" `sp` xe `sp` ye <> ")) (bvule" `sp` cx `sp` cy <> ")))" ]

-- const cancellation (sound, no-overflow guarded): (c1*x)/c2 == (c1/c2)*x
-- when c2 | c1 — the precision-scaling wrapper, e.g. amount*1e18/1e6.
-- `a` is the dividend expr (c1*x), kept so the div term matches the prop.
emitLemma enc (ConstCancel a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let c2bv = wordAsBV c2
      k    = c1 `div` c2                 -- exact, since c2 | c1
      rhs  = if k == 1 then xe else "(bvmul" `sp` wordAsBV k `sp` xe <> ")"
      dv   = "(abst_evm_bvudiv" `sp` ae `sp` c2bv <> ")"
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xe `sp` bnd <> ") (=" `sp` dv `sp` rhs <> ")))" ]

-- nested-division collapse (sound floor identity, no guard needed):
-- (A/c1)/c2 == A/(c1*c2) for literal c1,c2 with c1*c2 < 2^256,
-- e.g. x*rate/1e9/1e18 == x*rate/1e27.
emitLemma enc (NestedDiv innerA c1 c2) = do
  ae <- enc innerA
  let inner     = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c1 <> ")"
      outer     = "(abst_evm_bvudiv" `sp` inner `sp` wordAsBV c2 <> ")"
      collapsed = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV (c1 * c2) <> ")"
  pure [ SMTCommand $ "(assert (=" `sp` outer `sp` collapsed <> "))" ]

-- fraction-reduce (sound, no-overflow guarded): (c1*x)/c2 == x/(c2/c1) when
-- c1 | c2 — the mirror of const-cancel (multiply by small, divide by large,
-- e.g. x*1e6/1e18 == x/1e12). Under the guard c1*x is exact, and
-- floor(c1*x / (c1*k)) = floor(x/k).
emitLemma enc (FracReduce a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let k    = c2 `div` c1                 -- exact and >= 2, since c1 | c2 and c2 /= c1
      dv   = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c2 <> ")"   -- (c1*x)/c2
      rhs  = "(abst_evm_bvudiv" `sp` xe `sp` wordAsBV k <> ")"    -- x/(c2/c1)
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xe `sp` bnd <> ") (=" `sp` dv `sp` rhs <> ")))" ]

-- ceilDiv-cancel (sound, guarded): pins the abstracted divide inside
-- OpenZeppelin's Math.ceilDiv(c1*x, c2) = (c1*x - 1)/c2 + 1. When c2 | c1,
-- write c1 = c2*m: floor((c2*m*x - 1)/c2) = m*x - 1 for m*x >= 1, so with the
-- ceilDiv's +1 the quote is exactly (c1/c2)*x. Guarded by x >= 1 (the ceilDiv
-- ITE handles x==0) and no-overflow. `a` is the (c1*x - 1) dividend expr.
emitLemma enc (CeilDivCancel a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let m    = c1 `div` c2                 -- exact, since c2 | c1
      mx   = if m == 1 then xe else "(bvmul" `sp` wordAsBV m `sp` xe <> ")"
      dv   = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c2 <> ")"   -- (c1*x - 1)/c2
      rhs  = "(bvsub" `sp` mx `sp` one <> ")"                     -- (c1/c2)*x - 1
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (and (bvuge" `sp` xe `sp` one <> ")"
         <> " (bvule" `sp` xe `sp` bnd <> ")) (=" `sp` dv `sp` rhs <> ")))" ]

-- scaled-product telescoping (sound, no-overflow guarded). For products
-- sharing factor a whose other factors differ by a literal k with c | k:
--   floor(a*b/c) == floor(a*(b-k)/c) + a*(k/c)
-- Sound: a*b = a*(b-k) + a*k and a*k is an exact multiple of c, so removing it
-- shifts the floor by exactly a*(k/c). The only lemma pinning the EXACT
-- difference of two abstract products (value-change accounting, e.g.
-- susds*rate/1e27 - susds). b >= k in the guard rules out wraparound in b-k.
emitLemma enc (Telescope a b k c) = do
  ae <- enc a; be <- enc b
  let m       = k `div` c                       -- exact, since c | k
      cbv     = wordAsBV c
      full    = "(abst_evm_bvmul" `sp` ae `sp` be <> ")"
      stepped = "(abst_evm_bvmul" `sp` ae `sp` ("(bvsub" `sp` be `sp` wordAsBV k <> ")") <> ")"
      dFull   = "(abst_evm_bvudiv" `sp` full `sp` cbv <> ")"
      dStep   = "(abst_evm_bvudiv" `sp` stepped `sp` cbv <> ")"
      coeff   = if m == 1 then ae else "(bvmul" `sp` wordAsBV m `sp` ae <> ")"
      rhs     = "(bvadd" `sp` dStep `sp` coeff <> ")"
  pure [ SMTCommand $ "(assert (=> (and" `sp` mulNoOverflow ae be
         <> " (bvuge" `sp` be `sp` wordAsBV k <> ")) (=" `sp` dFull `sp` rhs <> ")))" ]

-- | Both operand orders of each product, so monotonicity fires regardless of
-- how the simplifier ordered the operands.
bothOrders :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord)]
bothOrders xs = nubOrd (xs <> [ (b, a) | (a, b) <- xs ])

-- | Any product, literal factors included, in BOTH operand orders. 'asMul' is
-- symbolic-only, which is right for the mul abstraction but wrong for shape
-- matching: a round trip scaled by a precision constant is still a round trip.
mulPairs :: Expr EWord -> [(Expr EWord, Expr EWord)]
mulPairs (T.Mul u v) = nubOrd [(u, v), (v, u)]
mulPairs _           = []

-- | See through the ITE that OpenZeppelin's mulDiv leaves behind. Its result is
-- `prod1 == 0 ? prod0/denominator : <512-bit newton>`, and that condition is
-- SYMBOLIC, so the simplifier keeps the ITE (it collapses only literal
-- conditions, Expr.hs). A single cancellation still verifies because the solver
-- reasons semantically, but a lemma matched SYNTACTICALLY against Div(...) never
-- fires on the nested shape. Consider both branches: the lemma is guarded and
-- sound whichever branch the quotient actually came from.
unIte :: Expr EWord -> [Expr EWord]
unIte (T.ITE _ t f) = concatMap unIte [t, f]
unIte e             = [e]

-- | Ordered pairs (x, y, z) where (x,z) and (y,z) both occur (shared 2nd
-- operand): products by a common factor, or divisions by a common divisor.
sharedPairs :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord, Expr EWord)]
sharedPairs xs = [ (x, y, z) | (x, z) <- xs, (y, z') <- xs, z == z', x /= y ]

-- | Ordered pairs (y1, y2, x) where (x,y1) and (x,y2) both occur (shared 1st
-- operand): divisions of the same dividend by different divisors.
divisorPairs :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord, Expr EWord)]
divisorPairs xs = [ (y1, y2, x) | (x, y1) <- xs, (x', y2) <- xs, x == x', y1 /= y2 ]
