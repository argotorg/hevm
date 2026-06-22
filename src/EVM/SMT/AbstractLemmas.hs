{- |
   Module: EVM.SMT.AbstractLemmas
   Description: The catalogue of sound algebraic lemmas for abstract arithmetic.

   This is the review surface. Multiplication is kept fully uninterpreted (no
   ground truth, so the solver never bit-blasts a symbolic product); we add only
   /sound/ algebraic facts about @abst_evm_bvmul@/@abst_evm_bvudiv@. Each lemma
   appears in three aligned places, under a shared banner:

   1. a 'LemmaInst' constructor (its arguments),
   2. a clause in 'collectLemmas' (when it fires — the trigger), and
   3. a clause in 'emitLemma' (the SMT it emits + why it is sound).

   To audit soundness, read 'emitLemma': every emitted assertion is true of
   ordinary multiplication/division, so anything the solver derives from them
   holds for the real operations too. To add a lemma, add a constructor, a
   'collectLemmas' clause, and an 'emitLemma' clause — GHC's exhaustiveness
   checker forces the third once you add the first.

   The emission order in 'collectLemmas' is family-by-family and is preserved
   from the original monolithic encoder, so the generated query is unchanged.
-}
module EVM.SMT.AbstractLemmas
  ( LemmaInst(..)
  , collectLemmas
  , emitLemma
  ) where

import Data.Containers.ListUtils (nubOrd)

import EVM.SMT.AbstractBase
import EVM.SMT.Types (SMTEntry(..))
import EVM.Types (EType(EWord), Err, W256, Expr, Expr(Lit))
import EVM.Types qualified as T

-- | A single firing of a lemma family, carrying the sub-terms it matched.
-- Field meanings are documented at the corresponding 'emitLemma' clause.
data LemmaInst
  = Comm          (Expr EWord) (Expr EWord)                            -- ^ a*b = b*a
  | Identity      (Expr EWord) (Expr EWord)                            -- ^ x*0, 0*y, x*1, 1*y
  | DivMulLink    (Expr EWord) (Expr EWord)                            -- ^ (a/b)*b <= a
  | MulMono       (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ x<=y => x*z<=y*z
  | DivMono       (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ x<=y => x/z<=y/z
  | DivisorMono   (Expr EWord) (Expr EWord) (Expr EWord)               -- ^ y1<=y2 => x/y2<=x/y1
  | MulDivBound   (Expr EWord) (Expr EWord) (Expr EWord) (Expr EWord)  -- ^ (x*y)/z <= x or y
  | ConstMulMono  W256 (Expr EWord) (Expr EWord)                       -- ^ x<=y => c*x<=c*y
  | ConstCancel   (Expr EWord) W256 W256 (Expr EWord)                  -- ^ (c1*x)/c2 == (c1/c2)*x
  | NestedDiv     (Expr EWord) W256 W256                               -- ^ (A/c1)/c2 == A/(c1*c2)
  | FracReduce    (Expr EWord) W256 W256 (Expr EWord)                  -- ^ (c1*x)/c2 == x/(c2/c1)
  | CeilDivCancel (Expr EWord) W256 W256 (Expr EWord)                  -- ^ ceilDiv(c1*x,c2) inner divide
  | Telescope     (Expr EWord) (Expr EWord) W256 W256                  -- ^ (a*b)/c - (a*(b-k))/c == a*(k/c)
  deriving (Eq, Ord)

-- | Every lemma instance triggered by the saturated term set, in the order the
-- assertions are emitted. One clause per family; see 'emitLemma' for the math.
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

-- | Emit the SMT assertion(s) for a single lemma instance. Each clause is the
-- sound fact, with its no-overflow / divisor guard where one is required.
emitLemma :: Enc -> LemmaInst -> Err [SMTEntry]

-- commutativity: abst_evm_bvmul(a,b) = abst_evm_bvmul(b,a). Needed so lemma
-- terms match the props regardless of the simplifier's operand order.
emitLemma enc (Comm a b) = do
  aenc <- enc a; benc <- enc b
  let m1 = "(abst_evm_bvmul" `sp` aenc `sp` benc <> ")"
      m2 = "(abst_evm_bvmul" `sp` benc `sp` aenc <> ")"
  pure [ SMTCommand $ "(assert (=" `sp` m1 `sp` m2 <> "))" ]

-- sound identities pinning the otherwise-free UF on 0/1 operands:
--   x*0 = 0, 0*y = 0, x*1 = x, 1*y = y
emitLemma enc (Identity a b) = do
  aenc <- enc a; benc <- enc b
  let m = "(abst_evm_bvmul" `sp` aenc `sp` benc <> ")"
  pure [ SMTCommand $ "(assert (=> (=" `sp` aenc `sp` zero <> ") (=" `sp` m `sp` zero  <> ")))"
       , SMTCommand $ "(assert (=> (=" `sp` benc `sp` zero <> ") (=" `sp` m `sp` zero  <> ")))"
       , SMTCommand $ "(assert (=> (=" `sp` aenc `sp` one  <> ") (=" `sp` m `sp` benc  <> ")))"
       , SMTCommand $ "(assert (=> (=" `sp` benc `sp` one  <> ") (=" `sp` m `sp` aenc  <> ")))"
       ]

-- div<->mul link (sound unconditionally): quotient*divisor <= dividend, i.e.
--   abst_evm_bvmul(abst_evm_bvudiv(a,b), b) <= a.
-- (a/b)*b <= a < 2^256 can never overflow, so no guard. This links the div and
-- mul abstractions and chains nested divisions.
emitLemma enc (DivMulLink a b) = do
  aenc <- enc a; benc <- enc b
  let q  = "(abst_evm_bvudiv" `sp` aenc `sp` benc <> ")"
      qb = "(abst_evm_bvmul" `sp` q `sp` benc <> ")"
  pure [ SMTCommand $ "(assert (bvule" `sp` qb `sp` aenc <> "))" ]

-- mul monotonicity (guarded by no-overflow, hence sound): if neither x*z nor
-- y*z overflows then x <= y => x*z <= y*z. The guard is bound-free; bounding
-- operands (e.g. a Solidity require) keeps it cheap to discharge.
emitLemma enc (MulMono x y z) = do
  xenc <- enc x; yenc <- enc y; zenc <- enc z
  let mxz = "(abst_evm_bvmul" `sp` xenc `sp` zenc <> ")"
      myz = "(abst_evm_bvmul" `sp` yenc `sp` zenc <> ")"
  pure [ SMTCommand $ "(assert (=> (and" `sp` mulNoOverflow xenc zenc `sp` mulNoOverflow yenc zenc
         <> " (bvule" `sp` xenc `sp` yenc <> ")) (bvule" `sp` mxz `sp` myz <> ")))" ]

-- div monotonicity in the dividend (sound unconditionally): for a common
-- divisor z, x <= y => floor(x/z) <= floor(y/z).
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

-- const-mul monotonicity (sound, no-overflow guarded): for a fixed literal
-- constant c, x <= y => c*x <= c*y. Because c is concrete we compute the exact
-- no-overflow bound floor((2^256-1)/c) at encode time, so the guard is a single
-- comparison against a constant. c*x stays a native bvmul; this lemma just lets
-- the solver order two such products without bit-blasting the multiply.
emitLemma enc (ConstMulMono c x y) = do
  xe <- enc x; ye <- enc y
  let cbv  = wordAsBV c
      cx   = "(bvmul" `sp` cbv `sp` xe <> ")"
      cy   = "(bvmul" `sp` cbv `sp` ye <> ")"
      bnd  = wordAsBV ((maxBound :: W256) `div` c)  -- largest x with c*x < 2^256
  pure [ SMTCommand $ "(assert (=> (and (bvule" `sp` xe `sp` bnd <> ") (bvule" `sp` ye `sp` bnd <> ")"
         <> " (bvule" `sp` xe `sp` ye <> ")) (bvule" `sp` cx `sp` cy <> ")))" ]

-- const cancellation (sound, no-overflow guarded): a product c1*x divided by a
-- literal c2 that divides c1 collapses to (c1/c2)*x. The multiply by a constant
-- stays a native bvmul but the divide is abstracted, so without this the
-- precision-scaling wrapper c1*x/c2 (e.g. amount*1e18/1e6 in _getUsdcValue) is
-- not provably its closed form. `a` is the dividend (c1*x); c2 | c1 makes c1/c2
-- exact, and the bound floor((2^256-1)/c1) is computed at encode time.
emitLemma enc (ConstCancel a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let c2bv = wordAsBV c2
      k    = c1 `div` c2                 -- exact, since c2 | c1
      rhs  = if k == 1 then xe else "(bvmul" `sp` wordAsBV k `sp` xe <> ")"
      dv   = "(abst_evm_bvudiv" `sp` ae `sp` c2bv <> ")"
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xe `sp` bnd <> ") (=" `sp` dv `sp` rhs <> ")))" ]

-- nested-division collapse (sound, floor identity): (A/c1)/c2 == A/(c1*c2) for
-- literal c1,c2 with c1*c2 < 2^256. Lets the solver simplify chained constant
-- divisions such as x*rate/1e9/1e18 to x*rate/1e27. No operand bound needed.
emitLemma enc (NestedDiv innerA c1 c2) = do
  ae <- enc innerA
  let inner     = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c1 <> ")"
      outer     = "(abst_evm_bvudiv" `sp` inner `sp` wordAsBV c2 <> ")"
      collapsed = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV (c1 * c2) <> ")"
  pure [ SMTCommand $ "(assert (=" `sp` outer `sp` collapsed <> "))" ]

-- fraction-reduce (sound, no-overflow guarded): a product c1*x divided by a
-- literal c2 that c1 divides collapses to x/(c2/c1). The mirror of const-cancel:
-- const-cancel needs c2 | c1 (multiply by large, divide by small); this needs
-- c1 | c2 (multiply by small, divide by large, e.g. x*1e6/1e18 == x/1e12 — the
-- convert-to-usdc precision step). Under the guard c1*x is exact and
-- floor(c1*x / (c1*k)) = floor(x/k). `a` is the dividend (c1*x).
emitLemma enc (FracReduce a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let k    = c2 `div` c1                 -- exact and >= 2, since c1 | c2 and c2 /= c1
      dv   = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c2 <> ")"   -- (c1*x)/c2
      rhs  = "(abst_evm_bvudiv" `sp` xe `sp` wordAsBV k <> ")"    -- x/(c2/c1)
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xe `sp` bnd <> ") (=" `sp` dv `sp` rhs <> ")))" ]

-- ceilDiv-cancel (sound, guarded): pins the abstracted divide inside
-- OpenZeppelin's Math.ceilDiv(c1*x, c2) = (c1*x - 1)/c2 + 1 (the c1*x != 0
-- branch). `a` is the (c1*x - 1) dividend. When c2 | c1, write c1 = c2*m: then
-- c1*x = c2*(m*x), so floor((c2*m*x - 1)/c2) = m*x - 1 (for m*x >= 1). Adding the
-- ceilDiv's +1 gives m*x = (c1/c2)*x exactly. Guarded by x >= 1 (the ceilDiv ITE
-- handles x==0) and the encode-time no-overflow bound floor((2^256-1)/c1).
emitLemma enc (CeilDivCancel a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let m    = c1 `div` c2                 -- exact, since c2 | c1
      mx   = if m == 1 then xe else "(bvmul" `sp` wordAsBV m `sp` xe <> ")"
      dv   = "(abst_evm_bvudiv" `sp` ae `sp` wordAsBV c2 <> ")"   -- (c1*x - 1)/c2
      rhs  = "(bvsub" `sp` mx `sp` one <> ")"                     -- (c1/c2)*x - 1
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (and (bvuge" `sp` xe `sp` one <> ")"
         <> " (bvule" `sp` xe `sp` bnd <> ")) (=" `sp` dv `sp` rhs <> ")))" ]

-- scaled-product telescoping (sound, no-overflow guarded). For products sharing
-- factor a whose other factors differ by a literal k with c | k:
--   floor(a*b/c) == floor(a*(b-k)/c) + a*(k/c).
-- Sound because a*b = a*(b-k) + a*k and a*k is an exact multiple of c, so
-- removing it shifts the floor by exactly a*(k/c). The only lemma pinning the
-- EXACT difference of two distinct abstract products; discharges value-change
-- accounting like susds*rate/1e27 - susds == susds*(rate-1e27)/1e27. Guarded by
-- no-overflow on a*b and b >= k (so b-k is a true difference, no wraparound).
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

-- | Include both operand orders of each product. Multiplication is commutative
-- (and we assert that), but the simplifier/solc may order a product's operands
-- either way; considering both ensures monotonicity is found regardless of
-- ordering. Only used for the (commutative) mul lemmas.
bothOrders :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord)]
bothOrders xs = nubOrd (xs <> [ (b, a) | (a, b) <- xs ])

-- | Ordered pairs (x, y, z) where (x,z) and (y,z) both occur (shared 2nd
-- operand): products by a common factor, or divisions by a common divisor.
sharedPairs :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord, Expr EWord)]
sharedPairs xs = [ (x, y, z) | (x, z) <- xs, (y, z') <- xs, z == z', x /= y ]

-- | Ordered pairs (y1, y2, x) where (x,y1) and (x,y2) both occur (shared 1st
-- operand): divisions of the same dividend by different divisors.
divisorPairs :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord, Expr EWord)]
divisorPairs xs = [ (y1, y2, x) | (x, y1) <- xs, (x', y2) <- xs, x == x', y1 /= y2 ]
