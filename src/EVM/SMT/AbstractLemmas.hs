{- |
   Module: EVM.SMT.AbstractLemmas
   Description: The catalogue of sound algebraic lemmas for abstract arithmetic.

   Multiplication starts uninterpreted, so the solver does not bit-blast a
   symbolic product during the proof phase; we add only /sound/ algebraic facts
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
  , lemmaFamily
  , lemmaDivs
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
  | MulModCollapse (Expr EWord) (Expr EWord) (Expr EWord)              -- ^ mulmod(a,b,c) bounds and collapse
  | RoundTrip     (Expr EWord) (Expr EWord) (Expr EWord) [(Expr EWord, Expr EWord)] -- ^ guarded ((x*A)/B * B)/A <= x
  | ConstMulMono  W256 (Expr EWord) (Expr EWord)                       -- ^ x<=y => c*x<=c*y
  | ConstCancel   (Expr EWord) W256 W256 (Expr EWord)                  -- ^ (c1*x)/c2 == (c1/c2)*x
  | NestedDiv     (Expr EWord) W256 W256                               -- ^ (A/c1)/c2 == A/(c1*c2)
  | FracReduce    (Expr EWord) W256 W256 (Expr EWord)                  -- ^ (c1*x)/c2 == x/(c2/c1)
  | CeilDivCancel (Expr EWord) W256 W256 (Expr EWord)                  -- ^ ceilDiv(c1*x,c2) inner divide
  | Telescope     (Expr EWord) (Expr EWord) W256 W256                  -- ^ (a*b)/c - (a*(b-k))/c == a*(k/c)
  deriving (Eq, Ord)

-- | The family an instance belongs to, for reporting which lemmas fired.
lemmaFamily :: LemmaInst -> String
lemmaFamily = \case
  Comm{} -> "commutativity"
  Identity{} -> "zero/one identity"
  DivMulLink{} -> "div-mul link"
  MulMono{} -> "mul monotonicity"
  DivMono{} -> "dividend monotonicity"
  DivisorMono{} -> "divisor monotonicity"
  MulDivBound{} -> "mulDiv bound"
  MulDivExact{} -> "mulDiv cancellation"
  DivModEuclid{} -> "div-mod identity"
  MulModCollapse{} -> "mulmod collapse"
  RoundTrip{} -> "round-trip bound"
  ConstMulMono{} -> "const-mul monotonicity"
  ConstCancel{} -> "const cancellation"
  NestedDiv{} -> "nested-division collapse"
  FracReduce{} -> "fraction reduction"
  CeilDivCancel{} -> "ceilDiv cancellation"
  Telescope{} -> "telescope"

-- | Divisions an instance's assertion mentions that are neither in the goal
-- nor in the saturated set.
lemmaDivs :: LemmaInst -> [(Expr EWord, Expr EWord)]
lemmaDivs = \case
  FracReduce _ c1 c2 x -> [(x, Lit (c2 `div` c1))]
  _ -> []

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
     -- link matching quotient and remainder terms
  <> [ DivModEuclid a b | (a, b) <- ctx.acUDivs, (a', b') <- ctx.acUMods, a == a', b == b' ]
     -- mulmod bounds and collapse, one per mulmod term
  <> [ MulModCollapse a b c | (a, b, c) <- ctx.acMulMods ]
     -- direct cross-divisor round trips matched on the nested shape
  <> [ RoundTrip outerNum aA x guards | (outerNum, aA, x, guards) <- roundTrips ]
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
    -- Conditional matches require the expression to equal the matched branch.
    roundTrips = nubOrd
      [ (outerNum, aA, x, [(q0, q) | q0 /= q] <> [(innerNum0, innerNum) | innerNum0 /= innerNum])
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
  let m1 = mulSMT (a, aenc) (b, benc)
      m2 = mulSMT (b, benc) (a, aenc)
  pure [ SMTCommand $ "(assert (=" `sp` m1 `sp` m2 <> "))" ]

-- 0/1 identities pinning the otherwise-free UF: x*0 = 0*y = 0, x*1 = x, 1*y = y
emitLemma enc (Identity a b) = do
  aenc <- enc a; benc <- enc b
  let m = mulSMT (a, aenc) (b, benc)
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
  let q  = udivSMT aenc benc
      qb = mulSMT (T.Div a b, q) (b, benc)
  pure [ SMTCommand $ "(assert (bvule" `sp` qb `sp` aenc <> "))" ]

-- mul monotonicity (no-overflow guarded, hence sound):
--   x <= y => x*z <= y*z
emitLemma enc (MulMono x y z) = do
  xenc <- enc x; yenc <- enc y; zenc <- enc z
  let mxz = mulSMT (x, xenc) (z, zenc)
      myz = mulSMT (y, yenc) (z, zenc)
  pure [ SMTCommand $ "(assert (=> (and" `sp` mulNoOverflow xenc zenc `sp` mulNoOverflow yenc zenc
         <> " (bvule" `sp` xenc `sp` yenc <> ")) (bvule" `sp` mxz `sp` myz <> ")))" ]

-- div monotonicity in the dividend (sound unconditionally):
--   x <= y => floor(x/z) <= floor(y/z)
emitLemma enc (DivMono x y z) = do
  xenc <- enc x; yenc <- enc y; zenc <- enc z
  let dxz = udivSMT xenc zenc
      dyz = udivSMT yenc zenc
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xenc `sp` yenc <> ") (bvule" `sp` dxz `sp` dyz <> ")))" ]

-- div anti-monotonicity in the divisor (sound for nonzero divisors): a bigger
-- divisor yields a smaller-or-equal quotient.
--   y1 <= y2 && y1 != 0  =>  x/y2 <= x/y1
emitLemma enc (DivisorMono y1 y2 x) = do
  y1e <- enc y1; y2e <- enc y2; xe <- enc x
  let dxy1 = udivSMT xe y1e
      dxy2 = udivSMT xe y2e
  pure [ SMTCommand $ "(assert (=> (and (distinct" `sp` y1e `sp` zero <> ")"
         <> " (bvule" `sp` y1e `sp` y2e <> ")) (bvule" `sp` dxy2 `sp` dxy1 <> ")))" ]

-- mulDiv bound (sound under no-overflow of x*z): if one factor is <= the
-- divisor then dividing the product by it cannot exceed the other factor.
--   y <= z  =>  (x*y)/z <= x       x <= z  =>  (x*y)/z <= y
-- `a` is the original product expr, so the div term matches the prop exactly.
emitLemma enc (MulDivBound a x y z) = do
  ae <- enc a; xe <- enc x; ye <- enc y; ze <- enc z
  let dv = udivSMT ae ze
  pure [ SMTCommand $ "(assert (=> (and (bvule" `sp` ye `sp` ze <> ")" `sp` mulNoOverflow xe ze
           <> ") (bvule" `sp` dv `sp` xe <> ")))"
       , SMTCommand $ "(assert (=> (and (bvule" `sp` xe `sp` ze <> ")" `sp` mulNoOverflow ye ze
           <> ") (bvule" `sp` dv `sp` ye <> ")))" ]

-- Cancelling a nonzero factor is exact when the product cannot overflow.
emitLemma enc (MulDivExact a x y z) = do
  ae <- enc a; xe <- enc x; ye <- enc y; ze <- enc z
  let dv = udivSMT ae ze
      nz = "(distinct" `sp` ze `sp` zero <> ")"
      lemma other = SMTCommand $ "(assert (=> (and" `sp` nz `sp` mulNoOverflow xe ye
                      <> ") (=" `sp` dv `sp` other <> ")))"
  pure $ [ lemma xe | y == z ] <> [ lemma ye | x == z ]

-- b != 0 => (a/b)*b + a%b == a; the quotient product cannot overflow.
emitLemma enc (DivModEuclid a b) = do
  ae <- enc a; be <- enc b
  let q  = udivSMT ae be
      qb = mulSMT (T.Div a b, q) (b, be)
      r  = "(" <> abstFnName IsUMod `sp` ae `sp` be <> ")"
  pure [ SMTCommand $ "(assert (=> (distinct" `sp` be `sp` zero <> ") (= (bvadd"
         `sp` qb `sp` r <> ")" `sp` ae <> ")))" ]

-- Without overflow, MULMOD equals the ordinary product's remainder.
-- For modulus 2^256-1, two 128-bit factors give a product below the modulus.
emitLemma enc (MulModCollapse a b c) = do
  ae <- enc a; be <- enc b; ce <- enc c
  let mm   = mulModSMT ae be ce
      prod = mulSMT (a, ae) (b, be)
      nzc  = "(distinct" `sp` ce `sp` zero <> ")"
      gen  = SMTCommand $ "(assert (=> (and" `sp` nzc `sp` mulNoOverflow ae be
               <> ") (=" `sp` mm `sp` "(" <> abstFnName IsUMod `sp` prod `sp` ce <> ")" <> ")))"
      big  = [ SMTCommand $ "(assert (=>" `sp` mulNoOverflow ae be
                 `sp` "(=" `sp` mm `sp` prod <> ")))"
             | Lit m <- [c], m == maxBound ]
      bnd  = SMTCommand $ "(assert (=>" `sp` nzc `sp` "(bvult" `sp` mm `sp` ce <> ")))"
      zeroMod = SMTCommand $ "(assert (=> (= " <> ce `sp` zero <> ") (= " <> mm `sp` zero <> ")))"
  pure (gen : bnd : zeroMod : big)

-- floor(x*A/B)*B <= x*A, so dividing back by A cannot increase x.
emitLemma enc (RoundTrip outerNum aA x guards) = do
  oe <- enc outerNum; ae <- enc aA; xe <- enc x
  matches <- mapM (\(whole, branch) -> do
    we <- enc whole; be <- enc branch
    pure $ "(=" `sp` we `sp` be <> ")") guards
  let dv = udivSMT oe ae
      nz = "(distinct" `sp` ae `sp` zero <> ")"
  pure [ SMTCommand $ "(assert (=> (and" `sp` nz `sp` mulNoOverflow xe ae
         <> foldMap (" " <>) matches <> ") (bvule" `sp` dv `sp` xe <> ")))" ]

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
      dv   = udivSMT ae c2bv
      bnd  = wordAsBV ((maxBound :: W256) `div` c1)  -- largest x with c1*x < 2^256
  pure [ SMTCommand $ "(assert (=> (bvule" `sp` xe `sp` bnd <> ") (=" `sp` dv `sp` rhs <> ")))" ]

-- nested-division collapse (sound floor identity, no guard needed):
-- (A/c1)/c2 == A/(c1*c2) for literal c1,c2 with c1*c2 < 2^256,
-- e.g. x*rate/1e9/1e18 == x*rate/1e27.
emitLemma enc (NestedDiv innerA c1 c2) = do
  ae <- enc innerA
  let inner     = udivSMT ae (wordAsBV c1)
      outer     = udivSMT inner (wordAsBV c2)
      collapsed = udivSMT ae (wordAsBV (c1 * c2))
  pure [ SMTCommand $ "(assert (=" `sp` outer `sp` collapsed <> "))" ]

-- fraction-reduce (sound, no-overflow guarded): (c1*x)/c2 == x/(c2/c1) when
-- c1 | c2 — the mirror of const-cancel (multiply by small, divide by large,
-- e.g. x*1e6/1e18 == x/1e12). Under the guard c1*x is exact, and
-- floor(c1*x / (c1*k)) = floor(x/k).
emitLemma enc (FracReduce a c1 c2 x) = do
  ae <- enc a; xe <- enc x
  let k    = c2 `div` c1                 -- exact and >= 2, since c1 | c2 and c2 /= c1
      dv   = udivSMT ae (wordAsBV c2)   -- (c1*x)/c2
      rhs  = udivSMT xe (wordAsBV k)    -- x/(c2/c1)
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
      dv   = udivSMT ae (wordAsBV c2)   -- (c1*x - 1)/c2
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
      full    = mulSMT (a, ae) (b, be)
      stepped = mulSMT (a, ae) (T.Sub b (Lit k), "(bvsub" `sp` be `sp` wordAsBV k <> ")")
      dFull   = udivSMT full cbv
      dStep   = udivSMT stepped cbv
      coeff   = if m == 1 then ae else "(bvmul" `sp` wordAsBV m `sp` ae <> ")"
      rhs     = "(bvadd" `sp` dStep `sp` coeff <> ")"
  pure [ SMTCommand $ "(assert (=> (and" `sp` mulNoOverflow ae be
         <> " (bvuge" `sp` be `sp` wordAsBV k <> ")) (=" `sp` dFull `sp` rhs <> ")))" ]

-- | Both operand orders of each product, so monotonicity fires regardless of
-- how the simplifier ordered the operands.
bothOrders :: [(Expr EWord, Expr EWord)] -> [(Expr EWord, Expr EWord)]
bothOrders xs = nubOrd (xs <> [ (b, a) | (a, b) <- xs ])

-- | Both operand orders, including literal factors.
mulPairs :: Expr EWord -> [(Expr EWord, Expr EWord)]
mulPairs (T.Mul u v) = nubOrd [(u, v), (v, u)]
mulPairs _           = []

-- | Candidate branches; callers must guard matches against the original ITE.
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
