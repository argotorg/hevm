{- |
   Module: EVM.SMT.AbstractBase
   Description: Shared vocabulary for the abstract arithmetic encoding.

   This is the base layer both 'EVM.SMT.AbstractLemmas' (the lemma catalogue) and
   'EVM.SMT.DivModEncoding' (the orchestration + div/mod ground truth) build on. It
   holds, with no dependency on either of them:

   * the SMT-LIB builder primitives ('sp', 'zero', 'mulNoOverflow', 'wordAsBV', …)
     and signed helpers ('smtAbsolute', 'signedFromUnsignedDiv', …);
   * the div/mod operation taxonomy ('DivModKind' and friends);
   * the term collectors ('collectDivMods', 'collectMuls', 'collectConstMuls') and
     shape matchers ('asMul', 'asConstMul');
   * the abstract-term /saturation/ ('saturate'), which closes the set of div/mul
     terms the lemmas range over (synthetic divisions, nested-division collapse,
     div-mul link products) into an 'AbstractCtx'.

   Keeping this separate breaks the import cycle: @DivModEncoding@ imports
   @AbstractLemmas@, so the primitives the lemmas need cannot live in
   @DivModEncoding@.
-}
module EVM.SMT.AbstractBase
  ( -- * Encoder alias
    Enc
    -- * UF declarations
  , divModAbstractDecls
    -- * SMT-LIB builder primitives
  , sp
  , zero
  , one
  , mulNoOverflow
  , wordAsBV
    -- * Div/mod taxonomy
  , DivModKind(..)
  , DivModOp
  , AbstractKey(..)
  , isDiv
  , isSigned
  , abstFnName
  , concFnName
  , abstractKey
    -- * Collectors and shape matchers
  , collectDivMods
  , collectMuls
  , collectConstMuls
  , hasAbstractMul
  , asMul
  , asConstMul
    -- * Signed reconstruction helpers
  , smtZeroGuard
  , smtAbsolute
  , signedFromUnsignedDiv
  , signedFromUnsignedMod
    -- * Abstract-term saturation
  , AbstractCtx(..)
  , saturate
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Text.Lazy.Builder
import qualified Data.Text.Lazy.Builder.Int

import EVM.SMT.Types
import EVM.Traversals
import EVM.Types (Prop(..), EType(EWord), Err, W256, Expr, Expr(Lit))
import EVM.Types qualified as T

-- | The expression-to-SMT encoder threaded through every emitter.
type Enc = Expr EWord -> Err Builder

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

abstractKey :: DivModOp -> AbstractKey
abstractKey (kind, a, b) = AbstractKey a b kind

-- | Collect all div/mod operations from an expression.
collectDivMods :: Expr a -> [DivModOp]
collectDivMods = \case
  T.SDiv a b -> [(IsSDiv, a, b)]
  T.SMod a b -> [(IsSMod, a, b)]
  T.Div  a b -> [(IsUDiv, a, b)]
  T.Mod  a b -> [(IsUMod, a, b)]
  _          -> []

-- | Collect symbolic*symbolic multiplications (neither operand a literal).
collectMuls :: Expr a -> [(Expr EWord, Expr EWord)]
collectMuls = maybe [] pure . asMul

-- | Collect multiplications by a non-trivial literal constant @(c, x)@.
collectConstMuls :: Expr a -> [(W256, Expr EWord)]
collectConstMuls = maybe [] pure . asConstMul

-- | True if any prop contains a symbolic*symbolic multiplication, i.e. the
-- multiplication abstraction is in play. Because abst_evm_bvmul is left
-- uninterpreted (no ground truth), a satisfying model may assign it values
-- inconsistent with real multiplication, so a counterexample cannot be
-- trusted; callers must downgrade SAT results to Unknown to stay SOUND.
hasAbstractMul :: [Prop] -> Bool
hasAbstractMul props = not $ null $ concatMap (foldProp collectMuls []) props

-- | Recognise an abstract symbolic*symbolic product (neither operand a literal).
-- Concrete factors (incl. 0/1/power-of-two) are handled natively by the
-- simplifier, so only genuinely symbolic products are abstracted.
asMul :: Expr a -> Maybe (Expr EWord, Expr EWord)
asMul (T.Mul x y) | notLit x, notLit y = Just (x, y)
asMul _ = Nothing

-- | Recognise multiplication by a non-trivial literal constant: c*x or x*c
-- (excluding 0 and 1). These stay native @bvmul@, but const-mul monotonicity
-- lets the solver order such products without bit-blasting the multiply.
asConstMul :: Expr a -> Maybe (W256, Expr EWord)
asConstMul (T.Mul (Lit c) x) | notLit x, c /= 0, c /= 1 = Just (c, x)
asConstMul (T.Mul x (Lit c)) | notLit x, c /= 0, c /= 1 = Just (c, x)
asConstMul _ = Nothing

notLit :: Expr a -> Bool
notLit (Lit _) = False
notLit _       = True

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

-- | The saturated set of abstract arithmetic terms a property mentions, closed
-- under the synthetic terms the lemmas need to fire. Built once by 'saturate';
-- the lemma catalogue ('EVM.SMT.AbstractLemmas') ranges over these fields.
data AbstractCtx = AbstractCtx
  { acUDivs     :: [(Expr EWord, Expr EWord)]
    -- ^ Unsigned divisions, saturated: the raw @(a,b)@ for @a/b@ found in the
    -- props, plus synthetic divisions and nested-division collapses (see below).
  , acMuls      :: [(Expr EWord, Expr EWord)]
    -- ^ Symbolic*symbolic products, saturated with the div-mul link products
    -- @(a/b)*b@ introduced by the link lemma.
  , acConstMuls :: [(W256, Expr EWord)]
    -- ^ Products @c*x@ by a non-trivial literal constant.
  }

-- | Close the set of div/mul terms the lemmas range over.
--
-- Beyond the raw products and divisions a prop mentions, three synthetic
-- families are added so single-level lemmas can bridge multi-level code (all
-- SOUND — each synthetic term is an exact EVM operation that some lemma below
-- then equates to its closed form):
--
--   * /synthetic divisions/: when an abstract product @a*b@ reuses a factor that
--     is a divisor elsewhere, add @(a*b)/factor@ — lets mulDiv-bound and
--     div-monotonicity bridge cross-divisor round-trips.
--   * /nested-division collapse/: a nested constant division @(A/c1)/c2@ also
--     contributes a single @A/(c1*c2)@, so the single-divide lemmas match code
--     that splits precision across two divides.
--   * /div-mul link products/: every division @a/b@ contributes the product
--     @(a/b)*b@ that the link lemma bounds by @a@.
saturate :: [Prop] -> AbstractCtx
saturate props =
  let udivs = [ (a, b) | (IsUDiv, a, b) <- nubOrd $ concatMap (foldProp collectDivMods []) props ]
      muls  = nubOrd $ concatMap (foldProp collectMuls []) props
      constMuls = nubOrd $ concatMap (foldProp collectConstMuls []) props
      divisors  = nubOrd [ b | (_, b) <- udivs ]
      synthDivs = nubOrd $ [ (T.Mul a b, b) | (a, b) <- muls, b `elem` divisors ]
                        <> [ (T.Mul a b, a) | (a, b) <- muls, a `elem` divisors ]
      collapsedDivs = nubOrd
        [ (innerA, Lit (c1 * c2))
        | (a, b) <- udivs <> synthDivs, Lit c2 <- [b]
        , T.Div innerA (Lit c1) <- [a]
        , c1 /= 0, c2 /= 0, toInteger c1 * toInteger c2 < 2 ^ (256 :: Int) ]
      udivsAll  = nubOrd (udivs <> synthDivs <> collapsedDivs)
      linkMuls  = [ (T.Div a b, b) | (a, b) <- udivsAll ]
      allMuls   = nubOrd (muls <> linkMuls)
  in AbstractCtx { acUDivs = udivsAll, acMuls = allMuls, acConstMuls = constMuls }
