{- |
   Module: EVM.SMT.AbstractBase
   Description: Shared vocabulary for the abstract arithmetic encoding.

   Base layer for 'EVM.SMT.AbstractLemmas' (the lemma catalogue) and
   'EVM.SMT.DivModEncoding' (orchestration + div/mod ground truth): the div/mod
   taxonomy, term collectors/matchers, signed-reconstruction helpers, and the
   term /saturation/ ('saturate') that closes the set of div/mul terms the
   lemmas range over. Lives below both so neither needs to import the other for
   these definitions.
-}
module EVM.SMT.AbstractBase
  ( Enc
  , divModAbstractDecls
  , mulNoOverflow
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

import EVM.SMT.SMTLIB (sp, zero)
import EVM.SMT.Types
import EVM.Traversals
import EVM.Types (Prop(..), EType(EWord), Err, W256, Expr, Expr(Lit), internalError)
import EVM.Types qualified as T

-- | The expression-to-SMT encoder threaded through every emitter.
type Enc = Expr EWord -> Err Builder

-- | Uninterpreted-function declarations standing in for div/mod/mul. The
-- div/mod UFs are refined against the native ops in phase two; abst_evm_bvmul
-- is kept fully uninterpreted (no ground truth), constrained only by the
-- lemmas in "EVM.SMT.AbstractLemmas".
divModAbstractDecls :: [SMTEntry]
divModAbstractDecls =
  [ SMTComment "abstract division/modulo/multiplication (uninterpreted functions; mul has no ground truth)"
  , SMTCommand "(declare-fun abst_evm_bvsdiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvsrem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvudiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvurem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvmul ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

-- | A /sufficient/ condition for x*y not to overflow 256 bits: both operands
-- fit in 128 bits. Deliberately cheaper than the exact predicate
-- @extract 511 256 (bvmul (zext x) (zext y)) = 0@, which forces a 512-bit
-- multiply per lemma instance and times out on large operands. SOUND: when the
-- guard holds there is genuinely no overflow; the cost is completeness for
-- operands above 2^128 (callers bound operands, e.g. @require(x < 2**128)@).
mulNoOverflow :: Builder -> Builder -> Builder
mulNoOverflow x y =
  "(and (bvule " <> x <> " " <> maxU128 <> ") (bvule " <> y <> " " <> maxU128 <> "))"
  where maxU128 = "(_ bv340282366920938463463374607431768211455 256)"

-- | The four EVM division/modulo operations, kept in signed/unsigned groups so
-- the sign-reconstruction machinery is never applied to unsigned operands.
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

collectDivMods :: Expr a -> [DivModOp]
collectDivMods = \case
  T.SDiv a b -> [(IsSDiv, a, b)]
  T.SMod a b -> [(IsSMod, a, b)]
  T.Div  a b -> [(IsUDiv, a, b)]
  T.Mod  a b -> [(IsUMod, a, b)]
  _          -> []

collectMuls :: Expr a -> [(Expr EWord, Expr EWord)]
collectMuls = maybe [] pure . asMul

collectConstMuls :: Expr a -> [(W256, Expr EWord)]
collectConstMuls = maybe [] pure . asConstMul

-- | True if any prop contains a symbolic*symbolic multiplication. Because
-- abst_evm_bvmul has no ground truth, a satisfying model may assign it values
-- inconsistent with real multiplication; callers must downgrade SAT to Unknown
-- to stay sound. (UNSAT — the proof direction — is unaffected.)
hasAbstractMul :: [Prop] -> Bool
hasAbstractMul props = not $ null $ concatMap (foldProp collectMuls []) props

-- | An abstracted symbolic*symbolic product. Products with a concrete factor
-- are handled natively, so only genuinely symbolic products are abstracted.
asMul :: Expr a -> Maybe (Expr EWord, Expr EWord)
asMul (T.Mul x y) | notLit x, notLit y = Just (x, y)
asMul (T.Mul _ (Lit _)) = internalError "non-normalized multiplication: literal must be the first operand"
asMul _ = Nothing

-- | A product by a non-trivial literal constant: c*x (excluding 0, 1).
-- These stay native @bvmul@; the const-mul lemmas range over them.
asConstMul :: Expr a -> Maybe (W256, Expr EWord)
asConstMul (T.Mul (Lit c) x) | notLit x, c /= 0, c /= 1 = Just (c, x)
asConstMul (T.Mul _ (Lit _)) = internalError "non-normalized multiplication: literal must be the first operand"
asConstMul _ = Nothing

notLit :: Expr a -> Bool
notLit (Lit _) = False
notLit _       = True

-- | (ite (= divisor 0) 0 result) — the EVM's x/0 = 0 convention.
smtZeroGuard :: Builder -> Builder -> Builder
smtZeroGuard divisor nonZeroResult =
  "(ite (=" `sp` divisor `sp` zero <> ")" `sp` zero `sp` nonZeroResult <> ")"

smtAbsolute :: Builder -> Builder
smtAbsolute x = "(ite (bvsge" `sp` x `sp` zero <> ")" `sp` x `sp` "(bvsub" `sp` zero `sp` x <> "))"

smtNeg :: Builder -> Builder
smtNeg x = "(bvsub" `sp` zero `sp` x <> ")"

smtSameSign :: Builder -> Builder -> Builder
smtSameSign a b = "(=" `sp` "(bvslt" `sp` a `sp` zero <> ")" `sp` "(bvslt" `sp` b `sp` zero <> "))"

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

-- | The saturated set of abstract arithmetic terms a property mentions, built
-- once by 'saturate'; the lemma catalogue ranges over these fields.
data AbstractCtx = AbstractCtx
  { acUDivs     :: [(Expr EWord, Expr EWord)]
    -- ^ Unsigned divisions, including the synthetic ones added by 'saturate'.
  , acMuls      :: [(Expr EWord, Expr EWord)]
    -- ^ Symbolic*symbolic products, including the div-mul link products.
  , acConstMuls :: [(W256, Expr EWord)]
    -- ^ Products @c*x@ by a non-trivial literal constant.
  }

-- | Close the set of div/mul terms the lemmas range over. Beyond the raw terms
-- a prop mentions, three synthetic families are added so single-level lemmas
-- can bridge multi-level code (SOUND — each synthetic term is an exact EVM
-- operation some lemma then equates to its closed form):
--
--   * /synthetic divisions/: when a product @a*b@ reuses a factor that is a
--     divisor elsewhere, add @(a*b)/factor@ — lets mulDiv-bound and
--     div-monotonicity bridge cross-divisor round-trips.
--   * /nested-division collapse/: @(A/c1)/c2@ also contributes @A/(c1*c2)@, so
--     single-divide lemmas match code that splits precision across two divides.
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
