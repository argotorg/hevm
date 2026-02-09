module EVM.SMT.Common where

import Data.Text.Lazy.Builder

-- | Space-separated concatenation of two builders
sp :: Builder -> Builder -> Builder
a `sp` b = a <> " " <> b

-- | Zero constant for 256-bit bitvectors
zero :: Builder
zero = "(_ bv0 256)"

-- | One constant for 256-bit bitvectors
one :: Builder
one = "(_ bv1 256)"

-- | Encode absolute value: |x| = (ite (bvsge x 0) x (- x))
smtAbs :: Builder -> Builder
smtAbs x = "(ite (bvsge" `sp` x `sp` zero <> ")" `sp` x `sp` "(bvsub" `sp` zero `sp` x <> "))"

-- | Encode negation: -x = (bvsub 0 x)
smtNeg :: Builder -> Builder
smtNeg x = "(bvsub" `sp` zero `sp` x <> ")"

-- | Check if two values have the same sign (both negative or both non-negative)
smtSameSign :: Builder -> Builder -> Builder
smtSameSign a b = "(=" `sp` "(bvslt" `sp` a `sp` zero <> ")" `sp` "(bvslt" `sp` b `sp` zero <> "))"

-- | Check if value is non-negative: x >= 0
smtIsNonNeg :: Builder -> Builder
smtIsNonNeg x = "(bvsge" `sp` x `sp` zero <> ")"

-- | Encode SDiv result given the unsigned division of absolute values.
-- SDiv semantics: result sign depends on whether operand signs match.
-- sdiv(a, b) = if b == 0 then 0 else (if sameSign(a,b) then udiv(|a|,|b|) else -udiv(|a|,|b|))
smtSdivResult :: Builder -> Builder -> Builder -> Builder
smtSdivResult aenc benc udivResult =
  "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero `sp`
  "(ite" `sp` smtSameSign aenc benc `sp` udivResult `sp` smtNeg udivResult <> "))"

-- | Encode SMod result given the unsigned remainder of absolute values.
-- SMod semantics: result sign matches the dividend (a).
-- smod(a, b) = if b == 0 then 0 else (if a >= 0 then urem(|a|,|b|) else -urem(|a|,|b|))
smtSmodResult :: Builder -> Builder -> Builder -> Builder
smtSmodResult aenc benc uremResult =
  "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero `sp`
  "(ite" `sp` smtIsNonNeg aenc `sp` uremResult `sp` smtNeg uremResult <> "))"
