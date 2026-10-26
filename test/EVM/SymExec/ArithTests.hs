{-# LANGUAGE QuasiQuotes #-}

module EVM.SymExec.ArithTests (tests, arithmeticTests) where

import Control.Monad.State.Strict
import System.Timeout (timeout)
import Control.Monad.Reader (ReaderT)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.String.Here
import Data.Text (Text)
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (ignoreTestBecause)

import EVM.ABI
import EVM.Expr qualified as Expr
import EVM.Solidity
import EVM.Solvers
import EVM.SymExec
import EVM.Types hiding (Env)
import EVM.Effects

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testGroup "Arith" (arithGroups True)
  , testGroup "Abstract-Arith"
    -- Unsigned div/mod exercise the abst_evm_bvudiv / abst_evm_bvurem
    -- uninterpreted functions and the two-phase refinement.
    [ testAbstractArith "udiv-by-one" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_udiv_by_one(uint256 a) external pure {
              uint256 result = a / 1;
              assert(result == a);
            }
          } |]
        (_, res) <- withShortBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "udiv-by-zero" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_udiv_by_zero(uint256 a) external pure {
              // EVM div-by-zero yields 0; Solidity's `/` reverts, so use raw DIV
              uint256 result;
              assembly { result := div(a, 0) }
              assert(result == 0);
            }
          } |]
        (_, res) <- withShortBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "udiv-self" $ do
        -- symbolic divisor: a genuine abst_evm_bvudiv application
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_udiv_self(uint256 a) external pure {
              require(a != 0);
              uint256 result = a / a;
              assert(result == 1);
            }
          } |]
        (_, res) <- withShortBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "umod-by-one" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_umod_by_one(uint256 a) external pure {
              uint256 result = a % 1;
              assert(result == 0);
            }
          } |]
        (_, res) <- withShortBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "umod-range" $ do
        -- a % b < b for b != 0; needs the ground-truth refinement of bvurem
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_umod_range(uint256 a, uint256 b) external pure {
              require(b != 0);
              uint256 result = a % b;
              assert(result < b);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "udiv-le-dividend" $ do
        -- a / b <= a for b != 0; refines bvudiv (symbolic divisor)
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_udiv_le_dividend(uint256 a, uint256 b) external pure {
              require(b != 0);
              uint256 r = a / b;
              assert(r <= a);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "udiv-cex" $ do
        -- false property: div(a,b) can be 0 (e.g. a=0). The abstract path must
        -- still find a real counterexample after refinement.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_udiv_nonzero(uint256 a, uint256 b) external pure {
              require(b != 0);
              uint256 result = a / b;
              assert(result != 0);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected counterexample" (any isCex res)
    , testAbstractArith "vault-preview-shares" $ do
        -- ERC-4626-style share pricing in 64.64 fixed point:
        --   shares = (assets * 2^64) / price
        -- When each share costs at least 1.0 (price >= 2^64), a deposit can
        -- never mint more shares than assets. The power-of-two dividend
        -- (assets << 64) lets the shift-bounds encoding discharge this without
        -- the bvudiv theory; native bvudiv leaves the solver at "unknown".
        Just c <- solcRuntime "C" [i|
          contract C {
            function previewShares(uint256 assets, uint256 price) internal pure returns (uint256 shares) {
              shares = (assets << 64) / price;
            }
            function prove_vault_no_inflation(uint256 assets, uint256 price) external pure {
              require(price >= (1 << 64));   // >= 1.0 per share
              require(assets < (1 << 128));  // assets << 64 stays within 256 bits
              uint256 shares = previewShares(assets, price);
              assert(shares <= assets);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    ]
  -- x == (x * d) / d is encoded with bvumulo instead of the division
  , testGroup "Checked-Mul-Encoding" $ flip concatMap [Bitwuzla, Z3, CVC5] $ \solver ->
    let
      x = Var "x"
      d = Var "d"
      check a b = PEq a (Div (Mul a b) b)
      sat props = runEnv (Env { config = testEnv.config { simp = False } }) $
        withSolvers solver 1 (Just 30) defMemLimit $ \s -> checkSatWithProps s props
      name n = n <> "-" <> show solver
    in
    [ testCase (name "checked-mul-overflow") $ do
        res <- sat [check x d, PGT x (Lit (2^(128 :: Int))), PGT d (Lit (2^(128 :: Int)))]
        assertEqual "the check fails on overflow" Qed res
    , testCase (name "checked-mul-zero-divisor") $ do
        res <- sat [check x d, PEq d (Lit 0), PGT x (Lit 0)]
        assertEqual "(x * 0) / 0 is 0" Qed res
    , testCase (name "checked-mul-no-overflow") $ do
        res <- sat [PNeg (check x d), PLT x (Lit 1000), PLT d (Lit 1000), PGT d (Lit 0)]
        assertEqual "the check holds without overflow" Qed res
    , testCase (name "checked-mul-cex") $ do
        res <- sat [PNeg (check x d), PEq x (Lit (2^(255 :: Int)))]
        assertBool "the check can fail" (isCex res)
    -- literals folded: 100 == (100c * y) / (c * y)
    , testCase (name "checked-mul-folded") $ do
        let y = Var "y"
            c = 8539408935947150350830
            foldedCheck = PEq (Lit 100) (Div (Mul (Lit (100 * c)) y) (Mul (Lit c) y))
        noOverflow <- sat [PNeg foldedCheck, PLT y (Lit 1000), PGT y (Lit 0)]
        assertEqual "the folded check holds without overflow" Qed noOverflow
        -- c * y must not wrap for 100 * (c * y) to overflow
        overflow <- sat [foldedCheck, PGT y (Lit (2^(177 :: Int))), PLT y (Lit (2^(182 :: Int)))]
        assertEqual "the folded check fails on overflow" Qed overflow
    ]
  , testCase "smt-branch-timeout" $ do
      -- factoring a product of two 64-bit primes is far beyond the 1s branch timeout
      let x = Var "x"
          y = Var "y"
          n = 17324573639174612641 * 16789950873655392269
          props = [PEq (Mul x y) (Lit n), PGT x (Lit 1), PGT y (Lit 1), PLT x (Lit (2^(64 :: Int))), PLT y (Lit (2^(64 :: Int)))]
          env = Env { config = testEnv.config { smtBranchTimeout = Just 1 } }
      res <- timeout 60_000_000 $ runEnv env $ withSolvers Bitwuzla 1 (Just 300) defMemLimit $ \s -> checkBranchSat s props
      case res of
        Nothing -> assertFailure "the branch query ignored the branch timeout"
        Just r -> assertBool ("expected unknown, got " <> show r) (isUnknown r)
  , testGroup "Mul-Abstraction"
    -- Symbolic*symbolic multiplication is abstracted as an uninterpreted
    -- function (abst_evm_bvmul) with sound lemmas (commutativity, 0/1
    -- identities, quotient*divisor<=dividend, no-overflow-guarded monotonicity)
    -- during the proof phase. An abstract counterexample is checked again with
    -- exact multiplication before it is returned.
    [ testAbstractArith "mul-monotone" $ do
        -- a1 <= a2 => a1*c <= a2*c, under no-overflow (mul-monotonicity lemma)
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_mul_monotone(uint256 a1, uint256 a2, uint256 k) external pure {
              require(a1 < (1<<128) && a2 < (1<<128) && k < (1<<128));
              require(a1 <= a2);
              uint256 p1; uint256 p2;
              assembly { p1 := mul(a1, k)  p2 := mul(a2, k) }
              assert(p1 <= p2);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    -- the refinement proves the identities too, so only the phase shows the
    -- lemma at work
    , testCase "mul-by-zero" $ do
        res <- abstractPhase [PNeg (PEq (Mul (Var "x") (Var "y")) (Lit 0)), PEq (Var "y") (Lit 0)]
        assertEqual "x*0 == 0 must not need the refinement" (Qed, PhaseAbstract) res
    , testCase "mul-by-one" $ do
        res <- abstractPhase [PNeg (PEq (Mul (Var "x") (Var "y")) (Var "x")), PEq (Var "y") (Lit 1)]
        assertEqual "x*1 == x must not need the refinement" (Qed, PhaseAbstract) res
    , testCase "mul-refinement-rejects-spurious-cex" $ do
        let env = Env { config = testEnv.config { abstractArith = True, simp = False } }
            x = Var "x"
            y = Var "y"
            productIs n = PEq (Mul x y) (Lit n)
            inputs = [PEq x (Lit 2), PEq y (Lit 3)]
        runEnv env $ do
          res <- withShortBitwuzlaSolver $ \s -> checkSatWithProps s (PNeg (productIs 6) : inputs)
          assertEqualM "Must be QED after multiplication refinement" Qed res
    -- storage decomposition rewrites the mapping read in the goal, so ground
    -- truth built from the raw props would not cover the goal's product
    , testCase "mul-refinement-covers-decomposed-storage" $ do
        let env = Env { config = testEnv.config { abstractArith = True } }
            x = Var "x"
            v = SLoad (Expr.MappingSlot (BS.replicate 64 0) (Var "k")) (AbstractStore (SymAddr "c") Nothing)
            -- v, x in [2,3]: not single values, so the simplifier cannot fold the
            -- product into a constant multiplication, and it can never be 5
            inputs = [PGT v (Lit 1), PLT v (Lit 4), PGT x (Lit 1), PLT x (Lit 4)]
        runEnv env $ do
          res <- withShortBitwuzlaSolver $ \s -> checkSatWithProps s (PEq (Mul v x) (Lit 5) : inputs)
          assertEqualM "Must be QED after multiplication refinement" Qed res
    , testCase "mul-refinement-returns-real-cex" $ do
        let env = Env { config = testEnv.config { abstractArith = True, simp = False } }
            x = Var "x"
            y = Var "y"
            productIs n = PEq (Mul x y) (Lit n)
            inputs = [PEq x (Lit 2), PEq y (Lit 3)]
        runEnv env $ do
          res <- withShortBitwuzlaSolver $ \s -> checkSatWithProps s (PNeg (productIs 7) : inputs)
          liftIO $ assertBool "Expected a refined counterexample" (isCex res)
    , testCase "signed-zero-divisor-refinement-preserves-cex" $ do
        let env = Env { config = testEnv.config { abstractArith = True, simp = False } }
            x = Var "x"
            divisor = Var "divisor"
            expression = Add (SDiv x divisor) (SMod x divisor)
            inputs = [PEq x (Lit 0xe392), PEq divisor (Lit 0)]
        runEnv env $ do
          res <- withShortBitwuzlaSolver $ \s ->
            checkSatWithProps s (PNeg (PEq expression (Lit 1)) : inputs)
          liftIO $ assertBool "Expected a signed zero-divisor counterexample" (isCex res)
    , testAbstractArith "div-mul-link" $ do
        -- (x/y)*y <= x for y != 0 (div x mul link lemma; needs commutativity)
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_div_mul_link(uint256 x, uint256 y) external pure {
              require(y != 0);
              uint256 q; uint256 p;
              assembly { q := div(x, y)  p := mul(q, y) }
              assert(p <= x);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "vault-shares-monotonic" $ do
        -- ERC-4626: more assets deposited => at least as many shares. Provable
        -- WITH abstraction, native solving times out (unknown).
        Just c <- solcRuntime "C" [i|
          contract C {
            uint256 public totalAssets;
            uint256 public totalShares;
            function prove_shares_monotonic(uint256 a1, uint256 a2) external view {
              require(totalAssets != 0);
              require(a1 < (1<<128) && a2 < (1<<128) && totalShares < (1<<128));
              require(a1 <= a2);
              uint256 ts = totalShares; uint256 ta = totalAssets;
              uint256 s1; uint256 s2;
              assembly { s1 := div(mul(a1, ts), ta)  s2 := div(mul(a2, ts), ta) }
              assert(s1 <= s2);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED with abstraction" [] res
    , testAbstractArith "mul-overflow-cex" $ do
        -- Unbounded monotonicity is false because raw multiplication wraps.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_mul_monotone_overflow(uint256 a1, uint256 a2, uint256 k) external pure {
              require(a1 <= a2);
              uint256 p1; uint256 p2;
              assembly { p1 := mul(a1, k)  p2 := mul(a2, k) }
              assert(p1 <= p2);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected an overflow counterexample" (any isCex res)
    , testAbstractArith "mul-uint256-monotone-cex" $ do
        -- Same lemma shape as the uint128-bounded proof, but with full-width
        -- uint256 inputs. The 128-bit no-overflow guard must not be assumed from
        -- the type alone; exact refinement exposes the overflow counterexample.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_mul_uint256_monotone(uint256 a1, uint256 a2, uint256 k) external pure {
              require(a1 <= a2);
              uint256 p1; uint256 p2;
              assembly { p1 := mul(a1, k)  p2 := mul(a2, k) }
              assert(p1 <= p2);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected a uint256 overflow counterexample" (any isCex res)
    , testAbstractArith "roundtrip-no-inflation" $ do
        -- The cross-divisor round-trip convertToAssetValue(convertToShares(x)),
        -- i.e. ((x*ts)/ta)*ta/ts <= x, is the stateless core of inflation-attack
        -- safety: converting a value to shares and back never yields more than
        -- you started with. It needs two nested divisions to be related, which
        -- the cancellation synthesis (the synthetic (x*ts)/ts term plus div
        -- monotonicity) discharges. SOUND: shares*ta <= x*ts (div-mul-link), so
        -- floor(shares*ta/ts) <= floor(x*ts/ts) = x.
        Just c <- solcRuntime "C" [i|
          contract C {
            uint256 public totalAssets;
            uint256 public totalShares;
            function prove_roundtrip(uint256 assets) external view {
              require(totalAssets != 0 && totalShares != 0);
              require(assets < (1<<128) && totalShares < (1<<128) && totalAssets < (1<<128));
              uint256 ts = totalShares; uint256 ta = totalAssets;
              uint256 shares; uint256 outv;
              assembly { shares := div(mul(assets, ts), ta)  outv := div(mul(shares, ta), ts) }
              assert(outv <= assets);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "div-cex-preserved" $ do
        -- No symbolic*symbolic mul is present, so no multiplication refinement
        -- is needed to return the real counterexample.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_div_cex(uint256 a, uint256 b) external pure {
              require(b != 0);
              uint256 q; assembly { q := div(a, b) }
              assert(q != 0);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected counterexample" (any isCex res)
    , testAbstractArith "constmul-cex-preserved" $ do
        -- Multiplication by a constant is NOT abstracted, so a real
        -- counterexample is still reported.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_constmul_cex(uint256 x) external pure {
              require(x < (1<<128));
              uint256 p; assembly { p := mul(x, 3) }
              assert(p != 6);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected counterexample" (any isCex res)
    , testAbstractArith "div-divisor-monotone" $ do
        -- a bigger divisor yields a smaller-or-equal quotient (div anti-monotonicity)
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_divisor_monotone(uint256 amt, uint256 p1, uint256 p2) external pure {
              require(p1 != 0 && p2 != 0);
              require(p1 <= p2);
              uint256 q1; uint256 q2;
              assembly { q1 := div(amt, p1)  q2 := div(amt, p2) }
              assert(q2 <= q1);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "muldiv-fee-cap" $ do
        -- a fee of feeBps/10000 never exceeds the principal (mulDiv bound)
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_fee_le(uint256 amount, uint256 feeBps) external pure {
              require(amount < (1<<128) && feeBps <= 10000);
              uint256 fee; assembly { fee := div(mul(amount, feeBps), 10000) }
              assert(fee <= amount);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "muldiv-fee-uncapped-cex" $ do
        -- Without the feeBps <= 100% bound the property is false.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_fee_uncapped(uint256 amount, uint256 feeBps) external pure {
              require(amount < (1<<128));
              uint256 fee; assembly { fee := div(mul(amount, feeBps), 10000) }
              assert(fee <= amount);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected an uncapped fee counterexample" (any isCex res)
    , testAbstractArith "constmul-div-monotone" $ do
        -- (v * 1e27) / rate is monotonic in v. The dividend is a multiplication
        -- by a large literal (1e27), which stays a native bvmul; const-mul
        -- monotonicity lets the solver order the two dividends without
        -- bit-blasting that multiply, which is otherwise the bottleneck.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_constmul_div_monotone(uint256 v1, uint256 v2, uint256 rate) external pure {
              require(rate != 0);
              require(v1 <= v2 && v2 < (1<<80));
              uint256 a1; uint256 a2;
              assembly {
                a1 := div(mul(v1, 1000000000000000000000000000), rate)
                a2 := div(mul(v2, 1000000000000000000000000000), rate)
              }
              assert(a1 <= a2);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "const-cancel" $ do
        -- (x * c) / c == x for a literal c (const-cancellation lemma). The
        -- multiply by c stays a native bvmul but the divide is abstracted
        -- (uninterpreted), so without the lemma this identity is not provable.
        -- This is what discharges precision-scaling wrappers like
        -- `amount * 1e18 / 1e18` that otherwise block round-trip properties.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_const_cancel(uint256 x) external pure {
              require(x < (1<<128));
              uint256 y; assembly { y := div(mul(x, 1000000000000000000), 1000000000000000000) }
              assert(y == x);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "const-cancel-scaled" $ do
        -- generalized const-cancel: (c1*x)/c2 == (c1/c2)*x when c2 | c1.
        -- (x*1e18)/1e6 == x*1e12 — discharges lossless precision scaling between
        -- different decimals (e.g. _getUsdcValue).
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_const_cancel_scaled(uint256 x) external pure {
              require(x < (1<<80));
              uint256 y; uint256 z;
              assembly { y := div(mul(x, 1000000000000000000), 1000000)  z := mul(x, 1000000000000) }
              assert(y == z);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "nested-div-collapse" $ do
        -- (A/c1)/c2 == A/(c1*c2) for literals c1,c2 (floor identity). With A a
        -- symbolic product the divisions are abstracted, so the lemma is what
        -- collapses chained constant divisions like x*rate/1e9/1e18 to x*rate/1e27.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_nested_div_collapse(uint256 a, uint256 b) external pure {
              uint256 lhs; uint256 rhs;
              assembly { let p := mul(a, b)
                lhs := div(div(p, 1000000000), 1000000000000000000)
                rhs := div(p, 1000000000000000000000000000) }
              assert(lhs == rhs);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "fraction-reduce" $ do
        -- fraction-reduce: (c1*x)/c2 == x/(c2/c1) when c1 | c2 (mirror of
        -- const-cancel, which needs c2 | c1). (x*1e6)/1e18 == x/1e12 — discharges
        -- the precision step that scales DOWN to fewer decimals (convert-to-usdc).
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_fraction_reduce(uint256 x) external pure {
              require(x < (1<<128));
              uint256 y; uint256 z;
              assembly { y := div(mul(x, 1000000), 1000000000000000000)  z := div(x, 1000000000000) }
              assert(y == z);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "fraction-reduce-cex" $ do
        -- soundness guard: the fraction-reduce lemma must not over-prove. A wrong
        -- closed form ((x*1e6)/1e18 == x/1e12 + 1) is false for every x, so it
        -- must NOT come back QED (the lemma pins the LHS to x/1e12, exposing the
        -- off-by-one as a real counterexample rather than a spurious proof).
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_fraction_reduce_wrong(uint256 x) external pure {
              require(x < (1<<128));
              uint256 y; uint256 z;
              assembly { y := div(mul(x, 1000000), 1000000000000000000)  z := add(div(x, 1000000000000), 1) }
              assert(y == z);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Wrong closed form must not be QED" (not (null res))
    , testAbstractArith "ceildiv-cancel" $ do
        -- ceilDiv-cancel: Math.ceilDiv(c1*x, c2) == (c1/c2)*x when c2 | c1 (the
        -- product is always divisible, so round-up equals round-down). The divide is
        -- abstracted over the (c1*x - 1) dividend, so the lemma pins it. Discharges
        -- the round-up multiply-up in previewSwapExactOut (e.g. usds->usdc == x*1e12).
        Just c <- solcRuntime "C" [i|
          contract C {
            function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
              return a == 0 ? 0 : (a - 1) / b + 1;
            }
            function prove_ceildiv_cancel(uint256 x) external pure {
              require(x < (1<<128));
              uint256 y = ceilDiv(x * 1000000000000000000, 1000000);
              uint256 z; unchecked { z = x * 1000000000000; }
              assert(y == z);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "ceildiv-cancel-cex" $ do
        -- soundness guard: a wrong closed form (off by one) must NOT be QED.
        Just c <- solcRuntime "C" [i|
          contract C {
            function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
              return a == 0 ? 0 : (a - 1) / b + 1;
            }
            function prove_ceildiv_cancel_wrong(uint256 x) external pure {
              require(x < (1<<128));
              uint256 y = ceilDiv(x * 1000000000000000000, 1000000);
              uint256 z; unchecked { z = x * 1000000000000 + 1; }
              assert(y == z);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Wrong closed form must not be QED" (not (null res))
    , testAbstractArith "ceildiv-symbolic-divisor" $ do
        -- dividend step: ceilDiv(a, r) is a/r or one more, for a symbolic divisor r,
        -- as in previewSwapExactOut's round-up against a round-down expectation
        Just c <- solcRuntime "C" [i|
          contract C {
            function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
              return a == 0 ? 0 : (a - 1) / b + 1;
            }
            function prove_ceildiv_step(uint256 x, uint256 r) external pure {
              require(x < (1<<128) && r != 0);
              uint256 a = x * 1000000000000000000000000000;
              assert(ceilDiv(a, r) - a / r <= 1);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "ceildiv-symbolic-divisor-cex" $ do
        -- soundness guard: rounding up is not always the same as rounding down
        Just c <- solcRuntime "C" [i|
          contract C {
            function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
              return a == 0 ? 0 : (a - 1) / b + 1;
            }
            function prove_ceildiv_step_wrong(uint256 x, uint256 r) external pure {
              require(x < (1<<128) && r != 0);
              uint256 a = x * 1000000000000000000000000000;
              assert(ceilDiv(a, r) == a / r);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected a counterexample" (any isCex res)
    , testAbstractArith "scaled-product-telescope" $ do
        -- scaled-product telescoping: a*b/c - a*(b-k)/c == a*(k/c) when c | k (here
        -- c == k == 1e27, so the coefficient is a). This is the ONLY lemma that
        -- relates two DISTINCT abstract products (a*b and a*(b-1e27), both
        -- symbolic*symbolic), so it discharges value-change accounting identities
        -- like s*rate/1e27 - s == s*(rate-1e27)/1e27 (the third assertion of an
        -- ERC4626 conversionRate test).
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_telescope(uint256 s, uint256 q) external pure {
              require(s <= 1000000000000000000000000000000);   // 1e30
              require(q >= 1000000000000000000000000000);      // 1e27
              require(q <= 1000000000000000000000000000000);   // 1e30
              assert(s * q / 1000000000000000000000000000 - s
                  == s * (q - 1000000000000000000000000000) / 1000000000000000000000000000);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
    , testAbstractArith "scaled-product-telescope-cex" $ do
        -- A wrong difference (+1) is exposed after exact multiplication refinement.
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_telescope_wrong(uint256 s, uint256 q) external pure {
              require(s <= 1000000000000000000000000000000);
              require(q >= 1000000000000000000000000000);
              require(q <= 1000000000000000000000000000000);
              assert(s * q / 1000000000000000000000000000 - s
                  == s * (q - 1000000000000000000000000000) / 1000000000000000000000000000 + 1);
            }
          } |]
        (_, res) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "Expected an off-by-one counterexample" (any isCex res)
    -- natively these all time out
    , provesAbstractly "muldiv-symbolic-denominator-cap" "uint256 a, uint256 n, uint256 d"
        "require(a < (1<<128) && d < (1<<128) && n <= d); uint256 r; assembly { r := div(mul(a, n), d) } assert(r <= a);"
    , provesAbstractly "share-price-falls-as-assets-grow" "uint256 a, uint256 ts, uint256 ta1, uint256 ta2"
        "require(ta1 != 0 && ta1 <= ta2); uint256 s1; uint256 s2; assembly { s1 := div(mul(a, ts), ta1) s2 := div(mul(a, ts), ta2) } assert(s2 <= s1);"
    , provesAbstractly "two-hop-fee-cap" "uint256 a, uint256 f1, uint256 f2, uint256 d"
        "require(a < (1<<128) && d < (1<<128) && f1 <= d && f2 <= d); uint256 x; uint256 y; assembly { x := div(mul(a, f1), d) y := div(mul(x, f2), d) } assert(y <= a);"
    , provesAbstractly "floor-rounding" "uint256 a, uint256 b, uint256 c"
        "uint256 p; uint256 q; uint256 r; assembly { p := mul(a, b) q := div(p, c) r := mul(q, c) } assert(r <= p);"
    , provesAbstractly "roundtrip-virtual-offset" "uint256 a, uint256 ts, uint256 ta"
        "require(a < (1<<127) && ts < (1<<127) && ta < (1<<127)); uint256 s; uint256 o; assembly { s := div(mul(a, add(ts, 1)), add(ta, 1)) o := div(mul(s, add(ta, 1)), add(ts, 1)) } assert(o <= a);"
    -- checked arithmetic: the overflow check is itself a division of the product
    , provesAbstractly "checked-muldiv-cap" "uint256 a, uint256 n, uint256 d"
        "require(a < (1<<128) && d < (1<<128) && n <= d && d != 0); uint256 r = a * n / d; assert(r <= a);"
    , provesAbstractly "checked-mul-div-cancel" "uint256 x, uint256 y"
        "require(y != 0); uint256 r = x * y / y; assert(r == x);"
    , provesAbstractly "muldiv-monotone-literal-divisor" "uint256 a1, uint256 a2, uint256 p"
        "require(a1 <= a2 && a2 < (1<<128) && p < (1<<128)); uint256 r1; uint256 r2; assembly { r1 := div(mul(a1, p), 1000000000000000000) r2 := div(mul(a2, p), 1000000000000000000) } assert(r1 <= r2);"
    -- PSM3's previewSwapExactOut: a ceilDiv by a symbolic rate, scaled up and back, against the round-down
    , provesAbstractly "ceildiv-rate-vs-floor" "uint256 x, uint256 r"
        "require(x <= type(uint128).max && r >= 1e23 && r <= 1e30); uint256 a = x * 1e27; uint256 e = a / r; uint256 u = a == 0 ? 0 : (a - 1) / r + 1; uint256 v = u * 1e18; uint256 w = v == 0 ? 0 : (v - 1) / 1e18 + 1; assert(w - e <= 1);"
    , abstractArithGap "gap-divmod-identity" "uint256 a, uint256 b"
        "require(b != 0); uint256 r; assembly { r := add(mul(div(a, b), b), mod(a, b)) } assert(r == a);"
    -- the lemmas would need the cross term x2*w1, which the query never mentions
    , abstractArithGap "gap-monotone-in-both-factors" "uint256 x1, uint256 x2, uint256 w1, uint256 w2"
        "require(x1 <= x2 && w1 <= w2 && x2 < (1<<100) && w2 < (1<<100)); uint256 r1; uint256 r2; assembly { r1 := div(mul(x1, w1), 1000000000000000000) r2 := div(mul(x2, w2), 1000000000000000000) } assert(r1 <= r2);"
    ]
  ]

testAbstractArith :: TestName -> ReaderT Env IO () -> TestTree
testAbstractArith a b = let testEnvAbstract = Env { config = testEnv.config { abstractArith = True } }
  in testCase a $ runEnv testEnvAbstract b

withShortBitwuzlaSolver :: App m => (SolverGroup -> m a) -> m a
withShortBitwuzlaSolver = withSolvers Bitwuzla 3 (Just 5) defMemLimit

-- | The result for these props under abstract arithmetic, and the phase that gave it.
abstractPhase :: [Prop] -> IO (SMTResult, SolvePhase)
abstractPhase ps = runEnv env $ withShortBitwuzlaSolver $ \s -> checkSatWithPropsPhase s Nothing ps
  where env = Env { config = testEnv.config { abstractArith = True, simp = False } }

abstractArithContract :: Text -> Text -> App m => m (Maybe ByteString)
abstractArithContract params body =
  solcRuntime "C" ("contract C { function prove(" <> params <> ") external pure { " <> body <> " } }")

-- | A function body whose assertions must verify with abstract arithmetic.
provesAbstractly :: TestName -> Text -> Text -> TestTree
provesAbstractly name params body = testAbstractArith name $ do
  Just c <- abstractArithContract params body
  (_, res) <- withShortBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
  assertEqualM "Must be QED" [] res

-- | A true property that neither the lemmas nor the solver decide yet. When
-- one of these starts verifying, move it to 'provesAbstractly'.
abstractArithGap :: TestName -> Text -> Text -> TestTree
abstractArithGap name params body = testAbstractArith name $ do
  Just c <- abstractArithContract params body
  (_, res) <- withSolvers Bitwuzla 1 (Just 1) defMemLimit $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
  assertBoolM "a true property must not be falsified" (not (any isCex res))
  assertBoolM "expected no proof yet" (not (null res))

-- | The cases of the "Arith" group without abstract arithmetic
arithmeticTests :: TestTree
arithmeticTests = testGroup "Arithmetic tests" (arithGroups False)

arithGroups :: Bool -> [TestTree]
arithGroups abstract =
  map (runArithCase abstract) arithCases ++
  [ testGroup "Tests for signed division and modulo" (map (runArithCase abstract) signedDivModCases)
  , testGroup "ABDK math tests" (map (runArithCase abstract) abdkMathCases)
  ]

data ArithCase = ArithCase
  { acName :: TestName
  , acSig :: Maybe Sig
  , acProved :: Bool
  , acTimeout :: Maybe Natural
  , acSlowNatively :: Bool
  , acSrc :: Text
  }

proves, refutes :: TestName -> Text -> ArithCase
proves n = ArithCase n Nothing True (Just 5) False
refutes n = ArithCase n Nothing False (Just 5) False

runArithCase :: Bool -> ArithCase -> TestTree
runArithCase abstract ac = skip $ testCase ac.acName $ runEnv env $ do
  Just c <- solcRuntime "C" ac.acSrc
  (_, res) <- withSolvers Bitwuzla 3 ac.acTimeout defMemLimit $ \s -> checkAssert s defaultPanicCodes c ac.acSig [] defaultVeriOpts
  liftIO $ case (ac.acProved, res) of
    (True, _) -> assertEqual "Must be QED" [] res
    (False, _) | abstract -> assertBool "Expected counterexample" (any isCex res)
    (False, [Cex _]) -> pure ()
    (False, _) -> assertFailure "There should be exactly one cex"
  where
    env = Env { config = testEnv.config { abstractArith = abstract } }
    skip = if ac.acSlowNatively && not abstract then ignoreTestBecause "Currently takes too long" else id

-- Adapted from halmos (tests/regression/test/Arith.t.sol, tests/solver/test/SignedDiv.t.sol, tests/solver/test/Math.t.sol)
arithCases :: [ArithCase]
arithCases =
  [ (proves "math-avg" [i|
      contract C {
        function prove_Avg(uint a, uint b) external pure {
          require(a + b >= a);
          unchecked {
            uint r1 = (a & b) + (a ^ b) / 2;
            uint r2 = (a + b) / 2;
            assert(r1 == r2);
          }
        }
      } |]) { acTimeout = Nothing }
  , proves "unsigned-div-by-zero" [i|
      contract C {
        function prove_unsigned_div_by_zero(uint256 a) external pure {
          uint256 result;
          assembly { result := div(a, 0) }
          assert(result == 0);
        }
      } |]
  , (proves "arith-div-pass" [i|
      contract C {
        function prove_Div_pass(uint x, uint y) external pure {
          require(x > y);
          require(y > 0);
          uint q;
          assembly { q := div(x, y) }
          assert(q != 0);
        }
      } |]) { acTimeout = Nothing }
  , (refutes "arith-div-fail" [i|
      contract C {
        function prove_Div_fail(uint x, uint y) external pure {
          require(x > y);
          uint q;
          assembly { q := div(x, y) }
          assert(q != 0);
        }
      } |]) { acTimeout = Nothing }
  , (refutes "arith-mod-fail" [i|
      contract C {
        function prove_Mod_fail(uint x, uint y) external pure {
          require(x > y);
          uint q;
          assembly { q := mod(x, y) }
          assert(q != 0);
        }
      } |]) { acTimeout = Nothing }
  , (proves "arith-mod" [i|
      contract C {
        function unchecked_smod(int x, int y) internal pure returns (int ret) {
          assembly { ret := smod(x, y) }
        }
        function prove_Mod(int x, int y) external pure {
          unchecked {
            assert(unchecked_smod(x, 0) == 0);
            assert(x % 1 == 0);
            assert(x % 2 < 2 && x % 2 > -2);
            assert(x % 4 < 4 && x % 4 > -4);
            int x_smod_y = unchecked_smod(x, y);
            assert(x_smod_y <= y || y < 0);}
        }
      } |]) { acTimeout = Nothing }
  , (refutes "math-mint-fail" [i|
      contract C {
        function prove_mint(uint s, uint A1, uint S1) external pure {
          uint a = (s * A1) / S1;
          uint A2 = A1 + a;
          uint S2 = S1 + s;
          assert(A1 * S2 <= A2 * S1);
        }
      } |]) { acTimeout = Nothing, acSlowNatively = True }
  ]

signedDivModCases :: [ArithCase]
signedDivModCases =
  [ proves "sdiv-by-one" [i|
      contract C {
        function prove_sdiv_by_one(int256 a) external pure {
          int256 result;
          assembly { result := sdiv(a, 1) }
          assert(result == a);
        }
      } |]
  , proves "sdiv-by-neg-one" [i|
      contract C {
        function prove_sdiv_by_neg_one(int256 a) external pure {
          int256 result;
          assembly { result := sdiv(a, sub(0, 1)) }
          if (a == -170141183460469231731687303715884105728 * 2**128) { // type(int256).min
              assert(result == a);
          } else {
              assert(result == -a);
          }
        }
      } |]
  , proves "sdiv-intmin-by-two" [i|
      contract C {
        function prove_sdiv_intmin_by_two() external pure {
          int256 result;
          assembly {
            let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
            result := sdiv(intmin, 2)
          }
          // -2**254 is 0xc000...0000
          assert(result == -0x4000000000000000000000000000000000000000000000000000000000000000);
        }
      } |]
  , proves "smod-by-zero" [i|
      contract C {
        function prove_smod_by_zero(int256 a) external pure {
          int256 result;
          assembly { result := smod(a, 0) }
          assert(result == 0);
        }
      } |]
  , proves "smod-intmin-by-three" [i|
      contract C {
        function prove_smod_intmin_by_three() external pure {
          int256 result;
          assembly { result := smod(0x8000000000000000000000000000000000000000000000000000000000000000, 3) }
          assert(result == -2);
        }
      } |]
  , proves "sdiv-by-zero" [i|
      contract C {
        function prove_sdiv_by_zero(int256 a) external pure {
          int256 result;
          assembly { result := sdiv(a, 0) }
          assert(result == 0);
        }
      } |]
  , proves "sdiv-zero-dividend" [i|
      contract C {
        function prove_sdiv_zero_dividend(int256 b) external pure {
          int256 result;
          assembly { result := sdiv(0, b) }
          assert(result == 0);
        }
      } |]
  , proves "sdiv-truncation" [i|
      contract C {
        function prove_sdiv_truncation() external pure {
          int256 result;
          assembly { result := sdiv(sub(0, 7), 2) }
          assert(result == -3);
        }
      } |]
  , (proves "sdiv-sign-symmetry" [i|
      contract C {
        function prove_sdiv_sign_symmetry(int256 a, int256 b) external pure {
          if (a == -57896044618658097711785492504343953926634992332820282019728792003956564819968) return;
          if (b == -57896044618658097711785492504343953926634992332820282019728792003956564819968) return;
          if (b == 0) return;
          int256 r1;
          int256 r2;
          assembly {
            r1 := sdiv(a, b)
            r2 := sdiv(sub(0, a), sub(0, b))
          }
          assert(r1 == r2);
        }
      } |]) { acTimeout = Nothing, acSlowNatively = True }
  , (proves "sdiv-sign-antisymmetry" [i|
      contract C {
        function prove_sdiv_sign_antisymmetry(int256 a, int256 b) external pure {
          if (a == -57896044618658097711785492504343953926634992332820282019728792003956564819968) return;
          if (b == 0) return;
          int256 r1;
          int256 r2;
          assembly {
            r1 := sdiv(a, b)
            r2 := sdiv(sub(0, a), b)
          }
          assert(r1 == -r2);
        }
      } |]) { acSlowNatively = True }
  , proves "smod-by-one" [i|
      contract C {
        function prove_smod_by_one(int256 a) external pure {
          int256 r1;
          int256 r2;
          assembly {
            r1 := smod(a, 1)
            r2 := smod(a, sub(0, 1))
          }
          assert(r1 == 0);
          assert(r2 == 0);
        }
      } |]
  , proves "smod-zero-dividend" [i|
      contract C {
        function prove_smod_zero_dividend(int256 b) external pure {
          int256 result;
          assembly { result := smod(0, b) }
          assert(result == 0);
        }
      } |]
  , proves "smod-sign-matches-dividend" [i|
      contract C {
        function prove_smod_sign_matches_dividend(int256 a, int256 b) external pure {
          if (b == 0 || a == 0) return;
          int256 result;
          assembly { result := smod(a, b) }
          if (result != 0) {
            assert((a > 0 && result > 0) || (a < 0 && result < 0));
          }
        }
      } |]
  , proves "smod-intmin" [i|
      contract C {
        function prove_smod_intmin() external pure {
          int256 result;
          assembly { result := smod(0x8000000000000000000000000000000000000000000000000000000000000000, 2) }
          assert(result == 0);
        }
      } |]
  , proves "sdiv-intmin-by-neg-one" [i|
      contract C {
        function prove_sdiv_intmin_by_neg_one() external pure {
          int256 result;
          assembly {
            let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
            result := sdiv(intmin, sub(0, 1))
          }
          // EVM defines sdiv(MIN_INT, -1) = MIN_INT (overflow)
          assert(result == -57896044618658097711785492504343953926634992332820282019728792003956564819968);
        }
      } |]
  , proves "smod-intmin-by-neg-one" [i|
      contract C {
        function prove_smod_intmin_by_neg_one() external pure {
          int256 result;
          assembly {
            let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
            result := smod(intmin, sub(0, 1))
          }
          // smod(MIN_INT, -1) = 0 since MIN_INT is divisible by -1
          assert(result == 0);
        }
      } |]
  , proves "sdiv-intmin-by-intmin" [i|
      contract C {
        function prove_sdiv_intmin_by_intmin() external pure {
          int256 result;
          assembly {
            let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
            result := sdiv(intmin, intmin)
          }
          assert(result == 1);
        }
      } |]
  ]

abdkMathCases :: [ArithCase]
abdkMathCases =
  -- "make verify-hevm T=<function>" in https://github.com/gustavo-grieco/abdk-math-64.64-verification
  [ (proves "prove_div_values-abdk" [i|
      contract C {
          bool public IS_TEST = true;

          int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;
          int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

          // ABDKMath64x64.fromInt(0) == 0
          int128 private constant ZERO_FP = 0;
          // ABDKMath64x64.fromInt(1) == 1 << 64
          int128 private constant ONE_FP = 0x10000000000000000;

          // ABDKMath64x64.div
          function div(int128 x, int128 y) internal pure returns (int128) {
              unchecked {
                  require(y != 0);
                  int256 result = (int256(x) << 64) / y;
                  require(result >= MIN_64x64 && result <= MAX_64x64);
                  return int128(result);
              }
          }

          // ABDKMath64x64.abs
          function abs(int128 x) internal pure returns (int128) {
              unchecked {
                  require(x != MIN_64x64);
                  return x < 0 ? -x : x;
              }
          }

          // Property: |x / y| <= |x| when |y| >= 1, and |x / y| >= |x| when |y| < 1
          function prove_div_values(int128 x, int128 y) public pure {
              require(y != ZERO_FP);

              int128 x_y = abs(div(x, y));

              if (abs(y) >= ONE_FP) {
                  assert(x_y <= abs(x));
              } else {
                  assert(x_y >= abs(x));
              }
          }
      } |]) { acSig = Just $ Sig "prove_div_values(int128,int128)" [AbiIntType 128, AbiIntType 128], acSlowNatively = True }
  , (proves "prove_div_negative_divisor" [i|
      contract C {
          bool public IS_TEST = true;

          int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;
          int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

          // ABDKMath64x64.fromInt(0) == 0
          int128 private constant ZERO_FP = 0;

          // ABDKMath64x64.div
          function div(int128 x, int128 y) internal pure returns (int128) {
              unchecked {
                  require(y != 0);
                  int256 result = (int256(x) << 64) / y;
                  require(result >= MIN_64x64 && result <= MAX_64x64);
                  return int128(result);
              }
          }

          // ABDKMath64x64.neg
          function neg(int128 x) internal pure returns (int128) {
              unchecked {
                  require(x != MIN_64x64);
                  return -x;
              }
          }

          // Property: x / (-y) == -(x / y)
          function prove_div_negative_divisor(int128 x, int128 y) public pure {
              require(y < ZERO_FP);

              int128 x_y = div(x, y);
              int128 x_minus_y = div(x, neg(y));

              assert(x_y == neg(x_minus_y));
          }
      } |]) { acSig = Just $ Sig "prove_div_negative_divisor(int128,int128)" [AbiIntType 128, AbiIntType 128], acSlowNatively = True }
  ]
