{-# LANGUAGE QuasiQuotes #-}

module EVM.SymExec.LoopTests (tests) where

import Control.Monad
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Data.List qualified as List
import Data.Maybe
import Data.String.Here
import Data.Text qualified as T
import Data.Vector qualified as V
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import Witch (into)

import Optics.Core hiding (pre, re, elements)
import Optics.State

import EVM.ABI
import EVM.Expr qualified as Expr
import EVM.Format (hexByteString)
import EVM.Merge qualified as Merge
import EVM.Solidity
import EVM.Solvers
import EVM.SymExec
import EVM.Types hiding (Env)
import EVM.Effects

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testGroup "max-iterations"
    [ test "concrete-loops-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 5; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun()" []
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxConcreteIter = Just 3 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is not partial" $ any isPartial e
    -- concrete loops have their own bound, maxIter is for symbolic ones
    , test "concrete-loops-ignore-max-iterations" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 255; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun()" []
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 3, maxConcreteIter = Just 10000 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is partial" $ not $ any isPartial e
    , test "concrete-loops-not-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 5; i++) count++;
                return count;
              }
            }
            |]

        let sig = Just $ Sig "fun()" []
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxConcreteIter = Just 6 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is partial" $ not $ any isPartial e
    , test "symbolic-loops-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let veriOpts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 5 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] veriOpts
        assertBoolM "The expression MUST be partial" $ any (Expr.containsNode isPartial) e
    , test "jumptable-without-solver" $ do
        -- jumps to table[selector mod 3], read with CODECOPY as Vyper's dispatcher does;
        -- the empty solver answers nothing, so the targets must be found without it
        let c = fromJust $ hexByteString $ "5f3560e01c600260038206600" <> "11b61003301601e395f5156"
              <> "5b60015f5260205ff3" <> "5b60025f5260205ff3" <> "5b60035f5260205ff3" <> "00180021002a"
        (e, _) <- withSolvers EmptySolver 1 Nothing defMemLimit $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any (Expr.containsNode isPartial) e)
        assertEqualM "One path per table entry" 3 (length (filter Expr.isSuccess e))
    , test "inconsistent-paths" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 1000);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- we don't ask the solver about the loop condition until we're
            -- already in an inconsistent path (i == 5, j <= 1000, i < j), so we
            -- will continue looping here until we hit max iterations
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 10, askSmtIters = 5 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression MUST be partial" $ any (Expr.containsNode isPartial) e
    , test "bounded-loop-fully-explored" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 3);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- the loop condition is decided by j's bound, by simplification or by forking on j's 4 values
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 10, askSmtIters = 5 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The bounded loop must not be partial" $ not (any (Expr.containsNode isPartial) e)
        assertEqualM "All feasible iteration counts remain" (map Lit [0..3])
          (List.sort [Expr.readWord (Lit 0) buf | Success _ _ buf _ <- e])
    , test "mem-tuple" $ do
        Just c <- solcRuntime "C"
          [i|
            contract C {
              struct Pair {
                uint x;
                uint y;
              }
              function prove_tuple_pass(Pair memory p) public pure {
                uint256 f = p.x;
                uint256 g = p.y;
                unchecked {
                  p.x+=p.y;
                  assert(p.x == (f + g));
                }
              }
            }
          |]
        let opts = defaultVeriOpts
        let sig = Just $ Sig "prove_tuple_pass((uint256,uint256))" [AbiTupleType (V.fromList [AbiUIntType 256, AbiUIntType 256])]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] opts
        pure ()
    , test "symbolic-loops-not-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 3);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- askSmtIters is low enough here to avoid the inconsistent path
            -- conditions, so we never hit maxIters
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 5, askSmtIters = 1 }}
        (e, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression MUST NOT be partial" $ not (any (Expr.containsNode isPartial) e)
    ]
  , testGroup "state-merging"
    -- Tests for ITE-based state merging during symbolic execution
    -- State merging combines multiple execution paths into a single path with ITE expressions
    [ testCase "merge-skips-folded-keccak-conditions" $ do
        vm <- stToIO $ loadEmptySymVM (RuntimeCode (ConcreteRuntimeCode "")) (Lit 0) (ConcreteBuf "", []) >>= freezeVM
        let bytes = word256Bytes 0x5eed1234
            h = Keccak (ConcreteBuf bytes)
            stack = [Lit 7]
            initial = vm & set (#state % #stack) stack
            step = error "concrete conditions must not trigger speculation"
        forM_ [Lit 0, Lit 1, h, Eq h (Lit (keccak' bytes)), Eq h (Lit (keccak' bytes + 1)), Lit maxBound, WAddr (LitAddr 0), WAddr (LitAddr 1)] $ \cond -> do
          (merged, result) <- stToIO $
            runStateT (Merge.tryMergeForwardJump testEnv.config step 0 2 cond stack) initial
          assertBool "leave concrete branches to the executor" (not merged)
          assertEqual "PC is unchanged" initial.state.pc result.state.pc
          assertEqual "stack is unchanged" stack result.state.stack
    , test "merge-folded-keccak-keeps-concrete-results" $ do
        let input = 0x5eed1234 :: W256
            digest = T.pack $ show (keccak' (word256Bytes input))
        Just c <- solcRuntime "C" [i|
          contract C {
            function f(uint256 x) external pure returns (uint256 result) {
              result = 7;
              if (keccak256(abi.encode(x)) != bytes32(${digest})) result = 42;
            }
          }
        |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        forM_ [(input, 7), (input + 1, 42)] $ \(arg, expected) -> do
          paths <- withDefaultSolver $ \s ->
            getExpr s c sig [show (into arg :: Integer)] defaultVeriOpts
          assertBoolM "execution finishes" (not (any Expr.isPartial paths))
          assertEqualM "the selected branch returns a literal" [Lit expected]
            [Expr.readWord (Lit 0) buf | Success _ _ buf _ <- paths]
    , testCase "merge-preserves-unchanged-stack-slots" $ do
        vm <- stToIO $ loadEmptySymVM (RuntimeCode (ConcreteRuntimeCode "")) (Lit 0) (ConcreteBuf "", []) >>= freezeVM
        let cond = Var "cond"
            untouched = Add (Lit 0) (Var "untouched")
            stack = [Var "value", untouched]
            step = do
              assign (#state % #pc) 2
              assign (#state % #stack) [Mul (Lit 0) (Var "value"), untouched]
        (merged, result) <- stToIO $ runStateT (Merge.tryMergeForwardJump testEnv.config step 0 2 cond stack) vm
        assertBool "symbolic branches still merge" merged
        assertEqual "only changed slots are simplified"
          [ITE cond (Var "value") (Lit 0), untouched] result.state.stack
    , testCase "merge-simple-branches" $ do
        -- Simple branching pattern that should be merged
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              unchecked {
              uint256 result = 1;
              if (x & 0x1 != 0) result = result * 2;
              if (x & 0x2 != 0) result = result * 3;
              assert(result > 0);
              }
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        noMerege <- runEnv testEnv { config = testEnv.config {mergeMaxBudget = 0}} $ do
          e <- withDefaultSolver $ \s -> getExpr s c sig [] defaultVeriOpts
          pure $ length e
        merge <- runEnv testEnv { config = testEnv.config {mergeMaxBudget = 1000}} $ do
          e <- withDefaultSolver $ \s -> getExpr s c sig [] defaultVeriOpts
          pure $ length e
        assertBoolM "Merging should reduce number of paths" (merge < noMerege)
     -- Checked arithmetic reverts in one of the branches, which is not supported by
     -- the current state merging implementation
     , expectFail $ testCase "merge-simple-branches-revert" $ do
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              uint256 result = 1;
              if (x & 0x1 != 0) result = result * 2;
              if (x & 0x2 != 0) result = result * 3;
              assert(result > 0);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        noMerege <- runEnv testEnv { config = testEnv.config {mergeMaxBudget = 0}} $ do
          e <- withDefaultSolver $ \s -> getExpr s c sig [] defaultVeriOpts
          pure $ length e
        merge <- runEnv testEnv { config = testEnv.config {mergeMaxBudget = 1000}} $ do
          e <- withDefaultSolver $ \s -> getExpr s c sig [] defaultVeriOpts
          pure $ length e
        assertBoolM "Merging should reduce number of paths" (merge < noMerege)
    , test "merge-finds-counterexample" $ do
        -- Merged paths should still find counterexamples
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              uint256 result = 1;
              if (x & 0x1 != 0) result = result * 2;
              if (x & 0x2 != 0) result = result * 3;
              // Bug: result == 6 when both bits are set
              assert(result != 6);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "One counterexample should be found even with merging" (exactlyCex 1 ret)
    , test "merge-many-branches-unchecked" $ do
        -- Multiple branches with unchecked arithmetic
        -- 4 branches = 2^4 = 16 paths without merging
        -- With unchecked + merging, should be minimal paths
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              uint256 result = 1;
              unchecked {
                if (x & 0x1 != 0) result = result * 2;
                if (x & 0x2 != 0) result = result * 3;
                if (x & 0x4 != 0) result = result * 5;
                if (x & 0x8 != 0) result = result * 7;
              }
              assert(result > 0);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        paths <- withDefaultSolver $ \s -> getExpr s c sig [] defaultVeriOpts
        let numPaths = length paths
        -- Without merging: 16 paths. With unchecked + merging: should be <= 4
        liftIO $ assertBool ("Expected at most 4 paths with unchecked merging, got " ++ show numPaths) (numPaths <= 4)
    , test "merge-with-unchecked-arithmetic" $ do
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 tick) public pure returns (uint256 ratio) {
              ratio = 0x100000000000000000000000000000000;
              unchecked {
                if (tick & 0x1 != 0) ratio = 0xfffcb933bd6fad37aa2d162d1a594001;
                if (tick & 0x2 != 0) ratio = (ratio * 0xfff97272373d413259a46990580e213a) >> 128;
                if (tick & 0x4 != 0) ratio = (ratio * 0xfff2e50f5f656932ef12357cf3c7fdcc) >> 128;
                if (tick & 0x8 != 0) ratio = (ratio * 0xffe5caca7e10e4e61c3624eaa0941cd0) >> 128;
              }
              assert(ratio > 0);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (paths, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        let numPaths = length paths
        -- Without merging: 16 paths. With unchecked + merging: should be <= 4
        liftIO $ assertBool ("Expected at most 4 paths with unchecked merging, got " ++ show numPaths) (numPaths <= 4)
    , test "merge-counterexample-three-branches" $ do
        -- Find counterexample with 3 merged branches
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              uint256 result = 1;
              if (x & 0x1 != 0) result = result * 100;
              if (x & 0x2 != 0) result = result * 100;
              if (x & 0x4 != 0) result = result * 100;
              // Bug: result = 1000000 when all 3 bits are set
              assert(result < 1000000);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "Expected a counterexample with merged branches" (exactlyCex 1 ret)
    , test "no-false-positive-nested-branches" $ do
        -- Verify that nested branches don't cause false positives
        -- This tests soundness: if both paths of a nested branch don't converge
        -- to the same point, merging should be disabled to avoid invalid states
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x, uint256 y) public pure {
              uint256 result = 1;
              // Nested branches that depend on different inputs
              if (x & 0x1 != 0) {
                if (y & 0x1 != 0) {
                  result = result * 2;
                } else {
                  result = result * 3;
                }
              }
              // result is either 1, 2, or 3
              assert(result == 1 || result == 2 || result == 3);
            }
          }
          |]
        let sig = Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        pure ()
    , test "merge-simplify-zero-mul-in-loop" $ do
        -- Regression test: merging inside a loop where one branch multiplies by zero.
        -- Without simplification of merged ITE expressions, Mul (Lit 0) (ITE ...)
        -- accumulates unsimplified across loop iterations, causing unbounded memory growth.
        -- This is the pattern from ABDKMath64x64.pow(0, x).
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              uint256 base = 0;
              uint256 result = 0x100000000;
              unchecked {
                // Unrolled loop: 8 sequential conditional multiplications by zero.
                // Each creates an ITE where true-branch is Mul(result, 0) and false
                // leaves result unchanged. Without simplifying Mul(Lit 0, ITE(...))
                // to Lit 0 at merge time, the expression tree grows unboundedly.
                if (x & 0x1 != 0) result = result * base;
                base = base * base;
                if (x & 0x2 != 0) result = result * base;
                base = base * base;
                if (x & 0x4 != 0) result = result * base;
                base = base * base;
                if (x & 0x8 != 0) result = result * base;
                base = base * base;
                if (x & 0x10 != 0) result = result * base;
                base = base * base;
                if (x & 0x20 != 0) result = result * base;
                base = base * base;
                if (x & 0x40 != 0) result = result * base;
                base = base * base;
                if (x & 0x80 != 0) result = result * base;
              }
              // If any bit is set, result becomes 0; if x&0xff==0, result stays 0x100000000
              // Either way result <= 0x100000000
              assert(result <= 0x100000000);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertEqualM "Zero-mul loop merging works without expression blowup" [] ret
    , test "no-merge-with-memory-write" $ do
        -- Branches with memory writes should not cause issues
        Just c <- solcRuntime "C"
          [i|
          contract C {
            function f(uint256 x) public pure {
              uint256[] memory arr = new uint256[](2);
              arr[0] = 1;
              if (x & 0x1 != 0) {
                arr[1] = 2;
              }
              assert(arr[0] == 1);
            }
          }
          |]
        let sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertEqualM "Merging should not cause issues with memory writes" [] ret
    ]
  ]

exactlyCex :: Int -> [VerifyResult] -> Bool
exactlyCex n results = let numcex = sum $ map (fromEnum . isCex) results
  in numcex == n && length results == n
