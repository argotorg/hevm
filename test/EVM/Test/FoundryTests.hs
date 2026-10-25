{-|
Module      : EVM.Test.FoundryTests
Description : hevm test on the Solidity files in test/contracts

Each case compiles a file with forge and checks whether hevm reports
counterexamples or warnings.
-}
module EVM.Test.FoundryTests (tests) where

import Control.Monad (forM_)
import Control.Monad.Catch (MonadMask)
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT)
import Data.Text (Text, isPrefixOf, unpack)
import Test.Tasty
import Test.Tasty.HUnit

import EVM.ABI (Sig(..))
import EVM.Dapp (TestMethodFilter, TestMethodInfo(..))
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Test.Utils (WithOutput, assertRun, runForgeTest, runForgeTestResults, runForgeTestResultsCustom)
import EVM.Types (regexMatches)

foundryTestConfig :: Config
foundryTestConfig = defaultConfig


test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv (Env foundryTestConfig) b

testAbstractArith :: TestName -> ReaderT Env IO () -> TestTree
testAbstractArith a b =
  testCase a $ runEnv (Env (foundryTestConfig { abstractArith = True })) b

tests :: TestTree
tests = testGroup "Foundry tests"
    [ test "Trivial-Pass" $ do
        let testFile = "test/contracts/pass/trivial.sol"
        executeSingleMethod testFile "prove_true" >>= assertRun "test result" (True, True)
    , test "Foundry" $ do
        -- quick smokecheck to make sure that we can parse ForgeStdLib style build outputs
        -- return is a pair of (No Cex, No Warnings)
        let cases =
              [ ("test/contracts/pass/trivial.sol",       ".*", (True, True))
              , ("test/contracts/pass/dsProvePass.sol",   ".*", (True, True))
              , ("test/contracts/pass/revertEmpty.sol",   ".*", (True, True))
              , ("test/contracts/pass/revertString.sol",  ".*", (True, True))
              , ("test/contracts/pass/requireEmpty.sol",  ".*", (True, True))
              , ("test/contracts/pass/requireString.sol", ".*", (True, True))
              -- overapproximation
              , ("test/contracts/pass/no-overapprox-staticcall.sol", ".*", (True, True))
              , ("test/contracts/pass/no-overapprox-delegatecall.sol", ".*", (True, True))
              -- failure cases
              , ("test/contracts/fail/trivial.sol",       ".*", (False, False))
              , ("test/contracts/fail/dsProveFail.sol",   "prove_add", (False, True))
              , ("test/contracts/fail/dsProveFail.sol",   "prove_multi", (False, True))
              -- all branches revert, which is a warning
              , ("test/contracts/fail/dsProveFail.sol",   "prove_trivial.*", (False, False))
              , ("test/contracts/fail/dsProveFail.sol",   "prove_distributivity", (False, True))
              , ("test/contracts/fail/assertEq.sol",      ".*", (False, True))
              -- bad cheatcode detected, hence the warning
              , ("test/contracts/fail/bad-cheatcode.sol", ".*", (False, False))
              , ("test/contracts/fail/failCall.sol",      ".*", (False, True))
              , ("test/contracts/fail/selectForkMissing.sol", ".*", (False, True))
              -- cheatcodes that cannot handle their symbolic arguments must leave the path partial
              , ("test/contracts/fail/symbolicCheatArgs.sol", ".*", (True, False))
              -- symbolic failures -- either the text or the selector is symbolic
              , ("test/contracts/fail/symbolicFail.sol",      "prove_conc_fail_allrev.*", (False, False))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_conc_fail_somerev.*", (False, True))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_allrev_text.*", (False, False))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_somerev_text.*", (False, True))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_allrev_selector.*", (False, False))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_somerev_selector.*", (False, True))
              -- vm.etch
              , ("test/contracts/pass/etch.sol",          "prove_etch.*", (True, True))
              , ("test/contracts/pass/etch.sol",          "prove_deal.*", (True, True))
              , ("test/contracts/fail/etchFail.sol",      "prove_etch_fail.*", (False, True))
              ]
        forM_ cases $ \(testFile, match, expected) -> do
          assertAllTestMethodsMatching testFile match expected
    , test "Trivial-Fail" $ do
        let testFile = "test/contracts/fail/trivial.sol"
        executeSingleMethod testFile "prove_false" >>= assertRun "test result" (False, False)
    , test "Abstract" $ do
        let testFile = "test/contracts/pass/abstract.sol"
        assertAllMethodsWithPrefix testFile "test" (True, True)
    , test "Constantinople" $ do
        let testFile = "test/contracts/pass/constantinople.sol"
        assertAllMethodsWithPrefix testFile "check_" (True, True)
    , test "Fusaka" $ do
        let testFile = "test/contracts/pass/fusaka.sol"
        assertAllMethodsWithPrefix testFile "check_" (True, True)
    , test "Prove-Tests-Pass" $ do
        let testFile = "test/contracts/pass/dsProvePass.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "prefix-check" $ do
        let testFile = "test/contracts/fail/check-prefix.sol"
        executeSingleMethod testFile "check_trivial" >>= assertRun "test result" (False, False)
    , test "transfer-dapp" $ do
        let testFile = "test/contracts/pass/transfer.sol"
        executeSingleMethod testFile "prove_transfer" >>= assertRun "should prove transfer" (True, True)
    , test "nonce-issues" $ do
        let testFile = "test/contracts/pass/nonce-issues.sol"
        executeSingleMethod testFile "prove_prank_addr_exists" >>= assertRun "should not bail" (True, True)
        executeSingleMethod testFile "prove_nonce_addr_nonexistent" >>= assertRun "should not bail" (True, True)
    , test "Prove-Tests-Fail" $ do
        let testFile = "test/contracts/fail/dsProveFail.sol"
        executeSingleMethod testFile "prove_trivial" >>= assertRun "prove_trivial" (False, False)
        executeSingleMethod testFile "prove_trivial_dstest" >>= assertRun "prove_trivial_dstest" (False, False)
        executeSingleMethod testFile "prove_add" >>= assertRun "prove_add" (False, True)
        runForgeTestResultsCustom testFile (\(TestMethodInfo _ (Sig name _)) -> name == "prove_smtTimeout") (Just 1) Nothing False Fetch.noRpc
          >>= assertRun "prove_smtTimeout" [(True, False)]
        executeSingleMethod testFile "prove_multi" >>= assertRun "prove_multi" (False, True)
        executeSingleMethod testFile "prove_distributivity" >>= assertRun "prove_distributivity" (False, True)
    , test "Loop-Tests" $ do
        let testFile = "test/contracts/pass/loops.sol"
        runForgeTestResultsCustom testFile (\(TestMethodInfo _ (Sig name _)) -> name == "prove_loop") Nothing (Just 10) False Fetch.noRpc
          >>= assertRun "test result" [(True, False)]
        runForgeTestResultsCustom testFile (\(TestMethodInfo _ (Sig name _)) -> name == "prove_loop") Nothing (Just 100) False Fetch.noRpc
          >>= assertRun "test result" [(False, False)]
    , test "Cheat-Codes-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodes.sol"
        executeAllMethodsWithPrefix testFile "prove" >>= assertRun "test result" (True, False)
    , test "Expect-Revert-Pass" $ do
        let testFile = "test/contracts/pass/expectRevert.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "Expect-Revert-Fail" $ do
        let testFile = "test/contracts/fail/expectRevert.sol"
        assertAllMethodsWithPrefix testFile "prove" (False, True)
    , test "Precompile-Cheats-Fail" $ do
        let testFile = "test/contracts/fail/precompileCheats.sol"
        executeSingleMethod testFile "prove_prank_not_kept_past_precompile" >>= assertRun "prank must be used up by the precompile call" (False, False)
        executeSingleMethod testFile "prove_expectRevert_on_succeeding_precompile" >>= assertRun "a succeeding precompile call must fail expectRevert" (False, False)
    -- the replay used to crash and then hang
    , localOption (mkTimeout 120_000_000) $ test "Tx-Context-Cex" $ do
        let testFile = "test/contracts/fail/txContextCex.sol"
        executeSingleMethod testFile "prove_origin" >>= assertRun "origin cex" (False, True)
        executeSingleMethod testFile "prove_coinbase" >>= assertRun "coinbase cex" (False, True)
    , test "Unlinked-Library-Skipped" $ do
        let testFile = "test/contracts/pass/unlinkedLibrary.sol"
        executeSingleMethod testFile "prove_unrelated" >>= assertRun "a non-test contract with unlinked libraries must not stop the tests" (True, True)
    , test "Cheat-Codes-Fork-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodesFork.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "Unwind" $ do
        let testFile = "test/contracts/pass/unwind.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "Keccak" $ do
        let testFile = "test/contracts/pass/keccak.sol"
        executeSingleMethod testFile "prove_access" >>= assertRun "test result" (True, True)
    , test "Symbolic-Key-SLoad" $ do
        -- #1082: without the fix the untouched-mapping read does not complete
        let testFile = "test/contracts/pass/symbolicKeySload.sol"
        executeSingleMethod testFile "prove_symbolic_key_empty_store" >>= assertRun "empty store reads zero" (True, True)
        executeSingleMethod testFile "prove_symbolic_key_untouched_mapping" >>= assertRun "untouched mapping reads zero" (True, True)
    , test "Symbolic-Key-SLoad-Fail" $ do
        -- #1082 soundness: same-mapping entries must be kept, so this falsifies
        let testFile = "test/contracts/fail/symbolicKeySload.sol"
        executeSingleMethod testFile "prove_same_mapping_falsifiable" >>= assertRun "same-mapping read must falsify" (False, True)
    , testAbstractArith "Abstract-Arithmetic-Storage-Reads" $ do
        let testFile = "test/contracts/pass/abstractArithStorage.sol"
        runForgeTestResultsCustom testFile
          (\(TestMethodInfo _ (Sig name _)) -> name == "check_constCancelConcreteKey")
          (Just 10) Nothing False Fetch.noRpc
          >>= assertRun "test result" [(True, True)]
    , test "Mapping-Decomposition" $ do
        let testFile = "test/contracts/pass/mappingDecomposition.sol"
        executeSingleMethod testFile "prove_unwritten" >>= assertRun "unwritten mapping reads zero" (True, True)
    , test "Mapping-Decomposition-Fail" $ do
        let testFile = "test/contracts/fail/mappingDecomposition.sol"
        executeSingleMethod testFile "prove_written_is_zero" >>= assertRun "written mapping read must falsify" (False, True)
    , test "Packed-Storage-Fields" $ do
        let testFile = "test/contracts/pass/packedStorageFields.sol"
        executeSingleMethod testFile "prove_read_back" >>= assertRun "packed fields retain their values" (True, True)
    , test "Array-Mapping-Same-Slot" $ do
        let testFile = "test/contracts/pass/arrayMappingSameSlot.sol"
        executeSingleMethod testFile "prove_array_write_not_read" >>= assertRun "array write is not a mapping write" (True, True)
    , test "Array-Mapping-Same-Slot-Fail" $ do
        let testFile = "test/contracts/fail/arrayMappingSameSlot.sol"
        executeSingleMethod testFile "prove_array_write_read" >>= assertRun "unwritten mapping read must falsify" (False, True)
    , test "Keccak-Literal-Slot" $ do
        let testFile = "test/contracts/pass/keccakLiteralSlot.sol"
        executeSingleMethod testFile "prove_other_mapping" >>= assertRun "folded slot literal must not alias another mapping" (True, True)
    , test "Keccak-Literal-Slot-Fail" $ do
        let testFile = "test/contracts/fail/keccakLiteralSlot.sol"
        executeSingleMethod testFile "prove_same_mapping" >>= assertRun "folded slot literal of the same mapping must falsify" (False, True)
    , test "Recorded-Preimage-Loop" $ do
        let testFile = "test/contracts/pass/recordedPreimageLoop.sol"
        runForgeTestResultsCustom testFile (\(TestMethodInfo _ (Sig name _)) -> name == "prove_loop_bound_from_other_key") Nothing (Just 5) False Fetch.noRpc
          >>= assertRun "the loop must not be entered, so not explored up to the bound" [(True, True)]
    , test "AssertApproxEqAbs-Pass" $ do
        let testFile = "test/contracts/pass/assertApproxEqAbs.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "AssertApproxEqAbs-Fail" $ do
        let testFile = "test/contracts/fail/assertApproxEqAbs.sol"
        let cases =
              -- concrete-only tests: all branches revert, hence (False, False)
              [ ("prove_approx_eq_abs_uint_exceeds_delta", (False, False))
              , ("prove_approx_eq_abs_uint_zero_delta_neq", (False, False))
              , ("prove_approx_eq_abs_int_exceeds_delta", (False, False))
              , ("prove_approx_eq_abs_int_min_zero_tight", (False, False))
              -- symbolic: not all branches revert
              , ("prove_approx_eq_abs_uint_symbolic_fail", (False, True))
              , ("prove_approx_eq_abs_int_symbolic_min_max", (False, False))
              ]
        forM_ cases $ \(method, expected) -> do
          executeSingleMethod testFile method >>= assertRun (unpack method) expected
    , test "AssertApproxEqRel-Pass" $ do
        let testFile = "test/contracts/pass/assertApproxEqRel.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "AssertApproxEqRel-Fail" $ do
        let testFile = "test/contracts/fail/assertApproxEqRel.sol"
        let cases =
              -- concrete-only tests: all branches revert, hence (False, False)
              [ ("prove_approx_eq_rel_uint_exceeds_delta", (False, False))
              , ("prove_approx_eq_rel_uint_b_zero_neq", (False, False))
              , ("prove_approx_eq_rel_uint_overflow_delta", (False, False))
              , ("prove_approx_eq_rel_int_exceeds_delta", (False, False))
              , ("prove_approx_eq_rel_int_b_zero_neq", (False, False))
              -- symbolic: not all branches revert
              , ("prove_approx_eq_rel_uint_symbolic_fail", (False, True))
              ]
        forM_ cases $ \(method, expected) -> do
          executeSingleMethod testFile method >>= assertRun (unpack method) expected
    , test "AssertMsg-Pass" $ do
        let testFile = "test/contracts/pass/assertMsg.sol"
        assertAllMethodsWithPrefix testFile "prove" (True, True)
    , test "AssertMsg-Fail" $ do
        -- every message/bytes overload is violated; all concrete, so all branches
        -- revert -> (False, False)
        let testFile = "test/contracts/fail/assertMsg.sol"
        assertAllMethodsWithPrefix testFile "prove" (False, False)
    , test "Panic-Source-Location" $ do
        -- Regression test for #895: panic in a called contract should not show "<source not found>"
        let testFile = "test/contracts/fail/assertPanic.sol"
        executeSingleMethod testFile "prove_panic" >>= assertRun "prove_panic" (False, False)
    ]

executeSingleMethod :: (App m, MonadMask m) => FilePath -> Text -> m (WithOutput (Bool, Bool))
executeSingleMethod file methodName = do
  (results, out) <- runForgeTestResults file (\(TestMethodInfo _ (Sig name _)) -> name == methodName)
  case results of
    [result] -> pure (result, out)
    _ -> do
      _ <- liftIO $ assertFailure ("expected exactly one method named " <> unpack methodName <> ", got " <> show (length results))
      pure ((True, True), out)

executeAllMethodsWithPrefix :: (App m, MonadMask m) => FilePath -> Text -> m (WithOutput (Bool, Bool))
executeAllMethodsWithPrefix file prefix = runForgeTest file (\(TestMethodInfo _ (Sig name _)) -> prefix `isPrefixOf` name)

assertAllMethodsWithPrefix :: (App m, MonadMask m) => FilePath -> Text -> (Bool, Bool) -> m ()
assertAllMethodsWithPrefix file prefix =
  assertAllMethods file ("prefix: " <> unpack prefix) (\(TestMethodInfo _ (Sig name _)) -> prefix `isPrefixOf` name)

assertAllTestMethodsMatching :: (App m, MonadMask m) => FilePath -> Text -> (Bool, Bool) -> m ()
assertAllTestMethodsMatching file matcher =
  assertAllMethods file ("regex: " <> unpack matcher) (\(TestMethodInfo _ (Sig name _)) -> regexMatches matcher name && "prove" `isPrefixOf` name)

assertAllMethods :: (App m, MonadMask m) => FilePath -> String -> TestMethodFilter -> (Bool, Bool) -> m ()
assertAllMethods file description methodFilter expected = do
  run@(results, _) <- runForgeTestResults file methodFilter
  liftIO $ assertBool ("no methods matching " <> description) (not $ null results)
  assertRun "test results" (replicate (length results) expected) run
