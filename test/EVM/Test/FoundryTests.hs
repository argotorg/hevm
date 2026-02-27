module EVM.Test.FoundryTests (tests) where

import Control.Monad (forM_)
import Control.Monad.Catch (MonadMask)
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT)
import Data.Text (Text, isPrefixOf)
import Test.Tasty
import Test.Tasty.HUnit

import EVM.ABI (Sig(..))
import EVM.Dapp (TestMethodInfo(..))
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Test.Utils (runForgeTest, runForgeTestCustom)
import EVM.Types (regexMatches)

foundryTestConfig :: Config
foundryTestConfig = defaultConfig


test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv (Env foundryTestConfig) b

assertEqualM :: (MonadIO m, Eq a, Show a, HasCallStack) => String -> a -> a -> m ()
assertEqualM a b c = liftIO $ assertEqual a b c

tests :: TestTree
tests = testGroup "Foundry tests"
    [ test "Trivial-Pass" $ do
        let testFile = "test/contracts/pass/trivial.sol"
        executeSingleMethod testFile "prove_true" >>= assertEqualM "test result" (True, True)
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
          actual <- executeTestMethodsMatching testFile match
          assertEqualM "Must match" expected actual
    , test "Trivial-Fail" $ do
        let testFile = "test/contracts/fail/trivial.sol"
        executeSingleMethod testFile "prove_false" >>= assertEqualM "test result" (False, False)
    , test "Abstract" $ do
        let testFile = "test/contracts/pass/abstract.sol"
        executeAllMethodsWithPrefix testFile "test" >>= assertEqualM "test result" (True, True)
    , test "Constantinople" $ do
        let testFile = "test/contracts/pass/constantinople.sol"
        executeAllMethodsWithPrefix testFile "check_" >>= assertEqualM "test result" (True, True)
    , test "Fusaka" $ do
        let testFile = "test/contracts/pass/fusaka.sol"
        executeAllMethodsWithPrefix testFile "check_" >>= assertEqualM "test result" (True, True)
    , test "Prove-Tests-Pass" $ do
        let testFile = "test/contracts/pass/dsProvePass.sol"
        executeAllMethodsWithPrefix testFile "prove" >>= assertEqualM "test result" (True, True)
    , test "prefix-check" $ do
        let testFile = "test/contracts/fail/check-prefix.sol"
        executeSingleMethod testFile "check_trivial" >>= assertEqualM "test result" (False, False)
    , test "transfer-dapp" $ do
        let testFile = "test/contracts/pass/transfer.sol"
        executeSingleMethod testFile "prove_transfer" >>= assertEqualM "should prove transfer" (True, True)
    , test "nonce-issues" $ do
        let testFile = "test/contracts/pass/nonce-issues.sol"
        executeSingleMethod testFile "prove_prank_addr_exists" >>= assertEqualM "should not bail" (True, True)
        executeSingleMethod testFile "prove_nonce_addr_nonexistent" >>= assertEqualM "should not bail" (True, True)
    , test "Prove-Tests-Fail" $ do
        let testFile = "test/contracts/fail/dsProveFail.sol"
        executeSingleMethod testFile "prove_trivial" >>= assertEqualM "prove_trivial" (False, False)
        executeSingleMethod testFile "prove_trivial_dstest" >>= assertEqualM "prove_trivial_dstest" (False, False)
        executeSingleMethod testFile "prove_add" >>= assertEqualM "prove_add" (False, True)
        runForgeTestCustom testFile (\(TestMethodInfo _ (Sig name _)) -> regexMatches "prove_smtTimeout" name) (Just 1) Nothing False Fetch.noRpc
          >>= assertEqualM "prove_smtTimeout" (True, False)
        executeSingleMethod testFile "prove_multi" >>= assertEqualM "prove_multi" (False, True)
        executeSingleMethod testFile "prove_distributivity" >>= assertEqualM "prove_distributivity" (False, True)
    , test "Loop-Tests" $ do
        let testFile = "test/contracts/pass/loops.sol"
        runForgeTestCustom testFile (\(TestMethodInfo _ (Sig name _)) -> regexMatches "prove_loop" name) Nothing (Just 10) False Fetch.noRpc  >>= assertEqualM "test result" (True, False)
        runForgeTestCustom testFile (\(TestMethodInfo _ (Sig name _)) -> regexMatches "prove_loop" name) Nothing (Just 100) False Fetch.noRpc >>= assertEqualM "test result" (False, False)
    , test "Cheat-Codes-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodes.sol"
        executeAllMethodsWithPrefix testFile "prove" >>= assertEqualM "test result" (True, False)
    , test "Cheat-Codes-Fork-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodesFork.sol"
        executeAllMethodsWithPrefix testFile "prove" >>= assertEqualM "test result" (True, True)
    , test "Unwind" $ do
        let testFile = "test/contracts/pass/unwind.sol"
        executeAllMethodsWithPrefix testFile "prove" >>= assertEqualM "test result" (True, True)
    , test "Keccak" $ do
        let testFile = "test/contracts/pass/keccak.sol"
        executeSingleMethod testFile "prove_access" >>= assertEqualM "test result" (True, True)
    ]

executeSingleMethod :: (App m, MonadMask m) => FilePath -> Text -> m (Bool, Bool)
executeSingleMethod file methodName = runForgeTest file (\(TestMethodInfo _ (Sig name _)) -> regexMatches methodName name)

executeAllMethodsWithPrefix :: (App m, MonadMask m) => FilePath -> Text -> m (Bool, Bool)
executeAllMethodsWithPrefix file prefix = runForgeTest file (\(TestMethodInfo _ (Sig name _)) -> prefix `isPrefixOf` name)

executeTestMethodsMatching :: (App m, MonadMask m) => FilePath -> Text -> m (Bool, Bool)
executeTestMethodsMatching file matcher = runForgeTest file (\(TestMethodInfo _ (Sig name _)) -> regexMatches matcher name && "prove" `isPrefixOf` name)