{-|
Module      : EVM.Invariant.InvariantTests
Description : hevm test on invariant_ functions, and halmos' invariant tests

Each case compiles a file in test/contracts/invariant with forge and checks
the results of its invariants.
-}
module EVM.Invariant.InvariantTests (tests) where

import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT)
import Data.Bifunctor (first)
import Data.List (sort)
import Data.Text (Text, isPrefixOf, isInfixOf)
import Data.Text qualified as T
import Test.Tasty
import Test.Tasty.HUnit

import EVM.ABI (Sig(..))
import EVM.Dapp (TestMethodInfo(..))
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Test.Utils (WithOutput, assertRun, runForgeTestResultsWith)
import EVM.UnitTest (UnitTestOptions(..))

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv (Env defaultConfig) b

-- | The results of the matching invariants in a file, up to the given depth
runInvariants :: Int -> FilePath -> (Text -> Bool) -> ReaderT Env IO (WithOutput [((Text, Text), (Bool, Bool))])
runInvariants depth file match =
  runForgeTestResultsWith (\o -> o { invariantDepth = depth }) ("test/contracts/invariant/" <> file)
    (\(TestMethodInfo _ (Sig n _)) -> "invariant_" `isPrefixOf` n && match n) Nothing Nothing False Fetch.noRpc

-- | The result of the one invariant of that name
runInvariant :: Int -> FilePath -> Text -> ReaderT Env IO (WithOutput [(Bool, Bool)])
runInvariant depth file name = first (map snd) <$> runInvariants depth file (== name)

tests :: TestTree
tests = testGroup "invariant"
  [ test "pass" $ do
      (results, out) <- runInvariants 2 "pass.sol" (const True)
      liftIO $ assertBool "some invariants ran" (not (null results))
      assertRun "all pass" (map (const (True, True)) results) (map snd results, out)
  , test "states-seen-before" $ do
      out <- runInvariant 4 "pass.sol" "invariant_bool"
      assertRun "toggle" [(True, True)] out
      liftIO $ assertBool "states seen before are not explored again" ("(2 states, up to 4 calls deep)" `isInfixOf` snd out)
  , test "infeasible-states-dropped" $ do
      out <- runInvariant 2 "pass.sol" "invariant_neither"
      assertRun "unreachable" [(True, True)] out
      liftIO $ assertBool "only the initial state" ("(1 states, up to 2 calls deep)" `isInfixOf` snd out)
  , test "same-states-merged" $ do
      out <- runInvariant 1 "pass.sol" "invariant_any"
      assertRun "holds" [(True, True)] out
      liftIO $ assertBool "both branches give one state" ("(2 states, up to 1 calls deep)" `isInfixOf` snd out)
      runInvariant 1 "fail.sol" "invariant_last_small" >>= assertRun "fails in a merged state" [(False, True)]
  , test "fail" $ do
      runInvariant 1 "fail.sol" "invariant_below_two" >>= assertRun "one call is not enough" [(True, True)]
      out <- runInvariant 2 "fail.sol" "invariant_below_two"
      assertRun "two calls break it" [(False, True)] out
      liftIO $ assertBool "the calls are shown" ("calls:    Counter.incr(0)" `isInfixOf` snd out)
      runInvariant 9 "fail.sol" "invariant_buggy" >>= assertRun "nine calls are not enough" [(True, True)]
      runInvariant 10 "fail.sol" "invariant_buggy" >>= assertRun "ten calls break it" [(False, True)]
      runInvariant 2 "fail.sol" "invariant_not_taken" >>= assertRun "the same caller claims and takes" [(False, True)]
      runInvariant 2 "fail.sol" "invariant_zero" >>= assertRun "an uncallable function is a warning" [(True, False)]
  , test "probes" $ do
      out <- runInvariant 4 "halmos-probes.sol" "invariant_probes_found"
      assertRun "assertion failures in the calls" [(False, True)] out
      liftIO $ assertEqual "all three are found" 3 (length (filter ("Assertion failure in a call" `isInfixOf`) (T.lines (snd out))))
  , test "prank-from-list" $ do
      runInvariant 1 "actors.sol" "invariant_actor_from_list" >>= assertRun "one branch per actor" [(True, True)]
      runInvariant 1 "actors.sol" "invariant_not_third_actor" >>= assertRun "the third actor breaks it" [(False, True)]
  , test "partial-warnings-short" $ do
      out <- runInvariant 1 "actors.sol" "invariant_named"
      assertRun "partially explored" [(True, False)] out
      liftIO $ assertBool "grouped by location" (" -> " `isInfixOf` snd out)
      liftIO $ assertBool "no expressions printed" (not ("ReadWord" `isInfixOf` snd out))
  , testGroup "halmos" [ test file $ do
      (results, out) <- runInvariants depth file (const True)
      let expect = [((c, n), outcome) | (c, cases) <- expected, (n, outcome) <- cases]
      assertRun "results as in halmos" (sort expect) (sort results, out)
    | (file, depth, expected) <- halmosInvariants ]
  ]

-- | halmos' invariant tests, with the results halmos expects (tests/expected/all.json)
halmosInvariants :: [(FilePath, Int, [(Text, [(Text, (Bool, Bool))])])]
halmosInvariants =
  [ ("halmos-basic.sol", 2,
      [ ("InvariantTest", [("invariant_1", pass), ("invariant_2", cex)])
      , ("InvariantProxyTest", [("invariant_proxy_1", pass), ("invariant_proxy_2", cex)])
      , ("TStoreTest", [("invariant_storage", cex), ("invariant_transient_storage", pass)]) ])
  -- halmos only prints the assertion failures in the target functions, hevm fails the test
  , ("halmos-probes.sol", 4, [("InvariantProbesTest", [("invariant_probes_found", cex)])])
  , ("halmos-target.sol", 2,
      [ ("InvariantTargetTest_0", [("invariant_0", cex), ("invariant_1", pass), ("invariant_2", pass), ("invariant_3", pass), ("invariant_4", pass)])
      , ("InvariantTargetTest_0_1_2_3", [("invariant_0", cex), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", cex), ("invariant_4", pass)])
      , ("InvariantTargetTest_1_2", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", pass), ("invariant_4", pass)])
      , ("InvariantTargetTest_3", [("invariant_0", pass), ("invariant_1", pass), ("invariant_2", pass), ("invariant_3", cex), ("invariant_4", pass)])
      , ("InvariantTargetTest_all", [("invariant_0", cex), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", cex), ("invariant_4", cex)])
      , ("InvariantTargetTest_target_contract_this", [("invariant_0", cex), ("invariant_1", pass), ("invariant_2", pass), ("invariant_3", pass), ("invariant_4", pass)])
      , ("InvariantTargetTest_excludeContract_0_0", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", cex), ("invariant_4", cex)])
      , ("InvariantTargetTest_excludeContract_0_1", [(n, noTargets) | n <- ["invariant_0", "invariant_1", "invariant_2", "invariant_3", "invariant_4"]])
      , ("InvariantTargetTest_excludeContract_0_2", [("invariant_0", pass), ("invariant_1", pass), ("invariant_2", pass), ("invariant_3", cex), ("invariant_4", cex)])
      , ("InvariantTargetTest_excludeContract_0_3", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", pass), ("invariant_3", pass), ("invariant_4", pass)])
      , ("InvariantTargetTest_excludeContract_0_4", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", pass), ("invariant_3", cex), ("invariant_4", cex)])
      , ("InvariantTargetTest_excludeContract_1", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", pass), ("invariant_4", pass)])
      , ("InvariantTargetTest_excludeContract_2", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", pass), ("invariant_4", pass)])
      , ("InvariantTargetTest_excludeSelector_1", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", cex), ("invariant_4", cex)])
      , ("InvariantTargetTest_excludeSelector_2", [("invariant_0", pass), ("invariant_1", cex), ("invariant_2", cex), ("invariant_3", cex), ("invariant_4", cex)])
      , ("InvariantTargetTest_excludeSelector_3", [("invariant_0", pass), ("invariant_1", pass), ("invariant_2", cex), ("invariant_3", cex), ("invariant_4", cex)]) ])
  , ("halmos-target-this.sol", 1,
      [ ("InvariantTargetThis",
          [ ("invariant_targets_foo_included", cex), ("invariant_targets_inception_afterInvariant_included", cex)
          , ("invariant_targets_inception_check_included", cex), ("invariant_targets_inception_invariant_included", cex)
          , ("invariant_targets_inception_setUp_included", cex), ("invariant_targets_inception_test_included", cex)
          , ("invariant_targets_special_functions_excluded", pass), ("invariant_this", pass) ]) ])
  , ("halmos-sender.sol", 2,
      [ ("InvariantSenderTest_all", [("invariant_num", cex)])
      , ("InvariantSenderTest_non_owner_1", [("invariant_num", pass)])
      , ("InvariantSenderTest_non_owner_2", [("invariant_num", pass)])
      , ("InvariantSenderTest_owner", [("invariant_num", cex)]) ])
  , ("halmos-sender2.sol", 2,
      [ ("InvariantSenderTest_excludeSender_0", [("invariant_num1", pass), ("invariant_num2", cex), ("invariant_num3", cex)])
      , ("InvariantSenderTest_excludeSender_1", [("invariant_num1", cex), ("invariant_num2", pass), ("invariant_num3", pass)])
      , ("InvariantSenderTest_excludeSender_2", [("invariant_num1", cex), ("invariant_num2", pass), ("invariant_num3", pass)])
      , ("InvariantSenderTest_excludeSender_3", [("invariant_num1", pass), ("invariant_num2", pass), ("invariant_num3", cex)])
      -- halmos finds a cex for num1 too, from user1 = 0x11, which is a precompile:
      -- hevm assumes no symbolic address is one, as no transaction comes from them
      , ("InvariantSenderTest_excludeSender_empty", [("invariant_num1", pass), ("invariant_num2", cex), ("invariant_num3", cex)]) ])
  , ("halmos-timestamp.sol", 2,
      [ ("InvariantTimestampTest",
          [ ("invariant_timestamp_can_change", cex), ("invariant_timestamp_can_only_move_forward", pass)
          , ("invariant_timestamp_does_not_have_to_change", cex), ("invariant_timestamp_is_bounded", pass)
          , ("invariant_timestamp_setup", cex), ("invariant_timestamp_timekeeper", cex) ]) ])
  , ("halmos-examples.sol", 10,
      [ ("MiniVatTest", [("invariant_dai", cex)])
      , ("SimpleStateTest", [("invariant_buggy", cex)]) ])
  ]
  where
    pass = (True, True)
    cex = (False, True)
    noTargets = (True, False)
