module Main where

{-|
Description : Runs hevm against the @grandizzy/symbolic-bug-suite@ project

hevm must find a validated counterexample ([FAIL] + [validated]) for each exploit. The suite is
vendored as a submodule under @forge-symbolic-tests/symbolic-bug-suite@; we compile
it once with @forge build@ and run each function via @hevm test@.
-}

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Runners (NumThreads(..))
import EVM.Types (internalError)

import Control.Monad (void)
import Data.List (isInfixOf)
import Data.Maybe (listToMaybe, fromMaybe)
import System.Directory (getCurrentDirectory, createDirectoryIfMissing, removeDirectoryRecursive)
import System.Environment (getEnv)
import System.FilePath ((</>))
import System.IO.Temp (getCanonicalTemporaryDirectory, createTempDirectory)
import System.Process (readProcess, readProcessWithExitCode)

-- | (label, @check*@ function) for each of the 22 cases.
cases :: [(String, String)]
cases =
  [ ("01 Nomad Bridge zero-root acceptance",    "checkOnlyInstalledRootsAreAccepted")
  , ("03 BeautyChain batchTransfer overflow",   "checkAttackerWithoutBalanceCannotMint")
  , ("04 Euler Finance donation",               "checkDonationDoesNotEnableProfit")
  , ("05 Curve/Vyper reentrancy",               "checkLpCannotWithdrawMoreThanDeposited")
  , ("06 Hundred Finance empty market",         "checkVictimDepositMintsAtLeastOneShare")
  , ("10 Velocore fee underflow",               "checkFeeRebateCannotExceedAmount")
  , ("14 zkLend first-depositor inflation",     "checkRedeemNeverYieldsMoreThanFair")
  , ("15 Abracadabra cauldron liquidation",     "checkLiquidationClearsAtMostRepay")
  , ("17 SushiSwap MISO selector confusion",    "checkCreditNeverExceedsMsgValue")
  , ("18 Akutar refund revert loop",            "checkRefundLoopReachesCompletion")
  , ("19 Sonne Finance empty market",           "checkVictimDepositMintsAtLeastOneShareSonne")
  , ("20 Onyx Protocol empty market",           "checkVictimDepositMintsAtLeastOneShareOnyx")
  , ("21 Polter Finance empty market",          "checkVictimDepositMintsAtLeastOneSharePolter")
  , ("23 MonoX same-token swap",                "checkSwapOutputCannotExceedInputForSelfSwap")
  , ("30 The DAO reentrancy",                   "checkWithdrawCannotBeReentered")
  , ("33 Indexed Finance reweight underflow",   "checkReweightCannotZeroWeight")
  , ("34 DEI/Deus allowance reversal",          "checkBurnFromCannotCreateVictimAllowance")
  , ("35 DFX Finance flash-loan side entrance", "checkFlashLoanCannotMintWithdrawableLiquidity")
  , ("36 Rari/Fuse borrow reentrancy",          "checkBorrowCannotUnlockCollateral")
  , ("37 Uranium Finance invariant typo",       "checkAcceptedSwapCannotViolateIntendedInvariant")
  , ("38 Platypus emergency withdraw",          "checkEmergencyWithdrawCannotLeaveUnbackedDebt")
  , ("39 Cover Protocol stale reward index",    "checkNewStakeCannotClaimOldRewards")
  ]

-- | Build the suite once in a fresh temp project, returning its root directory.
setup :: IO FilePath
setup = do
  forgeStd <- getEnv "HEVM_FORGE_STD_REPO"  -- set by the nix dev shell
  solc <- fromMaybe (internalError "solc not found in PATH") .
    listToMaybe <$> lines <$> readProcess "which" ["solc"] ""
  suite <- (</> "forge-symbolic-tests" </> "symbolic-bug-suite") <$> getCurrentDirectory
  root <- (`createTempDirectory` "symbolic-suite") =<< getCanonicalTemporaryDirectory
  void $ cp (suite </> "src") (root </> "src")
  void $ cp (suite </> "test") (root </> "test")
  writeFile (root </> "foundry.toml") $ unlines
    [ "[profile.default]", "solc = \"" <> solc <> "\"", "evm_version = \"cancun\"", "ast = true" ]
  createDirectoryIfMissing True (root </> "lib" </> "forge-std")
  -- nix-store sources are read-only; --no-preserve=mode keeps the copy removable
  void $ readProcess "cp" ["-r", "--no-preserve=mode", forgeStd </> "src", root </> "lib" </> "forge-std" </> "src"] ""
  void $ readProcess "forge" ["build", "--root", root] ""
  pure root
  where
    cp from to = void $ readProcess "cp" ["-r", from, to] ""

-- | Run hevm on one @check*@ function and assert it found a validated counterexample.
runCase :: IO FilePath -> String -> Assertion
runCase getRoot fn = do
  root <- getRoot
  (_, out, err) <- readProcessWithExitCode "cabal"
    [ "run", "-v0", "exe:hevm", "--", "test", "--root", root
    , "--prefix", "check", "--match", fn, "--solver", "bitwuzla", "--max-iterations", "100" ] ""
  let report = "\n--- stdout ---\n" <> out <> "\n--- stderr ---\n" <> err
  assertBool ("no validated counterexample for " <> fn <> report)
    ("[FAIL]" `isInfixOf` out && "validated" `isInfixOf` out)
  assertBool ("hevm crashed for " <> fn <> report) (not ("CallStack" `isInfixOf` err))

main :: IO ()
main = defaultMain $ localOption (NumThreads 1) $  -- one solver process at a time
  withResource setup removeDirectoryRecursive $ \getRoot ->
    testGroup "symbolic-bug-suite" [ testCase label (runCase getRoot fn) | (label, fn) <- cases ]
