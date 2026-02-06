module EVM.Test.BlockchainTests (prepareTests, problematicTests, findIgnoreReason, Case, vmForCase, checkExpectation, allTestCases) where

import EVM (initialContract, makeVm, setEIP4788Storage, setEIP2935Storage)
import EVM.Concrete qualified as EVM
import EVM.Effects
import EVM.Expr (maybeLitAddrSimp)
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.Stepper qualified
import EVM.Transaction
import EVM.Types hiding (Block, Case, Env)
import EVM.UnitTest (writeTrace)

import Optics.Core
import Control.Arrow ((***), (&&&))
import Control.Monad
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Data.Aeson ((.:), (.:?), FromJSON (..))
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as Lazy
import Data.List (isPrefixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.Word (Word64)
import GHC.Generics (Generic)
import System.Environment (getEnv)
import System.FilePath.Find qualified as Find
import System.FilePath.Posix (makeRelative)
import Witch (into, unsafeInto)
import Witherable (Filterable, catMaybes)

import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

data Which = Pre | Post

-- EIP-4895: Withdrawal from beacon chain
data Withdrawal = Withdrawal
  { wAddress :: Addr
  , wAmount  :: W256  -- amount in Gwei
  } deriving (Show, Eq)

data Block = Block
  { coinbase    :: Addr
  , difficulty  :: W256
  , mixHash     :: W256
  , gasLimit    :: Word64
  , baseFee     :: W256
  , number      :: W256
  , timestamp   :: W256
  , txs         :: [Transaction]
  , beaconRoot  :: W256
  , parentHash  :: W256
  , withdrawals :: [Withdrawal]
  } deriving Show

data BlockchainContract = BlockchainContract
  { code    :: ByteStringS
  , nonce   :: W64
  , balance :: W256
  , storage :: Map W256 W256
  } deriving (Eq, Show, Generic)

instance FromJSON BlockchainContract

asBCContract :: Contract -> BlockchainContract
asBCContract c = BlockchainContract code nonce balance storage
  where
    code = case c.code of
      (RuntimeCode (ConcreteRuntimeCode bs)) -> ByteStringS bs
      _ -> internalError "Expected concrete contract"
    nonce = fromJust c.nonce
    balance = forceLit (c.balance)
    storage = fromConcrete c.storage

makeContract :: BlockchainContract -> Contract
makeContract (BlockchainContract (ByteStringS code) nonce balance storage) =
    initialContract (RuntimeCode (ConcreteRuntimeCode code))
      & set #nonce    (Just nonce)
      & set #balance  (Lit balance)
      & set #storage (ConcreteStore storage)
      & set #origStorage (ConcreteStore storage)

type BlockchainContracts = Map Addr BlockchainContract

data Case = Case
  { vmOpts          :: VMOpts Concrete
  , checkContracts  :: BlockchainContracts
  , testExpectation :: BlockchainContracts
  , caseWithdrawals :: [Withdrawal]
  } deriving Show

data BlockchainCase = BlockchainCase
  { blocks  :: [Block]
  , pre     :: BlockchainContracts
  , post    :: BlockchainContracts
  , network :: String
  } deriving Show

prepareTests :: App m => m TestTree
prepareTests = do
  rootDir <- liftIO rootDirectory
  liftIO $ putStrLn $ "Loading and parsing json files from ethereum-tests from " <> show rootDir
  cases <- liftIO allTestCases
  let testCount = sum . fmap Map.size $ cases
  let expectedTestCount = 16989
  when (testCount < expectedTestCount) $ internalError $ "Lower than expected number of tests!\nExpected: " <> (show expectedTestCount) <> "\nGot: " <> (show testCount)
  groups <- forM (Map.toList cases) (\(f, subtests) -> testGroup (makeRelative rootDir f) <$> (process subtests))
  liftIO $ putStrLn "Loaded."
  pure $ testGroup "ethereum-tests" groups
  where
    process :: forall m . App m => (Map String Case) -> m [TestTree]
    process tests = forM (Map.toList tests) runTest

    runTest :: App m => (String, Case) -> m TestTree
    runTest (name, x) = do
      let fetcher q = withSolvers Z3 0 (Just 0) defMemLimit $ \s -> EVM.Fetch.noRpcFetcher s q
      exec <- toIO $ runVMTest fetcher x
      pure $ testCase' name exec
    testCase' :: String -> Assertion -> TestTree
    testCase' name assertion =
      case findIgnoreReason name of
        Just reason -> ignoreTestBecause reason (testCase name assertion)
        Nothing -> testCase name assertion

-- | Find if a test name matches any problematic test prefix
findIgnoreReason :: String -> Maybe String
findIgnoreReason name = lookup True [(prefix `isPrefixOf` name, reason) | (prefix, reason) <- problematicTests]

rootDirectory :: IO FilePath
rootDirectory = getEnv "HEVM_ETHEREUM_TESTS_REPO"
  -- Env var now points directly to the blockchain_tests directory

collectJsonFiles :: FilePath -> IO [FilePath]
collectJsonFiles rootDir = Find.find Find.always (Find.extension Find.==? ".json") rootDir

allTestCases :: IO (Map FilePath (Map String Case))
allTestCases = do
  root <- rootDirectory
  jsons <- collectJsonFiles root
  cases <- forM jsons (\fname -> do
      fContents <- BS.readFile fname
      parsed <- case (parseBCSuite (Lazy.fromStrict fContents)) of
                    Left "No cases to check." -> pure mempty
                    Left err -> do
                      putStrLn $ "Warning: Failed to parse " ++ fname ++ ": " ++ err
                      pure mempty
                    Right allTests -> pure allTests
      pure (fname, parsed)
    )
  pure $ Map.fromList cases

-- | Tests that are known to fail or are too slow to run in CI.
-- Uses prefix matching: any test name starting with a prefix will be ignored.
-- Test names are from the execution-spec-tests fixtures format.
problematicTests :: [(String, String)]
problematicTests =
  [ -- EIP-4844 point evaluation precompile (0x0A) not implemented
    ("tests/cancun/eip4844_blobs/test_point_evaluation_precompile.py::", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/cancun/eip4844_blobs/test_point_evaluation_precompile_gas.py::", "EIP-4844 point evaluation precompile (0x0A) not implemented")
    -- EIP-2537 precompiles
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_g1add.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_g1msm.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_g1mul.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_g2add.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_g2msm.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_g2mul.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_map_fp_to_g1.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_map_fp2_to_g2.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_pairing.py::", "EIP-2537 precompiles not implemented")
  , ("tests/prague/eip2537_bls_12_381_precompiles/test_bls12_variable_length_input_contracts.py::", "EIP-2537 precompiles not implemented")
    -- EIP-7951
  , ("tests/osaka/eip7951_p256verify_precompiles/test_eip_mainnet.py::", "EIP-7951 precompiles not implemented")
  , ("tests/osaka/eip7951_p256verify_precompiles/test_p256verify.py::", "EIP-7951 precompiles not implemented")
    -- Other tests that invoke the 0x0A precompile
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x000000000000000000000000000000000000000a", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stSpecialTest/failed_tx_xcf416c53_ParisFiller.json::", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-11]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-13]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-24]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-28]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-39]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-42]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-53]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-64]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-75]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-86]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-97]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-108]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-119]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-130]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-141]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-152]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-163]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-174]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-185]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-196]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-207]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929OsakaFiller.yml::precompsEIP2929Osaka[fork_Osaka-blockchain_test_from_state_test-yes-218]", "EIP-4844 point evaluation precompile (0x0A) not implemented")
    -- Other precompile tests
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x000000000000000000000000000000000000000b", "0xB precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x000000000000000000000000000000000000000c", "0xC precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x000000000000000000000000000000000000000d", "0xD precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x000000000000000000000000000000000000000e", "0xE precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x000000000000000000000000000000000000000f", "0xF precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x0000000000000000000000000000000000000010", "0x10 precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x0000000000000000000000000000000000000011", "0x11 precompile not implemented")
  , ("tests/frontier/precompiles/test_precompiles.py::test_precompiles[fork_Osaka-address_0x0000000000000000000000000000000000000100", "0x100 precompile not implemented")
  , ("tests/static/state_tests/stPreCompiledContracts/precompsEIP2929CancunFiller.yml::", "TODO")
    -- Other tests (TODO: fix or re-sort them)
  , ("tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds.py::test_modexp_upper_bounds[fork_Osaka-blockchain_test_from_state_test-near_uint64_max_base", "needs EIP-7623 floor gas")
  , ("tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds.py::test_modexp_upper_bounds[fork_Osaka-blockchain_test_from_state_test-zero_exp_mod_exceed", "needs EIP-7623 floor gas")
  , ("tests/osaka/eip7883_modexp_gas_increase/test_modexp_thresholds.py::test_modexp_used_in_transaction_entry_points[fork_Osaka-blockchain_test_from_state_test-extra_gas", "needs EIP-7623 floor gas")
  , ("tests/osaka/eip7883_modexp_gas_increase/test_modexp_thresholds.py::test_modexp_used_in_transaction_entry_points[fork_Osaka-blockchain_test_from_state_test-extra_value", "needs EIP-7623 floor gas")
  , ("tests/osaka/eip7883_modexp_gas_increase/test_modexp_thresholds.py::test_modexp_used_in_transaction_entry_points[fork_Osaka-blockchain_test_from_state_test-insufficient_gas", "needs EIP-7623 floor gas")
  , ("tests/osaka/eip7883_modexp_gas_increase/test_modexp_thresholds.py::test_modexp_used_in_transaction_entry_points[fork_Osaka-blockchain_test_from_state_test-exact_gas", "needs EIP-7623 floor gas")
  , ("tests/frontier/precompiles/test_ripemd.py::", "TODO")
  , ("tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_limit.py::", "TODO")
  , ("tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes.py::", "TODO")
  , ("tests/prague/eip6110_deposits/test_deposits.py::", "TODO")
  , ("tests/prague/eip7002_el_triggerable_withdrawals/test_modified_withdrawal_contract.py::", "TODO")
  , ("tests/prague/eip7251_consolidations/test_modified_consolidation_contract.py::", "TODO")
  , ("tests/prague/eip7623_increase_calldata_cost/test_execution_gas.py::", "TODO")
  , ("tests/prague/eip7623_increase_calldata_cost/test_refunds.py::", "TODO")
  , ("tests/prague/eip7685_general_purpose_el_requests/test_multi_type_requests.py::", "TODO")
  , ("tests/prague/eip7702_set_code_tx/test_calls.py::", "TODO")
  , ("tests/prague/eip7702_set_code_tx/test_gas.py::", "TODO")
  , ("tests/prague/eip7702_set_code_tx/test_set_code_txs_2.py::", "TODO")
  , ("tests/shanghai/eip3860_initcode/test_initcode.py::", "TODO")
  , ("tests/shanghai/eip3860_initcode/test_with_eof.py::", "TODO")
  , ("tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_memory_expansion_costFiller.yml::", "TODO")
  , ("tests/static/state_tests/stCreate2/create2collisionSelfdestructed2Filler.json::", "TODO")
  , ("tests/static/state_tests/stCreate2/create2collisionSelfdestructedFiller.json::", "TODO")
  , ("tests/static/state_tests/stCreate2/create2collisionSelfdestructedRevertFiller.json::", "TODO")
  , ("tests/static/state_tests/stEIP150singleCodeGasPrices/gasCostExpFiller.yml::", "TODO")
  , ("tests/static/state_tests/stEIP150singleCodeGasPrices/gasCostMemoryFiller.yml::", "TODO")
  , ("tests/static/state_tests/stEIP150singleCodeGasPrices/gasCostMemSegFiller.yml::", "TODO")
  , ("tests/static/state_tests/stEIP2930/transactionCostsFiller.yml::", "TODO")
  , ("tests/static/state_tests/stMemoryTest/memReturnFiller.json::", "TODO")
  , ("tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALLwithData_ToEmpty_ParisFiller.json::", "TODO")
  , ("tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALLwithData_ToNonNonZeroBalanceFiller.json::", "TODO")
  , ("tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALLwithData_ToOneStorageKey_ParisFiller.json::", "TODO")
  , ("tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALLwithDataFiller.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest0Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest126Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest144Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest157Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest172Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest176Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest190Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest197Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest209Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest230Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest251Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest252Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest25Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest271Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest275Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest288Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest300Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest312Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest321Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest323Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest345Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest350Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest45Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest57Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest5Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest72Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest78Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom/randomStatetest82Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest396Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest404Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest414Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest420Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest428Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest444Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest478Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest509Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest531Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest543Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest558Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest567Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest572Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest609Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest624Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest644Filler.json::", "TODO")
  , ("tests/static/state_tests/stRandom2/randomStatetest645Filler.json::", "TODO")
  , ("tests/static/state_tests/stRevertTest/PythonRevertTestTue201814-1430Filler.json::", "TODO")
  , ("tests/static/state_tests/stStackTests/stackOverflowM1PUSHFiller.json::", "TODO")
  , ("tests/static/state_tests/stTransactionTest/HighGasLimitFiller.json::", "TODO")
  , ("tests/static/state_tests/stTransactionTest/TransactionDataCosts652Filler.json::", "TODO")
  , ("tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALLwithData_ToEmpty_ParisFiller.json::", "TODO")
  , ("tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALLwithData_ToNonZeroBalanceFiller.json::", "TODO")
  , ("tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALLwithData_ToOneStorageKey_ParisFiller.json::", "TODO")
  , ("tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALLwithDataFiller.json::", "TODO")
  ]


runVMTest :: App m => EVM.Fetch.Fetcher Concrete m -> Case -> m ()
runVMTest fetcher x = do
  -- traceVsGeth fname name x
  vm0 <- liftIO $ vmForCase x
  result <- EVM.Stepper.interpret fetcher vm0 EVM.Stepper.runFully
  writeTrace result
  -- Apply EIP-4895 withdrawals after transaction execution
  let resultWithWithdrawals = applyWithdrawals x.caseWithdrawals result
  let maybeReason = checkExpectation x resultWithWithdrawals
  liftIO $ forM_ maybeReason (liftIO >=> assertFailure)

-- | Apply EIP-4895 withdrawals to VM state
-- Withdrawals credit balance to addresses (amount is in Gwei, multiply by 10^9 for Wei)
applyWithdrawals :: [Withdrawal] -> VM Concrete -> VM Concrete
applyWithdrawals ws vm = foldl applyWithdrawal vm ws
  where
    applyWithdrawal :: VM Concrete -> Withdrawal -> VM Concrete
    applyWithdrawal vm' (Withdrawal addr amount) =
      let weiAmount = Lit (amount * 1000000000)  -- Gwei to Wei
          addrExpr = LitAddr addr
          contracts' = Map.alter (creditBalance weiAmount) addrExpr vm'.env.contracts
      in vm' { env = vm'.env { contracts = contracts' } }

    creditBalance :: Expr EWord -> Maybe Contract -> Maybe Contract
    creditBalance weiAmount Nothing =
      -- Create new account with just the withdrawal balance
      Just $ (EVM.initialContract (RuntimeCode (ConcreteRuntimeCode "")))
        { balance = weiAmount }
    creditBalance (Lit weiAmount) (Just c) =
      -- Add to existing balance
      Just $ c { balance = Lit (forceLit c.balance + weiAmount) }
    creditBalance _ (Just c) = Just c  -- shouldn't happen in concrete execution

checkExpectation :: Case -> VM Concrete -> Maybe (IO String)
checkExpectation x vm = let (okState, okBal, okNonce, okStor, okCode) = checkExpectedContracts vm x.testExpectation in
  if okState then Nothing else Just $ checkStateFail x (okBal, okNonce, okStor, okCode)
  where
    checkExpectedContracts :: VM Concrete -> BlockchainContracts -> (Bool, Bool, Bool, Bool, Bool)
    checkExpectedContracts vm' expected =
      let cs = fmap (asBCContract . clearZeroStorage) $ forceConcreteAddrs vm'.env.contracts
      in ( (expected ~= cs)
        , (clearBalance <$> expected) ~= (clearBalance <$> cs)
        , (clearNonce   <$> expected) ~= (clearNonce   <$> cs)
        , (clearStorage <$> expected) ~= (clearStorage <$> cs)
        , (clearCode    <$> expected) ~= (clearCode    <$> cs)
        )

    -- quotient account state by nullness
    (~=) :: BlockchainContracts -> BlockchainContracts -> Bool
    (~=) cs1 cs2 =
        let nullAccount = asBCContract $ EVM.initialContract (RuntimeCode (ConcreteRuntimeCode ""))
            padNewAccounts cs ks = Map.union cs $ Map.fromList [(k, nullAccount) | k <- ks]
            padded_cs1 = padNewAccounts cs1 (Map.keys cs2)
            padded_cs2 = padNewAccounts cs2 (Map.keys cs1)
        in and $ zipWith (==) (Map.elems padded_cs1) (Map.elems padded_cs2)
    
    checkStateFail :: Case -> (Bool, Bool, Bool, Bool) -> IO String
    checkStateFail x' (okBal, okNonce, okData, okCode) = do
      let
        printContracts :: BlockchainContracts -> IO ()
        printContracts cs = putStrLn $ Map.foldrWithKey (\k c acc ->
          acc ++ "-->" <> show k ++ " : "
                      ++ (show c.nonce) ++ " "
                      ++ (show c.balance) ++ " "
                      ++ (show c.storage)
            ++ "\n") "" cs

        reason = map fst (filter (not . snd)
            [ ("bad-state",       okBal   || okNonce || okData  || okCode)
            , ("bad-balance", not okBal   || okNonce || okData  || okCode)
            , ("bad-nonce",   not okNonce || okBal   || okData  || okCode)
            , ("bad-storage", not okData  || okBal   || okNonce || okCode)
            , ("bad-code",    not okCode  || okBal   || okNonce || okData)
            ])
        check = x'.checkContracts
        expected = x'.testExpectation
        actual = fmap (asBCContract . clearZeroStorage) $ forceConcreteAddrs vm.env.contracts

      putStrLn $ "-> Failing because of: " <> (unwords reason)
      putStrLn "-> Pre balance/state: "
      printContracts check
      putStrLn "-> Expected balance/state: "
      printContracts expected
      putStrLn "-> Actual balance/state: "
      printContracts actual
      pure (unwords reason)


splitEithers :: (Filterable f) => f (Either a b) -> (f a, f b)
splitEithers =
  (catMaybes *** catMaybes)
  . (fmap fst &&& fmap snd)
  . (fmap (preview _Left &&& preview _Right))

fromConcrete :: Expr Storage -> Map W256 W256
fromConcrete (ConcreteStore s) = s
fromConcrete s = internalError $ "unexpected abstract store: " <> show s

clearZeroStorage :: Contract -> Contract
clearZeroStorage c = case c.storage of
  ConcreteStore m -> let store = Map.filter (/= 0) m
                     in set #storage (ConcreteStore store) c
  _ -> internalError "Internal Error: unexpected abstract store"

clearStorage :: BlockchainContract -> BlockchainContract
clearStorage c = c { storage = mempty}

clearBalance :: BlockchainContract -> BlockchainContract
clearBalance c = c {balance = 0}

clearNonce :: BlockchainContract -> BlockchainContract
clearNonce c = c {nonce = 0}

clearCode :: BlockchainContract -> BlockchainContract
clearCode c = c {code = (ByteStringS "")}

instance FromJSON BlockchainCase where
  parseJSON (JSON.Object v) = BlockchainCase
    <$> v .: "blocks"
    <*> parseContracts Pre v
    <*> parseContracts Post v
    <*> v .: "network"
  parseJSON invalid =
    JSON.typeMismatch "GeneralState test case" invalid

instance FromJSON Withdrawal where
  parseJSON (JSON.Object v) = do
    addr   <- addrField v "address"
    amount <- wordField v "amount"
    pure $ Withdrawal addr amount
  parseJSON invalid =
    JSON.typeMismatch "Withdrawal" invalid

instance FromJSON Block where
  parseJSON (JSON.Object v) = do
    v'         <- v .: "blockHeader"
    txs        <- v .: "transactions"
    coinbase   <- addrField v' "coinbase"
    difficulty <- wordField v' "difficulty"
    gasLimit   <- word64Field v' "gasLimit"
    number     <- wordField v' "number"
    baseFee    <- fmap read <$> v' .:? "baseFeePerGas"
    timestamp  <- wordField v' "timestamp"
    mixHash    <- wordField v' "mixHash"
    beaconRoot <- fmap read <$> v' .:? "parentBeaconBlockRoot"
    parentHash <- wordField v' "parentHash"
    ws         <- v .:? "withdrawals"
    pure $ Block { coinbase, difficulty, mixHash, gasLimit
                 , baseFee = fromMaybe 0 baseFee, number, timestamp
                 , txs, beaconRoot = fromMaybe 0 beaconRoot
                 , parentHash, withdrawals = fromMaybe [] ws
                 }
  parseJSON invalid =
    JSON.typeMismatch "Block" invalid

parseContracts :: Which -> JSON.Object -> JSON.Parser (BlockchainContracts)
parseContracts w v = v .: which >>= parseJSON
  where which = case w of
          Pre  -> "pre"
          Post -> "postState"

parseBCSuite :: Lazy.ByteString -> Either String (Map String Case)
parseBCSuite x = case (JSON.eitherDecode' x) :: Either String (Map String BlockchainCase) of
  Left e        -> Left e
  Right bcCases -> let allCases = fromBlockchainCase <$> bcCases
                       keepError (Left e) = errorFatal e
                       keepError _        = True
                       filteredCases = Map.filter keepError allCases
                       (erroredCases, parsedCases) = splitEithers filteredCases
    in if Map.size erroredCases > 0
       then Left ("errored case: " ++ (show erroredCases))
       else if Map.size parsedCases == 0
            then Left "No cases to check."
            else Right parsedCases


data BlockchainError
  = TooManyBlocks
  | TooManyTxs
  | NoTxs
  | SignatureUnverified
  | InvalidTx
  | OldNetwork
  | FailedCreate
  | UnsupportedTxType
  deriving Show

errorFatal :: BlockchainError -> Bool
errorFatal FailedCreate = True
errorFatal SignatureUnverified = True
errorFatal InvalidTx = True
errorFatal _ = False

fromBlockchainCase :: BlockchainCase -> Either BlockchainError Case
fromBlockchainCase (BlockchainCase blocks preState postState network) =
  case (blocks, network) of
    ([block], "Osaka") -> case block.txs of
      [tx] | tx.txtype == EIP4844Transaction || tx.txtype == EIP7702Transaction -> Left UnsupportedTxType -- TODO EIP4844 / EIP7702
      [tx] -> fromBlockchainCase' block tx preState postState
      []        -> Left NoTxs
      _         -> Left TooManyTxs
    ([_], _) -> Left OldNetwork
    (_, _)   -> Left TooManyBlocks

maxCodeSize :: W256
maxCodeSize = 24576

fromBlockchainCase' :: Block -> Transaction
                       -> BlockchainContracts -> BlockchainContracts
                       -> Either BlockchainError Case
fromBlockchainCase' block tx preState postState =
  let isCreate = isNothing tx.toAddr in
  case (sender tx, checkTx tx block preState) of
    (Nothing, _) -> Left SignatureUnverified
    (_, Nothing) -> Left (if isCreate then FailedCreate else InvalidTx)
    (Just origin, Just checkState) -> Right $ Case
      (VMOpts
       { contract       = EVM.initialContract theCode
       , otherContracts = []
       , calldata       = (cd, [])
       , value          = Lit tx.value
       , address        = toAddr
       , caller         = LitAddr origin
       , baseState      = EmptyBase
       , origin         = LitAddr origin
       , gas            = tx.gasLimit - txGasCost feeSchedule tx
       , baseFee        = block.baseFee
       , priorityFee    = priorityFee tx block.baseFee
       , gaslimit       = tx.gasLimit
       , number         = Lit block.number
       , timestamp      = Lit block.timestamp
       , coinbase       = LitAddr block.coinbase
       , prevRandao     = block.mixHash
       , maxCodeSize    = maxCodeSize
       , blockGaslimit  = block.gasLimit
       , gasprice       = effectiveGasPrice
       , schedule       = feeSchedule
       , chainId        = 1
       , create         = isCreate
       , txAccessList   = Map.mapKeys LitAddr (txAccessMap tx)
       , allowFFI       = False
       , freshAddresses = 0
       , beaconRoot     = block.beaconRoot
       , parentHash     = block.parentHash
       })
      checkState
      postState
      block.withdrawals
        where
          toAddr = maybe (EVM.createAddress origin (fromJust senderNonce)) LitAddr (tx.toAddr)
          senderNonce = (.nonce) <$> Map.lookup origin preState
          toCode = Map.lookup toAddr (Map.mapKeys LitAddr preState)
          theCode = if isCreate
                    then InitCode tx.txdata mempty
                    else RuntimeCode . ConcreteRuntimeCode $ case toCode of
                      Nothing ->  ""
                      Just (BlockchainContract (ByteStringS bs) _ _ _) -> bs
          effectiveGasPrice = effectiveprice tx block.baseFee
          cd = if isCreate
               then mempty
               else ConcreteBuf tx.txdata

effectiveprice :: Transaction -> W256 -> W256
effectiveprice tx baseFee = priorityFee tx baseFee + baseFee

priorityFee :: Transaction -> W256 -> W256
priorityFee tx baseFee = let
    (txPrioMax, txMaxFee) = case tx.txtype of
               EIP1559Transaction ->
                 let maxPrio = fromJust tx.maxPriorityFeeGas
                     maxFee = fromJust tx.maxFeePerGas
                 in (maxPrio, maxFee)
               _ ->
                 let gasPrice = fromJust tx.gasPrice
                 in (gasPrice, gasPrice)
  in min txPrioMax (txMaxFee - baseFee)

maxBaseFee :: Transaction -> W256
maxBaseFee tx =
  case tx.txtype of
     EIP1559Transaction -> fromJust tx.maxFeePerGas
     _ -> fromJust tx.gasPrice

checkTx :: Transaction -> Block -> BlockchainContracts -> Maybe (BlockchainContracts)
checkTx tx block prestate = do
  validateTx tx block prestate
  let initCodeSizeExceeded = isNothing tx.toAddr
        && BS.length tx.txdata > (unsafeInto maxCodeSize * 2)
  if initCodeSizeExceeded then mzero
  else pure prestate

validateTx :: Transaction -> Block -> BlockchainContracts -> Maybe ()
validateTx tx block cs = do
  origin <- sender tx
  originBalance <- (.balance) <$> Map.lookup origin cs
  originNonce <- (.nonce) <$> Map.lookup origin cs
  let gasDeposit = (effectiveprice tx block.baseFee) * (into tx.gasLimit)
  if gasDeposit + tx.value <= originBalance
    && ((unsafeInto tx.nonce) == originNonce) && block.baseFee <= maxBaseFee tx
  then Just ()
  else Nothing

vmForCase :: Case -> IO (VM Concrete)
vmForCase x = do
  vm <- stToIO $ makeVm x.vmOpts
    -- TODO: why do we override contracts here instead of using VMOpts otherContracts?
    <&> set (#env % #contracts) (Map.mapKeys LitAddr $ Map.map makeContract x.checkContracts)
    -- TODO: we need to call this again because we override contracts in the
    -- previous line
    <&> setEIP4788Storage x.vmOpts
    <&> setEIP2935Storage x.vmOpts
  pure $ initTx vm

forceConcreteAddrs :: Map (Expr EAddr) Contract -> Map Addr Contract
forceConcreteAddrs cs = Map.mapKeys
      (fromMaybe (internalError "Internal Error: unexpected symbolic address") . maybeLitAddrSimp)
      cs
