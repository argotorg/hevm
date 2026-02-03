{-# LANGUAGE DataKinds #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Maybe
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Vector qualified as V

import EVM (makeVm, symbolify)
import EVM.ABI
import EVM.Fetch
import EVM.SMT
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Test.Utils
import EVM.Types hiding (BlockNumber, Env)
import Control.Monad.ST (stToIO)
import Control.Monad.Reader (ReaderT)
import Control.Monad.IO.Unlift
import EVM.Effects

rpcEnv :: Env
rpcEnv = Env { config = defaultConfig }

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv rpcEnv b

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "rpc"
  [ testGroup "Block Parsing Tests"
    [ test "pre-merge-block" $ do
        let block = BlockNumber 15537392
        conf <- readConfig
        sess <- mkSessionWithoutCache
        liftIO $ do
          (cb, numb, basefee, prevRan) <- fetchBlockWithSession conf sess block testRpc >>= \case
                        Nothing -> internalError "Could not fetch block"
                        Just Block{..} -> pure ( coinbase
                                                     , number
                                                     , baseFee
                                                     , prevRandao
                                                     )

          assertEqual "coinbase" (LitAddr 0xea674fdde714fd979de3edf0f56aa9716b898ec8) cb
          assertEqual "number" (BlockNumber (forceLit numb)) block
          assertEqual "basefee" 38572377838 basefee
          assertEqual "prevRan" 11049842297455506 prevRan
    , test "post-merge-block" $ do
        conf <- readConfig
        sess <- mkSessionWithoutCache
        liftIO $ do
          let block = BlockNumber 16184420
          (cb, numb, basefee, prevRan) <- fetchBlockWithSession conf sess block testRpc >>= \case
                        Nothing -> internalError "Could not fetch block"
                        Just Block{..} -> pure ( coinbase
                                                     , number
                                                     , baseFee
                                                     , prevRandao
                                                     )

          assertEqual "coinbase" (LitAddr 0x690b9a9e9aa1c9db991c7721a92d351db4fac990) cb
          assertEqual "number" (BlockNumber (forceLit numb)) block
          assertEqual "basefee" 22163046690 basefee
          assertEqual "prevRan" 0x2267531ab030ed32fd5f2ef51f81427332d0becbd74fe7f4cd5684ddf4b287e0 prevRan
    ]
  , testGroup "execution with remote state"
    -- execute against remote state from a ds-test harness
    [ test "dapp-test" $ do
        let testFile = "test/contracts/pass/rpc.sol"
        res <- runForgeTestCustom testFile ".*" Nothing Nothing False testRpcInfo
        liftIO $ assertEqual "test result" (True, True) res

    -- concretely exec "transfer" on WETH9 using remote rpc
    -- https://etherscan.io/token/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code
    , test "weth-conc" $ do
        let
          wad = 0x999999999999999999
          calldata' = ConcreteBuf $ abiMethod "transfer(address,uint256)" (AbiTuple (V.fromList [AbiAddress (Addr 0xdead), AbiUInt 256 wad]))
        sess <- mkSessionWithoutCache
        vm <- weth9VM sess testBlockNumber (calldata', [])
        postVm <- withSolvers Z3 1 Nothing defMemLimit $ \solvers ->
          Stepper.interpret (oracle solvers (Just sess) testRpcInfo) vm Stepper.runFully
        let
          wethStore = (fromJust $ Map.lookup (LitAddr 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2) postVm.env.contracts).storage
          wethStore' = case wethStore of
            ConcreteStore s -> s
            _ -> internalError "Expecting concrete store"
          receiverBal = fromJust $ Map.lookup (keccak' (word256Bytes 0xdead <> word256Bytes 0x3)) wethStore'
          msg = case postVm.result of
            Just (VMSuccess m) -> m
            _ -> internalError "VMSuccess expected"
        liftIO $ do
          assertEqual "should succeed" msg (ConcreteBuf $ word256Bytes 0x1)
          assertEqual "should revert" receiverBal (W256 $ 2595433725034301 + wad)

    -- symbolically exec "transfer" on WETH9 using remote rpc
    -- https://etherscan.io/token/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code
    , test "weth-sym" $ do
        calldata' <- symCalldata "transfer(address,uint256)" [AbiAddressType, AbiUIntType 256] ["0xdead"] (AbstractBuf "txdata")
        let
          postc _ (Failure _ _ (Revert _)) = PBool False
          postc _ _ = PBool True
        sess <- mkSession Nothing Nothing
        vm <- weth9VM sess testBlockNumber calldata'
        (_, [Cex (_, model)]) <- withSolvers Z3 1 Nothing defMemLimit $ \s ->
          verify s (oracle s (Just sess) testRpcInfo) (defaultVeriOpts {rpcInfo = testRpcInfo}) (symbolify vm) postc Nothing
        liftIO $ assertBool "model should exceed caller balance" (getVar model "arg2" >= 695836005599316055372648)
    ]
  ]

-- call into WETH9 from 0xf04a... (a large holder)
weth9VM :: App m => Session -> BlockNumber -> (Expr Buf, [Prop]) -> m (VM Concrete)
weth9VM sess blockNum calldata' = do
  let
    caller' = LitAddr 0xf04a5cc80b1e94c69b48f5ee68a08cd2f09a7c3e
    weth9 = Addr 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2
    callvalue' = Lit 0
  vmFromRpc sess blockNum calldata' callvalue' caller' weth9

vmFromRpc :: App m => Session -> BlockNumber -> (Expr Buf, [Prop]) -> Expr EWord -> Expr EAddr -> Addr -> m (VM Concrete)
vmFromRpc sess blockNum calldata callvalue caller address = do
  conf <- readConfig
  ctrct <- liftIO $ fetchContractWithSession conf sess blockNum testRpc address >>= \case
        FetchFailure _ -> internalError $ "contract not found: " <> show address
        FetchError e -> internalError $ "rpc error: " <> show e
        FetchSuccess contract' _ -> pure contract'

  liftIO $ addFetchCache sess address ctrct
  blk <- liftIO $ fetchBlockWithSession conf sess blockNum testRpc >>= \case
    Nothing -> internalError "could not fetch block"
    Just b -> pure b

  liftIO $ stToIO (makeVm $ VMOpts
    { contract       = makeContractFromRPC ctrct
    , otherContracts = []
    , calldata       = calldata
    , value          = callvalue
    , address        = LitAddr address
    , caller         = caller
    , origin         = LitAddr 0xacab
    , gas            = 0xffffffffffffffff
    , gaslimit       = 0xffffffffffffffff
    , baseFee        = blk.baseFee
    , priorityFee    = 0
    , coinbase       = blk.coinbase
    , number         = blk.number
    , timestamp      = blk.timestamp
    , blockGaslimit  = blk.gaslimit
    , gasprice       = 0
    , maxCodeSize    = blk.maxCodeSize
    , prevRandao     = blk.prevRandao
    , schedule       = blk.schedule
    , chainId        = 1
    , create         = False
    , baseState      = EmptyBase
    , txAccessList   = mempty
    , allowFFI       = False
    , freshAddresses = 0
    , beaconRoot     = 0
    , parentHash     = 0
    })

testRpc :: Text
testRpc = "https://eth-mainnet.g.alchemy.com/v2/vpeKFsEF6PHifHzdtcwXSDbhV3ym5Ro4"

testBlockNumber :: BlockNumber
testBlockNumber = BlockNumber 16198552

testRpcInfo :: RpcInfo
testRpcInfo = RpcInfo $ Just (testBlockNumber, testRpc)
