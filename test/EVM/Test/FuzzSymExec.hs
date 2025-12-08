{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Tracing
Description : Tests to fuzz concrete tracing, and symbolic execution

Functions here are used to generate traces for the concrete
execution of HEVM and check that against evmtool from go-ethereum. Re-using some
of this code, we also generate a symbolic expression then evaluate it
concretely through Expr.simplify, then check that against evmtool's output.
-}
module EVM.Test.FuzzSymExec where

import Control.Concurrent.STM.TVar (newTVarIO)
import Control.Monad (when)
import Control.Monad.IO.Unlift
import Control.Monad.ST (ST, stToIO, RealWorld)
import Control.Monad.State.Strict (StateT(..))
import Control.Monad.Reader (ReaderT)
import Data.Aeson ((.:), (.:?))
import Data.Aeson qualified as JSON
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.Maybe (fromJust, isJust, mapMaybe)

import Data.Map.Strict qualified as Map
import Data.Text.IO qualified as T
import Data.Vector qualified as Vector
import Data.Word (Word8, Word64)
import GHC.Generics (Generic)
import GHC.IO.Exception (ExitCode(ExitSuccess))
import Numeric (showHex)
import Optics.Core hiding (pre)
import System.Directory (removeDirectoryRecursive)
import System.FilePath ((</>))
import System.IO.Temp (getCanonicalTemporaryDirectory, createTempDirectory)
import System.Process (readCreateProcessWithExitCode, proc, CreateProcess(..))
import Test.QuickCheck (elements)
import Test.QuickCheck.Instances.Text()
import Test.QuickCheck.Instances.Natural()
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty (testGroup, after, TestTree, TestName, DependencyType(..))
import Test.Tasty.HUnit (assertEqual, testCase, assertBool)
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Witch (into, unsafeInto)

import EVM (makeVm, initialContract, symbolify)
import EVM.Assembler (assemble)
import EVM.Expr qualified as Expr
import EVM.Exec (ethrunAddress)
import EVM.Fetch qualified as Fetch
import EVM.Format (formatBinary)
import EVM.FeeSchedule
import EVM.Op (intToOpName)
import EVM.Sign (deriveAddr)
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Traversals (mapExpr)
import EVM.Transaction qualified
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Tracing (interpretWithTrace, VMTraceStep(..), VMTraceStepResult(..))

data EVMToolTrace =
  EVMToolTrace
    { pc :: Int
    , op :: Int
    , gas :: W256
    , memSize :: Integer
    , depth :: Int
    , refund :: Int
    , opName :: String
    , stack :: [W256]
    , error :: Maybe String
    , gasCost :: Maybe W256
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolTrace where
  parseJSON = JSON.withObject "EVMToolTrace" $ \v -> EVMToolTrace
    <$> v .: "pc"
    <*> v .: "op"
    <*> v .: "gas"
    <*> v .: "memSize"
    <*> v .: "depth"
    <*> v .: "refund"
    <*> v .: "opName"
    <*> v .: "stack"
    <*> v .:? "error"
    <*> v .:? "gasCost"

mkBlockHash:: Int -> Expr 'EWord
mkBlockHash x = (into x :: Integer) & show & Char8.pack & EVM.Types.keccak' & Lit

blockHashesDefault :: Map.Map Int W256
blockHashesDefault = Map.fromList [(x, forceLit $ mkBlockHash x) | x<- [1..256]]

data EVMToolOutput =
  EVMToolOutput
    { output :: ByteStringS
    , gasUsed :: W256
    , time :: Maybe Integer
    , error :: Maybe String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolOutput

data EVMToolTraceOutput =
  EVMToolTraceOutput
    { trace :: [EVMToolTrace]
    , output :: EVMToolOutput
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolTraceOutput

data EVMToolEnv = EVMToolEnv
  { coinbase    :: Addr
  , timestamp   :: Expr EWord
  , number      :: Expr EWord
  , gasLimit    :: Data.Word.Word64
  , baseFee     :: W256
  , maxCodeSize :: W256
  , schedule    :: FeeSchedule Data.Word.Word64
  , blockHashes :: Map.Map Int W256
  , withdrawals :: [Addr]
  , currentRandom :: W256
  , parentBeaconBlockRoot :: W256
  } deriving (Show, Generic)

instance JSON.ToJSON EVMToolEnv where
  toJSON b = JSON.object [ ("currentCoinBase"  , (JSON.toJSON b.coinbase))
                         , ("currentGasLimit"  , (JSON.toJSON ("0x" ++ showHex (into @Integer b.gasLimit) "")))
                         , ("currentNumber"    , (JSON.toJSON number))
                         , ("currentTimestamp" , (JSON.toJSON tstamp))
                         , ("currentBaseFee"   , (JSON.toJSON b.baseFee))
                         , ("blockHashes"      , (JSON.toJSON b.blockHashes))
                         , ("withdrawals"      , (JSON.toJSON b.withdrawals))
                         , ("currentRandom"    , (JSON.toJSON b.currentRandom))
                         , ("parentBeaconBlockRoot" , (JSON.toJSON b.parentBeaconBlockRoot))
                         ]
              where
                tstamp :: W256
                tstamp = case (b.timestamp) of
                              Lit a -> a
                              _ -> internalError "Timestamp needs to be a Lit"
                number :: W256
                number = case (b.number) of
                              Lit a -> a
                              _ -> internalError "Timestamp needs to be a Lit"

emptyEvmToolEnv :: EVMToolEnv
emptyEvmToolEnv = EVMToolEnv { coinbase = 0
                             , timestamp = Lit 0
                             , number     = Lit 0
                             , gasLimit   = 0xffffffffffffffff
                             , baseFee    = 0
                             , maxCodeSize= 0xffffffff
                             , schedule   = feeSchedule
                             , blockHashes = mempty
                             , withdrawals = mempty
                             , currentRandom = 42
                             , parentBeaconBlockRoot = 5
                             }

data EVMToolReceipt =
  EVMToolReceipt
    { _type :: String
    , root :: String
    , status :: String
    , cumulativeGasUsed :: String
    , logsBloom :: String
    , logs :: Maybe String
    , transactionHash :: String
    , contractAddress :: String
    , gasUsed :: String
    , effectiveGasPrice :: Maybe String
    , blockHash :: String
    , transactionIndex :: String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolReceipt where
    parseJSON = JSON.withObject "EVMReceipt" $ \v -> EVMToolReceipt
        <$> v .: "type"
        <*> v .: "root"
        <*> v .: "status"
        <*> v .: "cumulativeGasUsed"
        <*> v .: "logsBloom"
        <*> v .: "logs"
        <*> v .: "transactionHash"
        <*> v .: "contractAddress"
        <*> v .: "gasUsed"
        <*> v .: "effectiveGasPrice"
        <*> v .: "blockHash"
        <*> v .: "transactionIndex"

data EVMToolResult =
  EVMToolResult
  { stateRoot :: String
  , txRoot :: String
  , receiptsRoot :: String
  , logsHash :: String
  , logsBloom :: String
  , receipts :: [EVMToolReceipt]
  , currentDifficulty :: Maybe String
  , gasUsed :: String
  , currentBaseFee :: String
  , withdrawalsRoot :: String
  } deriving (Generic, Show)

instance JSON.FromJSON EVMToolResult


data EVMToolAlloc =
  EVMToolAlloc
  { balance :: W256
  , code :: ByteString
  , nonce :: W64
  } deriving (Generic)

instance JSON.ToJSON EVMToolAlloc where
  toJSON b = JSON.object [ ("balance" , (JSON.toJSON $ show b.balance))
                         , ("code", (JSON.toJSON $ ByteStringS b.code))
                         , ("nonce", (JSON.toJSON b.nonce))
                         ]

emptyEVMToolAlloc :: EVMToolAlloc
emptyEVMToolAlloc = EVMToolAlloc { balance = 0
                                 , code = mempty
                                 , nonce = 0
                                 }
-- Sets up common parts such as TX, origin contract, and environment that can
-- later be used to create & execute either an evmtool (from go-ethereum) or an
-- HEVM transaction. Some elements here are hard-coded such as the secret key,
-- which are currently not being fuzzed.
evmSetup :: OpContract -> ByteString -> Int -> (EVM.Transaction.Transaction, EVMToolEnv, EVMToolAlloc, Addr, Addr, Integer)
evmSetup contr txData gaslimitExec = (txn, evmEnv, contrAlloc, fromAddress, toAddress, sk)
  where
    contrLits = assemble $ getOpData contr
    toW8fromLitB :: Expr 'Byte -> Word8
    toW8fromLitB (LitByte a) = a
    toW8fromLitB _ = internalError "Cannot convert non-litB"

    bitcode = BS.pack . Vector.toList $ toW8fromLitB <$> contrLits
    contrAlloc = EVMToolAlloc{ balance = 0xa493d65e20984bc
                             , code = bitcode
                             , nonce = 0x48
                             }
    txn = EVM.Transaction.Transaction
      { txdata     = txData
      , gasLimit = unsafeInto gaslimitExec
      , gasPrice = Just 1
      , nonce    = 172
      , toAddr   = Just 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192
      , r        = 0 -- will be fixed when we sign
      , s        = 0 -- will be fixed when we sign
      , v        = 0 -- will be fixed when we sign
      , value    = 0 -- setting this > 0 fails because HEVM doesn't handle value sent in toplevel transaction
      , txtype     = EVM.Transaction.EIP1559Transaction
      , accessList = []
      , maxPriorityFeeGas =  Just 1
      , maxFeePerGas = Just 1
      , chainId = 1
      }
    evmEnv = EVMToolEnv { coinbase      = 0xff
                        , timestamp     = Lit 0x3e8
                        , number        = Lit 0
                        , gasLimit      = unsafeInto gaslimitExec
                        , baseFee       = 0x0
                        , maxCodeSize   = 0xfffff
                        , schedule      = feeSchedule
                        , blockHashes   = blockHashesDefault
                        , withdrawals   = mempty
                        , currentRandom = 42
                        , parentBeaconBlockRoot = 5
                        }
    sk = 0xDC38EE117CAE37750EB1ECC5CFD3DE8E85963B481B93E732C5D0CB66EE6B0C9D
    fromAddress = fromJust $ deriveAddr sk
    toAddress = 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192

getHEVMRet
  :: App m
  => OpContract -> ByteString -> Int -> m (Either (EvmError, [VMTraceStep]) ([Expr 'End], [VMTraceStep], VMTraceStepResult))
getHEVMRet contr txData gaslimitExec = do
  let (txn, evmEnv, contrAlloc, fromAddress, toAddress, _) = evmSetup contr txData gaslimitExec
  runCodeWithTrace Fetch.noRpc evmEnv contrAlloc txn (LitAddr fromAddress) (LitAddr toAddress)

getEVMToolRet :: FilePath -> OpContract -> ByteString -> Int -> IO (Maybe EVMToolResult)
getEVMToolRet evmDir contr txData gaslimitExec = do
  let (txn, evmEnv, contrAlloc, fromAddress, toAddress, sk) = evmSetup contr txData gaslimitExec
      txs = [EVM.Transaction.sign sk txn]
      walletAlloc = EVMToolAlloc{ balance = 0x5ffd4878be161d74
                                , code = BS.empty
                                , nonce = 0xac
                                }
      alloc :: Map.Map Addr EVMToolAlloc
      alloc = Map.fromList ([ (fromAddress, walletAlloc), (toAddress, contrAlloc)])
  JSON.encodeFile (evmDir </> "txs.json") txs
  JSON.encodeFile (evmDir </> "alloc.json") alloc
  JSON.encodeFile (evmDir </> "env.json") evmEnv
  let cmd = (proc "evm" [ "transition"
                        , "--state.fork", "Cancun"
                        , "--input.alloc", "alloc.json"
                        , "--input.env", "env.json"
                        , "--input.txs", "txs.json"
                        , "--output.alloc", "alloc-out.json"
                        , "--trace.returndata=true"
                        , "--trace", "trace.json"
                        , "--output.result", "result.json"
                        ]) { cwd = Just evmDir }
  (exitCode, evmtoolStdout, evmtoolStderr) <- readCreateProcessWithExitCode cmd ""
  when (exitCode /= ExitSuccess) $ do
    putStrLn $ "evmtool exited with code " <> show exitCode
    putStrLn $ "evmtool stderr output:" <> show evmtoolStderr
    putStrLn $ "evmtool stdout output:" <> show evmtoolStdout
  JSON.decodeFileStrict (evmDir </> "result.json") :: IO (Maybe EVMToolResult)

-- Compares traces of evmtool (from go-ethereum) and HEVM
compareTraces :: [VMTraceStep] -> [EVMToolTrace] -> IO (Bool)
compareTraces hevmTrace evmTrace = go hevmTrace evmTrace
  where
    go :: [VMTraceStep] -> [EVMToolTrace] -> IO (Bool)
    go [] [] = pure True
    go (a:ax) (b:bx) = do
      let aOp = a.op
          bOp = b.op
          aPc = a.pc
          bPc = b.pc
          aStack = a.stack
          bStack = b.stack
          aGas = into a.gas
          bGas = b.gas
      -- putStrLn $ "hevm: " <> intToOpName aOp <> " pc: " <> show aPc <> " gas: " <> show aGas <> " stack: " <> show aStack
      -- putStrLn $ "geth: " <> intToOpName bOp <> " pc: " <> show bPc <> " gas: " <> show bGas <> " stack: " <> show bStack

      when (aGas /= bGas) $ do
        putStrLn "GAS doesn't match:"
        putStrLn $ "HEVM's gas   : " <> (show aGas)
        putStrLn $ "evmtool's gas: " <> (show bGas)
        putStrLn $ "executing opcode: " <> (intToOpName aOp)
      when (aOp /= bOp || aPc /= bPc) $ do
        putStrLn $ "HEVM: " <> (intToOpName aOp) <> " (pc " <> (show aPc) <> ") --- evmtool " <> (intToOpName bOp) <> " (pc " <> (show bPc) <> ")"

      when (isJust b.error) $ do
        putStrLn $ "Error by evmtool: " <> (show b.error)
        putStrLn $ "Error by HEVM   : " <> (show a.error)

      when (aStack /= bStack) $ do
        putStrLn "stacks don't match:"
        putStrLn $ "HEVM's stack   : " <> (show aStack)
        putStrLn $ "evmtool's stack: " <> (show bStack)
      if aOp == bOp && aStack == bStack && aPc == bPc && aGas == bGas then go ax bx
      else pure False


    go a@(_:_) [] = do
      putStrLn $ "Traces don't match. HEVM's trace is longer by:" <> (show a)
      pure False
    go [] [b] = do
      -- evmtool produces ONE more trace element of the error
      -- hevm on the other hand stops and doesn't produce one more
      if isJust b.error then pure True
                           else do
                             putStrLn $ "Traces don't match. HEVM's trace is longer by:" <> (show b)
                             pure False
    go [] b@(_:_) = do
      putStrLn $ "Traces don't match. evmtool's trace is longer by:" <> (show b)
      pure False

getTraceFileName :: FilePath -> EVMToolResult -> String
getTraceFileName evmDir evmtoolResult = evmDir </> traceFileName
  where
    txName = ((evmtoolResult.receipts) !! 0).transactionHash
    traceFileName = "trace-0-" ++ txName ++ ".jsonl"

getTraceOutput :: FilePath -> Maybe EVMToolResult -> IO (Maybe EVMToolTraceOutput)
getTraceOutput evmDir evmtoolResult =
  case evmtoolResult of
    Nothing -> pure Nothing
    Just res -> do
      let traceFileName = getTraceFileName evmDir res
      decodeTraceOutputHelper traceFileName

decodeTraceOutputHelper :: String -> IO (Maybe EVMToolTraceOutput)
decodeTraceOutputHelper traceFileName = do
  traceContents <- readFile traceFileName
  let traceLines = lines traceContents
  let (traces, outputLines) = splitAt (length traceLines - 1) traceLines
  let parsedTraces = map decodeString traces :: [Maybe EVMToolTrace]
  let parsedOutput = decodeString (outputLines !! 0) :: Maybe EVMToolOutput
  if all isJust parsedTraces && isJust parsedOutput then
    pure $ Just $ EVMToolTraceOutput (map fromJust parsedTraces) (fromJust parsedOutput)
  else
    pure Nothing
  where
    decodeString :: (JSON.FromJSON a) => String -> Maybe a
    decodeString = JSON.decodeStrict . Char8.pack

-- | Takes a runtime code and calls it with the provided calldata
--   Uses evmtool's alloc and transaction to set up the VM correctly
runCodeWithTrace
  :: App m
  => Fetch.RpcInfo -> EVMToolEnv -> EVMToolAlloc -> EVM.Transaction.Transaction
  -> Expr EAddr -> Expr EAddr -> m (Either (EvmError, [VMTraceStep]) (([Expr 'End], [VMTraceStep], VMTraceStepResult)))
runCodeWithTrace rpcinfo evmEnv alloc txn fromAddr toAddress = withSolvers Z3 0 1 Nothing $ \solvers -> do
  let calldata' = ConcreteBuf txn.txdata
      code' = alloc.code
      iterConf = IterConfig { maxIter = Nothing, askSmtIters = 1, loopHeuristic = Naive }
      fetcherSym = Fetch.oracle solvers Nothing rpcinfo
      buildExpr vm = do
        abortFlag <- liftIO $ newTVarIO False
        interpret fetcherSym iterConf vm abortFlag runExpr pure
  origVM <- liftIO $ stToIO $ vmForRuntimeCode code' calldata' evmEnv alloc txn fromAddr toAddress
  expr <- buildExpr $ symbolify origVM

  let fetcherConc = Fetch.oracle solvers Nothing rpcinfo
  (res, (vm, trace)) <- runStateT (interpretWithTrace fetcherConc Stepper.execFully) (origVM, [])
  case res of
    Left x -> pure $ Left (x, trace)
    Right _ -> pure $ Right (expr, trace, vmres vm)

vmForRuntimeCode :: ByteString -> Expr Buf -> EVMToolEnv -> EVMToolAlloc -> EVM.Transaction.Transaction -> Expr EAddr -> Expr EAddr -> ST RealWorld (VM Concrete)
vmForRuntimeCode runtimecode calldata' evmToolEnv alloc txn fromAddr toAddress =
  let contract = initialContract (RuntimeCode (ConcreteRuntimeCode runtimecode))
                 & set #balance (Lit alloc.balance)
  in (makeVm $ VMOpts
    { contract = contract
    , otherContracts = []
    , calldata = (calldata', [])
    , value = Lit txn.value
    , baseState = EmptyBase
    , address =  toAddress
    , caller = fromAddr
    , origin = fromAddr
    , coinbase = LitAddr evmToolEnv.coinbase
    , number = evmToolEnv.number
    , timestamp = evmToolEnv.timestamp
    , gasprice = fromJust txn.gasPrice
    , gas = txn.gasLimit - (EVM.Transaction.txGasCost evmToolEnv.schedule txn)
    , gaslimit = txn.gasLimit
    , blockGaslimit = evmToolEnv.gasLimit
    , prevRandao = evmToolEnv.currentRandom
    , baseFee = evmToolEnv.baseFee
    , priorityFee = fromJust txn.maxPriorityFeeGas
    , maxCodeSize = evmToolEnv.maxCodeSize
    , schedule = evmToolEnv.schedule
    , chainId = txn.chainId
    , create = False
    , txAccessList = mempty
    , allowFFI = False
    , freshAddresses = 0
    , beaconRoot = 0
    }) <&> set (#env % #contracts % at (LitAddr ethrunAddress))
             (Just (initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty))))
       <&> set (#state % #calldata) calldata'

vmres :: VM Concrete -> VMTraceStepResult
vmres vm =
  let
    gasUsed' = vm.tx.gaslimit - vm.state.gas
    res = case vm.result of
      Just (VMSuccess (ConcreteBuf b)) -> (ByteStringS b)
      Just (VMSuccess x) -> internalError $ "unhandled: " <> (show x)
      Just (VMFailure (Revert (ConcreteBuf b))) -> (ByteStringS b)
      Just (VMFailure _) -> ByteStringS mempty
      _ -> ByteStringS mempty
  in VMTraceStepResult
     { out = res
     , gasUsed = gasUsed'
     }


newtype OpContract = OpContract [Op]
instance Show OpContract where
  show (OpContract a) = "OpContract " ++ (show a)

getOpData :: OpContract-> [Op]
getOpData (OpContract x) = x

instance Arbitrary OpContract where
  arbitrary = fmap OpContract (sized genContract)

removeExtcalls :: OpContract -> OpContract
removeExtcalls (OpContract ops) = OpContract (filter (noStorageNoExtcalls) ops)
  where
    noStorageNoExtcalls :: Op -> Bool
    noStorageNoExtcalls o = case o of
                               -- External info functions
                               OpExtcodecopy -> False
                               OpExtcodehash -> False
                               OpExtcodesize -> False
                               OpAddress -> False
                               OpOrigin -> False
                               OpCaller -> False
                               OpCoinbase -> False
                               OpCreate -> False
                               OpCreate2 -> False
                               -- External call functions
                               OpDelegatecall -> False
                               OpStaticcall -> False
                               OpCall -> False
                               OpCallcode -> False
                               -- Not interesting
                               OpBalance -> False
                               OpSelfdestruct -> False
                               _ -> True

getJumpDests :: [Op] -> [Int]
getJumpDests ops = go ops 0 []
    where
      go :: [Op] -> Int -> [Int] -> [Int]
      go [] _ dests = dests
      go (a:ax) pos dests = case a of
                       OpJumpdest -> go ax (pos+1) (pos:dests)
                       OpPush _ -> go ax (pos+33) dests
                       -- We'll fix these up later to add a Push in between, hence they are 34 bytes
                       OpJump -> go ax (pos+34) dests
                       OpJumpi -> go ax (pos+34) dests
                       -- everything else is 1 byte
                       _ -> go ax (pos+1) dests

fixContractJumps :: OpContract -> IO OpContract
fixContractJumps (OpContract ops) = do
  let
    addedOps = ops++[OpJumpdest]
    jumpDests = getJumpDests addedOps
    -- always end on an OpJumpdest so we don't have an issue with a "later" position
    ops2 = fixup addedOps 0 []
    -- original set of operations, the set of jumpDests NOW valid, current position, return value
    fixup :: [Op] -> Int -> [Op] -> IO [Op]
    fixup [] _ ret = pure ret
    fixup (a:ax) pos ret = case a of
      OpJumpi -> do
        let filtDests = (filter (> pos) jumpDests)
        rndPos <- randItem filtDests
        fixup ax (pos+34) (ret++[(OpPush (Lit (unsafeInto rndPos))), (OpJumpi)])
      OpJump -> do
        let filtDests = (filter (> pos) jumpDests)
        rndPos <- randItem filtDests
        fixup ax (pos+34) (ret++[(OpPush (Lit (unsafeInto rndPos))), (OpJump)])
      myop@(OpPush _) -> fixup ax (pos+33) (ret++[myop])
      myop -> fixup ax (pos+1) (ret++[myop])
  fmap OpContract ops2

genPush :: Int -> Gen [Op]
genPush n = vectorOf n onePush
  where
    onePush :: Gen Op
    onePush  = do
      p <- chooseInt (1, 10)
      pure $ OpPush (Lit (unsafeInto p))

genContract :: Int -> Gen [Op]
genContract n = do
    y <- chooseInt (3, 6)
    pushes <- genPush y
    normalOps <- vectorOf (3*n+40) genOne
    large :: Bool <- chooseAny
    extra <- if large then vectorOf (100) genOne
                      else pure []
    addReturn <- chooseInt (0, 10)
    let contr = pushes ++ normalOps ++ extra
    if addReturn < 10 then pure $ contr++[OpPush (Lit 0x40), OpPush (Lit 0x0), OpReturn]
                      else pure contr
  where
    genOne :: Gen Op
    genOne = frequency [
      -- math ops
      (20, frequency [
          (2, pure OpAdd)
        , (2, pure OpMul)
        , (1, pure OpSub)
        , (2, pure OpDiv)
        , (1, pure OpSdiv)
        , (2, pure OpMod)
        , (1, pure OpSmod)
        , (1, pure OpAddmod)
        , (2, pure OpMulmod)
        , (1, pure OpExp)
        , (1, pure OpSignextend)
        , (2, pure OpLt)
        , (2, pure OpGt)
        , (2, pure OpSlt)
        , (2, pure OpSgt)
        , (1, pure OpSha3)
      ])
      -- Comparison & binary ops
      , (200, frequency [
          (1, pure OpEq)
        , (1, pure OpIszero)
        , (1, pure OpAnd)
        , (1, pure OpOr)
        , (1, pure OpXor)
        , (1, pure OpNot)
        , (1, pure OpByte)
        , (1, pure OpShl)
        , (1, pure OpShr)
        , (1, pure OpSar)
      ])
      -- calldata
      , (200, pure OpCalldataload)
      , (800, pure OpCalldatacopy)
      -- Get some info
      , (100, frequency [
          (10, pure OpAddress)
        , (10, pure OpBalance)
        , (10, pure OpOrigin)
        , (10, pure OpCaller)
        , (10, pure OpCallvalue)
        , (10, pure OpCalldatasize)
        , (10, pure OpCodesize)
        , (10, pure OpGasprice)
        , (10, pure OpReturndatasize)
        , (10, pure OpReturndatacopy)
        , (10, pure OpExtcodehash)
        , (10, pure OpBlockhash)
        , (10, pure OpCoinbase)
        , (10, pure OpTimestamp)
        , (10, pure OpNumber)
        , (10, pure OpPrevRandao)
        , (10, pure OpGaslimit)
        , (10, pure OpChainid)
        , (10, pure OpSelfbalance)
        , (10, pure OpBaseFee)
        , (10, pure OpPc)
        , (10, pure OpMsize)
        , (10, pure OpGas)
        , (10, pure OpExtcodesize)
        , (10, pure OpCodecopy)
        , (10, pure OpExtcodecopy)
      ])
      -- memory manip
      , (1200, frequency [
          (10, pure OpMcopy)
        , (50, pure OpMload)
        , (1, pure OpMstore)
        , (300, pure OpMstore8)
      ])
      -- storage manip
      , (100, frequency [
          (1, pure OpSload)
        , (1, pure OpSstore)
        , (1, pure OpTstore)
        , (1, pure OpTload)
      ])
      -- Jumping around
      , (50, frequency [
            (1, pure OpJump)
          , (10, pure OpJumpi)
      ])
      -- calling out
      , (1, frequency [
          (1, pure OpStaticcall)
        , (1, pure OpCall)
        , (1, pure OpCallcode)
        , (1, pure OpDelegatecall)
        , (1, pure OpCreate)
        , (1, pure OpCreate2)
        , (1, pure OpSelfdestruct)
      ])
      -- manipulate stack
      , (13000, frequency [
          (1, pure OpPop)
        , (400, do
            -- x <- arbitrary
            large <- chooseInt (0, 2000)
            x <- if large == 0 then chooseBoundedIntegral (0::W256, (2::W256)^(256::W256)-1)
                               else chooseBoundedIntegral (0, 10)
            pure $ OpPush (Lit x))
        , (10, do
            x <- chooseInt (1, 10)
            pure $ OpDup (unsafeInto x))
        , (10, do
            x <- chooseInt (1, 10)
            pure $ OpSwap (unsafeInto x))
      ])]
      -- End states
      -- , (1, frequency [
      --    (1, pure OpStop)
      --  , (10, pure OpReturn)
      --  , (10, pure OpRevert)
      -- ])

randItem :: [a] -> IO a
randItem = generate . Test.QuickCheck.elements

getOpFromVM :: VM t -> Word8
getOpFromVM vm =
  let pcpos  = vm ^. #state % #pc
      code' = vm ^. #state % #code
      xs = case code' of
        UnknownCode _ -> internalError "UnknownCode instead of RuntimeCode"
        InitCode bs _ -> BS.drop pcpos bs
        RuntimeCode (ConcreteRuntimeCode xs') -> BS.drop pcpos xs'
        RuntimeCode (SymbolicRuntimeCode _) -> internalError "RuntimeCode is symbolic"
  in if xs == BS.empty then 0
                       else BS.head xs

testEnv :: Env
testEnv = Env { config = defaultConfig }

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv testEnv b

prop:: Testable prop => ReaderT Env IO prop -> Property
prop a = ioProperty $ runEnv testEnv a

tests :: TestTree
tests = testGroup "contract-quickcheck-run"
    [ testProperty "random-contract-concrete-call" $ \(contr :: OpContract, GasLimitInt gasLimit, TxDataRaw txDataRaw) -> prop $ do
        let txData = BS.pack $ toEnum <$> txDataRaw
        -- TODO: By removing external calls, we fuzz less
        --       It should work also when we external calls. Removing for now.
        contrFixed <- liftIO $ fixContractJumps $ removeExtcalls contr
        checkTraceAndOutputs contrFixed gasLimit txData
      , after AllFinish "random-contract-concrete-call" $ test "calldata-wraparound-1" $ do
        let contract = OpContract $ concat
              [ [OpPush (Lit 0xff),OpPush (Lit 31),OpMstore8] -- value, offs
              , [OpPush (Lit 0x3),OpPush (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),OpPush (Lit 0x0),OpCalldatacopy] -- size, offs, destOffs
              , [OpPush (Lit 0x20),OpPush (Lit 0),OpReturn] -- datasize, offs
              ]
        checkTraceAndOutputs contract 40000 (BS.pack [1, 2, 3, 4, 5])
      , after AllFinish "calldata-wraparound-1" $ test "calldata-wraparound-2" $ do
        let contract = OpContract $ concat
              [ [OpPush (Lit 0xff),OpPush (Lit 0),OpMstore8] -- value, offs
              , [OpPush (Lit 0x10),OpPush (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),OpPush (Lit 0x0),OpCalldatacopy] -- size, offs, destOffs
              , [OpPush (Lit 0x20),OpPush (Lit 0),OpReturn] -- datasize, offs
              ]
        checkTraceAndOutputs contract 40000 (BS.pack [1, 2, 3, 4, 5])
      , after AllFinish "calldata-wraparound-2" $ test "calldata-overwrite-with-0-if-oversized" $ do
        -- supposed to copy 1...6 and then 0s, overwriting the 0xff with 0
        let contract = OpContract $ concat
              [ [OpPush (Lit 0xff),OpPush (Lit 1),OpMstore8] -- value, offs
              , [OpPush (Lit 10),OpPush (Lit 0),OpPush (Lit 0), OpCalldatacopy] -- size, offs, destOffs
              , [OpPush (Lit 10),OpPush (Lit 0x0),OpReturn] -- datasize, offset
              ]
        checkTraceAndOutputs contract 40000 (BS.pack [1, 2, 3, 4, 5, 6])
      , after AllFinish "calldata-overwrite-with-0-if-oversized" $ test "calldata-overwrite-correct-size" $ do
        let contract = OpContract $ concat
              [ [OpPush (Lit 0xff),OpPush (Lit 8),OpMstore8] -- value, offs
              , [OpPush (Lit 10),OpPush (Lit 0),OpPush (Lit 0), OpCalldatacopy] -- size, offs, destOffs
              , [OpPush (Lit 10),OpPush (Lit 0x0),OpReturn] -- datasize, offset
              ]
        checkTraceAndOutputs contract 40000 (BS.pack [1, 2, 3, 4, 5, 6])
      , after AllFinish "calldata-overwrite-correct-size" $ test "calldata-offset-copy" $ do
        let contract = OpContract $ concat
              [ [OpPush (Lit 0xff),OpPush (Lit 8),OpMstore8] -- value, offs
              , [OpPush (Lit 0xff),OpPush (Lit 1),OpMstore8] -- value, offs
              , [OpPush (Lit 10),OpPush (Lit 4),OpPush (Lit 0), OpCalldatacopy] -- size, offs, destOffs
              , [OpPush (Lit 10),OpPush (Lit 0x0),OpReturn] -- datasize, offset
              ]
        checkTraceAndOutputs contract 40000 (BS.pack [1, 2, 3, 4, 5, 6])
    ]

checkTraceAndOutputs :: App m => OpContract -> Int -> ByteString -> m ()
checkTraceAndOutputs contract gasLimit txData = do
  tmpDir <- liftIO getCanonicalTemporaryDirectory
  evmDir <- liftIO $ createTempDirectory tmpDir "evm-trace"
  evmtoolResult <- liftIO $ getEVMToolRet evmDir contract txData gasLimit
  hevmRun <- getHEVMRet contract txData gasLimit
  evmtoolTraceOutput <- fmap fromJust $ liftIO $ getTraceOutput evmDir evmtoolResult
  case hevmRun of
    (Right (expr, hevmTrace, hevmTraceResult)) -> liftIO $ do
      let
        concretize :: Expr Buf -> Expr a ->  Expr a
        concretize c a = mapExpr go a
          where
            go :: Expr a -> Expr a
            go = \case
                       AbstractBuf "calldata" -> c
                       y -> y
        concretizedExpr = map (concretize (ConcreteBuf txData)) $ expr
        simplConcExpr = map Expr.simplify concretizedExpr
        getReturnVal :: Expr End -> Maybe ByteString
        getReturnVal (Success _ _ (ConcreteBuf bs) _) = Just bs
        getReturnVal _ = Nothing
        simplConcrExprRetval = mapMaybe getReturnVal simplConcExpr
      traceOK <- compareTraces hevmTrace (evmtoolTraceOutput.trace)
      -- putStrLn $ "HEVM trace   : " <> show hevmTrace
      -- putStrLn $ "evmtool trace: " <> show (evmtoolTraceOutput.trace)
      assertEqual "Traces and gas must match" traceOK True
      let resultOK = evmtoolTraceOutput.output.output == hevmTraceResult.out
      if resultOK then liftIO $ do
        putStrLn $ "HEVM & evmtool's outputs match: '" <> (bsToHex $ bssToBs evmtoolTraceOutput.output.output) <> "'"
        assertBool "Cannot have more than one success return value" (length simplConcrExprRetval <= 1)
        if null simplConcrExprRetval || (simplConcrExprRetval !! 0) == (bssToBs hevmTraceResult.out)
           then do
             putStr "OK, symbolic interpretation -> concrete calldata -> Expr.simplify gives the same answer."
             if null simplConcrExprRetval then putStrLn ", but it was a Nothing, so not strong equivalence"
                                          else putStrLn ""
           else do
             putStrLn $ "original expr                    : " <> (show expr)
             putStrLn $ "concretized expr                 : " <> (show concretizedExpr)
             putStrLn $ "simplified concretized expr      : " <> (show simplConcExpr)
             putStrLn $ "evmtoolTraceOutput.output.output : " <> (show (evmtoolTraceOutput.output.output))
             putStrLn $ "HEVM trace result output         : " <> (bsToHex (bssToBs hevmTraceResult.out))
             putStrLn $ "ret value computed via symb+conc : " <> (bsToHex (simplConcrExprRetval !! 0))
             assertEqual "Simplified, concretized expression must match evmtool's output." True False
      else do
        putStrLn $ "Name of trace file: " <> (getTraceFileName evmDir $ fromJust evmtoolResult)
        putStrLn $ "HEVM result  :" <> (show hevmTraceResult)
        T.putStrLn $ "HEVM result: " <> (formatBinary $ bssToBs hevmTraceResult.out)
        T.putStrLn $ "evm result : " <> (formatBinary $ bssToBs evmtoolTraceOutput.output.output)
        putStrLn $ "HEVM result len: " <> (show (BS.length $ bssToBs hevmTraceResult.out))
        putStrLn $ "evm result  len: " <> (show (BS.length $ bssToBs evmtoolTraceOutput.output.output))
      assertEqual "Contract exec successful. HEVM & evmtool's outputs must match" resultOK True
    Left (evmerr, hevmTrace) -> liftIO $ do
      putStrLn $ "HEVM contract exec issue: " <> (show evmerr)
      -- putStrLn $ "evmtool result was: " <> show (fromJust evmtoolResult)
      -- putStrLn $ "output by evmtool is: '" <> bsToHex evmtoolTraceOutput.toOutput.output <> "'"
      traceOK <- compareTraces hevmTrace (evmtoolTraceOutput.trace)
      assertEqual "Traces and gas must match" traceOK True
  liftIO $ removeDirectoryRecursive evmDir

-- GasLimitInt
newtype GasLimitInt = GasLimitInt (Int)
  deriving (Show, Eq)

instance Arbitrary GasLimitInt where
  arbitrary = do
    let mkLimit = chooseInt (50000, 0xfffff)
    fmap GasLimitInt mkLimit

-- GenTxDataRaw
newtype TxDataRaw = TxDataRaw ([Int])
  deriving (Show, Eq)

instance Arbitrary TxDataRaw where
  arbitrary = do
    let
      txDataRaw = sized $ \n -> vectorOf (10*n+5) $ chooseInt (0,255)
    fmap TxDataRaw txDataRaw
