module EVM.Test.BlockchainTestsAlt (prepareTests, problematicTests, Case, checkExpectation, allTestCases) where

import EVM.Concrete qualified as EVM
import EVM.ConcreteExecution qualified as CE (
  exec,
  RuntimeCode(..),
  CallData(..),
  CallValue(..),
  Transaction(..),
  BlockHeader(..),
  ExecutionContext(..),
  VMSnapshot(..),
  Account(..),
  Wei(..),
  Gas(..),
  Nonce(..)
  )
import EVM.Effects
import EVM.Transaction
import EVM.Types hiding (Block, Case, Env)

import Optics.Core
import Control.Arrow ((***), (&&&))
import Control.Monad
import Control.Monad.State.Strict
import Data.Aeson ((.:), (.:?), FromJSON (..))
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as Lazy
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe, isNothing, isJust)
import Data.Word (Word64)
import GHC.Generics (Generic)
import System.Environment (getEnv)
import System.FilePath.Find qualified as Find
import System.FilePath.Posix (makeRelative, (</>))
import Witch (into, unsafeInto)
import Witherable (Filterable, catMaybes)

import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

data Which = Pre | Post

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
  } deriving Show

data BlockchainContract = BlockchainContract
  { code    :: ByteStringS
  , nonce   :: W64
  , balance :: W256
  , storage :: Map W256 W256
  } deriving (Eq, Show, Generic)

instance FromJSON BlockchainContract

type BlockchainContracts = Map Addr BlockchainContract

data Case = Case
  { origin :: Addr
  , tx :: Transaction
  , block :: Block
  , checkContracts  :: BlockchainContracts
  , testExpectation :: BlockchainContracts
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
  groups <- forM (Map.toList cases) (\(f, subtests) -> testGroup (makeRelative rootDir f) <$> (process subtests))
  liftIO $ putStrLn "Loaded."
  pure $ testGroup "ethereum-tests" groups
  where
    process :: forall m . App m => (Map String Case) -> m [TestTree]
    process tests = forM (Map.toList tests) runTest

    runTest :: App m => (String, Case) -> m TestTree
    runTest (name, x) = do
      pure $ testCase' name (runVMTest x)
    testCase' :: String -> Assertion -> TestTree
    testCase' name assertion =
      case Map.lookup name problematicTests of
        Just f -> f (testCase name assertion)
        Nothing -> testCase name assertion

rootDirectory :: IO FilePath
rootDirectory = do
  repo <- getEnv "HEVM_ETHEREUM_TESTS_REPO"
  -- let testsDir = "BlockchainTests/GeneralStateTests/stBadOpcode"
  let testsDir = "BlockchainTests/GeneralStateTests/Cancun/stEIP1153-transientStorage"
  pure $ repo </> testsDir

collectJsonFiles :: FilePath -> IO [FilePath]
collectJsonFiles rootDir = Find.find Find.always (Find.extension Find.==? ".json") rootDir
-- collectJsonFiles rootDir = Find.find Find.always (Find.fileName Find.==? "01_tloadBeginningTxn.json") rootDir

allTestCases :: IO (Map FilePath (Map String Case))
allTestCases = do
  root <- rootDirectory
  jsons <- collectJsonFiles root
  cases <- forM jsons (\fname -> do
      fContents <- BS.readFile fname
      let parsed = case (parseBCSuite (Lazy.fromStrict fContents)) of
                    Left "No cases to check." -> mempty
                    Left _err -> mempty -- TODO: This should be an error
                    Right allTests -> allTests
      pure (fname, parsed)
    )
  pure $ Map.fromList cases

problematicTests :: Map String (TestTree -> TestTree)
problematicTests = Map.fromList
  [ ("loopMul_d0g0v0_Cancun", ignoreTestBecause "hevm is too slow")
  , ("loopMul_d1g0v0_Cancun", ignoreTestBecause "hevm is too slow")
  , ("loopMul_d2g0v0_Cancun", ignoreTestBecause "hevm is too slow")
  , ("CALLBlake2f_MaxRounds_d0g0v0_Cancun", ignoreTestBecause "very slow, bypasses timeout due time spent in FFI")

  , ("15_tstoreCannotBeDosd_d0g0v0_Cancun", ignoreTestBecause "slow test")
  , ("21_tstoreCannotBeDosdOOO_d0g0v0_Cancun", ignoreTestBecause "slow test")

  -- TODO: implement point evaluation, 0xa precompile, EIP-4844, Cancun
  , ("idPrecomps_d9g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d117g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d12g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d135g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d153g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d171g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d189g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d207g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d225g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d243g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d261g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d279g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d27g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d297g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d315g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d333g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d351g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d369g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d387g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d45g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d63g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d81g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("precompsEIP2929Cancun_d99g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("makeMoney_d0g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  , ("failed_tx_xcf416c53_d0g0v0_Cancun", ignoreTestBecause "EIP-4844 not implemented")
  ]


runVMTest :: Case -> IO ()
runVMTest test = do
  let (execContext, contracts) = executionContextFromCase
      (_, snapshot) = CE.exec execContext contracts
      maybeFailureReason = checkExpectation test snapshot
  forM_ maybeFailureReason (assertFailure =<<)

  where
    executionContextFromCase = (executionContext, accounts)
      where
        tx = test.tx
        block = test.block
        effectiveGasPrice = effectiveprice tx block.baseFee
        transaction = CE.Transaction (test.origin) (tx.toAddr) (CE.CallValue tx.value) (CE.CallData tx.txdata) (CE.Gas tx.gasLimit) effectiveGasPrice (priorityFee tx block.baseFee)
        blockHeader = CE.BlockHeader (block.coinbase) (block.timestamp) (block.number) (CE.Gas block.gasLimit) (block.mixHash) (block.baseFee)
        executionContext = CE.ExecutionContext transaction blockHeader
        accounts = Map.map asAccount test.checkContracts
        asAccount :: BlockchainContract -> CE.Account
        asAccount (BlockchainContract (ByteStringS bs) nonce balance storage) = CE.Account (CE.RuntimeCode bs) storage (CE.Wei balance) (CE.Nonce nonce)



checkExpectation :: Case -> CE.VMSnapshot -> Maybe (IO String)
checkExpectation x vm = let (okState, okBal, okNonce, okStor, okCode) = checkExpectedContracts vm x.testExpectation in
  if okState then Nothing else Just $ checkStateFail x (okBal, okNonce, okStor, okCode)
  where
    checkExpectedContracts :: CE.VMSnapshot -> BlockchainContracts -> (Bool, Bool, Bool, Bool, Bool)
    checkExpectedContracts vmSnapshot expected =
      let finalWorldState = finalContracts vmSnapshot
      in (finalWorldState ~= expected,
          (clearBalance <$> expected) ~= (clearBalance <$> finalWorldState),
          (clearNonce   <$> expected) ~= (clearNonce   <$> finalWorldState),
          (clearStorage <$> expected) ~= (clearStorage <$> finalWorldState),
          (clearCode    <$> expected) ~= (clearCode    <$> finalWorldState)
        )

    clearStorage :: BlockchainContract -> BlockchainContract
    clearStorage c = c { storage = mempty}
    clearBalance :: BlockchainContract -> BlockchainContract
    clearBalance c = c {balance = 0}
    clearNonce :: BlockchainContract -> BlockchainContract
    clearNonce c = c {nonce = 0}
    clearCode :: BlockchainContract -> BlockchainContract
    clearCode c = c {code = (ByteStringS BS.empty)}


    finalContracts :: CE.VMSnapshot -> BlockchainContracts
    finalContracts vm' = Map.map (\(CE.Account (CE.RuntimeCode code) storage (CE.Wei balance) (CE.Nonce nonce)) -> BlockchainContract (ByteStringS code) nonce balance (clearZeroStorage storage)) vm'.worldState

    clearZeroStorage = Map.filter (/= 0)


    -- quotient account state by nullness
    (~=) :: BlockchainContracts -> BlockchainContracts -> Bool
    (~=) cs1 cs2 =
        let nullAccount = BlockchainContract (ByteStringS BS.empty) 0 0 mempty
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
        actual = finalContracts vm

      putStrLn $ "-> Failing because of: " <> (unwords reason)
      putStrLn "-> Pre balance/state: "
      printContracts check
      putStrLn "-> Expected balance/state: "
      printContracts expected
      putStrLn "-> Actual balance/state: "
      printContracts actual
      pure (unwords reason)


instance FromJSON BlockchainCase where
  parseJSON (JSON.Object v) = BlockchainCase
    <$> v .: "blocks"
    <*> parseContracts Pre v
    <*> parseContracts Post v
    <*> v .: "network"
  parseJSON invalid =
    JSON.typeMismatch "GeneralState test case" invalid

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
    pure $ Block { coinbase, difficulty, mixHash, gasLimit
                 , baseFee = fromMaybe 0 baseFee, number, timestamp
                 , txs, beaconRoot = fromMaybe 0 beaconRoot
                 }
  parseJSON invalid =
    JSON.typeMismatch "Block" invalid

parseContracts :: Which -> JSON.Object -> JSON.Parser (BlockchainContracts)
parseContracts w v = v .: which >>= parseJSON
  where which = case w of
          Pre  -> "pre"
          Post -> "postState"

parseBCSuite :: Lazy.ByteString-> Either String (Map String Case)
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


splitEithers :: (Filterable f) => f (Either a b) -> (f a, f b)
splitEithers =
  (catMaybes *** catMaybes)
  . (fmap fst &&& fmap snd)
  . (fmap (preview _Left &&& preview _Right))


data BlockchainError
  = TooManyBlocks
  | TooManyTxs
  | NoTxs
  | SignatureUnverified
  | InvalidTx
  | OldNetwork
  | FailedCreate
  deriving Show

errorFatal :: BlockchainError -> Bool
errorFatal TooManyBlocks = True
errorFatal TooManyTxs = True
errorFatal SignatureUnverified = True
errorFatal InvalidTx = True
errorFatal _ = False

fromBlockchainCase :: BlockchainCase -> Either BlockchainError Case
fromBlockchainCase (BlockchainCase blocks preState postState network) =
  case (blocks, network) of
    ([block], "Cancun") -> case block.txs of
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
    (Just origin, Just checkState) -> Right $ Case origin tx block checkState postState


checkTx :: Transaction -> Block -> BlockchainContracts -> Maybe (BlockchainContracts)
checkTx tx block prestate = do
  origin <- sender tx
  validateTx tx block prestate
  if (isJust tx.toAddr) then pure prestate
  else
    let senderNonce = (.nonce) <$> Map.lookup origin prestate
        addr  = case EVM.createAddress origin (fromJust senderNonce) of
                  (LitAddr a) -> a
                  _ -> internalError "Cannot happen"
        freshContract = BlockchainContract (ByteStringS "") 0 0 mempty
        (BlockchainContract (ByteStringS b) prevNonce _ _) = (fromMaybe freshContract $ Map.lookup addr prestate)
        nonEmptyAccount = not (BS.null b)
        badNonce = prevNonce /= 0
        initCodeSizeExceeded = BS.length tx.txdata > (unsafeInto maxCodeSize * 2)
    in
    if (badNonce || nonEmptyAccount || initCodeSizeExceeded) then mzero
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

effectiveprice :: Transaction -> W256 -> W256
effectiveprice tx baseFee = priorityFee tx baseFee + baseFee

maxBaseFee :: Transaction -> W256
maxBaseFee tx =
  case tx.txtype of
     EIP1559Transaction -> fromJust tx.maxFeePerGas
     _ -> fromJust tx.gasPrice

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
