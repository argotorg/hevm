module EVM.Test.BlockchainTests (prepareTests, problematicTests, Case, vmForCase, checkExpectation, allTestCases) where

import EVM (initialContract, makeVm, setEIP4788Storage)
import EVM.Concrete qualified as EVM
import EVM.Effects
import EVM.Expr (maybeLitAddrSimp)
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified
import EVM.Solvers (withSolvers)
import EVM.SMT.Types (Solver(..))
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
  { vmOpts      :: VMOpts Concrete
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
      let fetcher q = withSolvers Z3 0 1 (Just 0) $ \s -> EVM.Fetch.noRpcFetcher s q
      exec <- toIO $ runVMTest fetcher x
      pure $ testCase' name exec
    testCase' :: String -> Assertion -> TestTree
    testCase' name assertion =
      case Map.lookup name problematicTests of
        Just f -> f (testCase name assertion)
        Nothing -> testCase name assertion

rootDirectory :: IO FilePath
rootDirectory = do
  repo <- getEnv "HEVM_ETHEREUM_TESTS_REPO"
  let testsDir = "BlockchainTests/GeneralStateTests"
  pure $ repo </> testsDir

collectJsonFiles :: FilePath -> IO [FilePath]
collectJsonFiles rootDir = Find.find Find.always (Find.extension Find.==? ".json") rootDir

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


runVMTest :: App m => EVM.Fetch.Fetcher Concrete m -> Case -> m ()
runVMTest fetcher x = do
  -- traceVsGeth fname name x
  vm0 <- liftIO $ vmForCase x
  result <- EVM.Stepper.interpret fetcher vm0 EVM.Stepper.runFully
  writeTrace result
  let maybeReason = checkExpectation x result
  liftIO $ forM_ maybeReason (liftIO >=> assertFailure)

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
       })
      checkState
      postState
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

vmForCase :: Case -> IO (VM Concrete)
vmForCase x = do
  vm <- stToIO $ makeVm x.vmOpts
    -- TODO: why do we override contracts here instead of using VMOpts otherContracts?
    <&> set (#env % #contracts) (Map.mapKeys LitAddr $ Map.map makeContract x.checkContracts)
    -- TODO: we need to call this again because we override contracts in the
    -- previous line
    <&> setEIP4788Storage x.vmOpts
  pure $ initTx vm

forceConcreteAddrs :: Map (Expr EAddr) Contract -> Map Addr Contract
forceConcreteAddrs cs = Map.mapKeys
      (fromMaybe (internalError "Internal Error: unexpected symbolic address") . maybeLitAddrSimp)
      cs
