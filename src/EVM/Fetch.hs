
module EVM.Fetch where

import EVM (initialContract, unknownContract)
import EVM.ABI
import EVM.FeeSchedule (feeSchedule)
import EVM.Format (hexText)
import EVM.SMT
import EVM.Solvers
import EVM.Types
import EVM (emptyContract)

import Optics.Core

import Control.Monad.Trans.Maybe
import Control.Applicative (Alternative(..))
import Data.Aeson hiding (Error)
import Data.Aeson.Optics
import Data.ByteString qualified as BS
import Data.Text (Text, unpack, pack)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.List (foldl')
import Data.Vector qualified as RegularVector
import Network.Wreq
import Network.Wreq.Session (Session)
import Network.Wreq.Session qualified as Session
import Numeric.Natural (Natural)
import System.Environment (lookupEnv, getEnvironment)
import System.Process
import Control.Monad.IO.Class
import Control.Monad (when)
import EVM.Effects
import qualified EVM.Expr as Expr
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.ByteString.Base16 qualified as BS16
import qualified Data.ByteString.Lazy as BSL
import Data.ByteString.Char8 qualified as Char8

-- | Abstract representation of an RPC fetch request
data RpcQuery a where
  QueryCode    :: Addr         -> RpcQuery BS.ByteString
  QueryBlock   ::                 RpcQuery Block
  QueryBalance :: Addr         -> RpcQuery W256
  QueryNonce   :: Addr         -> RpcQuery W64
  QuerySlot    :: Addr -> W256 -> RpcQuery W256
  QueryChainId ::                 RpcQuery W256

data BlockNumber = Latest | BlockNumber W256
  deriving (Show, Eq)

deriving instance Show (RpcQuery a)

data RPCContract = RPCContract
  { mcCode    :: BS.ByteString
  , mcNonce   :: W64
  , mcBalance :: W256
  }
  deriving (Eq, Show)

data RpcInfo = RpcInfo
  { blockNumURL  :: Maybe (BlockNumber, Text) -- ^ (block number, RPC url)
  , mockContract :: Maybe (Map.Map Addr RPCContract) -- ^ mock contracts (addr -> contract)
  , mockSlot     :: Maybe (Map.Map (Addr, W256) W256) -- ^ mock storage slots (addr, slot) -> value
  , mockBlock    :: Maybe (Map.Map W256 Block) -- ^ mock blocks (block number -> block)
  }
  deriving (Show)
instance Semigroup RpcInfo where
  RpcInfo a1 a2 a3 a4 <> RpcInfo b1 b2 b3 b4 =
    RpcInfo (a1 <|> b1) (a2 <|> b2) (a3 <|> b3) (a4 <|> b4)
instance Monoid RpcInfo where
  mempty = RpcInfo Nothing Nothing Nothing Nothing

rpc :: String -> [Value] -> Value
rpc method args = object
  [ "jsonrpc" .= ("2.0" :: String)
  , "id"      .= Number 1
  , "method"  .= method
  , "params"  .= args
  ]

class ToRPC a where
  toRPC :: a -> Value

instance ToRPC Addr where
  toRPC = String . pack . show

instance ToRPC W256 where
  toRPC = String . pack . show

instance ToRPC Bool where
  toRPC = Bool

instance ToRPC BlockNumber where
  toRPC Latest          = String "latest"
  toRPC (EVM.Fetch.BlockNumber n) = String . pack $ show n

readText :: Read a => Text -> a
readText = read . unpack

fetchQuery
  :: Show a
  => BlockNumber
  -> (Value -> IO (Maybe Value))
  -> RpcQuery a
  -> IO (Maybe a)
fetchQuery n f q =
  case q of
    QueryCode addr -> do
        m <- f (rpc "eth_getCode" [toRPC addr, toRPC n])
        pure $ do
          t <- preview _String <$> m
          hexText <$> t
    QueryNonce addr -> do
        m <- f (rpc "eth_getTransactionCount" [toRPC addr, toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
    QueryBlock -> do
      m <- f (rpc "eth_getBlockByNumber" [toRPC n, toRPC False])
      pure $ m >>= parseBlock
    QueryBalance addr -> do
        m <- f (rpc "eth_getBalance" [toRPC addr, toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
    QuerySlot addr slot -> do
        m <- f (rpc "eth_getStorageAt" [toRPC addr, toRPC slot, toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
    QueryChainId -> do
        m <- f (rpc "eth_chainId" [toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t

parseBlock :: (AsValue s, Show s) => s -> Maybe Block
parseBlock j = do
  coinbase   <- LitAddr . readText <$> j ^? key "miner" % _String
  timestamp  <- Lit . readText <$> j ^? key "timestamp" % _String
  number     <- Lit . readText <$> j ^? key "number" % _String
  gasLimit   <- readText <$> j ^? key "gasLimit" % _String
  let
   baseFee = readText <$> j ^? key "baseFeePerGas" % _String
   -- It seems unclear as to whether this field should still be called mixHash or renamed to prevRandao
   -- According to https://github.com/ethereum/EIPs/blob/master/EIPS/eip-4399.md it should be renamed
   -- but alchemy is still returning mixHash
   mixhash = readText <$> j ^? key "mixHash" % _String
   prevRandao = readText <$> j ^? key "prevRandao" % _String
   difficulty = readText <$> j ^? key "difficulty" % _String
   prd = case (prevRandao, mixhash, difficulty) of
     (Just p, _, _) -> p
     (Nothing, Just mh, Just 0x0) -> mh
     (Nothing, Just _, Just d) -> d
     _ -> internalError "block contains both difficulty and prevRandao"
  -- default codesize, default gas limit, default feescedule
  pure $ Block coinbase timestamp number prd gasLimit (fromMaybe 0 baseFee) 0xffffffff feeSchedule

instance ToJSON Block where
  toJSON (Block coinbase timestamp number prevRandao gaslimit baseFee maxCodeSize _) =
    object
      [ "coinbase" .= unExpr coinbase
      , "timestamp" .= unExpr2 timestamp
      , "number" .= unExpr2 number
      , "prevRandao" .= prevRandao
      , "gaslimit" .= gaslimit
      , "baseFee" .= baseFee
      , "maxCodeSize" .= maxCodeSize
      ]
    where
      unExpr2 :: Expr EWord -> W256
      unExpr2 (Lit n)     = n
      unExpr2 _           = internalError "Block fields must be concrete"
      unExpr :: Expr EAddr -> Addr
      unExpr (LitAddr a) = a
      unExpr _           = internalError "Block fields must be concrete"

instance FromJSON Block where
  parseJSON = withObject "Block" $ \v ->
    Block
      <$> (LitAddr <$> v .: "coinbase")
      <*> (Lit <$> v .: "timestamp")
      <*> (Lit <$> v .: "number")
      <*> v .: "prevRandao"
      <*> v .: "gaslimit"
      <*> v .: "baseFee"
      <*> v .: "maxCodeSize"
      <*> pure feeSchedule

data MockData = MockData
  { mockContract :: Maybe (Map.Map Addr RPCContract) -- ^ mock contracts (addr -> contract)
  , mockSlot     :: Maybe (Map.Map (Addr, W256) W256) -- ^ mock storage slots (addr, slot) -> value
  , mockBlock    :: Maybe (Map.Map W256 Block) -- ^ mock blocks (block number -> block)
  }
instance Semigroup MockData where
  MockData a1 a2 a3 <> MockData b1 b2 b3 =
    MockData (a1 <|> b1) (a2 <|> b2) (a3 <|> b3)
instance Monoid MockData where
  mempty = MockData Nothing Nothing Nothing
instance ToJSON RPCContract where
  toJSON (RPCContract code nonce balance) = object
    [ "mcCode" .= (T.pack $ "0x" ++ (concatMap (paddedShowHex 2) . BS.unpack $ code))
    , "mcNonce" .= nonce
    , "mcBalance" .= balance
    ]

instance FromJSON RPCContract where
  parseJSON = withObject "RPCContract" $ \v -> do
    codeHex <- v .: "mcCode"
    case (BS16.decodeBase16Untyped . strip0x . T.encodeUtf8) codeHex of
       Left _ -> fail "Invalid hex encoding for mcCode"
       Right bs -> RPCContract bs <$> v .: "mcNonce" <*> v .: "mcBalance"
    where
      strip0x :: BS.ByteString -> BS.ByteString
      strip0x bs = if "0x" `Char8.isPrefixOf` bs then Char8.drop 2 bs else bs

instance ToJSON MockData where
  toJSON (MockData contracts slots blocks) = object
    [ "mockContract" .= contracts
    , "mockSlot" .= slots
    , "mockBlock" .= blocks
    ]

instance FromJSON MockData where
  parseJSON = withObject "MockData" $ \v ->
    MockData <$> v .:? "mockContract" <*> v .:? "mockSlot" <*> v .:? "mockBlock"

readMockData :: FilePath -> IO (Either String MockData)
readMockData filePath = do
  jsonData <- BSL.readFile filePath
  pure $ eitherDecode jsonData

writeMockDataToFile :: FilePath -> MockData -> IO ()
writeMockDataToFile filePath mockData = do
  let jsonData = encodePretty mockData
  BSL.writeFile filePath jsonData
  putStrLn $ "Successfully wrote JSON to: " ++ filePath

fetchWithSession :: Text -> Session -> Value -> IO (Maybe Value)
fetchWithSession url sess x = do
  r <- asValue =<< Session.post sess (unpack url) x
  pure (r ^? (lensVL responseBody) % key "result")

fetchContractWithSession :: Config -> BlockNumber -> Text -> Addr -> Session -> IO (Maybe Contract)
fetchContractWithSession conf n url addr sess = runMaybeT $ do
  let fetch :: Show a => RpcQuery a -> IO (Maybe a)
      fetch = fetchQuery n (fetchWithSession url sess)
      fname  = "fetched_contract_" ++ show addr ++ ".json"
  code    <- MaybeT $ fetch (QueryCode addr)
  nonce   <- MaybeT $ fetch (QueryNonce addr)
  balance <- MaybeT $ fetch (QueryBalance addr)
  when (conf.debug) $ liftIO $ writeMockDataToFile fname (MockData (Just (Map.singleton addr (RPCContract code nonce balance))) Nothing Nothing)
  pure $ makeContractFromRPC (RPCContract code nonce balance)

makeContractFromRPC :: RPCContract -> Contract
makeContractFromRPC (RPCContract code nonce balance) =
    initialContract (RuntimeCode (ConcreteRuntimeCode code))
      & set #nonce    (Just nonce)
      & set #balance  (Lit balance)
      & set #external True

fetchSlotWithSession :: BlockNumber -> Text -> Session -> Addr -> W256 -> IO (Maybe W256)
fetchSlotWithSession n url sess addr slot =
  fetchQuery n (fetchWithSession url sess) (QuerySlot addr slot)

fetchBlockWithSession :: Config -> BlockNumber -> Text -> Session -> IO (Maybe Block)
fetchBlockWithSession conf n url sess = do
  ret <- fetchQuery n (fetchWithSession url sess) QueryBlock
  when (conf.debug) $ case n of
    Latest -> pure () -- do not save latest block to file
    EVM.Fetch.BlockNumber bn -> case ret of
      Just v -> let fname = "fetched_block_" ++ show bn ++ ".json"
        in writeMockDataToFile fname (MockData Nothing Nothing (Just (Map.singleton bn v)))
      Nothing -> pure ()
  pure ret

fetchBlockFrom :: Config -> BlockNumber -> Text -> IO (Maybe Block)
fetchBlockFrom conf n url = do
  when (conf.debug) $ putStrLn $ "Fetching block " ++ show n ++ " from " ++ unpack url
  sess <- Session.newAPISession
  fetchBlockWithSession conf n url sess

fetchContractFrom :: Config -> BlockNumber -> Text -> Addr -> IO (Maybe Contract)
fetchContractFrom conf n url addr = do
  sess <- Session.newAPISession
  fetchContractWithSession conf n url addr sess

fetchSlotFrom :: Config -> BlockNumber -> Text -> Addr -> W256 -> IO (Maybe W256)
fetchSlotFrom conf n url addr slot = do
  sess <- Session.newAPISession
  ret <- fetchSlotWithSession n url sess addr slot
  when (conf.debug) $ do
    let fname = "fetched_slot_" ++ show addr ++ "_" ++ show slot ++ ".json"
    case ret of
      Just v -> writeMockDataToFile fname (MockData Nothing (Just (Map.singleton (addr, slot) v)) Nothing)
      Nothing -> pure ()
  pure ret

-- Only used for testing (test.hs, BlockchainTests.hs)
zero :: Natural -> Maybe Natural -> Fetcher t m s
zero smtjobs smttimeout q =
  withSolvers Z3 smtjobs 1 smttimeout $ \s ->
    oracle s mempty q

-- SMT solving + RPC data fetching + reading from environment
oracle :: App m => SolverGroup -> RpcInfo -> Fetcher t m s
oracle solvers rpcInfo q = do
  case q of
    PleaseDoFFI vals envs continue -> case vals of
       cmd : args -> do
          existingEnv <- liftIO getEnvironment
          let mergedEnv = Map.toList $ Map.union envs $ Map.fromList existingEnv
          let process = (proc cmd args :: CreateProcess) { env = Just mergedEnv }
          (_, stdout', _) <- liftIO $ readCreateProcessWithExitCode process ""
          pure . continue . encodeAbiValue $
            AbiTuple (RegularVector.fromList [ AbiBytesDynamic . hexText . pack $ stdout'])
       _ -> internalError (show vals)

    PleaseAskSMT branchcondition pathconditions continue -> do
         let pathconds = foldl' PAnd (PBool True) pathconditions
         -- Is is possible to satisfy the condition?
         continue <$> checkBranch solvers (branchcondition ./= (Lit 0)) pathconds

    PleaseGetSols symExpr numBytes pathconditions continue -> do
         let pathconds = foldl' PAnd (PBool True) pathconditions
         continue <$> getSolutions solvers symExpr numBytes pathconds

    PleaseFetchContract addr base continue -> do
      conf <- readConfig
      when (conf.debug) $ liftIO $ putStrLn $ "Fetching contract at " ++ show addr
      when (addr == 0 && conf.verb > 0) $ liftIO $ putStrLn "Warning: fetching contract at address 0"
      contract <- case rpcInfo.mockContract >>= Map.lookup addr of
        Just c  -> do
          when (conf.debug) $ liftIO $ putStrLn $ "Using mocked contract at " ++ show addr
          pure $ Just (makeContractFromRPC c)
        Nothing -> case rpcInfo.blockNumURL of
            Nothing -> let
              c = case base of
                AbstractBase -> unknownContract (LitAddr addr)
                EmptyBase -> emptyContract
              in pure $ Just c
            Just (block, url) -> liftIO $ fetchContractFrom conf block url addr
      case contract of
        Just x -> pure $ continue x
        Nothing -> internalError $ "oracle error: " ++ show q

    PleaseFetchSlot addr slot continue -> do
      conf <- readConfig
      when (conf.debug) $ liftIO $ putStrLn $ "Fetching slot " <> (show slot) <> " at " <> (show addr)
      when (addr == 0 && conf.verb > 0) $ liftIO $ putStrLn "Warning: fetching slot from a contract at address 0"
      case rpcInfo.mockSlot >>= Map.lookup (addr, slot) of
        Just v  -> do
          when (conf.debug) $ liftIO $ putStrLn $ "Using mocked slot value for slot " <> show slot <> " at " <> show addr
          pure $ continue v
        Nothing -> case rpcInfo.blockNumURL of
            Nothing -> pure $ continue 0
            Just (block, url) ->
             liftIO $ fetchSlotFrom conf block url addr slot >>= \case
               Just x  -> pure $ continue x
               Nothing -> internalError $ "oracle error: " ++ show q

    PleaseReadEnv variable continue -> do
      value <- liftIO $ lookupEnv variable
      pure . continue $ fromMaybe "" value

type Fetcher t m s = App m => Query t s -> m (EVM t s ())

getSolutions :: forall m . App m => SolverGroup -> Expr EWord -> Int -> Prop -> m (Maybe [W256])
getSolutions solvers symExprPreSimp numBytes pathconditions = do
  conf <- readConfig
  liftIO $ do
    let symExpr = Expr.concKeccakSimpExpr symExprPreSimp
    -- when conf.debug $ putStrLn $ "Collecting solutions to symbolic query: " <> show symExpr
    ret <- collectSolutions symExpr pathconditions conf
    case ret of
      Nothing -> pure Nothing
      Just r -> case length r of
        0 -> pure Nothing
        _ -> pure $ Just r
    where
      collectSolutions :: Expr EWord -> Prop -> Config -> IO (Maybe [W256])
      collectSolutions symExpr conds conf = do
        let smt2 = assertProps conf [(PEq (Var "multiQueryVar") symExpr) .&& conds]
        checkMulti solvers smt2 $ MultiSol { maxSols = conf.maxWidth , numBytes = numBytes , var = "multiQueryVar" }

-- | Checks which branches are satisfiable, checking the pathconditions for consistency
-- if the third argument is true.
-- When in debug mode, we do not want to be able to navigate to dead paths,
-- but for normal execution paths with inconsistent pathconditions
-- will be pruned anyway.
checkBranch :: App m => SolverGroup -> Prop -> Prop -> m BranchCondition
checkBranch solvers branchcondition pathconditions = do
  let props = [pathconditions .&& branchcondition]
  checkSatWithProps solvers props >>= \case
    -- the condition is unsatisfiable
    (Qed, _) -> -- if pathconditions are consistent then the condition must be false
      pure $ Case False
    -- Sat means its possible for condition to hold
    (Cex {}, _) -> do -- is its negation also possible?
      let propsNeg = [pathconditions .&& (PNeg branchcondition)]
      checkSatWithProps solvers propsNeg >>= \case
        -- No. The condition must hold
        (Qed, _) -> pure $ Case True
        -- Yes. Both branches possible
        (Cex {}, _) -> pure UnknownBranch
        -- If the query times out, or can't be executed (e.g. symbolic copyslice) we simply explore both paths
        _ -> pure UnknownBranch
    -- If the query times out, or can't be executed (e.g. symbolic copyslice) we simply explore both paths
    _ -> pure UnknownBranch
