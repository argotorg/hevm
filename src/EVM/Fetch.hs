
module EVM.Fetch
  ( fetchContractWithSession
  , fetchBlockWithSession
  , oracle
  , Fetcher
  , RpcInfo (..)
  , EVM.Fetch.zero
  , readMockData
  , BlockNumber (..)
  , mkRpcInfo
  , mkSession
  , Session (..)
  , FetchCache (..)
  , addFetchCache
  ) where

import Prelude hiding (Foldable(..))

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
import Data.Foldable (Foldable(..))
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, fromJust)
import Data.Vector qualified as RegularVector
import Network.Wreq
import Network.Wreq.Session qualified as NetSession
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
import Control.Concurrent.MVar (MVar, newMVar, readMVar, modifyMVar_)

type Fetcher t m s = App m => Query t s -> m (EVM t s ())

data Session = Session
  { sess           :: NetSession.Session
  , latestBlockNum :: MVar (Maybe W256)
  , sharedCache    :: MVar FetchCache
  }

data FetchCache = FetchCache
  { contractCache :: Map.Map Addr Contract
  , slotCache     :: Map.Map (Addr, W256) W256
  , blockCache    :: Map.Map W256 Block
  }
instance Show FetchCache where
  show (FetchCache c s b) =
    "FetchCache { contractCache: " ++ show (Map.keys c) ++
    ", slotCache: " ++ show (Map.keys s) ++
    ", blockCache: " ++ show (Map.keys b) ++ " }"

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

mkRpcInfo :: Maybe (BlockNumber, Text) -> MockData -> RpcInfo
mkRpcInfo blockNumURL (MockData {..}) = RpcInfo blockNumURL mockContract mockSlot mockBlock

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

addFetchCache :: Session -> Addr -> Contract -> IO ()
addFetchCache sess address ctrct = do
  cache <- readMVar sess.sharedCache
  liftIO $ modifyMVar_ sess.sharedCache $ \c -> pure $ c { contractCache = (Map.insert address ctrct cache.contractCache) }

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

fetchWithSession :: Text -> NetSession.Session -> Value -> IO (Maybe Value)
fetchWithSession url sess x = do
  r <- asValue =<< NetSession.post sess (unpack url) x
  pure (r ^? (lensVL responseBody) % key "result")

fetchContractWithSession :: Config -> Session -> BlockNumber -> Text -> Addr -> IO (Maybe Contract)
fetchContractWithSession conf sess nPre url addr = do
  n <- getLatestBlockNum conf sess nPre url
  cache <- readMVar sess.sharedCache
  case Map.lookup addr cache.contractCache of
    Just c -> do
      when (conf.debug) $ putStrLn $ "-> Using cached contract at " ++ show addr
      pure $ Just c
    Nothing -> runMaybeT $ do
      let fetch :: Show a => RpcQuery a -> IO (Maybe a)
          fetch = fetchQuery n (fetchWithSession url sess.sess)
          fname  = "fetched_contract_" ++ show addr ++ ".json"
      code    <- MaybeT $ fetch (QueryCode addr)
      nonce   <- MaybeT $ fetch (QueryNonce addr)
      balance <- MaybeT $ fetch (QueryBalance addr)
      when (conf.debug) $ liftIO $ writeMockDataToFile fname (MockData (Just (Map.singleton addr (RPCContract code nonce balance))) Nothing Nothing)
      let contr = makeContractFromRPC (RPCContract code nonce balance)
      liftIO $ modifyMVar_ sess.sharedCache $ \c -> pure $ c { contractCache = (Map.insert addr contr cache.contractCache) }
      pure contr

-- In case the user asks for Latest, and we have not yet established what Latest is,
-- we fetch the block to find out. Otherwise, we update Latest to the value we have stored
getLatestBlockNum :: Config -> Session -> BlockNumber -> Text -> IO BlockNumber
getLatestBlockNum conf sess n url =
  case n of
   Latest -> do
     val <- readMVar sess.latestBlockNum
     case val of
        Nothing -> do
          blk <- internalBlockFetch conf sess Latest url
          case blk of
            Nothing -> pure Latest
            Just b -> do
              when (conf.debug) $ putStrLn $ "Setting latest block number to " ++ show b.number
              let m = forceLit b.number
              modifyMVar_ sess.latestBlockNum $ \_ -> pure $ Just m
              pure $ EVM.Fetch.BlockNumber m
        Just v -> pure $ EVM.Fetch.BlockNumber v
   _ -> pure n

makeContractFromRPC :: RPCContract -> Contract
makeContractFromRPC (RPCContract code nonce balance) =
    initialContract (RuntimeCode (ConcreteRuntimeCode code))
      & set #nonce    (Just nonce)
      & set #balance  (Lit balance)
      & set #external True

fetchSlotWithSession :: NetSession.Session -> BlockNumber -> Text -> Addr -> W256 -> IO (Maybe W256)
fetchSlotWithSession sess n url addr slot =
  fetchQuery n (fetchWithSession url sess) (QuerySlot addr slot)

fetchBlockWithSession :: Config -> Session  -> BlockNumber -> Text -> IO (Maybe Block)
fetchBlockWithSession conf sess nPre url = do
  n <- getLatestBlockNum conf sess nPre url
  internalBlockFetch conf sess n url

internalBlockFetch :: Config -> Session -> BlockNumber -> Text -> IO (Maybe Block)
internalBlockFetch conf sess n url = do
  when (conf.debug) $ putStrLn $ "Fetching block " ++ show n ++ " from " ++ unpack url
  ret <- fetchQuery n (fetchWithSession url sess.sess) QueryBlock
  case ret of
    Nothing -> pure ret
    Just b -> do
      let bn = forceLit b.number
      cache <- readMVar sess.sharedCache
      liftIO $ modifyMVar_ sess.sharedCache $ \c -> pure $ c { blockCache = (Map.insert bn b cache.blockCache) }
      when (conf.debug) $ do
        let fname = "fetched_block_" ++ show bn ++ ".json"
        writeMockDataToFile fname (MockData Nothing Nothing (Just (Map.singleton bn b)))
      pure ret

fetchSlotFrom :: App m => Session -> BlockNumber -> Text -> Addr -> W256 -> m (Maybe W256)
fetchSlotFrom sess nPre url addr slot = do
  conf <- readConfig
  n <- liftIO $ getLatestBlockNum conf sess nPre url
  cache <- liftIO $ readMVar sess.sharedCache
  case Map.lookup (addr, slot) cache.slotCache of
    Just s -> do
      when (conf.debug) $ liftIO $ putStrLn $ "-> Using cached slot value for slot " <> show slot <> " at " <> show addr
      pure $ Just s
    Nothing -> do
      ret <- liftIO $ fetchSlotWithSession sess.sess n url addr slot
      when (isJust ret) $ let val = fromJust ret in
        liftIO $ modifyMVar_ sess.sharedCache $ \c -> pure $ c { slotCache = (Map.insert (addr,slot) val cache.slotCache) }
      when (conf.debug) $ liftIO $ do
        let fname = "fetched_slot_" ++ show addr ++ "_" ++ show slot ++ ".json"
        case ret of
          Just v -> writeMockDataToFile fname (MockData Nothing (Just (Map.singleton (addr, slot) v)) Nothing)
          Nothing -> pure ()
      pure ret

mkSession :: App m => m Session
mkSession = do
  sess <- liftIO NetSession.newAPISession
  let emptyCache = FetchCache Map.empty Map.empty Map.empty
  cache <- liftIO $ newMVar emptyCache
  latestBlockNum <- liftIO $ newMVar Nothing
  pure $ Session sess latestBlockNum cache

-- Only used for testing (test.hs, BlockchainTests.hs)
zero :: Natural -> Maybe Natural -> Fetcher t m s
zero smtjobs smttimeout q = do
  sess <- mkSession
  withSolvers Z3 smtjobs 1 smttimeout $ \s ->
    oracle s (Just sess) mempty q

-- SMT solving + RPC data fetching + reading from environment
oracle :: forall t m s . App m => SolverGroup -> Maybe Session -> RpcInfo -> Fetcher t m s
oracle solvers preSess rpcInfo q = do
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

    PleaseFetchContract addr base continue -> withSession addr (continue (nothingContract base addr)) $ \sess -> do
      conf <- readConfig
      when (conf.debug) $ liftIO $ putStrLn $ "Fetching contract at " ++ show addr
      when (addr == 0 && conf.verb > 0) $ liftIO $ putStrLn "Warning: fetching contract at address 0"
      contract <- case rpcInfo.mockContract >>= Map.lookup addr of
        Just c  -> do
          when (conf.debug) $ liftIO $ putStrLn $ "Using mocked contract at " ++ show addr
          pure $ Just (makeContractFromRPC c)
        Nothing -> case rpcInfo.blockNumURL of
            Nothing -> pure $ Just $ nothingContract base addr
            Just (block, url) -> liftIO $ fetchContractWithSession conf sess block url addr
      case contract of
        Just x -> pure $ continue x
        Nothing -> internalError $ "oracle error: " ++ show q

    PleaseFetchSlot addr slot continue -> withSession addr (continue 0)$ \sess -> do
      conf <- readConfig
      when (conf.debug) $ liftIO $ putStrLn $ "Fetching slot " <> (show slot) <> " at " <> (show addr)
      when (addr == 0 && conf.verb > 0) $ liftIO $ putStrLn "Warning: fetching slot from a contract at address 0"
      case rpcInfo.mockSlot >>= Map.lookup (addr, slot) of
        Just v  -> do
          when (conf.debug) $ liftIO $ putStrLn $ "Using mocked slot value for slot " <> show slot <> " at " <> show addr
          pure $ continue v
        Nothing -> case rpcInfo.blockNumURL of
            Nothing -> pure $ continue 0
            Just (block, url) -> fetchSlotFrom sess block url addr slot >>= \case
               Just x  -> pure $ continue x
               Nothing -> internalError $ "oracle error: " ++ show q

    PleaseReadEnv variable continue -> do
      value <- liftIO $ lookupEnv variable
      pure . continue $ fromMaybe "" value

    where
      nothingContract base addr =
        case base of
          AbstractBase -> unknownContract (LitAddr addr)
          EmptyBase -> emptyContract
      withSession addr def f =
        case addr of
          -- special values such as 0, 0xdeadbeef, 0xacab, hevm cheatcodes, and the precompile addresses
          -- do not require a session, there is nothing deployed there, it's way too small or special, RPC would be pointless
          a | a <= 0xdeadbeef -> pure def
          0x7109709ECfa91a80626fF3989D68f67F5b1DD12D -> pure def
          _ -> case preSess of
            Just sess  -> f sess
            Nothing -> internalError $ "oracle: no session provided for fetch addr: " ++ show addr

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
    Qed -> -- if pathconditions are consistent then the condition must be false
      pure $ Case False
    -- Sat means its possible for condition to hold
    Cex {} -> do -- is its negation also possible?
      let propsNeg = [pathconditions .&& (PNeg branchcondition)]
      checkSatWithProps solvers propsNeg >>= \case
        -- No. The condition must hold
        Qed -> pure $ Case True
        -- Yes. Both branches possible
        Cex {} -> pure UnknownBranch
        -- If the query times out, or can't be executed (e.g. symbolic copyslice) we simply explore both paths
        _ -> pure UnknownBranch
    -- If the query times out, or can't be executed (e.g. symbolic copyslice) we simply explore both paths
    _ -> pure UnknownBranch
