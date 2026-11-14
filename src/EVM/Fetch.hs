
module EVM.Fetch
  ( fetchContractWithSession
  , fetchAccountWithSession
  , fetchBlockWithSession
  , fetchQuery
  , oracle
  , checkBranch
  , Fetcher
  , RpcInfo (..)
  , RpcQuery (..)
  , EVM.Fetch.zero
  , noRpc
  , noRpcFetcher
  , BlockNumber (..)
  , mkSession
  , mkSessionWithoutCache
  , Session (..)
  , FetchCache (..)
  , addFetchCache
  , saveCache
  , fetchChainId
  , CacheLocation (..)
  , withCachedSession
  , RPCContract (..)
  , makeContractFromRPC
  -- Below 4 are needed for Echidna
  , fetchSlotWithSession
  , fetchSlotWithCache
  , fetchWithSession
  , getCacheState
  , FetchStatus(..)
  , FetchResult(..)
  ) where

import Prelude hiding (Foldable(..))

import EVM (initialContract, unknownContract)
import EVM.ABI
import EVM.FeeSchedule (feeSchedule)
import EVM.Format (hexText)
import EVM.SMT
import EVM.Solvers
import EVM.Types hiding (ByteStringS)
import EVM.Types (ByteStringS(..))
import EVM (emptyContract, cheatCode, consoleAddr)

import Optics.Core
import GHC.Generics (Generic)
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing, doesFileExist, renameFile)
import System.IO (openTempFile, hClose)
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy as BSL
import Data.Bifunctor (first)
import Control.Exception (Exception, SomeException, SomeAsyncException(..), try, catches, Handler(..), throwIO, mask, uninterruptibleMask_, fromException, finally)

import Data.Aeson hiding (Error)
import Data.Aeson.Optics
import Data.ByteString qualified as BS
import Data.Text (Text, unpack, pack)
import Data.Text qualified as T
import Data.Foldable (Foldable(..))
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, fromJust, isNothing)
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Vector qualified as RegularVector
import Network.Wreq
import Network.Wreq.Session qualified as NetSession
import Numeric.Natural (Natural)
import System.Environment (lookupEnv, getEnvironment)
import System.Process
import Control.Monad.IO.Class
import Control.Monad (forM, forM_, when)
import Control.Monad.IO.Unlift (withRunInIO)
import EVM.Effects
import qualified EVM.Expr as Expr
import Control.Concurrent (threadDelay)
import Control.Concurrent.MVar (MVar, newMVar, newEmptyMVar, putMVar, readMVar, modifyMVar, modifyMVar_)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Data.Time.Clock (UTCTime, getCurrentTime, diffUTCTime, addUTCTime)
import System.Random (randomRIO)

type Fetcher t m = App m => Query t -> m (EVM t ())

data FetchStatus = Cached | Fresh
  deriving (Show, Eq)

data FetchResult a
  = FetchSuccess a FetchStatus
  | FetchFailure FetchStatus
  | FetchError Text
  deriving (Show, Eq)

data Session = Session
  { sess            :: NetSession.Session
  , latestBlockNum  :: MVar (Maybe W256)
  , sharedCache     :: MVar FetchCache
  , cacheDir        :: Maybe FilePath
  -- Track ephemeral failures (network errors, not found, etc.)
  -- These are NOT persisted to disk
  , failedContracts :: MVar (Set Addr)
  , failedSlots     :: MVar (Set (Addr, W256))
  -- Shared rate limit cooldown across workers. When any worker hits a
  -- rate limit, it sets a deadline; other workers wait before retrying.
  , rpcThrottle     :: IORef (Maybe UTCTime)
  -- | Microseconds before the first retry of a failed request, doubling for each further one
  , retryDelay      :: Int
  , slotsInFlight   :: InFlight (Addr, W256) (FetchResult W256)
  , accountsInFlight :: InFlight Addr (FetchResult RPCContract)
  }

-- | The fetches under way, each with where its result goes, so that callers racing on the
-- same state share one fetch
type InFlight k a = MVar (Map.Map k (MVar (Either SomeException a)))

data FetchCache = FetchCache
  { contractCache :: Map.Map Addr RPCContract
  , slotCache     :: Map.Map (Addr, W256) W256
  , blockCache    :: Map.Map W256 Block
  } deriving (Generic)


instance ToJSON FetchCache where
  toJSON (FetchCache cs ss bs) = object
    [ "contracts" .= Map.toList cs
    , "slots"     .= map (first (T.pack . show)) (Map.toList ss)
    , "blocks"    .= bs
    ]

instance FromJSON FetchCache where
  parseJSON = withObject "FetchCache" $ \v -> FetchCache
    <$> (Map.fromList <$> v .: "contracts")
    <*> (Map.fromList . map (first (read . T.unpack)) <$> v .: "slots")
    <*> (v .:? "blocks" .!= Map.empty)

instance Show FetchCache where
  show (FetchCache c s b) =
    "FetchCache { contractCache: " ++ show (Map.keys c) ++
    ", slotCache: " ++ show (Map.keys s) ++
    ", blockCache: " ++ show (Map.keys b) ++ " }"

data Signedness = Signed | Unsigned
  deriving (Show)

showDec :: Signedness -> W256 -> T.Text
showDec signed (W256 w) = T.pack (show (i :: Integer))
  where
    i = case signed of
          Signed   -> fromIntegral (fromIntegral w :: Int)
          Unsigned -> fromIntegral w

-- | Abstract representation of an RPC fetch request
data RpcQuery a where
  QueryCode    :: Addr         -> RpcQuery BS.ByteString
  QueryBlock   ::                 RpcQuery Block
  QueryBalance :: Addr         -> RpcQuery W256
  QueryNonce   :: Addr         -> RpcQuery W64
  QuerySlot    :: Addr -> W256 -> RpcQuery W256
  QueryChainId ::                 RpcQuery W256
  QueryStorageRoot :: Addr     -> RpcQuery W256

data BlockNumber = Latest | BlockNumber W256
  deriving (Show, Eq)

deriving instance Show (RpcQuery a)

data RPCContract = RPCContract
  { code    :: ByteStringS
  , nonce   :: W64
  , balance :: W256
  -- | Only fetched for accounts without code and nonce, where it decides CREATE collisions (EIP-7610)
  , storageRoot :: Maybe W256
  }
  deriving (Eq, Show, Generic)

instance ToJSON RPCContract

instance FromJSON RPCContract

newtype RpcInfo = RpcInfo { blockNumURL  :: Maybe (BlockNumber, Text)} -- ^ (block number, RPC url)
  deriving (Show)

noRpc :: RpcInfo
noRpc = RpcInfo Nothing

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

addFetchCache :: Session -> Addr -> RPCContract -> IO ()
addFetchCache sess address ctrct =
  modifyMVar_ sess.sharedCache $ \c -> pure $ c { contractCache = Map.insert address ctrct c.contractCache }

fetchQuery
  :: Show a
  => BlockNumber
  -> (Value -> IO (Either Text Value))
  -> RpcQuery a
  -> IO (Either Text a)
fetchQuery n f q =
  case q of
    QueryCode addr -> do
        m <- f (rpc "eth_getCode" [toRPC addr, toRPC n])
        pure $ m >>= \v -> maybeToRight "Parse error" (hexText <$> preview _String v)
    QueryNonce addr -> do
        m <- f (rpc "eth_getTransactionCount" [toRPC addr, toRPC n])
        pure $ m >>= \v -> maybeToRight "Parse error" (readText <$> preview _String v)
    QueryBlock -> do
      m <- f (rpc "eth_getBlockByNumber" [toRPC n, toRPC False])
      pure $ m >>= \v -> maybeToRight "Parse error" (parseBlock v)
    QueryBalance addr -> do
        m <- f (rpc "eth_getBalance" [toRPC addr, toRPC n])
        pure $ m >>= \v -> maybeToRight "Parse error" (readText <$> preview _String v)
    QuerySlot addr slot -> do
        m <- f (rpc "eth_getStorageAt" [toRPC addr, toRPC slot, toRPC n])
        pure $ m >>= \v -> maybeToRight "Parse error" (readText <$> preview _String v)
    QueryChainId -> do
        m <- f (rpc "eth_chainId" [])
        pure $ m >>= \v -> maybeToRight "Parse error" (readText <$> preview _String v)
    QueryStorageRoot addr -> do
        m <- f (rpc "eth_getProof" [toRPC addr, Array mempty, toRPC n])
        pure $ m >>= \v -> maybeToRight "Parse error" (readText <$> v ^? key "storageHash" % _String)

maybeToRight :: b -> Maybe a -> Either b a
maybeToRight _ (Just x) = Right x
maybeToRight y Nothing  = Left y

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
  pure $ Block coinbase timestamp number (Lit prd) gasLimit (Lit (fromMaybe 0 baseFee)) 0xffffffff feeSchedule

instance ToJSON Block where
  toJSON (Block coinbase timestamp number prevRandao gaslimit baseFee maxCodeSize _) =
    object
      [ "coinbase" .= unExpr coinbase
      , "timestamp" .= unExpr2 timestamp
      , "number" .= unExpr2 number
      , "prevRandao" .= unExpr2 prevRandao
      , "gaslimit" .= gaslimit
      , "baseFee" .= unExpr2 baseFee
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
      <*> (Lit <$> v .: "prevRandao")
      <*> v .: "gaslimit"
      <*> (Lit <$> v .: "baseFee")
      <*> v .: "maxCodeSize"
      <*> pure feeSchedule

-- | Wait if there's an active cooldown from a recent rate limit.
waitForCooldown :: IORef (Maybe UTCTime) -> IO ()
waitForCooldown ref = do
  mDeadline <- readIORef ref
  case mDeadline of
    Nothing -> pure ()
    Just deadline -> do
      now <- getCurrentTime
      let diff = diffUTCTime deadline now
      when (diff > 0) $
        threadDelay (ceiling (realToFrac diff * 1_000_000 :: Double))

-- | Set a cooldown deadline. Keeps the longer of existing vs new deadline.
setCooldown :: IORef (Maybe UTCTime) -> Int -> IO ()
setCooldown ref delayUs = do
  now <- getCurrentTime
  let newDeadline = addUTCTime (realToFrac delayUs / 1_000_000) now
  atomicModifyIORef' ref $ \existing ->
    let deadline = case existing of
          Just d | d > newDeadline -> d
          _ -> newDeadline
    in (Just deadline, ())

-- | Retry an IO action on exception with exponential backoff + jitter.
-- Uses a shared cooldown so all workers back off together.
-- Only retries synchronous exceptions (network errors, HTTP 429, etc.).
-- Re-throws all async exceptions (Timeout, ThreadKilled).
-- RPC-level errors (Left) are NOT retried — they pass through.
withRetry :: Bool -> Int -> IORef (Maybe UTCTime) -> IO (Either Text a) -> IO (Either Text a)
withRetry debug firstDelay throttle action = go 1
  where
  maxRetries = 5 :: Int
  go attempt = do
    waitForCooldown throttle
    result <- catches (Right <$> action)
      [ Handler $ \(SomeAsyncException e) -> throwIO e
      , Handler $ \(e :: SomeException) -> pure $ Left e
      ]
    case result of
      Right r -> pure r
      Left e
        | attempt <= maxRetries -> do
            let baseDelayUs = firstDelay * (2 ^ (attempt - 1)) :: Int
            jitter <- randomRIO (0, baseDelayUs)
            let delayUs = baseDelayUs + jitter
            setCooldown throttle delayUs
            when debug $ putStrLn $
              "RPC retry " <> show attempt <> "/" <> show maxRetries
              <> " in " <> show (delayUs `div` 1000) <> "ms"
            threadDelay delayUs
            go (attempt + 1)
        | otherwise ->
            pure $ Left $ pack $ show e

-- | Like fetchWithSession but with retry + shared cooldown from Session.
-- JSON-RPC errors that ask to slow down are retried too.
fetchWithRetry :: Bool -> Text -> Session -> Value -> IO (Either Text Value)
fetchWithRetry debug url session x = withRetry debug session.retryDelay session.rpcThrottle $
  postRpc url session.sess x >>= \case
    Left (Just err) | rateLimited err -> throwIO (RateLimited (pack (show err)))
    r -> pure (first rpcError r)

fetchWithSession :: Text -> NetSession.Session -> Value -> IO (Either Text Value)
fetchWithSession url sess x = first rpcError <$> postRpc url sess x

-- | The result of a JSON-RPC request, or its error, if any
postRpc :: Text -> NetSession.Session -> Value -> IO (Either (Maybe Value) Value)
postRpc url sess x = do
  r <- asValue =<< NetSession.post sess (unpack url) x
  let body = r ^. (lensVL responseBody)
  pure $ case body ^? key "result" of
    Just val -> Right val
    Nothing -> Left (body ^? key "error")

rpcError :: Maybe Value -> Text
rpcError = maybe "Unknown RPC error" (pack . show)

newtype RateLimited = RateLimited Text

instance Show RateLimited where
  show (RateLimited e) = unpack e

instance Exception RateLimited

-- | Whether a JSON-RPC error is a provider's rate limit: Alchemy's 429, Infura's -32005 and
-- QuickNode's -32007 codes, or a message saying so
rateLimited :: Value -> Bool
rateLimited err = code `elem` map Just [429, -32005, -32007]
  || any (`T.isInfixOf` T.toLower msg) ["rate limit", "too many requests"]
  where
    code = err ^? key "code" % _Integer
    msg = fromMaybe "" (err ^? key "message" % _String)

-- | Like 'fetchAccountWithSession', but an account without code is a 'FetchFailure'
fetchContractWithSession :: Config -> Session -> BlockNumber -> Text -> Addr -> IO (FetchResult RPCContract)
fetchContractWithSession conf sess nPre url addr =
  fetchAccountWithSession conf sess nPre url addr >>= \case
    FetchSuccess c status | c.code == ByteStringS BS.empty -> do
      modifyMVar_ sess.failedContracts $ pure . Set.insert addr
      pure (FetchFailure status)
    r -> pure r

-- | Fetches any account, including ones without code (EOAs and nonexistent accounts)
fetchAccountWithSession :: Config -> Session -> BlockNumber -> Text -> Addr -> IO (FetchResult RPCContract)
fetchAccountWithSession conf sess nPre url addr =
  fetchOnce sess.accountsInFlight addr cached $ do
    n <- getLatestBlockNum conf sess nPre url
    when (conf.debug) $ putStrLn $ "-> Fetching account at " ++ show addr
    let fetch :: Show a => RpcQuery a -> IO (Either Text a)
        fetch = fetchQuery n (fetchWithRetry conf.debug url sess)

    codeRes <- fetch (QueryCode addr)
    nonceRes <- fetch (QueryNonce addr)
    balRes <- fetch (QueryBalance addr)

    case (codeRes, nonceRes, balRes) of
      (Right c, Right no, Right ba) -> do
        -- nodes without eth_getProof are taken to report empty storage
        root <- if BS.null c && no == 0
          then either (const Nothing) Just <$> fetch (QueryStorageRoot addr)
          else pure Nothing
        let contr = RPCContract (ByteStringS c) no ba root
        modifyMVar_ sess.sharedCache $ \x -> pure $ x { contractCache = Map.insert addr contr x.contractCache }
        pure (FetchSuccess contr Fresh)
      (Left e, _, _) -> pure (FetchError e)
      (_, Left e, _) -> pure (FetchError e)
      (_, _, Left e) -> pure (FetchError e)
  where
    cached = do
      cache <- readMVar sess.sharedCache
      forM (Map.lookup addr cache.contractCache) $ \c -> do
        when (conf.debug) $ putStrLn $ "-> Using cached account at " ++ show addr
        pure (FetchSuccess c Cached)

-- | Answers from the cache, or else fetches unless a fetch of the same key is under way, then
-- sharing its result. The cache is checked again once the key is taken: a fetch may have
-- filled it in the meantime.
fetchOnce :: Ord k => InFlight k (FetchResult a) -> k -> IO (Maybe (FetchResult a)) -> IO (FetchResult a) -> IO (FetchResult a)
fetchOnce inFlight k cached fetch = cached >>= \case
  Just r -> pure r
  Nothing -> singleFlight inFlight k (cached >>= maybe fetch pure) <&> \case
    (FetchSuccess a Fresh, False) -> FetchSuccess a Cached
    (r, _) -> r

-- | Runs the action unless one for the same key is under way, then waiting for its result
-- instead, and returns whether it ran here. Callers that were waiting on a fetch whose thread
-- was killed run it again, rather than die of the same.
singleFlight :: Ord k => InFlight k a -> k -> IO a -> IO (a, Bool)
singleFlight inFlight k act = mask $ \restore -> do
  (var, owner) <- modifyMVar inFlight $ \m -> case Map.lookup k m of
    Just var -> pure (m, (var, False))
    Nothing -> do
      var <- newEmptyMVar
      pure (Map.insert k var m, (var, True))
  if owner
  then do
    res <- try (restore act)
    -- waiters would block forever if this were interrupted
    uninterruptibleMask_ $ modifyMVar_ inFlight (pure . Map.delete k) >> putMVar var res
    either throwIO (pure . (, True)) res
  else restore (readMVar var) >>= \case
    Right a -> pure (a, False)
    Left e | Just (SomeAsyncException _) <- fromException e -> restore (singleFlight inFlight k act)
           | otherwise -> throwIO e

-- In case the user asks for Latest, and we have not yet established what Latest is,
-- we fetch the block to find out. Otherwise, we update Latest to the value we have stored
getLatestBlockNum :: Config -> Session -> BlockNumber -> Text -> IO BlockNumber
getLatestBlockNum conf sess n url =
  case n of
   -- the lock is held while fetching, so that racing callers fetch the block only once
   Latest -> modifyMVar sess.latestBlockNum $ \case
     Just v -> pure (Just v, EVM.Fetch.BlockNumber v)
     Nothing -> internalBlockFetch conf sess Latest url >>= \case
       Nothing -> pure (Nothing, Latest)
       Just b -> do
         when (conf.debug) $ putStrLn $ "Setting latest block number to " ++ show b.number
         let m = forceLit b.number
         pure (Just m, EVM.Fetch.BlockNumber m)
   _ -> pure n

makeContractFromRPC :: RPCContract -> Contract
makeContractFromRPC (RPCContract (ByteStringS code) nonce balance root) =
    initialContract (RuntimeCode (ConcreteRuntimeCode code))
      & set #nonce    (Just nonce)
      & set #balance  (Lit balance)
      & set #external True
      -- for accounts that do not exist, nodes report a zero storage hash rather than the empty root
      & set #chainStorage (maybe False (`notElem` [0, emptyStorageRoot]) root)

-- | The root of an empty storage trie: keccak256(rlp(""))
emptyStorageRoot :: W256
emptyStorageRoot = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

-- Needed for Echidna only
fetchSlotWithCache :: Config -> Session -> BlockNumber -> Text -> Addr -> W256 -> IO (FetchResult W256)
fetchSlotWithCache conf sess nPre url addr slot =
  fetchOnce sess.slotsInFlight (addr, slot) cached $ do
    n <- getLatestBlockNum conf sess nPre url
    when (conf.debug) $ putStrLn $ "-> Fetching slot " <> show slot <> " at " <> show addr
    ret <- fetchQuery n (fetchWithRetry conf.debug url sess) (QuerySlot addr slot)
    case ret of
      Right val -> do
        modifyMVar_ sess.sharedCache $ \c ->
          pure $ c { slotCache = Map.insert (addr, slot) val c.slotCache }
        pure (FetchSuccess val Fresh)
      Left err -> pure (FetchError err)
  where
    cached = do
      cache <- readMVar sess.sharedCache
      case Map.lookup (addr, slot) cache.slotCache of
        Just s -> do
          when (conf.debug) $ putStrLn $ "-> Using cached slot value for slot " <> show slot <> " at " <> show addr
          pure $ Just (FetchSuccess s Cached)
        Nothing -> do
          failures <- readMVar sess.failedSlots
          if Set.member (addr, slot) failures
          then do
            when (conf.debug) $ putStrLn $ "-> Skipping previously failed slot " <> show slot <> " at " <> show addr
            pure $ Just (FetchFailure Cached)
          else pure Nothing

-- | Get the complete cache state including both successes and failures
-- Returns in the format expected by Echidna's UI:
--   - Map Addr (Maybe Contract): Just = success, Nothing = failure
--   - Map Addr (Map W256 (Maybe W256)): Just = success, Nothing = failure
getCacheState
  :: Session
  -> IO (Map.Map Addr (Maybe Contract), Map.Map Addr (Map.Map W256 (Maybe W256)))
getCacheState sess = do
  cache <- readMVar sess.sharedCache
  failedContracts <- readMVar sess.failedContracts
  failedSlots <- readMVar sess.failedSlots

  -- Convert contract cache
  let successfulContracts = fmap (Just . makeContractFromRPC) $
        Map.filter (\c -> c.code /= ByteStringS BS.empty) cache.contractCache
  let allContracts = successfulContracts
                  <> Map.fromSet (const Nothing) failedContracts

  -- Convert slot cache: group by address
  let successfulSlotsByAddr = Map.foldrWithKey
        (\(addr, slot) value acc ->
          Map.insertWith Map.union addr (Map.singleton slot (Just value)) acc)
        Map.empty
        cache.slotCache

  -- Add failed slots
  let allSlots = Set.foldr
        (\(addr, slot) acc ->
          Map.insertWith Map.union addr (Map.singleton slot Nothing) acc)
        successfulSlotsByAddr
        failedSlots

  pure (allContracts, allSlots)

fetchSlotWithSession :: NetSession.Session -> BlockNumber -> Text -> Addr -> W256 -> IO (Either Text W256)
fetchSlotWithSession sess n url addr slot =
  fetchQuery n (fetchWithSession url sess) (QuerySlot addr slot)

fetchBlockWithSession :: Config -> Session  -> BlockNumber -> Text -> IO (Maybe Block)
fetchBlockWithSession conf sess nPre url = do
  n <- getLatestBlockNum conf sess nPre url
  case n of
    Latest -> internalBlockFetch conf sess n url
    EVM.Fetch.BlockNumber blockNum -> do
      cache <- readMVar sess.sharedCache
      case Map.lookup blockNum cache.blockCache of
        Just b -> do
          when (conf.debug) $ putStrLn $ "-> Using cached block " ++ show n
          pure (Just b)
        Nothing -> internalBlockFetch conf sess n url

internalBlockFetch :: Config -> Session -> BlockNumber -> Text -> IO (Maybe Block)
internalBlockFetch conf sess n url = do
  when (conf.debug) $ putStrLn $ "Fetching block " ++ show n ++ " from " ++ unpack url
  ret <- fetchQuery n (fetchWithRetry conf.debug url sess) QueryBlock
  case ret of
    Left _ -> pure Nothing
    Right b -> do
      let bn = forceLit b.number
      liftIO $ modifyMVar_ sess.sharedCache $ \c ->
        pure $ c { blockCache = Map.insert bn b c.blockCache }
      pure (Just b)

cacheFileName :: W256 -> FilePath
cacheFileName n = "rpc-cache-" ++ T.unpack (showDec Unsigned n) ++ ".json"

emptyCache :: FetchCache
emptyCache = FetchCache Map.empty Map.empty Map.empty

loadCache :: FilePath -> W256 -> IO FetchCache
loadCache dir n = do
  let fp = dir </> cacheFileName n
  exists <- doesFileExist fp
  if exists
    then do
      res <- try (BSL.readFile fp) :: IO (Either SomeException BSL.ByteString)
      case res of
        Left e -> do
          putStrLn $ "Warning: could not read cache file " ++ fp ++ ": " ++ show e
          pure emptyCache
        Right content ->
          case eitherDecode content of
            Left err -> do
              putStrLn $ "Warning: could not parse cache file " ++ fp ++ ": " ++ err
              pure emptyCache
            Right cache -> pure cache
    else
      pure emptyCache

-- | Adds what the cache holds to the cache file, unless it holds nothing new. Other runs may
-- have saved to the file since this one loaded it, so it is merged with, and replaced at once.
saveCache :: FilePath -> W256 -> FetchCache -> IO ()
saveCache dir n cache = do
  createDirectoryIfMissing True dir
  old <- loadCache dir n
  let new = FetchCache
        (Map.union cache.contractCache old.contractCache)
        (Map.union cache.slotCache old.slotCache)
        (Map.union cache.blockCache old.blockCache)
      size c = Map.size c.contractCache + Map.size c.slotCache + Map.size c.blockCache
      fp = dir </> cacheFileName n
  when (size new > size old) $ do
    putStrLn $ "Saving RPC cache to " ++ fp
    (tmp, h) <- openTempFile dir (cacheFileName n)
    BSL.hPut h (encodePretty new) >> hClose h
    renameFile tmp fp

fetchChainId :: Config -> Session -> Text -> IO (Either Text W256)
fetchChainId conf sess url = fetchQuery Latest (fetchWithRetry conf.debug url sess) QueryChainId

mkSession :: App m => Maybe FilePath -> Maybe W256 -> m Session
mkSession cacheDir mblock = do
  sess <- liftIO NetSession.newAPISession
  initialCache <- case (cacheDir, mblock) of
      (Just dir, Just block) -> liftIO $ loadCache dir block
      _ -> pure emptyCache
  cache <- liftIO $ newMVar initialCache
  latestBlockNum <- liftIO $ newMVar Nothing
  -- Initialize ephemeral failure tracking
  failedContracts <- liftIO $ newMVar Set.empty
  failedSlots <- liftIO $ newMVar Set.empty
  rpcThrottle <- liftIO $ newIORef Nothing
  slotsInFlight <- liftIO $ newMVar Map.empty
  accountsInFlight <- liftIO $ newMVar Map.empty
  pure $ Session sess latestBlockNum cache cacheDir failedContracts failedSlots rpcThrottle 500_000 slotsInFlight accountsInFlight

mkSessionWithoutCache :: App m => m Session
mkSessionWithoutCache = mkSession Nothing Nothing

-- | Where the RPC cache lives: in a directory as given, or in the chain's own under one
data CacheLocation = CacheDir FilePath | PerChainUnder FilePath
  deriving (Show)

-- | A session that starts from the state saved at a fixed block, and saves what it fetched
-- however the action ends, so that runs do not fetch the same state over and over
withCachedSession :: App m => Maybe CacheLocation -> Maybe Text -> Maybe W256 -> (Session -> m a) -> m a
withCachedSession loc url block act = do
  dir <- case (loc, url, block) of
    (Just (CacheDir d), _, _) -> pure (Just d)
    (Just (PerChainUnder root), Just u, Just _) -> do
      conf <- readConfig
      probe <- mkSessionWithoutCache
      -- blocks of different chains share numbers
      liftIO (fetchChainId conf probe u) >>= \case
        Right chain -> pure $ Just (root </> show (toInteger chain))
        Left e -> do
          liftIO $ putStrLn $ "Warning: not caching RPC state, could not fetch the chain id: " <> unpack e
          pure Nothing
    _ -> pure Nothing
  sess <- mkSession dir block
  withRunInIO $ \run -> run (act sess) `finally` forM_ ((,) <$> dir <*> block) (\(d, b) ->
    readMVar sess.sharedCache >>= saveCache d b)

-- Only used for testing (test.hs, BlockchainTests.hs)
zero :: Natural -> Maybe Natural -> Natural -> Fetcher t m
zero smtjobs smttimeout maxMemoryMB q = do
  sess <- mkSessionWithoutCache
  withSolvers Z3 smtjobs smttimeout maxMemoryMB $ \s ->
    oracle s (Just sess) noRpc q

noRpcFetcher :: forall t m . App m => SolverGroup -> Fetcher t m
noRpcFetcher sg = oracle sg Nothing noRpc

-- SMT solving + RPC data fetching + reading from environment
oracle :: forall t m . App m => SolverGroup -> Maybe Session -> RpcInfo -> Fetcher t m
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
         case branchcondition of
           Lit 0 -> pure $ continue (Case False)
           Lit _ -> pure $ continue (Case True)
           _     -> continue <$> checkBranch solvers branchcondition pathconds

    PleaseCheckSat props continue -> checkSatWithProps solvers props <&> \case
      Cex _ -> continue (Just True)
      Qed -> continue (Just False)
      _ -> continue Nothing

    PleaseGetSols symExpr numBytes pathconditions continue -> do
         let pathconds = foldl' PAnd (PBool True) pathconditions
         continue <$> getSolutions solvers symExpr numBytes pathconds

    PleaseFetchContract addr base continue
      | isAddressSpecial addr -> pure $ continue nothingContract
      | isNothing rpcInfo.blockNumURL -> pure $ continue nothingContract
      | otherwise -> do
        let sess = fromMaybe (internalError $ "oracle: no session provided for fetch addr: " ++ show addr) preSess
        conf <- readConfig
        let (block, url) = fromJust rpcInfo.blockNumURL
        liftIO (fetchAccountWithSession conf sess block url addr) >>= \case
          FetchSuccess x _ -> pure $ continue (makeContractFromRPC x)
          FetchFailure _ -> internalError $ "oracle error: " ++ show q
          FetchError e -> internalError $ "oracle error: " ++ show e
      where
        nothingContract = case base of
          AbstractBase -> unknownContract (LitAddr addr)
          EmptyBase -> emptyContract

    PleaseFetchSlot addr slot continue
      | isAddressSpecial addr -> pure $ continue 0
      | isNothing rpcInfo.blockNumURL -> pure $ continue 0
      | otherwise -> do
        let sess = fromMaybe (internalError $ "oracle: no session provided for fetch addr: " ++ show addr) preSess
        conf <- readConfig
        let (block, url) = fromJust rpcInfo.blockNumURL
        liftIO (fetchSlotWithCache conf sess block url addr slot) >>= \case
          FetchSuccess val _ -> pure $ continue val
          FetchFailure _ -> internalError $ "oracle error: " ++ show q
          FetchError e -> internalError $ "oracle error: " ++ show e

    PleaseReadEnv variable continue -> do
      value <- liftIO $ lookupEnv variable
      pure . continue $ fromMaybe "" value

    where
      -- accounts that only exist in hevm
      isAddressSpecial addr = LitAddr addr == cheatCode || LitAddr addr == consoleAddr


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

-- | Which sides of a branch the path conditions allow. Each side is asked as
-- execution records it when taken, which simplification can take apart, and a
-- side the solver cannot decide, e.g. as it cannot encode it, does not keep the
-- other side from being refuted.
checkBranch :: App m => SolverGroup -> Expr EWord -> Prop -> m BranchCondition
checkBranch solvers cond pathconditions = do
  let condSimp = Expr.simplify cond
      true = Expr.simplifyProp (Lit 0 ./= condSimp)
      false = Expr.simplifyProp (Lit 0 .== condSimp)
      ask side = checkBranchSat solvers [pathconditions .&& side]
  ask true >>= \case
    -- the condition is unsatisfiable: it is false, unless the path conditions are too
    Qed -> ask false <&> \case
      Qed -> Infeasible
      _ -> Case False
    -- possibly true, or the solver could not tell: is false possible?
    _ -> ask false <&> \case
      Qed -> Case True
      -- both sides are possible, or the solver could not tell, e.g. a timeout or a
      -- query it cannot encode (a symbolic copyslice): explore both
      _ -> UnknownBranch
