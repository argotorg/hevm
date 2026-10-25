-- | A JSON-RPC node over HTTP on localhost, serving a fixed world state at one block the way
-- geth does, so tests can drive hevm's real RPC fetching path.
module EVM.Fetch.MockNode
  ( Account (..)
  , World
  , Node (..)
  , Request (..)
  , withMockNode
  , Faults (..)
  , noFaults
  , withFaultyMockNode
  , eoa
  ) where

import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Exception (bracket, finally)
import Control.Monad (forever, unless)
import Data.Aeson (Value(..), (.=), object)
import Data.Aeson qualified as JSON
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Lazy qualified as BSL
import Data.Char (toLower)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Network.Socket qualified as Net
import Network.Socket.ByteString (recv, sendAll)
import Numeric (showHex, readHex)
import Text.Read (readMaybe)

import EVM.Format (formatBinary)
import EVM.Types

data Account = Account
  { code :: ByteString
  , nonce :: W64
  , balance :: W256
  , storage :: Map W256 W256
  } deriving (Show, Eq)

eoa :: W64 -> W256 -> Account
eoa n b = Account mempty n b mempty

-- | Accounts missing from the world do not exist: no code, zero nonce, balance and storage
type World = Map Addr Account

data Request = Request { method :: Text, params :: [Value] }
  deriving (Show, Eq)

data Node = Node
  { url :: Text
  , block :: W256
  , requests :: IORef [Request] -- ^ every request answered, latest first
  , faults :: IORef Int -- ^ how many requests failed instead
  }

-- | How a node misbehaves: it answers each request after a latency within the given range of
-- microseconds, or fails it, by HTTP 429, by a JSON-RPC rate limit error or by hanging up,
-- for the given percentage of the first two attempts. Each is decided by hashing the salt,
-- the request and its attempt.
data Faults = Faults { salt :: W256, latency :: (Int, Int), faultPercent :: W256 }
  deriving (Show)

noFaults :: Faults
noFaults = Faults 0 (0, 0) 0

data Reply = Reply Value | TooManyRequests | HangUp

-- | Runs a node serving the world at the given block, which is also its "latest"
withMockNode :: W256 -> World -> (Node -> IO a) -> IO a
withMockNode = withFaultyMockNode noFaults

withFaultyMockNode :: Faults -> W256 -> World -> (Node -> IO a) -> IO a
withFaultyMockNode fs blk world act = do
  reqs <- newIORef []
  failed <- newIORef 0
  attempts <- newIORef (Map.empty :: Map ByteString Int)
  threads <- newIORef []
  let fork io = forkIO io >>= \t -> atomicModifyIORef' threads (\ts -> (t : ts, ()))
      open = do
        sock <- Net.socket Net.AF_INET Net.Stream Net.defaultProtocol
        Net.bind sock (Net.SockAddrInet 0 (Net.tupleToHostAddress (127, 0, 0, 1)))
        Net.listen sock 16
        pure sock
      -- connection threads block in recv for as long as the client keeps the connection alive
      close sock = readIORef threads >>= mapM_ killThread >> Net.close sock
      respond body = do
        n <- atomicModifyIORef' attempts (\m -> (Map.insertWith (+) body 1 m, Map.findWithDefault 0 body m))
        let h = keccak' (word256Bytes fs.salt <> body <> word256Bytes (fromIntegral n))
            (minL, maxL) = fs.latency
            wait = threadDelay (minL + fromIntegral (h `mod` fromIntegral (maxL - minL + 1)))
        if n < 2 && (h `div` 2) `mod` 100 < fs.faultPercent
          then do
            atomicModifyIORef' failed (\k -> (k + 1, ()))
            wait
            pure $ case (h `div` 200) `mod` 3 of
              0 -> TooManyRequests
              1 -> HangUp
              _ -> Reply $ object ["jsonrpc" .= ("2.0" :: Text), "id" .= (1 :: Int), "error" .= object
                ["code" .= (429 :: Int), "message" .= ("Your app has exceeded its compute units per second capacity" :: Text)]]
          else Reply <$> answer blk world reqs body <* wait
  bracket open close $ \sock -> do
    fork $ forever $ do
      (conn, _) <- Net.accept sock
      fork $ serveConn respond conn `finally` Net.close conn
    port <- Net.socketPort sock
    act (Node ("http://127.0.0.1:" <> T.pack (show port)) blk reqs failed)

-- | Serves the requests of one keep-alive connection
serveConn :: (ByteString -> IO Reply) -> Net.Socket -> IO ()
serveConn respond conn = go mempty
  where
    go buf = do
      (headers, rest) <- readUntil buf
      unless (BS.null headers) $ do
        (body, rest') <- readN rest (contentLength headers)
        respond body >>= \case
          Reply v -> do
            let resp = JSON.encode v
            sendAll conn $ "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: "
              <> Char8.pack (show (BSL.length resp)) <> "\r\n\r\n" <> BSL.toStrict resp
            go rest'
          TooManyRequests -> do
            sendAll conn "HTTP/1.1 429 Too Many Requests\r\nContent-Length: 0\r\n\r\n"
            go rest'
          HangUp -> pure ()
    readUntil buf = case BS.breakSubstring "\r\n\r\n" buf of
      (h, t) | not (BS.null t) -> pure (h, BS.drop 4 t)
      _ -> more buf >>= maybe (pure (mempty, mempty)) readUntil
    readN buf n
      | BS.length buf >= n = pure (BS.splitAt n buf)
      | otherwise = more buf >>= maybe (pure (buf, mempty)) (`readN` n)
    more buf = do
      chunk <- recv conn 65536
      pure $ if BS.null chunk then Nothing else Just (buf <> chunk)
    contentLength headers = case
      [ n | l <- Char8.lines headers
          , let (k, v) = Char8.break (== ':') l
          , Char8.map toLower k == "content-length"
          , Just n <- [readMaybe (Char8.unpack (Char8.strip (Char8.drop 1 v)))] ] of
        n : _ -> n
        [] -> 0

-- | Answers one JSON-RPC request body, recording it
answer :: W256 -> World -> IORef [Request] -> ByteString -> IO Value
answer blk world reqs body = case JSON.decodeStrict body of
  Just (Object o)
    | Just (String m) <- lookupKey "method" o
    , Just (Array ps) <- lookupKey "params" o -> do
        let req = Request m (V.toList ps)
        atomicModifyIORef' reqs (\rs -> (req : rs, ()))
        pure $ either (err (-32602)) result (dispatch req)
      where reply f = object ["jsonrpc" .= ("2.0" :: Text), "id" .= lookupKey "id" o, f]
            result v = reply ("result" .= v)
            err :: Int -> Text -> Value
            err c msg = reply ("error" .= object ["code" .= c, "message" .= msg])
  _ -> pure $ object ["jsonrpc" .= ("2.0" :: Text), "id" .= Null,
    "error" .= object ["code" .= (-32600 :: Int), "message" .= ("invalid request: " <> show body)]]
  where
    lookupKey = KeyMap.lookup
    account a = Map.findWithDefault (Account mempty 0 0 mempty) a world
    dispatch :: Request -> Either Text Value
    dispatch (Request m ps) = case (m, ps) of
      ("eth_getCode", [a, b]) -> atBlock b $ String . formatBinary . (.code) . account <$> addr a
      ("eth_getTransactionCount", [a, b]) -> atBlock b $ quantity . fromIntegral . (.nonce) . account <$> addr a
      ("eth_getBalance", [a, b]) -> atBlock b $ quantity . (.balance) . account <$> addr a
      ("eth_getStorageAt", [a, s, b]) -> atBlock b $ do
        acc <- account <$> addr a
        slot <- hex s
        pure $ String $ formatBinary $ word256Bytes $ Map.findWithDefault 0 slot acc.storage
      -- the root is a stand-in for the trie's: only whether storage is empty is meaningful
      -- like Alchemy, a zero storage hash for accounts that do not exist
      ("eth_getProof", [a, _, b]) -> atBlock b $ do
        acc <- account <$> addr a
        exists <- (`Map.member` world) <$> addr a
        let root | not exists = 0
                 | Map.null (Map.filter (/= 0) acc.storage) = emptyStorageRoot
                 | otherwise = keccak' (BS.concat [word256Bytes k <> word256Bytes v | (k, v) <- Map.toList acc.storage])
        pure $ object
          [ "balance" .= quantity acc.balance
          , "nonce" .= quantity (fromIntegral acc.nonce)
          , "codeHash" .= String (formatBinary (word256Bytes (keccak' acc.code)))
          , "storageHash" .= String (formatBinary (word256Bytes root))
          , "accountProof" .= ([] :: [Value])
          , "storageProof" .= ([] :: [Value])
          ]
      ("eth_getBlockByNumber", [b, _]) -> atBlock b $ Right $ object
        [ "number" .= quantity blk
        , "timestamp" .= quantity (1_700_000_000 + blk * 12)
        , "miner" .= String (T.pack (show (0xc0ffee :: Addr)))
        , "gasLimit" .= quantity 30_000_000
        , "baseFeePerGas" .= quantity 7
        , "difficulty" .= quantity 0
        , "mixHash" .= String (formatBinary (word256Bytes (keccak' (word256Bytes blk))))
        ]
      ("eth_chainId", _) -> Right (quantity 1)
      _ -> Left ("unsupported request: " <> T.pack (show (Request m ps)))
    atBlock b r = case b of
      String "latest" -> r
      _ | hex b == Right blk -> r
        | otherwise -> Left ("only block " <> T.pack (show blk) <> " is served, not " <> T.pack (show b))
    addr v = fromIntegral <$> hex v :: Either Text Addr
    hex :: Value -> Either Text W256
    hex = \case
      String t | Just h <- T.stripPrefix "0x" t, [(n, "")] <- readHex (T.unpack h) -> Right (fromInteger n)
      v -> Left ("not a hex quantity: " <> T.pack (show v))

emptyStorageRoot :: W256
emptyStorageRoot = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

-- | Hex without leading zeros, as JSON-RPC encodes quantities
quantity :: W256 -> Value
quantity w = String (T.pack ("0x" <> showHex w ""))
