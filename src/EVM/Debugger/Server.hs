-- | Minimal HTTP+JSON front end for a debugging session, bound to localhost.
-- Hand-rolled on top of 'network' to avoid pulling a web framework into hevm.
module EVM.Debugger.Server
  ( serveSession
  , announce
  , defaultDebuggerPort
  ) where

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Exception (SomeException, bracket, finally, try)
import Control.Monad (forever, void)
import Control.Monad.IO.Unlift (withRunInIO)
import Data.Aeson (FromJSON, ToJSON, (.=), (.:))
import Data.Aeson qualified as JSON
import Data.Aeson.Types (parseMaybe)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BC
import Data.ByteString.Lazy qualified as BL
import Data.Char (toLower)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8With, encodeUtf8)
import Data.Text.Encoding.Error (lenientDecode)
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import System.IO (hFlush, stdout)

import EVM.Debugger
import EVM.Effects (App)
import EVM.Fetch qualified as Fetch

defaultDebuggerPort :: Int
defaultDebuggerPort = 7317

data Request = Request
  { method :: ByteString
  , path   :: ByteString
  , query  :: [(ByteString, ByteString)]
  , body   :: ByteString
  }

data Response = Response
  { status      :: Int
  , contentType :: ByteString
  , content     :: ByteString
  }

-- | Serve the session until a client sends 'quit'. Requests are handled
-- concurrently, commands one at a time.
serveSession :: (App m, Debuggable t) => Fetch.Fetcher t m -> Int -> (Int -> IO ()) -> Session t -> m ()
serveSession fetcher port onListen s0 = withRunInIO $ \runInIO -> do
  sessVar <- newMVar s0
  done <- newEmptyMVar
  let run line = modifyMVar sessVar $ \s -> do
        s' <- runInIO (runCommandText fetcher line s)
        pure (s', s')
      handler req = route run sessVar done req
  addr : _ <- getAddrInfo (Just defaultHints { addrFlags = [AI_NUMERICHOST, AI_NUMERICSERV], addrSocketType = Stream })
                          (Just "127.0.0.1") (Just (show port))
  bracket (openSocket addr) close $ \sock -> do
    setSocketOption sock ReuseAddr 1
    bind sock (addrAddress addr)
    listen sock 16
    socketPort sock >>= onListen . fromIntegral
    acceptor <- forkIO $ forever $ do
      (conn, _) <- accept sock
      void $ forkIO $ (handleConn handler conn) `finally` close conn
    takeMVar done `finally` killThread acceptor

announce :: Int -> IO ()
announce port = do
  putStrLn $ "hevm debugger listening on http://127.0.0.1:" <> show port
    <> "  (connect with: hevm-debug --port " <> show port <> ")"
  hFlush stdout

handleConn :: (Request -> IO Response) -> Socket -> IO ()
handleConn handler conn = do
  r <- try (readRequest conn)
  resp <- case r of
    Left (e :: SomeException) -> pure $ Response 400 "text/plain" (BC.pack ("bad request: " <> show e))
    Right Nothing -> pure $ Response 400 "text/plain" "bad request"
    Right (Just req) -> try (handler req) >>= \case
      Left (e :: SomeException) -> pure $ Response 500 "text/plain" (BC.pack ("internal error: " <> show e))
      Right x -> pure x
  sendAll conn (renderResponse resp)

readRequest :: Socket -> IO (Maybe Request)
readRequest conn = go BS.empty
  where
    go acc
      | BS.length acc > 1024 * 1024 = pure Nothing
      | otherwise = case BS.breakSubstring "\r\n\r\n" acc of
          (hdr, rest) | not (BS.null rest) -> do
            let ls = BC.lines (BC.filter (/= '\r') hdr)
                headers = [ (BC.map toLower (BC.strip k), BC.strip (BS.drop 1 v)) | l <- drop 1 ls, let (k, v) = BC.break (== ':') l ]
                len = maybe 0 (maybe 0 fst . BC.readInt) (lookup "content-length" headers)
            b <- readBody (BS.drop 4 rest) len
            pure $ case BC.words (head' ls) of
              (m : target : _) ->
                let (p, q) = BC.break (== '?') target
                in Just (Request m p (parseQuery (BS.drop 1 q)) b)
              _ -> Nothing
          _ -> do
            chunk <- recv conn 4096
            if BS.null chunk then pure Nothing else go (acc <> chunk)
    readBody acc len
      | BS.length acc >= len = pure (BS.take len acc)
      | otherwise = do
          chunk <- recv conn 4096
          if BS.null chunk then pure acc else readBody (acc <> chunk) len
    head' = \case
      (x : _) -> x
      [] -> ""

parseQuery :: ByteString -> [(ByteString, ByteString)]
parseQuery q = [ (k, BS.drop 1 v) | kv <- BC.split '&' q, not (BS.null kv), let (k, v) = BC.break (== '=') kv ]

renderResponse :: Response -> ByteString
renderResponse r = BS.concat
  [ "HTTP/1.1 ", BC.pack (show r.status), " ", reason r.status, "\r\n"
  , "Content-Type: ", r.contentType, "\r\n"
  , "Content-Length: ", BC.pack (show (BS.length r.content)), "\r\n"
  , "Access-Control-Allow-Origin: *\r\n"
  , "Access-Control-Allow-Methods: GET, POST, OPTIONS\r\n"
  , "Access-Control-Allow-Headers: Content-Type\r\n"
  , "Connection: close\r\n\r\n"
  , r.content
  ]
  where
    reason = \case
      200 -> "OK"
      204 -> "No Content"
      400 -> "Bad Request"
      404 -> "Not Found"
      _ -> "Internal Server Error"

newtype CommandBody = CommandBody Text
instance FromJSON CommandBody where
  parseJSON = JSON.withObject "command" $ \o -> CommandBody <$> o .: "command"

route :: Debuggable t => (Text -> IO (Session t)) -> MVar (Session t) -> MVar () -> Request -> IO Response
route run sessVar done req = case (req.method, req.path) of
  ("OPTIONS", _) -> pure $ Response 204 "text/plain" ""
  ("GET", "/") -> pure $ Response 200 "text/plain; charset=utf-8" (encodeUtf8 apiHelp)
  ("GET", "/help") -> json $ JSON.object [ "commands" .= T.lines commandHelp, "api" .= T.lines apiHelp ]
  ("GET", "/state") -> readMVar sessVar >>= viewResponse
  ("GET", "/stats") -> do
    v <- sessionStats <$> readMVar sessVar
    if textFormat
      then pure $ Response 200 "text/plain; charset=utf-8" (encodeUtf8 (renderStats v))
      else json v
  ("POST", "/command") -> run commandLine >>= viewResponse
  ("POST", "/quit") -> do
    void $ tryPutMVar done ()
    json $ JSON.object [ "message" .= ("bye" :: Text) ]
  _ -> pure $ Response 404 "text/plain" "not found; GET / for the API"
  where
    textFormat = lookup "format" req.query == Just "text"
    viewResponse s = do
      v <- mkView s
      if textFormat
        then pure $ Response 200 "text/plain; charset=utf-8" (encodeUtf8 (renderView v))
        else json v
    commandLine = case JSON.decodeStrict req.body of
      Just v | Just (CommandBody c) <- parseMaybe JSON.parseJSON v -> c
      _ -> decodeUtf8With lenientDecode req.body

json :: ToJSON a => a -> IO Response
json = pure . Response 200 "application/json" . BL.toStrict . JSON.encode

apiHelp :: Text
apiHelp = T.unlines
  [ "hevm debugger HTTP API (all responses JSON unless ?format=text is given)"
  , "GET  /state            current view"
  , "POST /command          run a command, returns the new view"
  , "                       body: {\"command\": \"step 10\"} or the bare command text"
  , "GET  /stats            counters of what the session has done"
  , "GET  /help             commands and API"
  , "POST /quit             stop the debugger"
  , ""
  , "Commands:"
  ] <> commandHelp
