-- | Minimal HTTP+JSON API for debugging sessions and run progress, bound to
-- localhost. Clients, such as hevm-web-ui, format what it sends.
-- Hand-rolled on top of 'network' to avoid pulling a web framework into hevm.
module EVM.Debugger.Server
  ( serveSession
  , withProgressServer
  , announce
  , defaultDebuggerPort
  ) where

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Exception (SomeException, bracket, finally, throwIO, try)
import Control.Monad (forever, void)
import Control.Monad.IO.Unlift (MonadUnliftIO, withRunInIO)
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
import System.Timeout (timeout)

import EVM.Debugger
import EVM.Effects (App)
import EVM.Fetch qualified as Fetch
import EVM.Progress qualified as Progress

defaultDebuggerPort :: Int
defaultDebuggerPort = 7317

data Request = Request
  { method :: ByteString
  , path   :: ByteString
  , body   :: ByteString
  , host   :: Maybe ByteString
  }

data Response = Response
  { status      :: Int
  , contentType :: ByteString
  , content     :: ByteString
  }

type Route = Request -> IO (Maybe Response)

-- | Serves the session, and the progress of the run, until a client sends
-- 'quit'. Requests are handled concurrently, commands one at a time.
serveSession :: (App m, Debuggable t) => Fetch.Fetcher t m -> Int -> (Int -> IO ()) -> Session t -> m ()
serveSession fetcher port onListen s0 = withRunInIO $ \runInIO -> do
  sessVar <- newMVar s0
  done <- newEmptyMVar
  let run line = modifyMVar sessVar $ \s -> do
        s' <- runInIO (runCommandText fetcher line s)
        pure (s', s')
  serveRoutes port onListen done [sessionRoute run sessVar done, progressRoute]

withProgressServer :: MonadUnliftIO m => Int -> (Int -> IO ()) -> m a -> m a
withProgressServer port onListen act = withRunInIO $ \runInIO -> do
  done <- newEmptyMVar
  ready <- newEmptyMVar
  stopped <- newEmptyMVar
  void $ forkIO $ do
    r <- try $ serveRoutes port (\p -> onListen p >> void (tryPutMVar ready Nothing)) done [progressRoute]
    case r of
      Left (e :: SomeException) -> void (tryPutMVar ready (Just e))
      Right () -> pure ()
    putMVar stopped ()
  takeMVar ready >>= mapM_ throwIO
  runInIO act `finally` (tryPutMVar done () >> takeMVar stopped)

serveRoutes :: Int -> (Int -> IO ()) -> MVar () -> [Route] -> IO ()
serveRoutes port onListen done routes = do
  addr : _ <- getAddrInfo (Just defaultHints { addrFlags = [AI_NUMERICHOST, AI_NUMERICSERV], addrSocketType = Stream })
                          (Just "127.0.0.1") (Just (show port))
  bracket (openSocket addr) close $ \sock -> do
    setSocketOption sock ReuseAddr 1
    bind sock (addrAddress addr)
    listen sock maxListenQueue
    p <- fromIntegral <$> socketPort sock
    onListen p
    -- browsers send the Host they looked up, so another site's name pointing here
    -- (DNS rebinding) cannot reach the debugger
    let hosts = [h <> ":" <> BC.pack (show p) | h <- ["127.0.0.1", "localhost"]]
    acceptor <- forkIO $ forever $ do
      (conn, _) <- accept sock
      void $ forkIO $ handleConn hosts (dispatch routes) conn `finally` close conn
    takeMVar done `finally` killThread acceptor

dispatch :: [Route] -> Request -> IO Response
dispatch routes req = case (req.method, req.path) of
  (m, p) | m == "GET", p `elem` ["/", "/api"] -> pure $ Response 200 "text/plain; charset=utf-8" (encodeUtf8 apiHelp)
  _ -> go routes
  where
    go [] = pure $ Response 404 "text/plain" "not found; GET /api for the API"
    go (r : rest) = r req >>= maybe (go rest) pure

announce :: Int -> IO ()
announce port = do
  putStrLn $ "hevm debugger at http://127.0.0.1:" <> show port
  hFlush stdout

handleConn :: [ByteString] -> (Request -> IO Response) -> Socket -> IO ()
handleConn hosts handler conn = do
  r <- try (timeout 30000000 (readRequest conn))
  resp <- case r of
    Left (e :: SomeException) -> pure $ Response 400 "text/plain" (BC.pack ("bad request: " <> show e))
    Right Nothing -> pure $ Response 400 "text/plain" "bad request: timed out"
    Right (Just Nothing) -> pure $ Response 400 "text/plain" "bad request"
    Right (Just (Just req)) | fmap (BC.map toLower) req.host `notElem` map Just hosts ->
      pure $ Response 403 "text/plain" ("forbidden: the Host header must be one of " <> BC.unwords hosts)
    Right (Just (Just req)) -> try (handler req) >>= \case
      Left (e :: SomeException) -> pure $ Response 500 "text/plain" (BC.pack ("internal error: " <> show e))
      Right x -> pure x
  sendAll conn (renderResponse resp)

readRequest :: Socket -> IO (Maybe Request)
readRequest conn = go BS.empty
  where
    go acc
      | BS.length acc > maxSize = pure Nothing
      | otherwise = case BS.breakSubstring "\r\n\r\n" acc of
          (hdr, rest) | not (BS.null rest) -> do
            let ls = BC.lines (BC.filter (/= '\r') hdr)
                headers = [ (BC.map toLower (BC.strip k), BC.strip (BS.drop 1 v)) | l <- drop 1 ls, let (k, v) = BC.break (== ':') l ]
                len = maybe 0 (maybe 0 fst . BC.readInt) (lookup "content-length" headers)
            if len > maxSize then pure Nothing else do
              b <- readBody (BS.drop 4 rest) len
              pure $ case BC.words (head' ls) of
                (m : target : _) ->
                  Just (Request m (BC.takeWhile (/= '?') target) b (lookup "host" headers))
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
    maxSize = 1024 * 1024

renderResponse :: Response -> ByteString
renderResponse r = BS.concat
  [ "HTTP/1.1 ", BC.pack (show r.status), " ", reason r.status, "\r\n"
  , "Content-Type: ", r.contentType, "\r\n"
  , "Content-Length: ", BC.pack (show (BS.length r.content)), "\r\n"
  , "Connection: close\r\n\r\n"
  , r.content
  ]
  where
    reason = \case
      200 -> "OK"
      403 -> "Forbidden"
      400 -> "Bad Request"
      404 -> "Not Found"
      _ -> "Internal Server Error"

newtype CommandBody = CommandBody Text
instance FromJSON CommandBody where
  parseJSON = JSON.withObject "command" $ \o -> CommandBody <$> o .: "command"

sessionRoute :: Debuggable t => (Text -> IO (Session t)) -> MVar (Session t) -> MVar () -> Route
sessionRoute run sessVar done req = case (req.method, req.path) of
  ("GET", "/help") -> Just <$> json (JSON.object [ "commands" .= T.lines commandHelp, "api" .= T.lines apiHelp ])
  ("GET", "/state") -> Just <$> (readMVar sessVar >>= viewResponse)
  ("GET", "/stats") -> do
    v <- sessionStats <$> readMVar sessVar
    Just <$> json v
  ("GET", "/trace") -> do
    t <- sessionTrace <$> readMVar sessVar
    Just <$> json (JSON.object [ "trace" .= t ])
  ("POST", "/command") -> Just <$> (run commandLine >>= viewResponse)
  ("POST", "/quit") -> do
    void $ tryPutMVar done ()
    Just <$> json (JSON.object [ "message" .= ("bye" :: Text) ])
  _ -> pure Nothing
  where
    viewResponse s = do
      v <- mkView s
      json v
    commandLine = case JSON.decodeStrict req.body of
      Just v | Just (CommandBody c) <- parseMaybe JSON.parseJSON v -> c
      _ -> decodeUtf8With lenientDecode req.body

progressRoute :: Route
progressRoute req = case (req.method, req.path) of
  ("GET", "/progress") -> Just <$> (Progress.currentProgress >>= json)
  _ -> pure Nothing

json :: ToJSON a => a -> IO Response
json = pure . Response 200 "application/json" . BL.toStrict . JSON.encode

apiHelp :: Text
apiHelp = T.unlines
  [ "hevm HTTP API (responses are JSON: clients format what they show)"
  , "GET  /                 this help"
  , "GET  /api              this help"
  , "GET  /progress         progress of the run: phase, paths, solver queries, hot spots"
  , ""
  , "With --interactive:"
  , "GET  /state            current view"
  , "POST /command          run a command, returns the new view"
  , "                       body: {\"command\": \"step 10\"} or the bare command text"
  , "GET  /stats            counters of what the session has done"
  , "GET  /trace            the call trace so far"
  , "GET  /help             commands and API"
  , "POST /quit             stop the debugger"
  , ""
  , "Commands:"
  ] <> commandHelp
