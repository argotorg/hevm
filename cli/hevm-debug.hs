-- Line-based client for the hevm debugger server (hevm ... --debugger)

module Main where

import Control.Exception (SomeException, try)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson qualified as JSON
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as T
import Network.HTTP.Client
import Options.Applicative
import System.Console.Haskeline
import System.Exit (exitFailure)

import EVM.Debugger (View)
import EVM.Debugger.Server (defaultDebuggerPort)
import EVM.Debugger.Text (renderView)

data Opts = Opts
  { port     :: Int
  , commands :: [String]
  , noClear  :: Bool
  }

opts :: Parser Opts
opts = Opts
  <$> option auto (long "port" <> showDefault <> value defaultDebuggerPort <> help "Port of the hevm debugger")
  <*> many (strOption (long "command" <> short 'c' <> help "Run this command and exit instead of starting the prompt. Can be given multiple times"))
  <*> switch (long "no-clear" <> help "Don't clear the screen before each view")

main :: IO ()
main = do
  o <- execParser $ info (opts <**> helper)
    (fullDesc <> progDesc "Interactive client for the hevm debugger, started with e.g. `hevm test --debugger --match <test>`")
  mgr <- newManager defaultManagerSettings { managerResponseTimeout = responseTimeoutNone }
  let base = "http://127.0.0.1:" <> show o.port
      call method path body = do
        req <- parseRequest (method <> " " <> base <> path)
        r <- try $ httpLbs req { requestBody = RequestBodyBS (encodeUtf8 (T.pack body)) } mgr
        case r of
          Left (e :: SomeException) -> do
            putStrLn $ "Cannot reach the hevm debugger at " <> base <> ": " <> show e
            exitFailure
          Right resp -> pure (responseBody resp)
      clear = if o.noClear || not (null o.commands) then "" else "\ESC[H\ESC[2J"
      -- the server sends views as JSON, which this client formats for the terminal
      showView body = case JSON.eitherDecode body :: Either String View of
        Right v -> putStr clear >> T.putStr (renderView v)
        Left err -> putStrLn $ "Unexpected answer from the hevm debugger (" <> err <> "): " <> take 300 (BL.unpack body)
      send cmd = call "POST" "/command" cmd >>= showView
  case o.commands of
    [] -> do
      call "GET" "/state" "" >>= showView
      runInputT defaultSettings (loop send call "")
    cs -> mapM_ (\c -> if c `elem` ["q", "quit", "exit"] then call "POST" "/quit" "" >>= BL.putStrLn else send c) cs
  where
    loop send call prev = getInputLine "(hevm) " >>= \case
      Nothing -> pure ()
      Just l -> case words l of
        [w] | w `elem` ["q", "quit", "exit"] -> liftIO (call "POST" "/quit" "" >>= BL.putStrLn)
        ["detach"] -> pure ()
        -- an empty line repeats the previous command, as in gdb
        [] -> liftIO (send prev) >> loop send call prev
        _ -> liftIO (send l) >> loop send call l
