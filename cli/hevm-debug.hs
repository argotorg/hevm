-- Line-based client for the hevm debugger server (hevm ... --debugger)

module Main where

import Control.Exception (SomeException, try)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Network.HTTP.Client
import Options.Applicative
import System.Console.Haskeline
import System.Exit (exitFailure)

import EVM.Debugger.Server (defaultDebuggerPort)

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
          Right resp -> pure (BL.unpack (responseBody resp))
      clear = if o.noClear || not (null o.commands) then "" else "\ESC[H\ESC[2J"
      send cmd = call "POST" "/command?format=text" cmd >>= putStr . (clear <>)
  case o.commands of
    [] -> do
      call "GET" "/state?format=text" "" >>= putStr . (clear <>)
      runInputT defaultSettings (loop send call "")
    cs -> mapM_ (\c -> if c `elem` ["q", "quit", "exit"] then call "POST" "/quit" "" >>= putStrLn else send c) cs
  where
    loop send call prev = getInputLine "(hevm) " >>= \case
      Nothing -> pure ()
      Just l -> case words l of
        [w] | w `elem` ["q", "quit", "exit"] -> liftIO (call "POST" "/quit" "" >>= putStrLn)
        ["detach"] -> pure ()
        -- an empty line repeats the previous command, as in gdb
        [] -> liftIO (send prev) >> loop send call prev
        _ -> liftIO (send l) >> loop send call l
