-- | A tasty reporter appending a line when each test starts and when it ends,
-- so a run that seems stuck shows which tests are still going: a START
-- without a DONE. The console prints in test order, hiding them.
module EVM.Test.RunLog (runLogReporter) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newMVar, withMVar)
import Control.Concurrent.STM (atomically, readTVar, retry)
import Control.Monad (forM_, void)
import Data.IntMap qualified as IntMap
import Data.Proxy (Proxy(..))
import Data.Time (diffUTCTime, getCurrentTime, getZonedTime, formatTime, defaultTimeLocale)
import System.IO (IOMode(AppendMode), hFlush, hPutStrLn, openFile)
import Test.Tasty.Ingredients (Ingredient(..))
import Test.Tasty.Options (IsOption(..), OptionDescription(..), lookupOption)
import Test.Tasty.Runners (Status(..), resultSuccessful, testsNames)
import Text.Printf (printf)

newtype RunLog = RunLog (Maybe FilePath)

instance IsOption RunLog where
  defaultValue = RunLog Nothing
  parseValue = Just . RunLog . Just
  optionName = pure "run-log"
  optionHelp = pure "Append a line to this file when each test starts and ends"

runLogReporter :: Ingredient
runLogReporter = TestReporter [Option (Proxy :: Proxy RunLog)] $ \opts tree ->
  case lookupOption opts of
    RunLog Nothing -> Nothing
    RunLog (Just path) -> Just $ \statuses -> do
      h <- openFile path AppendMode
      lock <- newMVar ()
      let line s = withMVar lock $ \_ -> do
            now <- formatTime defaultTimeLocale "%H:%M:%S" <$> getZonedTime
            hPutStrLn h (now <> " " <> s)
            hFlush h
      forM_ (zip (testsNames opts tree) (IntMap.elems statuses)) $ \(name, var) -> void $ forkIO $ do
        atomically $ readTVar var >>= \case
          NotStarted -> retry
          _ -> pure ()
        line $ "START " <> name
        start <- getCurrentTime
        r <- atomically $ readTVar var >>= \case
          Done r -> pure r
          _ -> retry
        -- resultTime is 0 for a test that threw
        secs <- realToFrac . (`diffUTCTime` start) <$> getCurrentTime
        line $ printf "DONE  %s %.1fs %s" name (secs :: Double) (if resultSuccessful r then "OK" else "FAIL" :: String)
      pure $ \_ -> pure True
