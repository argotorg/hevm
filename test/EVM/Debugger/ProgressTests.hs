{-|
Module      : ProgressTests
Description : The progress of a run, read directly and over HTTP

The progress state is global, so these run one at a time and after every other
test: anything else running would report into it.
-}
module EVM.Debugger.ProgressTests (tests) where

import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Concurrent.MVar
import Control.Exception (SomeException, bracket, try)
import Control.Monad (forM, forM_, unless, void, when)
import Control.Monad.IO.Unlift (liftIO)
import Control.Monad.ST (stToIO)
import Data.Aeson ((.=))
import Data.Aeson qualified as JSON
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString qualified as BS
import Data.IORef
import Data.Maybe (fromMaybe, isJust, mapMaybe, listToMaybe)
import Data.ByteString.Char8 qualified as BC
import System.IO.Temp (withSystemTempDirectory)
import Data.Text (Text)
import Data.Vector qualified as V
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import EVM.Dapp (emptyDapp)
import EVM.Debugger (newSession, runCommandText)
import EVM.Debugger.DebuggerTests (http, httpJSON, branchCode, branchJumpi)
import EVM.Debugger.Server (serveSession, withProgressServer)
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Progress
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.SymExec (abstractVM)
import EVM.Types (Expr(AbstractBuf))

tests :: TestTree
tests = after AllFinish "!/progress-global/" $ sequentialTestGroup "progress-global" AllFinish
  [ testCase "not-running" $ do
      v <- currentProgress
      assertEqual "running" (Just (JSON.Bool False)) (at ["running"] v)
  , testCase "phases-and-paths" $ withProgress tracking $ do
      inside <- withPhase "explore" ["test" .= ("t" :: Text)] (const ["found" .= (2 :: Int)]) $ do
        phaseTotal 5
        phaseTick
        phaseTick
        pathDone False
        pathDone True
        currentProgress
      assertEqual "phase" (Just "explore") (str =<< at ["phase", "name"] inside)
      assertEqual "done" (Just 2) (int =<< at ["phase", "done"] inside)
      assertEqual "total" (Just 5) (int =<< at ["phase", "total"] inside)
      assertEqual "paths" (Just 2) (int =<< at ["paths", "done"] inside)
      assertEqual "partial" (Just 1) (int =<< at ["paths", "partial"] inside)
      after' <- currentProgress
      case at ["phases"] after' of
        Just (JSON.Array ps) | [p] <- V.toList ps -> do
          assertEqual "ended phase" (Just "explore") (str =<< at ["phase"] p)
          assertEqual "its fields" (Just "t") (str =<< at ["test"] p)
          assertEqual "its summary" (Just 2) (int =<< at ["found"] p)
        other -> assertFailure $ "phases: " <> show other
  , testCase "queries-and-hot-spots" $ withProgress tracking $ do
      setWorker ["pc" .= (7 :: Int), "addr" .= ("0xabc" :: Text)]
      r <- timedQuery "test-kind" [] [] (const "sat") (\started -> started >> pure (5 :: Int))
      clearWorker
      v <- currentProgress
      assertEqual "result passed through" 5 r
      assertEqual "done" (Just 1) (int =<< at ["queries", "done"] v)
      assertEqual "none in flight" (Just 0) (len =<< at ["queries", "inFlight"] v)
      assertEqual "by result" (Just ["test-kind", "sat"]) $ do
        q <- first =<< at ["queries", "byResult"] v
        sequence [str =<< at ["kind"] q, str =<< at ["result"] q]
      assertEqual "hot spot" (Just (7, "0xabc", 1)) $ do
        h <- first =<< at ["hottest"] v
        (,,) <$> (int =<< at ["pc"] h) <*> (str =<< at ["addr"] h) <*> (int =<< at ["queries"] h)
      assertEqual "no workers" (Just 0) (len =<< at ["workers"] v)
  , testCase "in-flight-query" $ withProgress tracking $ do
      gate <- newEmptyMVar
      solving <- newEmptyMVar
      finished <- newEmptyMVar
      void $ forkIO $ do
        _ <- timedQuery "slow" ["n" .= (1 :: Int)] [] (const "unsat") (\started -> started >> putMVar solving () >> takeMVar gate)
        putMVar finished ()
      takeMVar solving
      v <- currentProgress
      assertEqual "nothing done yet" (Just 0) (int =<< at ["queries", "done"] v)
      assertEqual "in flight" (Just (JSON.Bool True, "slow")) $ do
        q <- first =<< at ["queries", "inFlight"] v
        (,) <$> at ["solving"] q <*> (str =<< at ["kind"] q)
      putMVar gate ()
      takeMVar finished
      v' <- currentProgress
      assertEqual "done" (Just 1) (int =<< at ["queries", "done"] v')
      assertEqual "none in flight" (Just 0) (len =<< at ["queries", "inFlight"] v')
  , testCase "progress-over-http" $ withProgress tracking $ do
      portVar <- newEmptyMVar
      withPhase "served" [] (const []) $ withProgressServer 0 (putMVar portVar) $ do
        port <- takeMVar portVar
        v <- JSON.Object <$> httpJSON port "GET" "/progress" ""
        assertEqual "running" (Just (JSON.Bool True)) (at ["running"] v)
        assertEqual "phase" (Just "served") (str =<< at ["phase", "name"] v)
        st <- http port "GET" "/state" ""
        assertBool "no debugging session" ("not found" `BS.isInfixOf` st)
        putMVar portVar port
      port <- takeMVar portVar
      r <- try (http port "GET" "/progress" "")
      assertBool "stopped with the run" (either (\(_ :: SomeException) -> True) (const False) r)
  , testCase "debugger-serves-progress" $ withProgress tracking $ runEnv (Env defaultConfig) $
      withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> do
        vm <- liftIO $ stToIO $ abstractVM (AbstractBuf "txdata", []) branchCode Nothing False
        sess <- liftIO $ newSession emptyDapp vm
        portVar <- liftIO newEmptyMVar
        done <- liftIO newEmptyMVar
        conf <- readConfig
        let serve = serveSession (Fetch.oracle solvers Nothing Fetch.noRpc) 0 (putMVar portVar) sess
        liftIO $ bracket (forkIO (runEnv (Env { config = conf }) serve >> putMVar done ())) killThread $ \_ -> do
          port <- takeMVar portVar
          _ <- httpJSON port "POST" "/command" "continue"
          v <- JSON.Object <$> httpJSON port "GET" "/progress" ""
          assertBool "solver queries" (maybe False (>= 1) (int =<< at ["queries", "done"] v))
          assertEqual "at the first JUMPI" (Just branchJumpi) (int =<< at ["pc"] =<< first =<< at ["hottest"] v)
          _ <- http port "POST" "/quit" ""
          takeMVar done
  , testCase "debugger-logs-events" $ withSystemTempDirectory "hevm-progress" $ \dir -> do
      let file = dir <> "/log.jsonl"
      withProgress (ProgressOpts (Just file) True False False) $ runEnv (Env defaultConfig) $
        withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> do
          vm <- liftIO $ stToIO $ abstractVM (AbstractBuf "txdata", []) branchCode Nothing False
          s0 <- liftIO $ newSession emptyDapp vm
          let run = runCommandText (Fetch.oracle solvers Nothing Fetch.noRpc)
          void $ run "break op STOP" s0 >>= run "continue" >>= run "branch true" >>= run "step" >>= run "back" >>= run "branch true" >>= run "continue"
      events <- mapMaybe JSON.decodeStrict . BC.lines <$> BS.readFile file
      let named n = [ e | e <- events, at ["ev"] e == Just (JSON.String n) ]
      forM_ ["debug-command", "debug-branch-offered", "debug-branch-taken", "debug-back", "debug-breakpoint", "debug-branch-condition"] $ \n ->
        assertBool ("logs " <> show n) (not (null (named n)))
      assertEqual "one event per command" 7 (length (named "debug-command"))
      assertEqual "the branch is offered again after going back" 2 (length (named "debug-branch-offered"))
      assertEqual "where it was offered" (Just branchJumpi) (int =<< at ["pc"] =<< headMay (named "debug-branch-offered"))
      assertBool "the condition at expression verbosity" $
        maybe False (const True) (str =<< at ["cond"] =<< headMay (named "debug-branch-condition"))
      assertEqual "going back replays the branch" (Just (JSON.Bool True)) (at ["branchAgain"] =<< headMay (named "debug-back"))
  , testProperty "concurrent-progress" $ \(Workers ws) (Positive clients') ->
      within 60_000_000 $ ioProperty $ withProgress tracking $ concurrentProgress ws (min 4 clients')
  ]

tracking :: ProgressOpts
tracking = ProgressOpts Nothing False False True

-- * Concurrent use

data Op = SetWorker Int | ClearWorker | Query Int Bool | Path Bool | Tick
  deriving (Show)

newtype Workers = Workers [[Op]]
  deriving (Show)

instance Arbitrary Workers where
  arbitrary = do
    n <- chooseInt (1, 6)
    Workers <$> vectorOf n (listOf genOp)
    where
      genOp = frequency
        [ (2, SetWorker <$> chooseInt (0, 20)), (1, pure ClearWorker)
        , (3, Query <$> chooseInt (0, 2000) <*> arbitrary), (2, Path <$> arbitrary), (1, pure Tick) ]
  shrink (Workers ws) = Workers <$> shrinkList (shrinkList (const [])) ws

-- | Workers report while clients poll: every answer is consistent and only
-- ever grows, and in the end the counts are exact
concurrentProgress :: [[Op]] -> Int -> IO Property
concurrentProgress ws nClients = withPhase "fuzz" [] (const []) $ do
  portVar <- newEmptyMVar
  withProgressServer 0 (putMVar portVar) $ do
    port <- takeMVar portVar
    stop <- newIORef False
    problems <- newIORef []
    let report p = atomicModifyIORef' problems (\ps -> (p : ps, ()))
        poll i prev = do
          fin <- readIORef stop
          r <- http port "GET" "/progress" ""
          prev' <- if odd i then pure prev else case JSON.decodeStrict r of
            Nothing -> report ("not JSON: " <> show r) >> pure prev
            Just v -> do
              let counts = (fromMaybe 0 (int =<< at ["queries", "done"] v), fromMaybe 0 (int =<< at ["paths", "done"] v))
                  partial = fromMaybe 0 (int =<< at ["paths", "partial"] v)
              when (fst counts < fst prev || snd counts < snd prev) $ report ("went back: " <> show prev <> " to " <> show counts)
              when (partial > snd counts) $ report ("more partial paths than paths: " <> show r)
              unless (all (isJust . at ["kind"]) (maybe [] V.toList (arr =<< at ["queries", "inFlight"] v))) $
                report ("query without a kind: " <> show r)
              pure counts
          unless fin $ poll (i + 1 :: Int) prev'
    pollers <- forM [1 .. nClients] $ \_ -> do
      d <- newEmptyMVar
      void $ forkIO $ poll 0 (0, 0) >> putMVar d ()
      pure d
    workers <- forM ws $ \ops -> do
      d <- newEmptyMVar
      void $ forkIO $ do
        forM_ ops $ \case
          SetWorker pc -> setWorker ["pc" .= pc, "addr" .= ("0xf" :: Text)]
          ClearWorker -> clearWorker
          Query us useStarted -> void $ timedQuery "fuzz" [] [] (const "sat") $ \started -> do
            when useStarted started
            threadDelay us
          Path partial -> pathDone partial
          Tick -> phaseTick
        putMVar d ()
      pure d
    mapM_ takeMVar workers
    writeIORef stop True
    mapM_ takeMVar pollers
    v <- currentProgress
    ps <- readIORef problems
    let ops = concat ws
        expect name got want = [ name <> ": " <> show got <> ", expected " <> show want | got /= Just want ]
        lastIsSet = \case
          [] -> False
          xs -> case [ o | o <- xs, isWorkerOp o ] of
            [] -> False
            ys -> case last ys of { SetWorker _ -> True; _ -> False }
        isWorkerOp = \case { SetWorker _ -> True; ClearWorker -> True; _ -> False }
        final = concat
          [ expect "queries done" (int =<< at ["queries", "done"] v) (length [ () | Query {} <- ops ])
          , expect "in flight" (len =<< at ["queries", "inFlight"] v) 0
          , expect "paths" (int =<< at ["paths", "done"] v) (length [ () | Path _ <- ops ])
          , expect "partial" (int =<< at ["paths", "partial"] v) (length [ () | Path True <- ops ])
          , expect "ticks" (int =<< at ["phase", "done"] v) (length [ () | Tick <- ops ])
          , expect "workers" (len =<< at ["workers"] v) (length (filter lastIsSet ws))
          ]
    pure $ counterexample (unlines (reverse ps <> final)) (null ps && null final)

-- * JSON

at :: [Text] -> JSON.Value -> Maybe JSON.Value
at [] v = Just v
at (k : ks) (JSON.Object o) = KM.lookup (Key.fromText k) o >>= at ks
at _ _ = Nothing

str :: JSON.Value -> Maybe Text
str = \case { JSON.String t -> Just t; _ -> Nothing }

int :: JSON.Value -> Maybe Int
int = \case { JSON.Number n -> Just (round n); _ -> Nothing }

arr :: JSON.Value -> Maybe (V.Vector JSON.Value)
arr = \case { JSON.Array a -> Just a; _ -> Nothing }

len :: JSON.Value -> Maybe Int
len = fmap V.length . arr

headMay :: [a] -> Maybe a
headMay = listToMaybe

first :: JSON.Value -> Maybe JSON.Value
first v = arr v >>= (V.!? 0)
