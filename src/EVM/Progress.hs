{-|
Module      : EVM.Progress
Description : Live status line and JSONL log of what the interpreter and the solvers are doing

The status line is drawn on stderr while a run is in progress: redrawn in place
on a terminal, as an occasional plain line otherwise. The JSONL log is enabled
by `--verb 3` or `--progress-log FILE`; `--verb 4` or `--progress-exprs` also
logs the expressions sent to the solver. Every event is one flushed JSON line,
so a run that is killed still leaves a usable log. A heartbeat periodically
snapshots what each worker thread and each in-flight solver query is doing.
Tests get the log through 'withProgressLogFromEnv' and @HEVM_PROGRESS_LOG_DIR@.
-}
module EVM.Progress
  ( ProgressOpts(..)
  , withProgress
  , withProgressLogFromEnv
  , stopStatus
  , emit
  , emitExprs
  , withPhase
  , markPhase
  , phaseTotal
  , phaseTick
  , phaseAt
  , pathDone
  , setTaskCounter
  , bigText
  , setWorker
  , clearWorker
  , timedQuery
  ) where

import Control.Concurrent (ThreadId, forkIO, killThread, myThreadId, threadDelay)
import Control.Concurrent.MVar (MVar, newMVar, withMVar)
import Control.Applicative ((<|>))
import Control.Exception (IOException, bracket, try)
import Control.Monad (forever, join, unless, when)
import Control.Monad.IO.Unlift (MonadIO, MonadUnliftIO, liftIO, withRunInIO)
import Data.Aeson ((.=))
import Data.Aeson qualified as JSON
import Data.Aeson.Key (Key)
import Data.Aeson.Key qualified as Key
import Data.Aeson.Types (Pair)
import Data.Scientific (floatingOrInteger)
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.IORef
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import GHC.Clock (getMonotonicTime)
import System.Console.ANSI
import System.Environment (lookupEnv)
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import System.Process (readCreateProcess, shell)
import Text.Printf (printf)
import Text.Read (readMaybe)

data ProgressOpts = ProgressOpts
  { logFile :: Maybe FilePath
  , logExprs :: Bool
  , statusLine :: Bool
  }

data Worker = Worker
  { fields :: [Pair]
  , since :: Double
  }

data Query = Query
  { qFields :: [Pair]
  , qPc :: Maybe Int
  , qStart :: Double
  }

data Phase = Phase
  { name :: Text
  , done :: Int
  , total :: Int
  }

data St = St
  { logH :: Maybe Handle
  , exprs :: Bool
  , tty :: Bool
  , lock :: MVar ()
  , start :: Double
  , workers :: IORef (Map ThreadId Worker)
  , queries :: IORef (Map Int Query)
  , nextQuery :: IORef Int
  , slowestDone :: IORef (Double, Maybe Int)
  , phase :: IORef Phase
  , paths :: IORef (Int, Int)
  , taskCounter :: IORef (IO Int)
  , statusOn :: IORef Bool
  , closed :: IORef Bool
  }

-- Global so that pure-ish IO code deep in the solver layer can report progress
-- without threading a handle through every signature.
{-# NOINLINE global #-}
global :: IORef (Maybe St)
global = unsafePerformIO $ newIORef Nothing

withProgress :: MonadUnliftIO m => ProgressOpts -> m a -> m a
withProgress opts act
  | Nothing <- opts.logFile, not opts.statusLine = act
  | otherwise = withRunInIO $ \run -> bracket open close (const $ run act)
  where
    open = do
      h <- mapM (`openFile` WriteMode) opts.logFile
      mapM_ (`hSetBuffering` BlockBuffering Nothing) h
      tty <- hSupportsANSI stderr
      st <- St h opts.logExprs tty
        <$> newMVar () <*> getMonotonicTime <*> newIORef mempty <*> newIORef mempty <*> newIORef 0 <*> newIORef (0, Nothing)
        <*> newIORef (Phase "starting" 0 0) <*> newIORef (0, 0) <*> newIORef (pure 0) <*> newIORef opts.statusLine <*> newIORef False
      writeIORef global (Just st)
      write st "start" []
      threads <- sequence $ catMaybes
        [ (forkIO $ forever $ threadDelay 2000000 >> heartbeat st) <$ h
        , if opts.statusLine then Just (forkIO $ statusLoop st tty) else Nothing
        ]
      pure (st, threads, tty)
    close (st, threads, tty) = do
      mapM_ killThread threads
      clearStatus st tty
      heartbeat st
      write st "end" []
      writeIORef global Nothing
      -- threads that read the global before it was cleared may still write
      withMVar st.lock $ \_ -> do
        writeIORef st.closed True
        mapM_ hClose st.logH

-- | Writes a JSONL log of @act@ to a new file in @$HEVM_PROGRESS_LOG_DIR@, if it
-- is set. The log state is global, so only one such @act@ may run at a time:
-- pick a single test with @-p@.
withProgressLogFromEnv :: MonadUnliftIO m => String -> m a -> m a
withProgressLogFromEnv label act = liftIO (lookupEnv "HEVM_PROGRESS_LOG_DIR") >>= \case
  Nothing -> act
  Just dir -> do
    n <- liftIO $ atomicModifyIORef' logCounter (\i -> (i + 1, i))
    withProgress (ProgressOpts (Just (dir <> "/" <> label <> "-" <> show n <> ".jsonl")) False False) act

{-# NOINLINE logCounter #-}
logCounter :: IORef Int
logCounter = unsafePerformIO $ newIORef 0

-- | Stops and erases the status line, e.g. before printing results.
stopStatus :: MonadIO m => m ()
stopStatus = liftIO $ readIORef global >>= mapM_ (\st -> do
  tty <- hSupportsANSI stderr
  clearStatus st tty)

clearStatus :: St -> Bool -> IO ()
clearStatus st tty = withMVar st.lock $ \_ -> do
  on <- atomicModifyIORef' st.statusOn (False,)
  when (on && tty) $ hPutStr stderr ("\r" <> clearLineCode) >> hFlush stderr

emit :: MonadIO m => Text -> [Pair] -> m ()
emit ev fs = liftIO $ readIORef global >>= mapM_ (\st -> write st ev fs)

-- | Like 'emit', but only when expressions are logged too. The fields are
-- not evaluated otherwise, so rendering them costs nothing.
emitExprs :: MonadIO m => Text -> [Pair] -> m ()
emitExprs ev fs = liftIO $ readIORef global >>= mapM_ (\st -> when st.exprs $ write st ev fs)

-- | A long text field, cut at 20000 characters. A cut adds @<key>Chars@ with
-- the full length, so a truncated field is never mistaken for a complete one.
bigText :: Key -> Text -> [Pair]
bigText k t
  | n > limit = [k .= T.take limit t, (k <> "Chars") .= n]
  | otherwise = [k .= t]
  where
    n = T.length t
    limit = 20000

-- | Brackets a phase of a run (e.g. exploring one program) with
-- @phase-start@ and @phase-end@ events; @summary@ adds fields to the end event.
withPhase :: MonadIO m => Text -> [Pair] -> (a -> [Pair]) -> m a -> m a
withPhase name fs summary act = do
  t0 <- liftIO getMonotonicTime
  startPhase name
  emit "phase-start" (("phase" .= name) : fs)
  r <- act
  t1 <- liftIO getMonotonicTime
  emit "phase-end" (["phase" .= name, "secs" .= (t1 - t0)] <> fs <> summary r)
  phaseDoneLine name (t1 - t0) (summary r)
  pure r

-- | Leaves a finished phase on the screen as a line of its own; the status
-- line continues below it.
phaseDoneLine :: MonadIO m => Text -> Double -> [Pair] -> m ()
phaseDoneLine name secs fs = liftIO $ readIORef global >>= mapM_ (\st -> withMVar st.lock $ \_ -> do
  on <- readIORef st.statusOn
  when on $ do
    let fields = T.intercalate " │ " [Key.toText k <> " " <> val v | (k, v) <- fs]
        txt = name <> T.pack (printf " %.1fs" secs) <> (if T.null fields then "" else " │ " <> fields)
    if st.tty
      then hPutStrLn stderr $ "\r" <> clearLineCode
             <> setSGRCode [SetColor Foreground Vivid Green] <> "✓ " <> setSGRCode [Reset]
             <> setSGRCode [SetConsoleIntensity BoldIntensity] <> T.unpack txt <> setSGRCode [Reset]
      else T.hPutStrLn stderr ("hevm: done " <> txt)
    hFlush stderr)
  where
    val = \case
      JSON.String t -> t
      JSON.Number n -> T.pack $ either (show :: Double -> String) (show :: Integer -> String) (floatingOrInteger n)
      v -> T.pack (show v)

-- | Marks the start of a phase that has no end event of its own, e.g. one
-- that ends by exiting; the final @end@ event closes it.
markPhase :: MonadIO m => Text -> [(Text, Int)] -> m ()
markPhase name fs = do
  startPhase name
  emit "phase-start" (("phase" .= name) : [Key.fromText k .= v | (k, v) <- fs])

startPhase :: MonadIO m => Text -> m ()
startPhase n = liftIO $ readIORef global >>= mapM_ (\st -> do
  writeIORef st.phase (Phase n 0 0)
  writeIORef st.paths (0, 0))

-- | How many items the current phase works through, for the status line.
phaseTotal :: MonadIO m => Int -> m ()
phaseTotal n = modifyPhase $ \p -> p { total = n }

phaseTick :: MonadIO m => m ()
phaseTick = modifyPhase $ \p -> p { done = p.done + 1 }

phaseAt :: MonadIO m => Int -> m ()
phaseAt i = modifyPhase $ \p -> p { done = i }

modifyPhase :: MonadIO m => (Phase -> Phase) -> m ()
modifyPhase f = liftIO $ readIORef global >>= mapM_ (\st -> atomicModifyIORef' st.phase ((,()) . f))

-- | Counts a finished path; @partial@ if it could not be fully explored.
pathDone :: MonadIO m => Bool -> m ()
pathDone partial = liftIO $ readIORef global >>= mapM_ (\st ->
  atomicModifyIORef' st.paths $ \(n, p) -> ((n + 1, if partial then p + 1 else p), ()))

-- | Registers how to read the number of interpreter tasks that are alive.
setTaskCounter :: MonadIO m => IO Int -> m ()
setTaskCounter c = liftIO $ readIORef global >>= mapM_ (\st -> writeIORef st.taskCounter c)

-- | Records what the calling thread is working on, shown in heartbeats and
-- attached to the solver queries it issues.
setWorker :: MonadIO m => [Pair] -> m ()
setWorker fs = liftIO $ readIORef global >>= mapM_ (\st -> do
  tid <- myThreadId
  now <- getMonotonicTime
  atomicModifyIORef' st.workers $ \m -> (Map.insert tid (Worker fs now) m, ()))

clearWorker :: MonadIO m => m ()
clearWorker = liftIO $ readIORef global >>= mapM_ (\st -> do
  tid <- myThreadId
  atomicModifyIORef' st.workers $ \m -> (Map.delete tid m, ()))

-- | Logs a solver query, tagged with the calling worker's context, together
-- with its duration and the result rendered by @showRes@.
timedQuery :: Text -> [Pair] -> (r -> Text) -> IO r -> IO r
timedQuery kind fs showRes act = readIORef global >>= \case
  Nothing -> act
  Just st -> do
    tid <- myThreadId
    ctx <- maybe [] (.fields) . Map.lookup tid <$> readIORef st.workers
    qid <- atomicModifyIORef' st.nextQuery $ \n -> (n + 1, n)
    t0 <- getMonotonicTime
    let qfs = ["query" .= qid, "kind" .= kind] <> fs <> ctx
        pc = case lookup "pc" ctx of
          Just (JSON.Number n) -> Just (round n)
          _ -> Nothing
    atomicModifyIORef' st.queries $ \m -> (Map.insert qid (Query qfs pc t0) m, ())
    write st "query-start" qfs
    r <- act
    t1 <- getMonotonicTime
    atomicModifyIORef' st.queries $ \m -> (Map.delete qid m, ())
    atomicModifyIORef' st.slowestDone $ \old -> (if t1 - t0 > fst old then (t1 - t0, pc) else old, ())
    write st "query-end" ["query" .= qid, "kind" .= kind, "secs" .= (t1 - t0), "result" .= showRes r]
    pure r

heartbeat :: St -> IO ()
heartbeat st = do
  now <- getMonotonicTime
  ws <- Map.toList <$> readIORef st.workers
  qs <- Map.elems <$> readIORef st.queries
  write st "heartbeat"
    [ "workers" .= [JSON.object (["thread" .= T.pack (show tid), "secs" .= (now - w.since)] <> w.fields) | (tid, w) <- ws]
    , "queries" .= [JSON.object (("secs" .= (now - q.qStart)) : q.qFields) | q <- qs]
    ]

write :: St -> Text -> [Pair] -> IO ()
write st ev fs = case st.logH of
  Nothing -> pure ()
  Just h -> do
    now <- getMonotonicTime
    tid <- myThreadId
    let line = JSON.encode $ JSON.object (["t" .= (now - st.start), "ev" .= ev, "thread" .= T.pack (show tid)] <> fs)
    withMVar st.lock $ \_ -> do
      isClosed <- readIORef st.closed
      unless isClosed $ do
        BL.hPutStrLn h line
        hFlush h

-- | Redraws the status line in place on a terminal; elsewhere (CI, pipes)
-- prints it as a plain line every 30 seconds instead.
statusLoop :: St -> Bool -> IO ()
statusLoop st tty = do
  -- not ansi-terminal's getTerminalSize: it queries the cursor position on
  -- stdout and reads the answer from stdin
  cols <- lookupEnv "COLUMNS"
  stty <- if tty
    then try (readCreateProcess (shell "stty size < /dev/tty 2>/dev/null") "") :: IO (Either IOException String)
    else pure (Left (userError "not a terminal"))
  let width = fromMaybe 100 $ (readMaybe =<< cols) <|> (either (const Nothing) (readMaybe . drop 1 . dropWhile (/= ' ') . takeWhile (/= '\n')) stty)
  go width (0 :: Int)
  where
    go width i = do
      threadDelay (if tty then 100000 else 30000000)
      segs <- statusSegments st
      withMVar st.lock $ \_ -> do
        on <- readIORef st.statusOn
        when on $
          if tty then do
            hPutStr stderr $ "\r" <> render (spinner i) width segs <> clearFromCursorToLineEndCode
            hFlush stderr
          else T.hPutStrLn stderr ("hevm: " <> T.intercalate " | " [T.strip (T.unwords (filter (Prelude.not . T.null) [l, v])) | (l, _, v) <- segs])
      on <- readIORef st.statusOn
      when on $ go width (i + 1)
    spinner i = T.singleton $ "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏" !! (i `mod` 10)

-- | Label (coloured) and value (plain, fixed width) of each part of the
-- status line. Every part is always shown and padded, so that the line does
-- not shift around as the numbers change.
statusSegments :: St -> IO [(Text, [SGR], Text)]
statusSegments st = do
  now <- getMonotonicTime
  p <- readIORef st.phase
  (nPaths, nPartial) <- readIORef st.paths
  tasks <- join (readIORef st.taskCounter)
  nWorkers <- Map.size <$> readIORef st.workers
  qs <- Map.elems <$> readIORef st.queries
  qDone <- readIORef st.nextQuery
  done <- readIORef st.slowestDone
  let running = length qs
      -- a query still running counts too, so a hanging one shows up
      (slowSecs, slowPc) = maximumOn fst $ done : [(now - q.qStart, q.qPc) | q <- qs]
      slowest
        | slowSecs > 0 = T.pack (printf "%6.1fs" slowSecs) <> maybe "         " (\pc -> " @pc " <> pad 5 pc) slowPc
        | otherwise = T.replicate 17 " "
      elapsed = now - st.start
      progress
        | p.total > 0 = pad (T.length (tshow p.total)) p.done <> "/" <> tshow p.total
        | otherwise = ""
  pure
    [ (T.justifyLeft 11 ' ' p.name, [bold, fg Magenta], progress)
    , ("paths", [fg Green], pad 6 nPaths <> " (" <> pad 5 nPartial <> " partial)")
    , ("tasks", [], pad 6 tasks <> ", " <> pad 3 nWorkers <> " busy")
    , ("SMT", [fg Blue], pad 7 (qDone - running) <> " done, " <> pad 3 running <> " running")
    , ("slowest", [fg Yellow], slowest)
    , ("", [], T.pack $ printf "%3d:%02d" (floor (elapsed / 60) :: Int) (floor elapsed `mod` 60 :: Int))
    ]
  where
    bold = SetConsoleIntensity BoldIntensity
    fg c = SetColor Foreground Vivid c
    tshow :: Show a => a -> Text
    tshow = T.pack . show
    pad :: Show a => Int -> a -> Text
    pad n = T.justifyRight n ' ' . tshow
    maximumOn f = foldr1 (\a b -> if f a >= f b then a else b)

-- | The segments, cut to @width@ columns, with colours.
render :: Text -> Int -> [(Text, [SGR], Text)] -> String
render spin width segs = go (width - 2) (zip [0 :: Int ..] segs) (setSGRCode [SetColor Foreground Vivid Cyan] <> T.unpack spin <> " " <> setSGRCode [Reset])
  where
    go _ [] acc = acc
    go room ((i, (label, sgr, value)) : rest) acc
      | room <= 0 = acc
      | otherwise =
          let sep = T.take room (if i == 0 then "" else " │ ")
              lbl = T.take (room - T.length sep) label
              val = T.take (room - T.length sep - T.length lbl) (if T.null label || T.null value then value else " " <> value)
              dim = setSGRCode [SetConsoleIntensity FaintIntensity]
          in go (room - T.length sep - T.length lbl - T.length val) rest $
               acc <> dim <> T.unpack sep <> setSGRCode [Reset]
                   <> setSGRCode sgr <> T.unpack lbl <> setSGRCode [Reset] <> T.unpack val
