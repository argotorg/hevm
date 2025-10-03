{- |
    Module: EVM.Solvers
    Description: Solver orchestration
-}
module EVM.Solvers where

import Prelude hiding (LT, GT)

import GHC.Natural
import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.STM (writeTChan, newTChan, TChan, tryReadTChan, atomically)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set, isSubsetOf, fromList, toList)
import Data.Maybe (fromMaybe, isJust, fromJust)
import Data.Either (isLeft)
import Data.Text qualified as TStrict
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Text.Lazy.Builder
import qualified Data.Text.Lazy.Builder.Int (decimal)
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..), createPipe)
import System.FilePath ((</>))
import EVM.Effects
import Data.Bits ((.&.))
import Numeric (showHex)
import EVM.Expr (simplifyProps)

import EVM.Keccak qualified as Keccak (concreteKeccaks)
import EVM.SMT
import EVM.Types

-- | Supported solvers
data Solver
  = Z3
  | CVC5
  | Bitwuzla
  | EmptySolver
  | Custom Text

instance Show Solver where
  show Z3 = "z3"
  show CVC5 = "cvc5"
  show Bitwuzla = "bitwuzla"
  show EmptySolver = "empty-smt-solver"
  show (Custom s) = T.unpack s


-- | A running solver instance
data SolverInstance = SolverInstance
  { solvertype :: Solver
  , stdin      :: Handle
  , stdout     :: Handle
  , process    :: ProcessHandle
  }

-- | A channel representing a group of solvers
newtype SolverGroup = SolverGroup (Chan Task)

data MultiSol = MultiSol
  { maxSols :: Int
  , numBytes :: Int
  , var :: String
  }

-- | A script to be executed, a list of models to be extracted in the case of a sat result, and a channel where the result should be written
data Task = TaskSingle SingleData | TaskMulti MultiData

newtype CacheEntry = CacheEntry [Prop]
  deriving (Show, Eq)

data MultiData = MultiData
  { smt2 :: SMT2
  , multiSol :: MultiSol
  , resultChan :: Chan (Maybe [W256])
  }

data SingleData = SingleData
  { smt2 :: SMT2
  , props :: Maybe [Prop]
  , resultChan :: Chan SMTResult
  }

-- returns True if a is a superset of any of the sets in bs
supersetAny :: Set Prop -> [Set Prop] -> Bool
supersetAny a bs = any (`isSubsetOf` a) bs

checkMulti :: SolverGroup -> Err SMT2 -> MultiSol -> IO (Maybe [W256])
checkMulti (SolverGroup taskq) smt2 multiSol = do
  if isLeft smt2 then pure Nothing
  else do
    -- prepare result channel
    resChan <- newChan
    -- send task to solver group
    writeChan taskq (TaskMulti (MultiData (getNonError smt2) multiSol resChan))
    -- collect result
    readChan resChan

checkSatWithProps :: App m => SolverGroup -> [Prop] -> m (SMTResult)
checkSatWithProps sg props = do
  conf <- readConfig
  let psSimp = if conf.simp then simplifyProps props else props
  if psSimp == [PBool False] then pure Qed
  else do
    let concreteKeccaks = fmap (\(buf,val) -> PEq (Lit val) (Keccak buf)) (toList $ Keccak.concreteKeccaks props)
    let smt2 = assertProps conf (if conf.simp then psSimp <> concreteKeccaks else psSimp)
    if isLeft smt2 then pure $ Error $ getError smt2
    else liftIO $ checkSat sg (Just props) smt2

-- When props is Nothing, the cache will not be filled or used
checkSat :: SolverGroup -> Maybe [Prop] -> Err SMT2 -> IO SMTResult
checkSat (SolverGroup taskq) props smt2 = do
  if isLeft smt2 then pure $ Error $ getError smt2
  else do
    -- prepare result channel
    resChan <- newChan
    -- send task to solver group
    writeChan taskq (TaskSingle (SingleData (getNonError smt2) props resChan))
    -- collect result
    readChan resChan

writeSMT2File :: SMT2 -> FilePath -> String -> IO ()
writeSMT2File smt2 path postfix = do
    let content = formatSMT2 smt2 <> "\n\n(check-sat)"
        fullPath = path </> "query-" <> postfix <> ".smt2"
    T.writeFile fullPath content

withSolvers :: App m => Solver -> Natural -> Natural -> Maybe Natural -> (SolverGroup -> m a) -> m a
withSolvers solver count threads timeout cont = do
    -- spawn solvers
    instances <- mapM (const $ liftIO $ spawnSolver solver threads timeout) [1..count]
    -- spawn orchestration thread
    taskq <- liftIO newChan
    cacheq <- liftIO . atomically $ newTChan
    availableInstances <- liftIO newChan
    liftIO $ forM_ instances (writeChan availableInstances)
    orchestrate' <- toIO $ orchestrate taskq cacheq availableInstances [] 0
    orchestrateId <- liftIO $ forkIO orchestrate'

    -- run continuation with task queue
    res <- cont (SolverGroup taskq)

    -- cleanup and return results
    liftIO $ mapM_ (stopSolver) instances
    liftIO $ killThread orchestrateId
    pure res
  where
    orchestrate :: App m => Chan Task -> TChan CacheEntry -> Chan SolverInstance -> [Set Prop] -> Int -> m b
    orchestrate taskq cacheq avail knownUnsat fileCounter = do
      conf <- readConfig
      mx <- liftIO . atomically $ tryReadTChan cacheq
      case mx of
        Just (CacheEntry props)  -> do
          let knownUnsat' = (fromList props):knownUnsat
          when conf.debug $ liftIO $ putStrLn "   adding UNSAT cache"
          orchestrate taskq cacheq avail knownUnsat' fileCounter
        Nothing -> do
          task <- liftIO $ readChan taskq
          case task of
            TaskSingle (SingleData _ props r) | isJust props && supersetAny (fromList (fromJust props)) knownUnsat -> do
              liftIO $ writeChan r Qed
              when conf.debug $ liftIO $ putStrLn "   Qed found via cache!"
              orchestrate taskq cacheq avail knownUnsat fileCounter
            _ -> do
              inst <- liftIO $ readChan avail
              runTask' <- case task of
                TaskSingle (SingleData smt2 props r) -> toIO $ getOneSol smt2 props r cacheq inst avail fileCounter
                TaskMulti (MultiData smt2 multiSol r) -> toIO $ getMultiSol smt2 multiSol r inst avail fileCounter
              _ <- liftIO $ forkIO runTask'
              orchestrate taskq cacheq avail knownUnsat (fileCounter + 1)

getMultiSol :: forall m. (MonadIO m, ReadConfig m) => SMT2 -> MultiSol -> (Chan (Maybe [W256])) -> SolverInstance -> Chan SolverInstance -> Int -> m ()
getMultiSol smt2@(SMT2 cmds cexvars _) multiSol r inst availableInstances fileCounter = do
  conf <- readConfig
  when conf.dumpQueries $ liftIO $ writeSMT2File smt2 "." (show fileCounter)
  -- reset solver and send all lines of provided script
  out <- liftIO $ do
    resetRes <- sendScript inst $ SMTScript [SMTCommand "(reset)"]
    case resetRes of
      e@(Left _) -> pure e
      _ -> sendScript inst cmds
  case out of
    Left err -> liftIO $ do
      when conf.debug $ putStrLn $ "Unable to write SMT to solver: " <> (T.unpack err)
      writeChan r Nothing
    Right _ -> do
      sat <- liftIO $ sendCommand inst $ SMTCommand "(check-sat)"
      when conf.dumpQueries $ liftIO $ writeSMT2File smt2 "." (show fileCounter <> "-origquery")
      subRun [] smt2 sat
  -- put the instance back in the list of available instances
  liftIO $ writeChan availableInstances inst
  where
    maskFromBytesCount k
      | k <= 32 = (2 ^ (8 * k) - 1)
      | otherwise = internalError "Byte length exceeds 256-bit capacity"
    subRun :: (MonadIO m, ReadConfig m) => [W256] -> SMT2 -> Text -> m ()
    subRun vals fullSmt sat = do
      conf <- readConfig
      case sat of
        "unsat" -> liftIO $ do
          when conf.debug $ putStrLn $ "No more solutions to query, returning: " <> show vals
          liftIO $ writeChan r (Just vals)
        "timeout" -> liftIO $ do
           when conf.debug $ putStrLn "Timeout inside SMT solver."
           writeChan r Nothing
        "unknown" -> liftIO $ do
           when conf.debug $ putStrLn "Unknown result by SMT solver."
           dumpUnsolved fullSmt fileCounter conf.dumpUnsolved
           writeChan r Nothing
        "sat" -> do
          if length vals >= multiSol.maxSols then liftIO $ do
            when conf.debug $ putStrLn "Too many solutions to symbolic query."
            writeChan r Nothing
          else do
            cex <- liftIO $ getModel inst cexvars
            case Map.lookup (Var (TStrict.pack multiSol.var)) cex.vars of
              Just v -> do
                let hexMask = maskFromBytesCount multiSol.numBytes
                    maskedVal = v .&. hexMask
                    toSMT n = Data.Text.Lazy.Builder.Int.decimal n
                    maskedVar = "(bvand " <> fromString multiSol.var <> " (_ bv" <> toSMT hexMask <> " 256))"
                    restrict = SMTCommand $ "(assert (not (= " <> maskedVar <> " (_ bv" <> toSMT maskedVal <> " 256))))"
                    newSmt = fullSmt <> SMT2 (SMTScript [restrict]) mempty mempty
                when conf.debug $ liftIO $ putStrLn $ "Got one solution to symbolic query, val: 0x" <> (showHex maskedVal "") <>
                  " now have " <> show (length vals + 1) <> " solution(s), max is: " <> show multiSol.maxSols
                when conf.dumpQueries $ liftIO $ writeSMT2File newSmt "." (show fileCounter <> "-sol" <> show (length vals))
                out <- liftIO $ sendCommand inst restrict
                case out of
                  "success" -> do
                    out2 <- liftIO $ sendCommand inst  (SMTCommand "(check-sat)")
                    subRun (maskedVal:vals) newSmt out2
                  err -> liftIO $ do
                    when conf.debug $ putStrLn $ "Unable to write SMT to solver: " <> (T.unpack err)
                    writeChan r Nothing
              Nothing -> internalError $ "variable " <>  multiSol.var <> " not part of model (i.e. cex) ... that's not possible"
        err -> liftIO $ do
          when conf.debug $ putStrLn $ "Unable to write SMT to solver: " <> (T.unpack err)
          writeChan r Nothing

getOneSol :: (MonadIO m, ReadConfig m) => SMT2 -> Maybe [Prop] -> Chan SMTResult -> TChan CacheEntry -> SolverInstance -> Chan SolverInstance -> Int -> m ()
getOneSol smt2@(SMT2 cmds cexvars _) props r cacheq inst availableInstances fileCounter = do
  conf <- readConfig
  liftIO $ do
    when (conf.dumpQueries) $ writeSMT2File smt2 "." (show fileCounter)
    -- reset solver and send all lines of provided script
    out <- do
      resetRes <- sendScript inst $ SMTScript [SMTCommand "(reset)"]
      case resetRes of
        e@(Left _) -> pure e
        _ -> sendScript inst cmds
    case out of
      -- if we got an error then return it
      Left e -> writeChan r (Error $ "Error while writing SMT to solver: " <> T.unpack e)
      -- otherwise call (check-sat), parse the result, and send it down the result channel
      Right () -> do
        sat <- sendCommand inst $ SMTCommand "(check-sat)"
        res <- do
            case sat of
              "unsat" -> do
                when (isJust props) $ liftIO . atomically $ writeTChan cacheq (CacheEntry (fromJust props))
                pure Qed
              "timeout" -> pure $ Unknown "Result timeout by SMT solver"
              "unknown" -> do
                dumpUnsolved smt2 fileCounter conf.dumpUnsolved
                pure $ Unknown "Result unknown by SMT solver"
              "sat" -> Cex <$> getModel inst cexvars
              _ -> pure . Error $ "Unable to parse SMT solver output: " <> T.unpack sat
        writeChan r res

    -- put the instance back in the list of available instances
    writeChan availableInstances inst

dumpUnsolved :: SMT2 -> Int -> Maybe FilePath -> IO ()
dumpUnsolved fullSmt fileCounter dump = do
   case dump of
     Just path -> writeSMT2File fullSmt path $ "unsolved-" <> show fileCounter
     Nothing -> pure ()

getModel :: SolverInstance -> CexVars -> IO SMTCex
getModel inst cexvars = do
  -- get an initial version of the model from the solver
  initialModel <- getRaw
  -- check the sizes of buffer models and shrink if needed
  if bufsUsable initialModel
  then pure initialModel
  else do
    -- get concrete values for each buffers max read index
    hints <- capHints <$> queryMaxReads (getValue inst) cexvars.buffers
    snd <$> runStateT (shrinkModel hints) initialModel
  where
    getRaw :: IO SMTCex
    getRaw = do
      vars <- getVars parseVar (getValue inst) (fmap T.toStrict cexvars.calldata)
      addrs <- getAddrs parseEAddr (getValue inst) (fmap T.toStrict cexvars.addrs)
      buffers <- getBufs (getValue inst) (Map.keys cexvars.buffers)
      storage <- getStore (getValue inst) cexvars.storeReads
      blockctx <- getVars parseBlockCtx (getValue inst) (fmap T.toStrict cexvars.blockContext)
      txctx <- getVars parseTxCtx (getValue inst) (fmap T.toStrict cexvars.txContext)
      pure $ SMTCex vars addrs buffers storage blockctx txctx

    -- sometimes the solver might give us back a model for the max read index
    -- that is too high to be a useful cex (e.g. in the case of reads from a
    -- symbolic index), so we cap the max value of the starting point to be 1024
    capHints :: Map Text W256 -> Map Text W256
    capHints = fmap (min 1024)

    -- shrink all the buffers in a model
    shrinkModel :: Map Text W256 -> StateT SMTCex IO ()
    shrinkModel hints = do
      m <- get
      -- iterate over all the buffers in the model, and shrink each one in turn if needed
      forM_ (Map.keys m.buffers) $ \case
        AbstractBuf b -> do
          let name = T.fromStrict b
              hint = fromMaybe
                       (internalError $ "Could not find hint for buffer: " <> T.unpack name)
                       (Map.lookup name hints)
          shrinkBuf name hint
        _ -> internalError "Received model from solver for non AbstractBuf"

    -- starting with some guess at the max useful size for a buffer, cap
    -- it's size to that value, and ask the solver to check satisfiability. If
    -- it's still sat with the new constraint, leave that constraint on the
    -- stack and return a new model, if it's unsat, double the size of the hint
    -- and try again.
    shrinkBuf :: Text -> W256 -> StateT SMTCex IO ()
    shrinkBuf buf hint = do
      let encBound = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal hint <> " 256)"
      answer <- liftIO $ do
        checkCommand inst $ SMTCommand "(push 1)"
        checkCommand inst $ SMTCommand ("(assert (bvule " <> (fromLazyText buf) <> "_length " <> encBound <> "))")
        sendCommand inst $ SMTCommand "(check-sat)"
      case answer of
        "sat" -> do
          model <- liftIO getRaw
          put model
        "unsat" -> do
          liftIO $ checkCommand inst $ SMTCommand "(pop 1)"
          let nextHint = if hint == 0 then 1 else hint * 2
          if nextHint < hint || nextHint > 1_073_741_824
            then pure () -- overflow or over 1GB
            else shrinkBuf buf nextHint
        _ -> do -- unexpected answer -> clean up and do not change the model
          liftIO $ checkCommand inst $ SMTCommand "(pop 1)"
          pure ()


    -- we set a pretty arbitrary upper limit (of 1024) to decide if we need to do some shrinking
    bufsUsable :: SMTCex -> Bool
    bufsUsable model = any (go . snd) (Map.toList model.buffers)
      where
        go (Flat _) = True
        go (Comp c) = case c of
          (Base _ sz) -> sz <= 1024
          -- TODO: do I need to check the write idx here?
          (Write _ idx next) -> idx <= 1024 && go (Comp next)

mkTimeout :: Maybe Natural -> Text
mkTimeout t = T.pack $ show $ (1000 *)$ case t of
  Nothing -> 300 :: Natural
  Just t' -> t'

-- | Arguments used when spawning a solver instance
solverArgs :: Solver -> Natural -> Maybe Natural -> [Text]
solverArgs solver threads timeout = case solver of
  Bitwuzla ->
    [ "--lang=smt2"
    , "--produce-models"
    , "--time-limit-per=" <> mkTimeout timeout
    , "--bv-solver=preprop"
    , "--bv-output-format=16"
    ]
  Z3 ->
    [ "-st"
    , "smt.threads=" <> (T.pack $ show threads)
    , "-in" ]
  CVC5 ->
    [ "--lang=smt"
    , "--produce-models"
    , "--print-success"
    , "--interactive"
    , "--incremental"
    , "--tlimit-per=" <> mkTimeout timeout
    , "--arrays-exp"
    ]
  EmptySolver -> []
  Custom _ -> []

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: Solver -> Natural -> Maybe (Natural) -> IO SolverInstance
spawnSolver solver threads timeout = do
  (readout, writeout) <- createPipe
  let cmd
        = (proc (show solver) (fmap T.unpack $ solverArgs solver threads timeout ))
            { std_in = CreatePipe
            , std_out = UseHandle writeout
            , std_err = UseHandle writeout
            }
  (Just stdin, Nothing, Nothing, process) <- createProcess cmd
  hSetBuffering stdin (BlockBuffering (Just 1000000))
  let solverInstance = SolverInstance solver stdin readout process

  case solver of
    CVC5 -> pure solverInstance
    Bitwuzla -> do
      _ <- sendCommand solverInstance $ SMTCommand "(set-option :print-success true)"
      pure solverInstance
    EmptySolver -> pure solverInstance
    Z3 -> do
      _ <- sendCommand solverInstance $ SMTCommand "(set-option :print-success true)"
      _ <- sendCommand solverInstance $ SMTCommand ("(set-option :timeout " <> (fromLazyText $ mkTimeout timeout) <> ")")
      pure solverInstance
    Custom _ -> pure solverInstance

-- | Cleanly shutdown a running solver instance
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout process) = cleanupProcess (Just stdin, Just stdout, Nothing, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendScript :: SolverInstance -> SMTScript -> IO (Either Text ())
sendScript solver (SMTScript entries) = do
  go entries
  where
    go [] = pure $ Right ()
    go (SMTComment _ : rest) = go rest
    go (c@(SMTCommand command):cs) = do
      out <- sendCommand solver c
      case out of
        "success" -> go cs
        e -> pure $ Left $ "Solver returned an error:\n" <> e <> "\nwhile sending the following command: " <> toLazyText command

checkCommand :: SolverInstance -> SMTEntry -> IO ()
checkCommand inst cmd = do
  res <- sendCommand inst cmd
  case res of
    "success" -> pure ()
    _ -> internalError $ "Unexpected solver output: " <> T.unpack res


-- | Strips trailing \r, if present
stripCarriageReturn :: Text -> Text
stripCarriageReturn t = fromMaybe t $ T.stripSuffix "\r" t

-- | Sends a string to the solver and appends a newline, returns the first available line from the output buffer
sendCommand :: SolverInstance -> SMTEntry -> IO Text
sendCommand _ (SMTComment _) = internalError "Attempting to send a comment as a command to SMT solver"
sendCommand (SolverInstance _ stdin stdout _) (SMTCommand cmd) = do
  T.hPutStrLn stdin $ toLazyText cmd
  hFlush stdin
  stripCarriageReturn <$> (T.hGetLine stdout)

-- | Returns a string representation of the model for the requested variable
getValue :: SolverInstance -> Text -> IO Text
getValue (SolverInstance _ stdin stdout _) var = do
  T.hPutStrLn stdin (T.append (T.append "(get-value (" var) "))")
  hFlush stdin
  fmap (T.unlines . reverse) (readSExpr stdout)

-- | Reads lines from h until we have a balanced sexpr
readSExpr :: Handle -> IO [Text]
readSExpr h = go 0 0 []
  where
    go 0 0 _ = do
      line <- T.hGetLine h
      let cleanLine = stripCarriageReturn line
          ls = T.length $ T.filter (== '(') cleanLine
          rs = T.length $ T.filter (== ')') cleanLine
      if ls == rs
         then pure [cleanLine]
         else go ls rs [cleanLine]
    go ls rs prev = do
      line <- T.hGetLine h
      let cleanLine = stripCarriageReturn line
          ls' = T.length $ T.filter (== '(') cleanLine
          rs' = T.length $ T.filter (== ')') cleanLine
      if (ls + ls') == (rs + rs')
         then pure $ cleanLine : prev
         else go (ls + ls') (rs + rs') (cleanLine : prev)
