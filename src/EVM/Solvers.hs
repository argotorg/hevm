{- |
    Module: EVM.Solvers
    Description: Solver orchestration
-}
{-# LANGUAGE CPP #-}
module EVM.Solvers
  ( withSolvers
  , Solver(..)
  , SolverGroup(..)
  , Task
  , MultiSol(..)
  , checkSat
  , checkSatWithProps
  , checkMulti
  , defMemLimit
  ) where



import Prelude hiding (LT, GT)

import GHC.Natural
import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.QSem (QSem, newQSem, waitQSem, signalQSem)
import Control.Exception (bracket, bracket_, try, IOException)
import Control.Concurrent.STM (writeTChan, newTChan, TChan, tryReadTChan, atomically)
import Control.Monad
import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set, isSubsetOf, fromList, toList)
import Data.Maybe (fromMaybe, isJust, fromJust)
import Data.Either (isLeft)
import Data.Foldable (for_)
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
import EVM.SMT.DivEncoding
import EVM.Types


-- In megabytes, i.e. 1GB
defMemLimit :: Natural
defMemLimit = 1024

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
  Solver -- solver type
  Handle -- stdin
  Handle -- stdout
  ProcessHandle

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
  SMT2
  MultiSol
  (Chan (Maybe [W256])) -- result channel

data SingleData = SingleData
  SMT2
  (Maybe [Prop])
  (Chan SMTResult) -- result channel

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
    let allProps = if conf.simp then psSimp <> concreteKeccaks else psSimp
    if not conf.abstractArith then do
      -- Original path: direct encoding with concrete division semantics
      let smt2 = assertProps conf allProps
      if isLeft smt2 then pure $ Error $ getError smt2
      else liftIO $ checkSat sg (Just props) smt2
    else do
      -- Two-phase solving with abstract division
      -- Phase 1: Use uninterpreted functions (overapproximation)
      let smt2Abstract = assertPropsAbstract conf allProps
      if isLeft smt2Abstract then pure $ Error $ getError smt2Abstract
      else do
        phase1 <- liftIO $ checkSat sg (Just props) smt2Abstract
        case phase1 of
          Qed -> pure Qed            -- UNSAT with abstractions => truly UNSAT (sound)
          e@(Error _) -> pure e
          u@(Unknown _) -> pure u
          Cex _ -> do
            -- Phase 2: Refine with exact definitions to validate counterexample
            when conf.debug $ liftIO $ putStrLn "Abstract div/mod: potential cex found, refining..."
            let smt2Refined = assertPropsRefined conf allProps
            if isLeft smt2Refined then pure $ Error $ getError smt2Refined
            else do
              when conf.dumpQueries $ liftIO $ writeSMT2File (getNonError smt2Refined) "." "refined"
              phase2 <- liftIO $ checkSat sg (Just props) smt2Refined
              case phase2 of
                Unknown _ -> do
                  -- Phase 3: Try shift-based bounds (avoids bvudiv entirely).
                  -- This is an overapproximation: only UNSAT results are sound.
                  -- SAT/Unknown results are discarded (fall back to phase2 Unknown).
                  when conf.debug $ liftIO $ putStrLn "Phase 2 unknown, trying shift-based bounds..."
                  let smt2Shift = assertPropsShiftBounds conf allProps
                  if isLeft smt2Shift then pure phase2
                  else do
                    when conf.dumpQueries $ liftIO $ writeSMT2File (getNonError smt2Shift) "." "shift-bounds"
                    phase3 <- liftIO $ checkSat sg (Just props) smt2Shift
                    case phase3 of
                      Qed -> pure Qed  -- UNSAT with shift bounds => truly UNSAT
                      _   -> pure phase2  -- SAT/Unknown from shift bounds is not reliable
                _ -> pure phase2

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

withSolvers :: App m => Solver -> Natural -> Maybe Natural -> Natural -> (SolverGroup -> m a) -> m a
withSolvers solver count timeout maxMemory cont = do
    -- spawn orchestration thread
    taskq <- liftIO newChan
    cacheq <- liftIO . atomically $ newTChan
    sem <- liftIO $ newQSem (fromIntegral count)
    orchestrate' <- toIO $ orchestrate taskq cacheq sem [] 0
    orchestrateId <- liftIO $ forkIO orchestrate'

    -- run continuation with task queue
    res <- cont (SolverGroup taskq)

    -- cleanup and return results
    liftIO $ killThread orchestrateId
    pure res
  where
    orchestrate :: App m => Chan Task -> TChan CacheEntry -> QSem -> [Set Prop] -> Int -> m b
    orchestrate taskq cacheq sem knownUnsat fileCounter = do
      conf <- readConfig
      mx <- liftIO . atomically $ tryReadTChan cacheq
      case mx of
        Just (CacheEntry props)  -> do
          let knownUnsat' = (fromList props):knownUnsat
          when conf.debug $ liftIO $ putStrLn "   adding UNSAT cache"
          orchestrate taskq cacheq sem knownUnsat' fileCounter
        Nothing -> do
          task <- liftIO $ readChan taskq
          case task of
            TaskSingle (SingleData _ props r) | isJust props && supersetAny (fromList (fromJust props)) knownUnsat -> do
              liftIO $ writeChan r Qed
              when conf.debug $ liftIO $ putStrLn "   Qed found via cache!"
              orchestrate taskq cacheq sem knownUnsat fileCounter
            _ -> do
              runTask' <- case task of
                TaskSingle (SingleData smt2 props r) -> toIO $ getOneSol solver timeout maxMemory smt2 props r cacheq sem fileCounter
                TaskMulti (MultiData smt2 multiSol r) -> toIO $ getMultiSol solver timeout maxMemory smt2 multiSol r sem fileCounter
              _ <- liftIO $ forkIO runTask'
              orchestrate taskq cacheq sem knownUnsat (fileCounter + 1)

getMultiSol :: forall m. (MonadIO m, ReadConfig m) => Solver -> Maybe Natural -> Natural -> SMT2 -> MultiSol -> Chan (Maybe [W256]) -> QSem -> Int -> m ()
getMultiSol solver timeout maxMemory smt2@(SMT2 cmds cexvars _) multiSol r sem fileCounter = do
  conf <- readConfig
  let
    maskFromBytesCount k
      | k <= 32 = (2 ^ (8 * k) - 1)
      | otherwise = internalError "Byte length exceeds 256-bit capacity"
    subRun :: SolverInstance -> [W256] -> SMT2 -> Text -> IO ()
    subRun inst vals fullSmt sat = do
      case sat of
        "unsat" -> do
          when conf.debug $ putStrLn $ "No more solutions to query, returning: " <> show vals
          writeChan r (Just vals)
        "timeout" -> do
           when conf.debug $ putStrLn "Timeout inside SMT solver."
           writeChan r Nothing
        "unknown" -> do
           when conf.debug $ putStrLn "Unknown result by SMT solver."
           dumpUnsolved fullSmt fileCounter conf.dumpUnsolved
           writeChan r Nothing
        "sat" -> do
          if length vals >= multiSol.maxSols then do
            when conf.debug $ putStrLn "Too many solutions to symbolic query."
            writeChan r Nothing
          else do
            mcex <- getModel inst cexvars
            case mcex of
              Nothing -> do
                when conf.debug $ putStrLn "Solver died while extracting model."
                writeChan r Nothing
              Just cex -> case Map.lookup (Var (TStrict.pack multiSol.var)) cex.vars of
                Just v -> do
                  let hexMask = maskFromBytesCount multiSol.numBytes
                      maskedVal = v .&. hexMask
                      toSMT n = Data.Text.Lazy.Builder.Int.decimal n
                      maskedVar = "(bvand " <> fromString multiSol.var <> " (_ bv" <> toSMT hexMask <> " 256))"
                      restrict = SMTCommand $ "(assert (not (= " <> maskedVar <> " (_ bv" <> toSMT maskedVal <> " 256))))"
                      newSmt = fullSmt <> SMT2 (SMTScript [restrict]) mempty mempty
                  when conf.debug $ putStrLn $ "Got one solution to symbolic query, val: 0x" <> (showHex maskedVal "") <>
                    " now have " <> show (length vals + 1) <> " solution(s), max is: " <> show multiSol.maxSols
                  when conf.dumpQueries $ writeSMT2File newSmt "." (show fileCounter <> "-sol" <> show (length vals))
                  out <- sendCommand inst restrict
                  case out of
                    "success" -> do
                      out2 <- sendCommand inst  (SMTCommand "(check-sat)")
                      subRun inst (maskedVal:vals) newSmt out2
                    err -> do
                      when conf.debug $ putStrLn $ "Error while writing SMT to solver: " <> (T.unpack err)
                      writeChan r Nothing
                Nothing -> internalError $ "variable " <>  multiSol.var <> " not part of model (i.e. cex) ... that's not possible"
        err -> do
          when conf.debug $ putStrLn $ "Error while writing SMT to solver: " <> (T.unpack err)
          writeChan r Nothing
  liftIO $ bracket_
    (waitQSem sem)
    (signalQSem sem)
    (do
      when conf.dumpQueries $ writeSMT2File smt2 "." (show fileCounter)
      bracket
        (spawnSolver solver timeout maxMemory)
        (stopSolver)
        (\inst -> do
          out <- sendScript inst cmds
          case out of
            Left err -> do
              when conf.debug $ putStrLn $ "Issue while writing SMT to solver (maybe it got killed)?: " <> (T.unpack err)
              writeChan r Nothing
            Right _ -> do
              sat <- sendCommand inst $ SMTCommand "(check-sat)"
              when conf.dumpQueries $ writeSMT2File smt2 "." (show fileCounter <> "-origquery")
              subRun inst [] smt2 sat
        )
    )

getOneSol :: (MonadIO m, ReadConfig m) => Solver -> Maybe Natural -> Natural -> SMT2 -> Maybe [Prop] -> Chan SMTResult -> TChan CacheEntry -> QSem -> Int -> m ()
getOneSol solver timeout maxMemory smt2@(SMT2 cmds cexvars _) props r cacheq sem fileCounter = do
  conf <- readConfig
  liftIO $ bracket_
    (waitQSem sem)
    (signalQSem sem)
    (do
      when (conf.dumpQueries) $ writeSMT2File smt2 "." (show fileCounter)
      bracket
        (spawnSolver solver timeout maxMemory)
        (stopSolver)
        (\inst -> do
          out <- sendScript inst cmds
          case out of
            Left e -> writeChan r (Unknown $ "Issue while writing SMT to solver (maybe it got killed?): " <> T.unpack e)
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
                    "sat" -> do
                      mmodel <- getModel inst cexvars
                      case mmodel of
                        Just model -> pure $ Cex model
                        Nothing -> pure $ Unknown "Solver died while extracting model"
                    _ -> let  supportIssue =
                                  ("does not yet support" `T.isInfixOf` sat)
                                  || ("unsupported" `T.isInfixOf` sat)
                                  || ("not support" `T.isInfixOf` sat)
                      in case supportIssue of
                       True -> pure . Error $ "SMT solver reported unsupported operation: " <> T.unpack sat
                       False -> pure . Unknown $ "Unable to parse SMT solver output (maybe it got killed?): " <> T.unpack sat
              writeChan r res
        )
    )

dumpUnsolved :: SMT2 -> Int -> Maybe FilePath -> IO ()
dumpUnsolved fullSmt fileCounter dump = do
   case dump of
     Just path -> writeSMT2File fullSmt path $ "unsolved-" <> show fileCounter
     Nothing -> pure ()

getModel :: SolverInstance -> CexVars -> IO (Maybe SMTCex)
getModel inst cexvars = runMaybeT $ do
  -- get an initial version of the model from the solver
  initialModel <- getRaw
  -- check the sizes of buffer models and shrink if needed
  if bufsUsable initialModel
  then pure initialModel
  else do
    -- get concrete values for each buffers max read index
    hints <- queryMaxReads (getValue inst) cexvars.buffers
    let cappedHints = capHints hints
    lift (execStateT (shrinkModel cappedHints) initialModel)
  where
    getRaw :: MaybeIO SMTCex
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
      -- Try to push and assert; if either fails, solver died, keep current model
      setup <- liftIO $ runMaybeT $ do
        MaybeT $ checkCommand inst $ SMTCommand "(push 1)"
        MaybeT $ checkCommand inst $ SMTCommand ("(assert (bvule " <> (fromLazyText buf) <> "_length " <> encBound <> "))")
      case setup of
        Nothing -> pure ()  -- solver died during setup, keep current model
        Just () -> do
          answer <- liftIO $ sendCommand inst $ SMTCommand "(check-sat)"
          case answer of
            "sat" -> do
              mmodel <- liftIO $ runMaybeT getRaw
              for_ mmodel put  -- solver died, keep current model
            "unsat" -> do
              mpop <- liftIO $ checkCommand inst $ SMTCommand "(pop 1)"
              case mpop of
                Nothing -> pure ()  -- solver died, keep current model
                Just () -> do
                  let nextHint = if hint == 0 then 1 else hint * 2
                  if nextHint < hint || nextHint > 1_073_741_824
                    then pure () -- overflow or over 1GB
                    else shrinkBuf buf nextHint
            _ -> do -- unexpected answer -> clean up and do not change the model
              _ <- liftIO $ checkCommand inst $ SMTCommand "(pop 1)"
              pure ()


    -- we set a pretty arbitrary upper limit (of 32) to decide if we need to do some shrinking
    bufsUsable :: SMTCex -> Bool
    bufsUsable model = any (go . snd) (Map.toList model.buffers)
      where
        go (Flat _) = True
        go (Comp c) = case c of
          (Base _ sz) -> sz <= 32
          -- TODO: do I need to check the write idx here?
          (Write _ idx next) -> idx <= 32 && go (Comp next)


-- Takes Maybe seconds, returns seconds
mkTimeout :: Maybe Natural -> Natural
mkTimeout = fromMaybe 300

-- | Arguments used when spawning a solver instance
solverArgs :: Solver -> Maybe Natural -> [Text]
solverArgs solver timeout = case solver of
  Bitwuzla ->
    [ "--lang=smt2"
    , "--produce-models"
    , "--time-limit-per=" <> millisecs
    , "--bv-output-format=16"
    ]
  Z3 ->
    [ "-st"
    , "-in" ]
  CVC5 ->
    [ "--lang=smt"
    , "--produce-models"
    , "--print-success"
    , "--interactive"
    , "--incremental"
    , "--tlimit-per=" <> millisecs
    , "--arrays-exp"
    ]
  EmptySolver -> []
  Custom _ -> []
  where millisecs = T.pack $ show $ 1000 * (mkTimeout timeout)

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: Solver -> Maybe (Natural) -> Natural -> IO SolverInstance
#if defined(mingw32_HOST_OS)
spawnSolver solver timeout _ = do
  (readout, writeout) <- createPipe
  let solverCmd = show solver
      solverArgsStr = fmap T.unpack $ solverArgs solver timeout
      -- Windows: no ulimit available
      cmd = (proc solverCmd solverArgsStr)
            { std_in = CreatePipe
            , std_out = UseHandle writeout
            , std_err = UseHandle writeout
            }
#elif defined(darwin_HOST_OS)
spawnSolver solver timeout _ = do
  (readout, writeout) <- createPipe
  let timeoutSeconds = mkTimeout timeout
      solverCmd = show solver
      solverArgsStr = fmap T.unpack $ solverArgs solver timeout
      -- macOS: memory limit not possible, but CPU limits work
      -- ulimit -t sets RLIMIT_CPU (kernel-enforced CPU time limit in seconds)
      shellCmd = "sh"
      shellArgs = ["-c", "ulimit -t " ++ show timeoutSeconds ++ "; exec \"$0\" \"$@\"", solverCmd] ++ solverArgsStr
      cmd = (proc shellCmd shellArgs)
            { std_in = CreatePipe
            , std_out = UseHandle writeout
            , std_err = UseHandle writeout
            }
#else
spawnSolver solver timeout maxMemoryMB = do
  (readout, writeout) <- createPipe
  let timeoutSeconds = mkTimeout timeout
      solverCmd = show solver
      solverArgsStr = fmap T.unpack $ solverArgs solver timeout
      -- Linux: both CPU and memory limits work
      -- ulimit -v sets RLIMIT_AS (kernel-enforced virtual memory limit in KB)
      shellCmd = "sh"
      maxMemoryKB = maxMemoryMB * 1024  -- Convert MB to KB for ulimit -v
      shellArgs = ["-c", "ulimit -t " ++ show timeoutSeconds ++ "; ulimit -v " ++ show maxMemoryKB ++ "; exec \"$0\" \"$@\"", solverCmd] ++ solverArgsStr
      cmd = (proc shellCmd shellArgs)
            { std_in = CreatePipe
            , std_out = UseHandle writeout
            , std_err = UseHandle writeout
            }
#endif
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

-- | Returns Nothing if the solver died or returned an error
checkCommand :: SolverInstance -> SMTEntry -> IO (Maybe ())
checkCommand inst cmd = do
  res <- sendCommand inst cmd
  pure $ if res == "success" then Just () else Nothing


-- | Strips trailing \r, if present
stripCarriageReturn :: Text -> Text
stripCarriageReturn t = fromMaybe t $ T.stripSuffix "\r" t

-- | Helper function for when we want to try an IO action and get Nothing on exception
tryIO :: forall a. IO a -> MaybeT IO a
tryIO action = MaybeT $ either (const Nothing) Just <$> (try action :: IO (Either IOException a))

-- | Sends a string to the solver and appends a newline, returns the first available line from the output buffer
-- Returns "unknown" if the solver process has died (timeout, crash, etc.)
sendCommand :: SolverInstance -> SMTEntry -> IO Text
sendCommand _ (SMTComment _) = internalError "Attempting to send a comment as a command to SMT solver"
sendCommand (SolverInstance _ stdin stdout _) (SMTCommand cmd) = do
  result <- runMaybeT $ do
    tryIO $ T.hPutStrLn stdin $ toLazyText cmd
    tryIO $ hFlush stdin
    tryIO $ stripCarriageReturn <$> T.hGetLine stdout
  pure $ fromMaybe "unknown" result

-- | Returns a string representation of the model for the requested variable
-- Returns Nothing if the solver process has died (timeout, crash, etc.)
getValue :: SolverInstance -> Text -> MaybeIO Text
getValue (SolverInstance _ stdin stdout _) var = do
  tryIO $ T.hPutStrLn stdin (T.append (T.append "(get-value (" var) "))")
  tryIO $ hFlush stdin
  val <- readSExpr stdout
  pure $ (T.unlines . reverse) val

-- | Reads lines from h until we have a balanced sexpr
-- Returns Nothing if the solver process has died or parsing fails
readSExpr :: Handle -> MaybeIO [Text]
readSExpr h = go 0 0 []
  where
    go 0 0 _ = do
      line <- tryIO $ T.hGetLine h
      let cleanLine = stripCarriageReturn line
          ls = T.length $ T.filter (== '(') cleanLine
          rs = T.length $ T.filter (== ')') cleanLine
      if ls == rs
         then pure [cleanLine]
         else go ls rs [cleanLine]
    go ls rs prev = do
      line <- tryIO $ T.hGetLine h
      let cleanLine = stripCarriageReturn line
          ls' = T.length $ T.filter (== '(') cleanLine
          rs' = T.length $ T.filter (== ')') cleanLine
      if (ls + ls') == (rs + rs')
         then pure $ cleanLine : prev
         else go (ls + ls') (rs + rs') (cleanLine : prev)
