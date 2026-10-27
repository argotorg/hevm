{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DisambiguateRecordFields #-}

module EVM.SymExec
  ( module EVM.SymExec
  , module EVM.SymExec.Calldata
  , module EVM.SymExec.Cex
  ) where

import Prelude hiding (Foldable(..))

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.Async ( mapConcurrently)
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent.STM (writeTChan, newTChan, TChan, readTChan, atomically, isEmptyTChan, STM, orElse)
import Control.Concurrent.STM.TVar (TVar, newTVarIO, modifyTVar, readTVar, readTVarIO, writeTVar)
import Control.Concurrent.STM.TMVar (TMVar, putTMVar, takeTMVar, readTMVar, tryPutTMVar, newEmptyTMVarIO)
import Control.Monad (when, unless, forM_, forM, forever, void)
import Control.Monad.Loops (whileM)
import Control.Exception (SomeException, SomeAsyncException, catch, throwIO, fromException)
import Control.Monad.IO.Unlift (MonadIO, toIO, withRunInIO)
import Control.Monad.Operational qualified as Operational
import Control.Monad.ST (RealWorld, stToIO, ST)
import Control.Monad.State.Strict (liftIO, runStateT, lift)
import Data.STRef (newSTRef, readSTRef, writeSTRef)
import Data.ByteString (ByteString)
import Data.DoubleWord (Word256)
import Data.Foldable (length, foldl')
import Data.List (sort)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, mapMaybe, catMaybes, isJust)
import System.Environment (lookupEnv)
import System.IO.Unsafe (unsafePerformIO)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Aeson ((.=))
import Data.Aeson qualified as JSON
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Tree.Zipper qualified as Zipper
import Data.Tuple (swap)
import GHC.Conc (numCapabilities)
import GHC.Generics (Generic)
import GHC.Num.Natural (Natural)
import Optics.Core
import Options.Generic (ParseField, ParseFields, ParseRecord)
import Text.Printf (printf)
import Witch (into, unsafeInto)

import EVM (makeVm, memoryBytes, abstractContract, initialContract, getCodeLocation, isValidJumpDest, defaultVMOpts)
import EVM.Exec (exec)
import EVM.Fetch qualified as Fetch
import EVM.ABI
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Keccak.Preimages qualified as Preimages
import EVM.Progress qualified as Progress
import EVM.Format (formatExpr, formatPartial, formatPartialDetailed, indent, formatProp)
import EVM.Solvers (SolverGroup, checkSatWithProps, checkSatWithPropsAbortable, withRunAbort)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.SymExec.Calldata
import EVM.SymExec.Cex
import EVM.HashCons qualified as HashCons
import EVM.Types

data LoopHeuristic
  = Naive
  | StackBased
  deriving (Eq, Show, Read, ParseField, ParseFields, ParseRecord, Generic)

groupIssues :: forall a b . GetUnknownStr b => [ProofResult a b] -> [(Integer, String)]
groupIssues results = map (\g -> (into (length g), NE.head g)) grouped
  where
    getIssue :: ProofResult a b -> Maybe String
    getIssue (Error k) = Just k
    getIssue (Unknown reason) = Just $ "SMT solver says: " <> getUnknownStr reason
    getIssue _ = Nothing
    grouped = NE.group $ sort $ mapMaybe getIssue results

groupPartials :: Maybe SrcLookup -> Map (Expr EAddr) Contract -> [Expr End] -> [(Integer, String)]
groupPartials srcLookupM contracts e = map (\g -> (into (length g), NE.head g)) grouped
  where
    getPartial :: Expr End -> Maybe String
    getPartial (Partial _ _ reason) = Just $ T.unpack $ formatPartialDetailed srcLookupM contracts reason
    getPartial _ = Nothing
    grouped = NE.group $ sort $ mapMaybe getPartial e

data IterConfig = IterConfig
  { maxIter :: Maybe Integer
  -- | the bound for branches whose condition is concrete: gas is not tracked, so it
  -- stops loops that would never end
  , maxConcreteIter :: Maybe Integer
  , askSmtIters :: Integer
  , loopHeuristic :: LoopHeuristic
  }
  deriving (Eq, Show)

defaultIterConf :: IterConfig
defaultIterConf = IterConfig
  { maxIter = Nothing
  , maxConcreteIter = Just 10000
  , askSmtIters = 1
  , loopHeuristic = StackBased
  }

data VeriOpts = VeriOpts
  { iterConf :: IterConfig
  , rpcInfo :: Fetch.RpcInfo
  }
  deriving (Show)

defaultVeriOpts :: VeriOpts
defaultVeriOpts = VeriOpts
  { iterConf = defaultIterConf
  , rpcInfo = Fetch.noRpc
  }

extractCex :: VerifyResult -> Maybe (Expr End, SMTCex)
extractCex (Cex c) = Just c
extractCex _ = Nothing

abstractVM
  :: (Expr Buf, [Prop])
  -> ByteString
  -> Maybe (Precondition)
  -> Bool
  -> ST RealWorld (VM Symbolic)
abstractVM cd contractCode maybepre create = do
  let value = TxValue
  let code = if create then InitCode contractCode (fst cd) else RuntimeCode (ConcreteRuntimeCode contractCode)
  vm <- loadSymVM code value (if create then mempty else cd) create
  let precond = case maybepre of
                Nothing -> []
                Just p -> [p vm]
  pure $ vm & over #constraints (<> precond)

-- Creates symbolic VM with empty storage, not symbolic storage like loadSymVM
loadEmptySymVM
  :: ContractCode
  -> Expr EWord
  -> (Expr Buf, [Prop])
  -> ST RealWorld (VM Symbolic)
loadEmptySymVM x callvalue cd =
  (makeVm $ defaultVMOpts
    { contract = initialContract x
    , calldata = cd
    , value = callvalue
    , address = SymAddr "entrypoint"
    , caller = SymAddr "caller"
    , origin = SymAddr "origin"
    , coinbase = SymAddr "coinbase"
    , number = BlockNumber
    , timestamp = Timestamp
    , blockGaslimit = 0
    , prevRandao = PrevRandao
    , baseFee = BaseFee
    })

-- Creates a symbolic VM that has symbolic storage, unlike loadEmptySymVM
loadSymVM
  :: ContractCode
  -> Expr EWord
  -> (Expr Buf, [Prop])
  -> Bool
  -> ST RealWorld (VM Symbolic)
loadSymVM x callvalue cd create =
  (makeVm $ defaultVMOpts
    { contract = if create then initialContract x else abstractContract x (SymAddr "entrypoint")
    , calldata = cd
    , value = callvalue
    , baseState = AbstractBase
    , address = SymAddr "entrypoint"
    , caller = SymAddr "caller"
    , origin = SymAddr "origin"
    , coinbase = SymAddr "coinbase"
    , number = BlockNumber
    , timestamp = Timestamp
    , blockGaslimit = 0
    , prevRandao = PrevRandao
    , baseFee = BaseFee
    , create = create
    })

-- freezes any mutable refs, making it safe to share between threads
freezeVM :: VM Symbolic -> ST RealWorld (VM Symbolic)
freezeVM vm = do
    state' <- do
      mem' <- freeze (vm.state.memory)
      pure $ vm.state { memory = mem' }
    frames' <- forM (vm.frames :: [Frame Symbolic]) $ \frame -> do
      mem' <- freeze frame.state.memory
      pure $ (frame :: Frame Symbolic) { state = frame.state { memory = mem' } }

    pure (vm :: VM Symbolic)
      { state = state'
      , frames = frames'
      }
  where
    freeze = \case
      ConcreteMemory m -> SymbolicMemory . ConcreteBuf <$> memoryBytes m
      m@(SymbolicMemory _) -> pure m

type PathHandler m a = Expr End -> TVar Bool -> m a

-- | Like 'PathHandler', also given the VM the path ended in
type VMPathHandler m a = Expr End -> VM Symbolic -> TVar Bool -> m a

data InterpTask m a = InterpTask
  {fetcher :: Fetch.Fetcher Symbolic m
  , iterConf :: IterConfig
  , vm :: VM Symbolic
  , taskQ :: Chan (InterpTask m a)
  , numTasks :: TVar Natural
  , stepper :: Stepper Symbolic (Expr End)
  , handler :: VMPathHandler m a
  , shouldAbort :: TVar Bool
  }

data Process m a = Process
  { result :: Expr End
  , vm :: VM Symbolic
  , handler :: VMPathHandler m a
  }

-- returns back the input path/branch of the program
noopPathHandler :: Applicative m => PathHandler m (Expr End)
noopPathHandler x _ = pure x

interpret :: forall m a . App m
  => Fetch.Fetcher Symbolic m
  -> IterConfig
  -> VM Symbolic
  -> Stepper Symbolic (Expr End)
  -> PathHandler m a
  -> m [a]
interpret fetcher iterConf vm stepper handler = do
  shouldAbort <- liftIO $ newTVarIO False
  interpretAbortable shouldAbort fetcher iterConf vm stepper handler

-- | Like 'interpret', stopping every path at its next step once the flag is set
interpretAbortable :: forall m a . App m
  => TVar Bool
  -> Fetch.Fetcher Symbolic m
  -> IterConfig
  -> VM Symbolic
  -> Stepper Symbolic (Expr End)
  -> PathHandler m a
  -> m [a]
interpretAbortable runFlag fetcher iterConf vm stepper handler =
  interpretVMAbortable runFlag fetcher iterConf vm stepper (\leaf _ -> handler leaf)

-- | Like 'interpretAbortable', the handler also gets the VM each path ended in
interpretVMAbortable :: forall m a . App m
  => TVar Bool
  -> Fetch.Fetcher Symbolic m
  -> IterConfig
  -> VM Symbolic
  -> Stepper Symbolic (Expr End)
  -> VMPathHandler m a
  -> m [a]
interpretVMAbortable runFlag fetcher iterConf vm stepper handler = do
  conf <- readConfig
  -- the flag is process-wide and outlives this exploration
  liftIO $ do HashCons.setHashConsEnabled conf.hashConsExplore
              HashCons.resetHashCons
  taskQ <- liftIO newChan
  processQ <- liftIO newChan

  -- spawn interpreters and process instances
  let interpInstances = replicate numCapabilities ()
      procInstances = replicate numCapabilities ()

  -- result channel
  resChan <- liftIO . atomically $ newTChan

  -- spawn orchestration thread with queues and flags
  availableInstances <- liftIO newChan
  liftIO $ forM_ interpInstances (writeChan availableInstances)
  availableProcs <- liftIO newChan
  liftIO $ forM_ procInstances (writeChan availableProcs)
  numTasks <- liftIO $ newTVarIO 1
  Progress.setTaskCounter (fromIntegral <$> readTVarIO numTasks)
  numProcs <- liftIO $ newTVarIO 0
  allProcessDone <- liftIO newEmptyTMVarIO
  -- an exception in a forked worker would otherwise only be printed, leaving
  -- us waiting on allProcessDone forever
  workerErr <- liftIO newEmptyTMVarIO

  -- spawn task orchestration thread
  taskOrchestrate' <- toIO $ taskOrchestrate taskQ runFlag availableInstances processQ numTasks numProcs allProcessDone workerErr
  taskOrchestrateId <- liftIO $ forkIO taskOrchestrate'

  -- spawn processing orchestration thread
  processOrchestrate' <- toIO $ processOrchestrate processQ runFlag availableProcs resChan numProcs numTasks allProcessDone workerErr
  processOrchestrateId <- liftIO $ forkIO processOrchestrate'

  -- Add in the first task, further tasks will be added by the interpreters themselves
  let interpTask = InterpTask
        { fetcher = fetcher
        , iterConf = iterConf
        , vm = vm
        , taskQ = taskQ
        , numTasks = numTasks
        , stepper = stepper
        , handler = handler
        , shouldAbort = runFlag
        }
  liftIO $ writeChan taskQ interpTask

  -- Wait for all done
  done <- liftIO . atomically $ (Left <$> readTMVar workerErr) `orElse` (Right <$> takeTMVar allProcessDone)
  liftIO $ killThread taskOrchestrateId
  liftIO $ killThread processOrchestrateId
  liftIO $ either throwIO pure done
  res <- liftIO $ atomically (whileM (not <$> isEmptyTChan resChan) (readTChan resChan) :: STM [a])
  when (conf.debug) $ liftIO $ do
    putStrLn $ "Interpretation finished, collected " <> show (length res) <> " results."
  pure res
  where
    -- orchestrator loop
    taskOrchestrate :: App m
      => Chan (InterpTask m a)
      -> TVar Bool
      -> Chan () -> Chan (Process m a)
      -> TVar Natural -> TVar Natural -> TMVar () -> TMVar SomeException -> m ()
    taskOrchestrate taskQ shouldAbort avail processQ numTasks numProcs allProcessDone workerErr = forever $ do
      _ <- liftIO $ readChan avail
      task <- liftIO $ readChan taskQ
      abortFlag <- liftIO $ readTVarIO shouldAbort
      if abortFlag
        then liftIO $ do
          writeChan avail ()
          atomically $ modifyTVar numTasks (subtract 1) >> signalIfDone numProcs numTasks allProcessDone
        else do
          runTask' <- toIO $ getOneExpr task avail processQ numTasks numProcs
          void $ liftIO $ forkIO $ reportTo workerErr shouldAbort runTask'

    -- processing orchestrator loop
    processOrchestrate :: App m
      => Chan (Process m a) -> TVar Bool -> Chan () -> TChan a
      -> TVar Natural -> TVar Natural -> TMVar () -> TMVar SomeException -> m ()
    processOrchestrate processQ shouldAbort avail resChan numProcs numTasks allProcessDone workerErr = forever $ do
      _ <- liftIO $ readChan avail
      proc <- liftIO $ readChan processQ
      abortFlag <- liftIO $ readTVarIO shouldAbort
      if abortFlag
        then liftIO $ do
          writeChan avail ()
          atomically $ modifyTVar numProcs (subtract 1) >> signalIfDone numProcs numTasks allProcessDone
        else do
          runProcess' <- toIO $ processOne proc shouldAbort avail resChan numProcs numTasks allProcessDone
          void $ liftIO $ forkIO $ reportTo workerErr shouldAbort runProcess'

    -- process one task
    processOne :: App m => Process m a -> TVar Bool -> Chan () -> TChan a -> TVar Natural -> TVar Natural -> TMVar () -> m ()
    processOne task shouldAbort avail resChan numProcs numTasks allProcessDone = do
      processed <- task.handler task.result task.vm shouldAbort
      liftIO . atomically $ writeTChan resChan processed

      -- Return instance to pool immediately after processing
      liftIO $ writeChan avail ()

      liftIO $ atomically $ modifyTVar numProcs (subtract 1) >> signalIfDone numProcs numTasks allProcessDone

    reportTo :: TMVar SomeException -> TVar Bool -> IO () -> IO ()
    reportTo workerErr shouldAbort io = io `catch` \e -> case fromException e of
      Just (_ :: SomeAsyncException) -> throwIO e
      Nothing -> atomically $ writeTVar shouldAbort True >> void (tryPutTMVar workerErr e)

    signalIfDone :: TVar Natural -> TVar Natural -> TMVar () -> STM ()
    signalIfDone numProcs numTasks allProcessDone = do
      np <- readTVar numProcs
      nt <- readTVar numTasks
      when (np == 0 && nt == 0) $ putTMVar allProcessDone ()

getOneExpr :: forall m a . App m
  => InterpTask m a
  -> Chan ()
  -> Chan (Process m a)
  -> TVar Natural
  -> TVar Natural
  -> m ()
getOneExpr task availableInstances processQ numTasks numProcs = do
  (out, endVm) <- interpretInternal task
  Progress.clearWorker
  Progress.pathDone (isPartial out)
  Progress.emit "path-end" $ case out of
    Partial _ _ reason -> ["leaf" .= ("partial" :: Text), "reason" .= T.take 2000 (formatPartial reason)]
    Failure _ _ err -> ["leaf" .= ("failure" :: Text), "reason" .= T.pack (show err)]
    Success {} -> ["leaf" .= ("success" :: Text)]
    _ -> ["leaf" .= T.take 200 (T.pack (show out))]

  -- Enqueue for processing
  let process = Process { result = out, vm = endVm, handler = task.handler }
  liftIO . atomically $ modifyTVar numProcs (+1)

  -- Return instance to pool & decrement tasks
  liftIO $ writeChan availableInstances ()
  liftIO $ atomically $ modifyTVar numTasks (subtract 1)

  -- Finally write to process queue. Must be done after numTasks decrement,
  -- or it could be that when we check in processOne, numTasks is still non-zero
  liftIO $ writeChan processQ process

-- | Symbolic interpreter that explores all paths. Returns an
-- '[Expr End]' representing the possible execution leafs, each with the VM it ended in.
interpretInternal :: forall m a . App m
  => InterpTask m a
  -> m (Expr End, VM Symbolic)
interpretInternal t@InterpTask{..} = eval (Operational.view stepper)
  where
  eval :: Operational.ProgramView (Stepper.Action Symbolic) (Expr End) -> m (Expr End, VM Symbolic)
  eval (Operational.Return x) = pure (x, vm)
  eval (action Operational.:>>= k) = liftIO (readTVarIO shouldAbort) >>= \case
    True -> pure (Partial vm.constraints (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) (Aborted vm.state.pc vm.state.contract), vm)
    False -> step action k
  step :: Stepper.Action Symbolic r -> (r -> Stepper Symbolic (Expr End)) -> m (Expr End, VM Symbolic)
  step action k = do
    Progress.setWorker
      [ "pc" .= vm.state.pc
      , "addr" .= T.pack (show vm.state.contract)
      , "frames" .= length vm.frames
      , "exploreDepth" .= vm.exploreDepth
      , "step" .= stepName action
      ]
    case action of
      Stepper.Exec -> do
        conf <- readConfig
        (r, vm') <- liftIO $ stToIO $ runStateT (exec conf) vm
        interpretInternal t { vm = vm', stepper =  (k r) }
      Stepper.EVM m -> do
        (r, vm') <- liftIO $ stToIO $ runStateT m vm
        interpretInternal t { vm = vm', stepper = (k r) }
      Stepper.Fork (PleaseRunAll vals continue) -> do
        when (length vals < 2) $ internalError "PleaseRunAll requires at least 2 branches"
        Progress.fork (T.pack (show vm.state.contract)) vm.state.pc (srcOf vm)
          ["branches" .= length vals, "values" .= map (T.pack . show) (take 20 vals)]
        frozen <- liftIO $ stToIO $ freezeVM vm
        let newDepth = vm.exploreDepth+1
        runOne frozen newDepth vals
        where
          runOne :: App m => VM 'Symbolic -> Int -> [Expr EWord] -> m (Expr End, VM Symbolic)
          runOne frozen newDepth [v] = do
            conf <- readConfig
            (ra, vma) <- liftIO $ stToIO $ runStateT (continue v) frozen { result = Nothing, exploreDepth = newDepth }
            when (conf.debug && conf.verb >= 2) $ liftIO $ putStrLn $ "Running last task for ForkMany at depth " <> show newDepth
            interpretInternal t { vm = vma, stepper = (k ra) }
          runOne frozen newDepth (v:rest) = do
            conf <- readConfig
            (ra, vma) <- liftIO $ stToIO $ runStateT (continue v) frozen { result = Nothing, exploreDepth = newDepth }
            -- Check abort flag before queuing new task
            abortFlag <- liftIO $ readTVarIO shouldAbort
            unless abortFlag $ do
              liftIO $ atomically $ modifyTVar numTasks (+1)
              when (conf.debug && conf.verb >=2) $ liftIO $ putStrLn $ "Queuing new task for ForkMany at depth " <> show newDepth
              liftIO $ writeChan taskQ t { vm = vma, stepper = (k ra) }
            runOne frozen newDepth rest
          runOne _ _ [] = internalError "unreachable"
      Stepper.Fork (PleaseRunBoth continue) -> do
        Progress.fork (T.pack (show vm.state.contract)) vm.state.pc (srcOf vm) ["branches" .= (2 :: Int)]
        conf <- readConfig
        frozen <- liftIO $ stToIO $ freezeVM vm
        let newDepth = vm.exploreDepth+1
        (ra, vma) <- liftIO $ stToIO $ runStateT (continue True) frozen { result = Nothing, exploreDepth = newDepth }
        -- Check abort flag before queuing new task
        abortFlag <- liftIO $ readTVarIO shouldAbort
        unless abortFlag $ do
          liftIO $ atomically $ modifyTVar numTasks (+1)
          liftIO $ writeChan taskQ $ t { vm = vma, stepper = (k ra) }
          when (conf.debug && conf.verb >= 2) $ liftIO $ putStrLn $ "Queued new task for Fork at depth " <> show newDepth

        (rb, vmb) <- liftIO $ stToIO $ runStateT (continue False) frozen { result = Nothing, exploreDepth = newDepth }
        when (conf.debug && conf.verb >=2) $ liftIO $ putStrLn $ "Continuing task for Fork at depth " <> show newDepth
        interpretInternal t { vm = vmb, stepper = (k rb) }
      Stepper.Wait q -> do
        let performQuery = do
              Progress.noteSrc (T.pack (show vm.state.contract)) vm.state.pc (srcOf vm)
              logQueryExprs q
              m <- fetcher q
              (r, vm') <- liftIO$ stToIO $ runStateT m vm
              interpretInternal t { vm = vm', stepper = (k r) }

        case q of
          PleaseAskSMT cond preconds continue -> do
            case Expr.concKeccakSimpExpr cond of
              -- is the condition concrete?
              Lit c ->
                -- have we reached max iterations, are we inside a loop?
                case (maxIterationsReached vm iterConf.maxConcreteIter, isLoopHead iterConf.loopHeuristic vm) of
                  -- Yes. return a partial leaf
                  (Just _, Just True) ->
                    pure (Partial vm.constraints (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) $ MaxIterationsReached vm.state.pc vm.state.contract, vm)
                  -- No. keep executing
                  _ -> do
                    (r, vm') <- liftIO $ stToIO $ runStateT (continue (Case (c > 0))) vm
                    interpretInternal t { vm = vm', stepper = (k r) }

              -- the condition is symbolic
              _ ->
                -- are in we a loop, have we hit maxIters, have we hit askSmtIters?
                case (isLoopHead iterConf.loopHeuristic vm, askSmtItersReached vm iterConf.askSmtIters, maxIterationsReached vm iterConf.maxIter) of
                  -- we're in a loop and maxIters has been reached
                  (Just True, _, Just n) -> do
                    -- continue execution down the opposite branch than the one that
                    -- got us to this point and queue a task to return a partial leaf for the other side
                    let taken = Expr.simplifyProp $ if n then Lit 0 ./= cond else Lit 0 .== cond
                        partialLeaf = Partial (taken : vm.constraints) (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) (MaxIterationsReached vm.state.pc vm.state.contract)
                    liftIO $ atomically $ modifyTVar numTasks (+1)
                    liftIO $ writeChan taskQ $ t { vm = vm, stepper = pure partialLeaf }
                    (r, vm') <- liftIO $ stToIO $ runStateT (continue (Case $ not n)) vm
                    interpretInternal t { vm = vm', stepper = (k r) }
                  -- we're in a loop and askSmtIters has been reached
                  (Just True, True, _) ->
                    -- ask the smt solver about the loop condition
                    performQuery
                  _ -> do
                    let decision = staticBranch cond preconds
                    conf <- readConfig
                    when (conf.checkStaticBranches || checkStaticBranchesFromEnv) $
                      checkStaticBranch fetcher vm cond preconds decision >>= \case
                        StaticWrong msg -> internalError $ "a branch side was dropped by simplification, but it is reachable: " <> msg
                        _ -> pure ()
                    (r, vm') <- liftIO $ stToIO $ runStateT (continue decision) vm
                    interpretInternal t { vm = vm', stepper = (k r) }
          _ -> performQuery

-- | The source location of the current pc, if there is debug info for it
srcOf :: VM t -> Text
srcOf vm = case vm.srcLookup of
  Nothing -> ""
  Just _ -> fromMaybe "" $ T.stripPrefix " in file " $ T.pack $ runSrcLookup vm.srcLookup vm.env.contracts vm.state.contract vm.state.pc

-- | How exploration decides a symbolic branch without the solver: a side is
-- dropped only if simplifying it with the path conditions gives false
staticBranch :: Expr EWord -> [Prop] -> BranchCondition
staticBranch cond preconds = case Expr.concKeccakSimpProps ((cond ./= Lit 0):preconds) of
  [PBool False] -> Case False
  [] -> Case True
  _ | Expr.concKeccakSimpProps ((cond .== Lit 0):preconds) == [PBool False] -> Case True
    | otherwise -> UnknownBranch

-- | Turns on 'checkStaticBranches' for every run, e.g. a whole test suite
{-# NOINLINE checkStaticBranchesFromEnv #-}
checkStaticBranchesFromEnv :: Bool
checkStaticBranchesFromEnv = unsafePerformIO $ isJust <$> lookupEnv "HEVM_CHECK_STATIC_BRANCHES"

-- | What the fetcher, normally the solver, decides about a branch condition
askBranch :: App m => Fetch.Fetcher Symbolic m -> VM Symbolic -> Expr EWord -> [Prop] -> m BranchCondition
askBranch fetcher vm cond preconds = askFetcher fetcher vm (PleaseAskSMT cond preconds) UnknownBranch

-- | Whether the fetcher, normally the solver, finds the props satisfiable
askSat :: App m => Fetch.Fetcher Symbolic m -> VM Symbolic -> [Prop] -> m (Maybe Bool)
askSat fetcher vm props = askFetcher fetcher vm (PleaseCheckSat props) Nothing

askFetcher :: App m => Fetch.Fetcher Symbolic m -> VM Symbolic -> ((a -> EVM Symbolic ()) -> Query Symbolic) -> a -> m a
askFetcher fetcher vm mkQuery dflt = do
  ref <- liftIO $ stToIO $ newSTRef Nothing
  m <- fetcher (mkQuery (\r -> lift (writeSTRef ref (Just r))))
  _ <- liftIO $ stToIO $ runStateT m vm
  fromMaybe dflt <$> liftIO (stToIO (readSTRef ref))

data StaticCheck
  = StaticOk
  -- | the solver finds a dropped side satisfiable, or a taken side unsatisfiable
  | StaticWrong String
  | StaticInconclusive
  -- | 'staticBranch' kept both sides, but the solver finds one unsatisfiable
  | StaticMissed
  deriving (Show)

-- | Asks the solver whether the sides 'staticBranch' dropped are unsatisfiable
checkStaticBranch :: App m => Fetch.Fetcher Symbolic m -> VM Symbolic -> Expr EWord -> [Prop] -> BranchCondition -> m StaticCheck
checkStaticBranch fetcher vm cond preconds decision = case decision of
  Case b -> askSat fetcher vm (side (not b) : preconds) <&> \case
    Just False -> StaticOk
    Nothing -> StaticInconclusive
    Just True -> StaticWrong $ "simplification decided " <> show b <> ", but the solver finds " <> show (not b) <> " satisfiable"
      <> " at pc " <> show vm.state.pc <> " of " <> show vm.state.contract
      <> "\ncondition: " <> T.unpack (formatExpr cond)
      <> "\npath conditions: " <> T.unpack (T.unlines (map formatProp preconds))
  _ -> do
    t <- askSat fetcher vm (side True : preconds)
    f <- askSat fetcher vm (side False : preconds)
    pure $ if t == Just False || f == Just False then StaticMissed else StaticOk
  where
    side True = cond ./= Lit 0
    side False = cond .== Lit 0

logQueryExprs :: MonadIO m => Query Symbolic -> m ()
logQueryExprs = \case
  PleaseAskSMT cond pathconds _ ->
    Progress.emitExprs "branch-query" $ Progress.bigText "cond" (formatExpr cond) <> props pathconds
  PleaseGetSols e numBytes pathconds _ ->
    Progress.emitExprs "solutions-query" $
      ["numBytes" .= numBytes] <> Progress.bigText "expr" (formatExpr e) <> props pathconds
  _ -> pure ()
  where
    props ps = ["pathconds" .= map (JSON.object . Progress.bigText "prop" . formatProp) ps]

stepName :: Stepper.Action Symbolic x -> Text
stepName = \case
  Stepper.Exec -> "exec"
  Stepper.EVM _ -> "evm"
  Stepper.Fork (PleaseRunAll vals _) -> "fork-" <> T.pack (show (length vals))
  Stepper.Fork (PleaseRunBoth _) -> "fork-2"
  Stepper.Wait q -> case q of
    PleaseAskSMT {} -> "query-branch"
    PleaseGetSols {} -> "query-solutions"
    PleaseFetchContract {} -> "query-fetch-contract"
    PleaseFetchSlot {} -> "query-fetch-slot"
    PleaseDoFFI {} -> "query-ffi"
    PleaseReadEnv {} -> "query-env"
    PleaseCheckSat {} -> "query-sat"

maxIterationsReached :: VM Symbolic -> Maybe Integer -> Maybe Bool
maxIterationsReached _ Nothing = Nothing
maxIterationsReached vm (Just maxIter) =
  let codelocation = getCodeLocation vm
      (iters, _) = view (at codelocation % non (0, [])) vm.iterations
  in if unsafeInto maxIter <= iters
     then Map.lookup (codelocation, iters - 1) vm.pathsVisited
     else Nothing

askSmtItersReached :: VM Symbolic -> Integer -> Bool
askSmtItersReached vm askSmtIters = let
    codelocation = getCodeLocation vm
    (iters, _) = view (at codelocation % non (0, [])) vm.iterations
  in askSmtIters <= into iters

{- | Loop head detection heuristic

 The main thing we wish to differentiate between, are actual loop heads, and branch points inside of internal functions that are called multiple times.

 One way to do this is to observe that for internal functions, the compiler must always store a stack item representing the location that it must jump back to. If we compare the stack at the time of the previous visit, and the time of the current visit, and notice that this location has changed, then we can guess that the location is a jump point within an internal function instead of a loop (where such locations should be constant between iterations).

 This heuristic is not perfect, and can certainly be tricked, but should generally be good enough for most compiler generated and non pathological user generated loops.
 -}
isLoopHead :: LoopHeuristic -> VM Symbolic -> Maybe Bool
isLoopHead Naive _ = Just True
isLoopHead StackBased vm = let
    loc = getCodeLocation vm
    oldIters = Map.lookup loc vm.iterations
    isValid (Lit wrd) = wrd <= unsafeInto (maxBound :: Int) && isValidJumpDest vm (unsafeInto wrd)
    isValid _ = False
  in case oldIters of
       Just (_, oldStack) -> Just $ filter isValid oldStack == filter isValid vm.state.stack
       Nothing -> Nothing

type Precondition = VM Symbolic -> Prop
type Postcondition = VM Symbolic -> Expr End -> Prop

-- Used only in testing
checkAssert
  :: App m
  => SolverGroup
  -> [Word256]
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> m ([Expr End], [VerifyResult])
checkAssert solvers errs c signature' concreteArgs opts = do
  verifyContract solvers c signature' concreteArgs opts Nothing (checkAssertions errs)

-- Used only in testing
getExprEmptyStore
  :: App m
  => SolverGroup
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> m [Expr End]
getExprEmptyStore solvers c signature' concreteArgs opts = do
  conf <- readConfig
  (calldata, _caveats) <- mkCalldata signature' concreteArgs
  preState <- liftIO $ stToIO $ loadEmptySymVM (RuntimeCode (ConcreteRuntimeCode c)) (Lit 0) calldata
  paths <- interpret (Fetch.oracle solvers Nothing opts.rpcInfo) opts.iterConf preState runExpr noopPathHandler
  if conf.simp then (pure $ map Expr.simplify paths) else pure paths

-- Used only in testing; TODO: unify with exploreContract, and keep only one
getExpr
  :: App m
  => SolverGroup
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> m [Expr End]
getExpr solvers c signature' concreteArgs opts = do
  paths <- exploreContract solvers c signature' concreteArgs opts Nothing
  conf <- readConfig
  if conf.simp then (pure $ map Expr.simplify paths) else pure paths

{- | Checks if an assertion violation has been encountered

  hevm recognises the following as an assertion violation:

  1. the invalid opcode (0xfe) (solc < 0.8)
  2. a revert with a reason of the form `abi.encodeWithSelector("Panic(uint256)", code)`, where code is one of the following (solc >= 0.8):
    - 0x00: Used for generic compiler inserted panics.
    - 0x01: If you call assert with an argument that evaluates to false.
    - 0x11: If an arithmetic operation results in underflow or overflow outside of an unchecked { ... } block.
    - 0x12; If you divide or modulo by zero (e.g. 5 / 0 or 23 % 0).
    - 0x21: If you convert a value that is too big or negative into an enum type.
    - 0x22: If you access a storage byte array that is incorrectly encoded.
    - 0x31: If you call .pop() on an empty array.
    - 0x32: If you access an array, bytesN or an array slice at an out-of-bounds or negative index (i.e. x[i] where i >= x.length or i < 0).
    - 0x41: If you allocate too much memory or create an array that is too large.
    - 0x51: If you call a zero-initialized variable of internal function type.

  see: https://docs.soliditylang.org/en/v0.8.6/control-structures.html?highlight=Panic#panic-via-assert-and-error-via-require
  NOTE: does not deal with e.g. `assertEq()`
-}
checkAssertions :: [Word256] -> Postcondition
checkAssertions errs _ = \case
  Failure _ _ (UnrecognizedOpcode 0xfe)  -> PBool False
  Failure _ _ (Revert (ConcreteBuf msg)) -> PBool $ msg `notElem` (fmap panicMsg errs)
  Failure _ _ (Revert b) -> foldl' PAnd (PBool True) (fmap (PNeg . PEq b . ConcreteBuf . panicMsg) errs)
  _ -> PBool True

-- | By default hevm only checks for user-defined assertions
defaultPanicCodes :: [Word256]
defaultPanicCodes = [0x01]

allPanicCodes :: [Word256]
allPanicCodes = [0x00, 0x01, 0x11, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51]

-- | Produces the revert message for solc >=0.8 assertion violations
panicMsg :: Word256 -> ByteString
panicMsg err = selector "Panic(uint256)" <> encodeAbiValue (AbiUInt 256 err)

-- Used only in testing
verifyContract :: forall m . App m
  => SolverGroup
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> Maybe Precondition
  -> Postcondition
  -> m ([Expr End], [VerifyResult])
verifyContract solvers theCode signature' concreteArgs opts maybepre post = do
  (calldata, _caveats) <- mkCalldata signature' concreteArgs
  preState <- liftIO $ stToIO $ abstractVM calldata theCode maybepre False
  let fetcher = Fetch.oracle solvers Nothing opts.rpcInfo
  verify solvers fetcher opts preState post Nothing

-- Used only in testing
exploreContract :: forall m . App m
  => SolverGroup
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> Maybe Precondition
  -> m [Expr End]
exploreContract solvers theCode signature' concreteArgs opts maybepre = do
  (calldata, _caveats) <- mkCalldata signature' concreteArgs
  preState <- liftIO $ stToIO $ abstractVM calldata theCode maybepre False
  let fetcher = Fetch.oracle solvers Nothing opts.rpcInfo
  executeVM fetcher opts.iterConf preState noopPathHandler

-- | Stepper that parses the result of Stepper.runFully into an Expr End
runExpr :: Stepper.Stepper Symbolic (Expr End)
runExpr = do
  vm <- Stepper.runFully
  let traces = TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels
  pure $ case vm.result of
    Just (VMSuccess buf) -> Success vm.constraints traces buf (fmap toEContract vm.env.contracts)
    Just (VMFailure e)   -> Failure vm.constraints traces e
    Just (Unfinished p)  -> Partial vm.constraints traces p
    _ -> internalError "vm in intermediate state after call to runFully"

toEContract :: Contract -> Expr EContract
toEContract c = C c.code c.storage c.tStorage c.balance c.nonce

-- | Strips unreachable branches from a given list of Expr End nodes
reachable :: App m => SolverGroup -> [Expr End] -> m [Expr End]
reachable solvers e = catMaybes <$> mapM go e
  where
    go leaf = do
        res <- checkSatWithProps solvers (extractProps leaf)
        case res of
          Qed -> pure Nothing
          Cex _ -> pure (Just leaf)
          -- if we get an error, we don't know if the leaf is reachable or not, so
          -- we assume it could be reachable
          _ -> pure (Just leaf)

-- | Extract constraints stored in Expr End nodes
extractProps :: Expr End -> [Prop]
extractProps = \case
  Success asserts _ _ _ -> asserts
  Failure asserts _ _ -> asserts
  Partial asserts _ _ -> asserts
  GVar _ -> internalError "cannot extract props from a GVar"

extractEndStates :: Expr End -> Map (Expr EAddr) (Expr EContract)
extractEndStates = \case
  Success _ _ _ contr -> contr
  Failure {} -> mempty
  Partial  {} -> mempty
  GVar _ -> internalError "cannot extract props from a GVar"

isPartial :: Expr a -> Bool
isPartial (Partial _ _ _) = True
isPartial _ = False

printPartialIssues :: [Expr End] -> String -> IO ()
printPartialIssues flattened call =
  when (any isPartial flattened) $ do
    T.putStrLn $ indent 3 "\x1b[33m[WARNING]\x1b[0m: hevm was only able to partially explore "
                <> T.pack call <> " due to the following issue(s):"
    T.putStr . T.unlines . fmap (indent 5 . ("- " <>)) . fmap formatPartial . (map fst) . getPartials $ flattened

getPartials :: [Expr End] -> [(PartialExec, Expr End)]
getPartials = mapMaybe go
  where
    go :: Expr End -> Maybe (PartialExec, Expr End)
    go = \case
      e@(Partial _ _ p) -> Just (p, e)
      _ -> Nothing


-- | Symbolically execute the VM and return the representention of the execution
executeVM :: forall m a . App m => Fetch.Fetcher Symbolic m -> IterConfig -> VM Symbolic -> (Expr End -> TVar Bool -> m a) -> m [a]
executeVM fetcher iterConfig preState handlePath = interpret fetcher iterConfig preState runExpr handlePath

-- | Symbolically execute the VM and check all endstates against the
-- postcondition, if available.
verify :: App m
  => SolverGroup
  -> Fetch.Fetcher Symbolic m
  -> VeriOpts
  -> VM Symbolic
  -> Postcondition
  -> Maybe (VM Symbolic -> SMTResult -> Expr End -> m ())
  -> m ([Expr End], [VerifyResult])
verify solvers fetcher opts preState post cexHandler = do
  abort <- liftIO $ newTVarIO False
  verifyAbortable abort solvers fetcher opts preState post cexHandler

-- | Like 'verify', stopping exploration and cancelling every solver query of the run once the
-- flag is set. With 'earlyAbort', the first counterexample sets it.
verifyAbortable :: App m
  => TVar Bool
  -> SolverGroup
  -> Fetch.Fetcher Symbolic m
  -> VeriOpts
  -> VM Symbolic
  -> Postcondition
  -> Maybe (VM Symbolic -> SMTResult -> Expr End -> m ())
  -> m ([Expr End], [VerifyResult])
verifyAbortable abort solvers fetcher opts preState post cexHandler = do
  (ends1, partials) <- verifyInputsWithHandler abort solvers opts fetcher preState post cexHandler
  let (ends2, results) = unzip $ map (verifyResult preState) ends1
  pure (ends2 <> fmap snd partials, filter (not . isQed) results)

verifyResult :: VM Symbolic-> (SMTResult, Expr End) -> (Expr End, VerifyResult)
verifyResult preState res = (snd res, toVRes res)
  where
    toVRes :: (SMTResult, Expr End) -> VerifyResult
    toVRes (res2, leaf) = case res2 of
      Cex model -> Cex (leaf, expandCex preState model)
      Unknown reason -> Unknown (reason, leaf)
      Error e -> Error e
      Qed -> Qed

-- | Symbolically execute the VM with optional custom handler for immediate Cex processing
verifyInputsWithHandler
  :: App m
  => TVar Bool
  -> SolverGroup
  -> VeriOpts
  -> Fetch.Fetcher Symbolic m
  -> VM Symbolic
  -> Postcondition
  -> Maybe (VM Symbolic -> SMTResult -> Expr End -> m ())
  -> m ([(SMTResult, Expr End)], [(PartialExec, Expr End)])
verifyInputsWithHandler runAbort solvers opts fetcher preState post cexHandler = do
  conf <- readConfig
  let call = mconcat ["prefix 0x", getCallPrefix preState.state.calldata]
  when conf.debug $ liftIO $ do
    putStrLn $ "   Keccak preimages in state: " <> (show $ length preState.keccakPreImgs)
    putStrLn $ "   Exploring call " <> call

  -- every query of the run, branch queries too, is cancelled when the flag is set
  results <- withRunAbort solvers runAbort $ interpretAbortable runAbort fetcher opts.iterConf preState runExpr $ \leaf shouldAbort -> liftIO (readTVarIO shouldAbort) >>= \case
   True -> pure Nothing
   False -> do
    -- Extract partial if applicable
    let mPartial = case leaf of
          Partial _ _ p -> Just (p, leaf)
          _ -> Nothing

    -- Check if this leaf needs SMT checking
    let props = toProps leaf preState.keccakPreImgs post
    smtResult <- if canBeSat (props, leaf)
      then do
        res <- checkSatWithPropsAbortable solvers (Just shouldAbort) props
        when (conf.debug && conf.verb >=2) $ liftIO $ putStrLn $ "   Checking leaf with props: " <> show props <> " SMT result: " <> show res
        -- Call custom handler if provided (for immediate Cex processing/validation/printing)
        -- stop the other paths first: the handler may replay the counterexample, which takes a while
        when (conf.earlyAbort && isCex res) $ liftIO $ atomically $ writeTVar shouldAbort True
        case (cexHandler, res) of
          (Just handler, cex@(Cex _)) -> handler preState cex leaf
          _ -> pure ()
        pure (res, leaf)
      else pure (Qed, leaf)
    aborted <- liftIO $ readTVarIO shouldAbort
    pure $ if aborted && not (isCex (fst smtResult)) then Nothing else Just (smtResult, mPartial)

  let (smtResults, partials) = unzip (catMaybes results)
  when conf.debug $ liftIO $ do
    putStrLn $ "   Exploration and solving finished, " <> show (length smtResults) <> " branch(es) checked in call " <> call <> " of which partial: "
                <> show (length (catMaybes partials))
    let cexs = filter (\(res, _) -> not . isQed $ res) smtResults
    putStrLn $ "   Found " <> show (length cexs) <> " potential counterexample(s) in call " <> call

  pure (smtResults, catMaybes partials)
  where
    getCallPrefix :: Expr Buf -> String
    getCallPrefix (WriteByte (Lit 0) (LitByte a) (WriteByte (Lit 1) (LitByte b) (WriteByte (Lit 2) (LitByte c) (WriteByte (Lit 3) (LitByte d) _)))) = mconcat $ map (printf "%02x") [a,b,c,d]
    getCallPrefix _ = "unknown"
    toProps leaf keccakPreImgs post' = let
      postCondition = post' preState leaf
     in case postCondition of
      PBool True -> [PBool False]
      _ -> PNeg postCondition : extractProps leaf <> Preimages.recordedProps keccakPreImgs

    canBeSat (a, _) = case a of
        [PBool False] -> False
        _ -> True

expandCex :: VM Symbolic -> SMTCex -> SMTCex
expandCex prestate c = c { store = Map.union c.store concretePreStore }
  where
    concretePreStore = Map.mapMaybe (Expr.maybeConcStoreSimp . (.storage))
                     . Map.filter (\v -> Expr.containsNode isConcreteStore v.storage)
                     $ (prestate.env.contracts)
    isConcreteStore = \case
      ConcreteStore _ -> True
      _ -> False

produceModels :: App m => SolverGroup -> [Expr End] -> m [(Expr End, SMTResult)]
produceModels solvers exprs = do
  let withQueries = fmap (\e -> (extractProps e, e)) exprs
  results <- withRunInIO $ \runInIO -> (flip mapConcurrently) withQueries $ \(query, leaf) -> do
    res <- runInIO $ checkSatWithProps solvers query
    pure (res, leaf)
  pure $ fmap swap $ filter (\(res, _) -> not . isQed $ res) results

getCex :: ProofResult a b -> Maybe a
getCex (Cex c) = Just c
getCex _ = Nothing
