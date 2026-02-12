{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DisambiguateRecordFields #-}

module EVM.SymExec where

import Prelude hiding (Foldable(..))

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.Async ( mapConcurrently)
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent.Spawn (parMapIO, pool)
import Control.Concurrent.STM (writeTChan, newTChan, TChan, readTChan, atomically, isEmptyTChan, STM)
import Control.Concurrent.STM.TVar (TVar, newTVarIO, modifyTVar, readTVar, readTVarIO, writeTVar)
import Control.Concurrent.STM.TMVar (TMVar, putTMVar, takeTMVar, newEmptyTMVarIO)
import Control.Monad (when, unless, forM_, forM, forever, void)
import Control.Monad.Loops (whileM)
import Control.Monad.IO.Unlift (MonadUnliftIO, toIO, withRunInIO)
import Control.Monad.Operational qualified as Operational
import Control.Monad.ST (RealWorld, stToIO, ST)
import Control.Monad.State.Strict (liftIO, runStateT)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.DoubleWord (Word256)
import Data.Foldable (length, foldl', foldr)
import Data.List (sortBy, sort)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe, catMaybes)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as T
import Data.Tree.Zipper qualified as Zipper
import Data.Tuple (swap)
import Data.Vector qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.ByteString (vectorToByteString)
import GHC.Conc (numCapabilities, getNumProcessors)
import GHC.Generics (Generic)
import GHC.Num.Natural (Natural)
import Optics.Core
import Options.Generic (ParseField, ParseFields, ParseRecord)
import Text.Printf (printf)
import Witch (into, unsafeInto)

import EVM (makeVm, abstractContract, initialContract, getCodeLocation, isValidJumpDest, defaultVMOpts)
import EVM.Exec (exec)
import EVM.Fetch qualified as Fetch
import EVM.ABI
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Format (formatExpr, formatPartial, formatPartialDetailed, showVal, indent, formatBinary, formatProp, formatState, formatError)
import EVM.SMT qualified as SMT
import EVM.Solvers (SolverGroup, checkSatWithProps)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.Traversals (mapExpr, mapExprM, foldTerm)
import EVM.Types hiding (Comp)
import EVM.Types qualified
import EVM.Solidity (WarningData (..))

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

groupPartials :: Maybe (WarningData t) -> [Expr End] -> [(Integer, String)]
groupPartials warnData e = map (\g -> (into (length g), NE.head g)) grouped
  where
    getPartial :: Expr End -> Maybe String
    getPartial (Partial _ _ reason) = Just $ T.unpack $ formatPartialDetailed warnData reason
    getPartial _ = Nothing
    grouped = NE.group $ sort $ mapMaybe getPartial e

data IterConfig = IterConfig
  { maxIter :: Maybe Integer
  , askSmtIters :: Integer
  , loopHeuristic :: LoopHeuristic
  }
  deriving (Eq, Show)

defaultIterConf :: IterConfig
defaultIterConf = IterConfig
  { maxIter = Nothing
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


-- | Abstract calldata argument generation
symAbiArg :: Text -> AbiType -> CalldataFragment
symAbiArg name = \case
  AbiUIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then St [] v
    else internalError "bad type"
  AbiIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then St [] v
    else internalError "bad type"
  AbiBoolType -> St [] v
  AbiAddressType -> St [] (WAddr (SymAddr name))
  AbiBytesType n ->
    if n > 0 && n <= 32
    then St [] v
    else internalError "bad type"
  AbiArrayType sz tps -> do
    Comp . V.toList . V.imap (\(T.pack . show -> i) tp -> symAbiArg (name <> "-a-" <> i) tp) $ (V.replicate sz tps)
  AbiTupleType tps ->
    Comp . V.toList . V.imap (\(T.pack . show -> i) tp -> symAbiArg (name <> "-t-" <> i) tp) $ tps
  t -> internalError $ "TODO: symbolic abi encoding for " <> show t
  where
    v = Var name

data CalldataFragment
  = St [Prop] (Expr EWord)
  | Dy [Prop] (Expr EWord) (Expr Buf)
  | Comp [CalldataFragment]
  deriving (Show, Eq)

-- | Generates calldata matching given type signature, optionally specialized
-- with concrete arguments.
-- Any argument given as "<symbolic>" or omitted at the tail of the list are
-- kept symbolic.
symCalldata :: App m => Text -> [AbiType] -> [String] -> Expr Buf -> m (Expr Buf, [Prop])
symCalldata sig typesignature concreteArgs base = do
  conf <- readConfig
  let
    args = concreteArgs <> replicate (length typesignature - length concreteArgs) "<symbolic>"
    mkArg :: AbiType -> String -> Int -> CalldataFragment
    mkArg typ "<symbolic>" n = symAbiArg (T.pack $ "arg" <> show n) typ
    mkArg typ arg _ =
      case makeAbiValue typ arg of
        AbiUInt _ w -> St [] . Lit . into $ w
        AbiInt _ w -> St [] . Lit . unsafeInto $ w
        AbiAddress w -> St [] . Lit . into $ w
        AbiBool w -> St [] . Lit $ if w then 1 else 0
        _ -> internalError "TODO"
    calldatas = zipWith3 mkArg typesignature args [1..]
    (cdBuf, props) = combineFragments calldatas base
    withSelector = writeSelector cdBuf sig
    sizeConstraints
      = (Expr.bufLength withSelector .>= cdLen calldatas)
      .&& (Expr.bufLength withSelector .< (Lit (2 ^ conf.maxBufSize)))
  pure (withSelector, sizeConstraints : props)

cdLen :: [CalldataFragment] -> Expr EWord
cdLen = go (Lit 4)
  where
    go acc = \case
      [] -> acc
      (hd:tl) -> case hd of
                   St _ _ -> go (Expr.add acc (Lit 32)) tl
                   Comp xs | all isSt xs -> go acc (xs <> tl)
                   _ -> internalError "unsupported"

writeSelector :: Expr Buf -> Text -> Expr Buf
writeSelector buf sig =
  writeSel (Lit 0) $ writeSel (Lit 1) $ writeSel (Lit 2) $ writeSel (Lit 3) buf
  where
    sel = ConcreteBuf $ selector sig
    writeSel idx = Expr.writeByte idx (Expr.readByte idx sel)

combineFragments :: [CalldataFragment] -> Expr Buf -> (Expr Buf, [Prop])
combineFragments fragments base = go (Lit 4) fragments (base, [])
  where
    go :: Expr EWord -> [CalldataFragment] -> (Expr Buf, [Prop]) -> (Expr Buf, [Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) =
      case f of
        -- static fragments get written as a word in place
        St p w -> go (Expr.add idx (Lit 32)) rest (Expr.writeWord idx w buf, p <> ps)
        -- compound fragments that contain only static fragments get written in place
        Comp xs | all isSt xs -> go idx (xs <> rest) (buf,ps)
        -- dynamic fragments are not yet supported... :/
        s -> internalError $ "unsupported cd fragment: " <> show s

isSt :: CalldataFragment -> Bool
isSt (St {}) = True
isSt (Comp fs) = all isSt fs
isSt _ = False


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
    , blockGaslimit = 0
    , prevRandao = 42069
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
    , blockGaslimit = 0
    , prevRandao = 42069
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
      ConcreteMemory m -> SymbolicMemory . ConcreteBuf . vectorToByteString <$> VS.freeze m
      m@(SymbolicMemory _) -> pure m

type PathHandler m a = Expr End -> TVar Bool -> m a

data InterpTask m a = InterpTask
  {fetcher :: Fetch.Fetcher Symbolic m
  , iterConf :: IterConfig
  , vm :: VM Symbolic
  , taskQ :: Chan (InterpTask m a)
  , numTasks :: TVar Natural
  , stepper :: Stepper Symbolic (Expr End)
  , handler :: PathHandler m a
  , shouldAbort :: TVar Bool
  }

data Process m a = Process
  { result :: Expr End
  , handler :: PathHandler m a
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
  conf <- readConfig
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
  numProcs <- liftIO $ newTVarIO 0
  allProcessDone <- liftIO newEmptyTMVarIO

  -- spawn task orchestration thread
  taskOrchestrate' <- toIO $ taskOrchestrate taskQ shouldAbort availableInstances processQ numTasks numProcs
  taskOrchestrateId <- liftIO $ forkIO taskOrchestrate'

  -- spawn processing orchestration thread
  processOrchestrate' <- toIO $ processOrchestrate processQ shouldAbort availableProcs resChan numProcs numTasks allProcessDone
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
        , shouldAbort = shouldAbort
        }
  liftIO $ writeChan taskQ interpTask

  -- Wait for all done
  liftIO . atomically $ takeTMVar allProcessDone
  liftIO $ killThread taskOrchestrateId
  liftIO $ killThread processOrchestrateId
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
      -> TVar Natural -> TVar Natural -> m ()
    taskOrchestrate taskQ shouldAbort avail processQ numTasks numProcs = forever $ do
      _ <- liftIO $ readChan avail
      task <- liftIO $ readChan taskQ
      abortFlag <- liftIO $ readTVarIO shouldAbort
      if abortFlag
        then liftIO $ writeChan avail ()
        else do
          runTask' <- toIO $ getOneExpr task avail processQ numTasks numProcs
          void $ liftIO $ forkIO runTask'

    -- processing orchestrator loop
    processOrchestrate :: App m
      => Chan (Process m a) -> TVar Bool -> Chan () -> TChan a
      -> TVar Natural -> TVar Natural -> TMVar () -> m ()
    processOrchestrate processQ shouldAbort avail resChan numProcs numTasks allProcessDone = forever $ do
      _ <- liftIO $ readChan avail
      proc <- liftIO $ readChan processQ
      abortFlag <- liftIO $ readTVarIO shouldAbort
      if abortFlag
        then liftIO $ writeChan avail ()
        else do
          runProcess' <- toIO $ processOne proc shouldAbort avail resChan numProcs numTasks allProcessDone
          void $ liftIO $ forkIO runProcess'

    -- process one task
    processOne :: App m => Process m a -> TVar Bool -> Chan () -> TChan a -> TVar Natural -> TVar Natural -> TMVar () -> m ()
    processOne task shouldAbort avail resChan numProcs numTasks allProcessDone = do
      processed <- task.handler task.result shouldAbort
      liftIO . atomically $ writeTChan resChan processed

      -- Return instance to pool immediately after processing
      liftIO $ writeChan avail ()

      -- Decrement and check if all done
      liftIO $ atomically $ do
        np <- readTVar numProcs
        let np' = np - 1
        writeTVar numProcs np'
        -- Check if both interpretation and processing are done
        nt <- readTVar numTasks
        when (np' == 0 && nt == 0) $ putTMVar allProcessDone ()

getOneExpr :: forall m a . App m
  => InterpTask m a
  -> Chan ()
  -> Chan (Process m a)
  -> TVar Natural
  -> TVar Natural
  -> m ()
getOneExpr task availableInstances processQ numTasks numProcs = do
  out <- interpretInternal task

  -- Enqueue for processing
  let process = Process { result = out, handler = task.handler }
  liftIO . atomically $ modifyTVar numProcs (+1)

  -- Return instance to pool & decrement tasks
  liftIO $ writeChan availableInstances ()
  liftIO $ atomically $ modifyTVar numTasks (subtract 1)

  -- Finally write to process queue. Must be done after numTasks decrement,
  -- or it could be that when we check in processOne, numTasks is still non-zero
  liftIO $ writeChan processQ process

-- | Symbolic interpreter that explores all paths. Returns an
-- '[Expr End]' representing the possible execution leafs.
interpretInternal :: forall m a . App m
  => InterpTask m a
  -> m (Expr End)
interpretInternal t@InterpTask{..} = eval (Operational.view stepper)
  where
  eval :: Operational.ProgramView (Stepper.Action Symbolic) (Expr End) -> m (Expr End)
  eval (Operational.Return x) = pure x
  eval (action Operational.:>>= k) =
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
        frozen <- liftIO $ stToIO $ freezeVM vm
        let newDepth = vm.exploreDepth+1
        runOne frozen newDepth vals
        where
          runOne :: App m => VM 'Symbolic -> Int -> [Expr EWord] -> m (Expr End)
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
              m <- fetcher q
              (r, vm') <- liftIO$ stToIO $ runStateT m vm
              interpretInternal t { vm = vm', stepper = (k r) }

        case q of
          PleaseAskSMT cond preconds continue -> do
            case Expr.concKeccakSimpExpr cond of
              -- is the condition concrete?
              Lit c ->
                -- have we reached max iterations, are we inside a loop?
                case (maxIterationsReached vm iterConf.maxIter, isLoopHead iterConf.loopHeuristic vm) of
                  -- Yes. return a partial leaf
                  (Just _, Just True) ->
                    pure $ Partial [] (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) $ MaxIterationsReached vm.state.pc vm.state.contract
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
                    let partialLeaf = Partial [] (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) (MaxIterationsReached vm.state.pc vm.state.contract)
                    liftIO $ atomically $ modifyTVar numTasks (+1)
                    liftIO $ writeChan taskQ $ t { vm = vm, stepper = pure partialLeaf }
                    (r, vm') <- liftIO $ stToIO $ runStateT (continue (Case $ not n)) vm
                    interpretInternal t { vm = vm', stepper = (k r) }
                  -- we're in a loop and askSmtIters has been reached
                  (Just True, True, _) ->
                    -- ask the smt solver about the loop condition
                    performQuery
                  _ -> do
                    let simpProps = Expr.concKeccakSimpProps ((cond ./= Lit 0):preconds)
                    (r, vm') <- case simpProps of
                      [PBool False] -> liftIO $ stToIO $ runStateT (continue (Case False)) vm
                      [] -> liftIO $ stToIO $ runStateT (continue (Case True)) vm
                      _ -> liftIO $ stToIO $ runStateT (continue UnknownBranch) vm
                    interpretInternal t { vm = vm', stepper = (k r) }
          _ -> performQuery

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
  calldata <- mkCalldata signature' concreteArgs
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

-- | Builds a buffer representing calldata from the provided method description
-- and concrete arguments
mkCalldata :: App m => Maybe Sig -> [String] -> m (Expr Buf, [Prop])
mkCalldata Nothing _ = do
  conf <- readConfig
  pure ( AbstractBuf "txdata"
       -- assert that the length of the calldata is never more than 2^64
       -- this is way larger than would ever be allowed by the gas limit
       -- and avoids spurious counterexamples during abi decoding
       -- TODO: can we encode calldata as an array with a smaller length?
       , [Expr.bufLength (AbstractBuf "txdata") .< (Lit (2 ^ conf.maxBufSize))]
       )
mkCalldata (Just (Sig name types)) args =
  symCalldata name types args (AbstractBuf "txdata")

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
  calldata <- mkCalldata signature' concreteArgs
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
  calldata <- mkCalldata signature' concreteArgs
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
  (ends1, partials) <- verifyInputsWithHandler solvers opts fetcher preState post cexHandler
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
  => SolverGroup
  -> VeriOpts
  -> Fetch.Fetcher Symbolic m
  -> VM Symbolic
  -> Postcondition
  -> Maybe (VM Symbolic -> SMTResult -> Expr End -> m ())
  -> m ([(SMTResult, Expr End)], [(PartialExec, Expr End)])
verifyInputsWithHandler solvers opts fetcher preState post cexHandler = do
  conf <- readConfig
  let call = mconcat ["prefix 0x", getCallPrefix preState.state.calldata]
  when conf.debug $ liftIO $ do
    putStrLn $ "   Keccak preimages in state: " <> (show $ length preState.keccakPreImgs)
    putStrLn $ "   Exploring call " <> call

  results <- executeVM fetcher opts.iterConf preState $ \leaf shouldAbort -> do
    -- Extract partial if applicable
    let mPartial = case leaf of
          Partial _ _ p -> Just (p, leaf)
          _ -> Nothing

    -- Check if this leaf needs SMT checking
    let props = toProps leaf preState.keccakPreImgs post
    smtResult <- if canBeSat (props, leaf)
      then do
        res <- checkSatWithProps solvers props
        when (conf.debug && conf.verb >=2) $ liftIO $ putStrLn $ "   Checking leaf with props: " <> show props <> " SMT result: " <> show res
        -- Call custom handler if provided (for immediate Cex processing/validation/printing)
        case (cexHandler, res) of
          (Just handler, cex@(Cex _)) -> do
            handler preState cex leaf
            when conf.earlyAbort $ liftIO $ atomically $ writeTVar shouldAbort True
          (_, (Cex _)) -> when conf.earlyAbort $ liftIO $ atomically $ writeTVar shouldAbort True
          _ -> pure ()
        pure (res, leaf)
      else pure (Qed, leaf)
    pure (smtResult, mPartial)

  let (smtResults, partials) = unzip results
  when conf.debug $ liftIO $ do
    putStrLn $ "   Exploration and solving finished, " <> show (length results) <> " branch(es) checked in call " <> call <> " of which partial: "
                <> show (length smtResults)
    let cexs = filter (\(res, _) -> not . isQed $ res) smtResults
    putStrLn $ "   Found " <> show (length cexs) <> " potential counterexample(s) in call " <> call

  pure (smtResults, catMaybes partials)
  where
    getCallPrefix :: Expr Buf -> String
    getCallPrefix (WriteByte (Lit 0) (LitByte a) (WriteByte (Lit 1) (LitByte b) (WriteByte (Lit 2) (LitByte c) (WriteByte (Lit 3) (LitByte d) _)))) = mconcat $ map (printf "%02x") [a,b,c,d]
    getCallPrefix _ = "unknown"
    toProps leaf keccakPreImgs post' = let
      postCondition = post' preState leaf
      keccakConstraints = map (\(bs, k)-> PEq (Keccak (ConcreteBuf bs)) (Lit k)) (Set.toList keccakPreImgs)
     in case postCondition of
      PBool True -> [PBool False]
      _ -> PNeg postCondition : extractProps leaf <> keccakConstraints

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

data EqIssues = EqIssues
  { res :: [(EquivResult, String)]
    , partials :: [Expr End]
  }
  deriving (Show, Eq)

instance Monoid EqIssues where
  mempty = EqIssues mempty mempty

instance Semigroup EqIssues where
  EqIssues a1 b1 <> EqIssues a2 b2 = EqIssues (a1 <> a2) (b1 <> b2)

-- | Compares two contract runtimes for trace equivalence by running two VMs
-- and comparing the end states.
--
-- We do this by asking the solver to find a common input for each pair of
-- endstates that satisfies the path conditions for both sides and produces a
-- differing output. If we can find such an input, then we have a clear
-- equivalence break, and since we run this check for every pair of end states,
-- the check is exhaustive.
equivalenceCheck
  :: forall m . App m
  => SolverGroup
  -> Maybe Fetch.Session
  -> ByteString
  -> ByteString
  -> VeriOpts
  -> (Expr Buf, [Prop])
  -> Bool
  -> m EqIssues
equivalenceCheck solvers sess bytecodeA bytecodeB opts calldata create = do
  conf <- readConfig
  case bytecodeA == bytecodeB of
    True -> liftIO $ do
      when conf.debug $ putStrLn "bytecodeA and bytecodeB are identical"
      pure mempty
    False -> do
      when conf.debug $ liftIO $ do
        putStrLn "bytecodeA and bytecodeB are different, checking for equivalence"
      branchesAorig <- getBranches bytecodeA
      branchesBorig <- getBranches bytecodeB
      when conf.debug $ liftIO $ do
        liftIO $ putStrLn $ "branchesA props: " <> show (map extractProps branchesAorig)
        liftIO $ putStrLn $ "branchesB props: " <> show (map extractProps branchesBorig)
        liftIO $ putStrLn ""
        liftIO $ putStrLn $ "branchesA endstates: " <> show (map extractEndStates branchesAorig)

        liftIO $ putStrLn $ "branchesB endstates: " <> show (map extractEndStates branchesBorig)
      let branchesA = rewriteFresh "A-" branchesAorig
          branchesB = rewriteFresh "B-" branchesBorig
      let partialIssues = EqIssues mempty (filter isPartial branchesA <> filter isPartial branchesB)
      issues <- equivalenceCheck' solvers sess branchesA branchesB create
      pure $ filterQeds (issues <> partialIssues)
  where
    -- decompiles the given bytecode into a list of branches
    getBranches :: App m => ByteString -> m [Expr End]
    getBranches bs = do
      let bytecode = if BS.null bs then BS.pack [0] else bs
      prestate <- liftIO $ stToIO $ abstractVM calldata bytecode Nothing create
      interpret (Fetch.oracle solvers sess Fetch.noRpc) opts.iterConf prestate runExpr noopPathHandler
    filterQeds (EqIssues res partials) = EqIssues (filter (\(r, _) -> not . isQed $ r) res) partials

rewriteFresh :: Text -> [Expr a] -> [Expr a]
rewriteFresh prefix exprs = fmap (mapExpr mymap) exprs
  where
    mymap :: Expr a -> Expr a
    mymap = \case
      Gas p x -> Gas (prefix <> p) x
      Var name | ("-fresh-" `T.isInfixOf` name) -> Var $ prefix <> name
      AbstractBuf name | ("-fresh-" `T.isInfixOf` name) -> AbstractBuf $ prefix <> name
      x -> x

equivalenceCheck'
  :: forall m . App m
  => SolverGroup -> Maybe Fetch.Session -> [Expr End] -> [Expr End] -> Bool -> m EqIssues
equivalenceCheck' solvers sess branchesA branchesB create = do
      conf <- readConfig
      when conf.debug $ do
        liftIO $ printPartialIssues branchesA "codeA"
        liftIO $ printPartialIssues branchesB "codeB"

      let allPairs = [(a,b) | a <- branchesA, b <- branchesB]
      when conf.debug $ liftIO $ putStrLn $ "Found " <> show (length allPairs) <> " total pairs of endstates"

      when conf.dumpEndStates $ liftIO $
        putStrLn $ "endstates in bytecodeA: " <> show (length branchesA)
                   <> "\nendstates in bytecodeB: " <> show (length branchesB)

      ps <- forM allPairs $ uncurry distinct
      let differingEndStates = sortBySize $ mapMaybe (view _1) ps
      let knownIssues = foldr ((<>) . (view _2)) mempty ps
      when conf.debug $ liftIO $ putStrLn $ "Asking the SMT solver for " <> (show $ length differingEndStates) <> " pairs"
      when conf.dumpEndStates $ forM_ (zip differingEndStates [(1::Integer)..]) (\((props, msg), i) ->
        liftIO $ T.writeFile ("prop-checked-" <> show i <> ".prop") (T.pack $ show props <> msg))

      procs <- liftIO getNumProcessors
      newDifferences <- checkAll differingEndStates procs
      let additionalIssues = EqIssues newDifferences mempty
      pure $ knownIssues <> additionalIssues

  where
    -- we order the sets by size because this gives us more UNSAT cache hits when
    -- running our queries later on (since we rely on a subset check)
    sortBySize :: [(Set a, b)] -> [(Set a, b)]
    sortBySize = sortBy (\(a, _) (b, _) -> compare (Set.size a) (Set.size b))

    -- Allows us to run the queries in parallel. Note that this (seems to) run it
    -- from left-to-right, and with a max of K threads. This is in contrast to
    -- mapConcurrently which would spawn as many threads as there are jobs, and
    -- run them in a random order. We ordered them correctly, though so that'd be bad
    checkAll :: (App m, MonadUnliftIO m) => [(Set Prop, String)] -> Int -> m [(EquivResult, String)]
    checkAll input numproc = withRunInIO $ \env -> do
       wrap <- pool numproc
       parMapIO (runOne env wrap) input
       where
         runOne env wrap (props, meaning) = do
           res <- wrap (env $ checkSatWithProps solvers (Set.toList props))
           pure (res, meaning)

    -- Takes two branches and returns a set of props that will need to be
    -- satisfied for the two branches to violate the equivalence check. i.e.
    -- for a given pair of branches, equivalence is violated if there exists an
    -- input that satisfies the branch conditions from both sides and produces
    -- a differing result in each branch
    distinct :: App m => Expr End -> Expr End -> m (Maybe (Set Prop, String), EqIssues)
    distinct aEnd bEnd = do
      (requireToDiff, issues) <- resultsDiffer aEnd bEnd
      let newIssues = EqIssues [] (filter isPartial [aEnd, bEnd])
      pure (collectReqs requireToDiff, issues <> newIssues)
      where
        collectReqs (Just (reqToDiff, meaning)) = Just (Set.fromList $ Expr.simplifyProps (reqToDiff : extractProps aEnd <> extractProps bEnd), meaning)
        collectReqs Nothing  = Nothing

    -- Note that the a==b and similar checks are ONLY syntactic checks. If they are true,
    -- then they are surely equivalent. But if not, we need to check via SMT
    resultsDiffer :: App m => Expr End -> Expr End -> m (Maybe (Prop, String), EqIssues)
    resultsDiffer aEnd bEnd = do
      let deployText :: String = if create then "Undeployed contracts. " else "Deployed contracts. "
      case (aEnd, bEnd) of
        (Success aProps _ aOut aState, Success bProps _ bOut bState) ->
          case (aOut == bOut, aState == bState, create) of
            (True, True, _) -> pure (Nothing, mempty)
            (_, _, True) -> do
              -- Either the deployed code doesn't behave the same, or they start with a different
              -- starting state
              deployedContractIssues <- deployedCodeDiffer aOut bOut aProps bProps
              let deployedStateDiffer = (statesDiffer aState bState,
                    deployText <> "Both end in Successful code deployment, but starting states differ. " <>
                    "\nRet of A: " <> T.unpack (formatExpr aOut) <>
                    "\nState of A: " <> T.unpack (formatState aState) <>
                    "\nRet of B: " <> T.unpack (formatExpr bOut) <>
                    "\nState of B: " <> T.unpack (formatState bState))
              pure (Just deployedStateDiffer, deployedContractIssues)
            (_, _, False) -> do
              pure (Just ((aOut ./= bOut) .|| (statesDiffer aState bState),
                deployText <> "Both end in Success, but return values or end state differ. " <>
                "\nRet of A: " <> T.unpack (formatExpr aOut) <>
                "\nState of A: " <> T.unpack (formatState aState) <>
                "\nRet of B: " <> T.unpack (formatExpr bOut) <>
                "\nState of B: " <> T.unpack (formatState bState)), mempty)
        (Failure _ _ a, Failure _ _ b) -> pure (Just (differentError a b,
                  deployText <> "Both end in Failure but different EVM error." <>
                  "\nA err: " <> T.unpack (formatError a) <>
                  "\nB err: " <> T.unpack (formatError b)), mempty)
        ((Failure _ _ a), (Success _ _ b _)) -> pure (Just (PBool True,
          deployText <> "Failure vs Success end states" <>
          "\nA err: " <> T.unpack (formatError a) <>
          "\nB ret: " <> T.unpack (formatExpr b)), mempty)
        ((Success _ _ a _), (Failure _ _ b)) -> pure (Just (PBool True,
          deployText <> "Success vs Failure end states" <>
          "\nA ret: " <> T.unpack (formatExpr a) <>
          "\nB err: " <> T.unpack (formatError b)), mempty)
        -- partial end states can't be compared to actual end states, so we always ignore them
        (Partial {}, _) -> pure (Nothing, mempty)
        (_, Partial {}) -> pure (Nothing, mempty)
        (GVar _, _) -> internalError "GVar in equivalence check"
        (_, GVar _) -> internalError "GVar in equivalence check"

        where
          -- All EVM errors that cannot be syntactically compared are compared semantically: BalanceTooLow, Revert, and MaxInitCodeSizeExceeded
          differentError :: EvmError ->EvmError -> Prop
          differentError a b =  case (a, b) of
            (BalanceTooLow a1Word a2Word, BalanceTooLow b1Word b2Word) -> (a1Word ./= b1Word) .|| (a2Word ./= b2Word)
            (Revert aBuf, Revert bBuf) -> aBuf ./= bBuf
            (MaxInitCodeSizeExceeded l1 aWord, MaxInitCodeSizeExceeded l2 bWord) -> (PBool (l1 /= l2)) .|| (aWord ./= bWord)
            (x, y) | x == y -> PBool False
                   | otherwise -> PBool True

    -- If the original check was for create (i.e. undeployed code), then we must also check that the deployed
    -- code is equivalent. The constraints from the undeployed code (aProps,bProps) influence this check.
    deployedCodeDiffer :: Expr Buf -> Expr Buf -> [Prop] -> [Prop] -> m EqIssues
    deployedCodeDiffer aOut bOut aProps bProps = do
      let simpA = Expr.simplify aOut
          simpB = Expr.simplify bOut
      conf <- readConfig
      case (simpA, simpB) of
        (ConcreteBuf codeA, ConcreteBuf codeB) -> do
          -- TODO: use aProps/bProps to constrain the deployed code
          --       since symbolic code (with constructors taking arguments) is not supported,
          --       this is currently not necessary
          when conf.debug $ liftIO $ do
            liftIO $ putStrLn $ "create deployed code A: " <> bsToHex codeA
              <> " with constraints: " <> (T.unpack . T.unlines $ map formatProp aProps)
            liftIO $ putStrLn $ "create deployed code B: " <> bsToHex codeB
              <> " with constraints: " <> (T.unpack . T.unlines $ map formatProp bProps)
          calldata <- mkCalldata Nothing []
          equivalenceCheck solvers sess codeA codeB defaultVeriOpts calldata False
        _ -> internalError $ "Symbolic code returned from constructor." <> " A: " <> show simpA <> " B: " <> show simpB

    statesDiffer :: Map (Expr EAddr) (Expr EContract) -> Map (Expr EAddr) (Expr EContract) -> Prop
    statesDiffer aState bState =
      case aState == bState of
        True -> PBool False
        False ->  if Set.fromList (Map.keys aState) /= Set.fromList (Map.keys bState)
          -- TODO: consider possibility of aliased symbolic addresses
          then PBool True
          else let
            merged = (Map.merge Map.dropMissing Map.dropMissing (Map.zipWithMatched (\_ x y -> (x,y))) aState bState)
          in Map.foldl' (\a (ac, bc) -> a .|| contractsDiffer ac bc) (PBool False) merged

    contractsDiffer :: Expr EContract -> Expr EContract -> Prop
    contractsDiffer ac bc = let
        balsDiffer = case (ac.balance, bc.balance) of
          (Lit ab, Lit bb) -> PBool $ ab /= bb
          (ab, bb) -> if ab == bb then PBool False else ab ./= bb
        -- TODO: is this sound? do we need a more sophisticated nonce representation?
        noncesDiffer = PBool (ac.nonce /= bc.nonce)
        storesDiffer = case (ac.storage, bc.storage) of
          (ConcreteStore as, ConcreteStore bs) | not (as == Map.empty || bs == Map.empty) -> PBool $ as /= bs
          (as, bs) -> if as == bs then PBool False else as ./= bs
      in balsDiffer .|| storesDiffer .|| noncesDiffer


both' :: (a -> b) -> (a, a) -> (b, b)
both' f (x, y) = (f x, f y)

produceModels :: App m => SolverGroup -> [Expr End] -> m [(Expr End, SMTResult)]
produceModels solvers exprs = do
  let withQueries = fmap (\e -> (extractProps e, e)) exprs
  results <- withRunInIO $ \runInIO -> (flip mapConcurrently) withQueries $ \(query, leaf) -> do
    res <- runInIO $ checkSatWithProps solvers query
    pure (res, leaf)
  pure $ fmap swap $ filter (\(res, _) -> not . isQed $ res) results

showModel :: Expr Buf -> (Expr End, SMTResult) -> IO ()
showModel cd (expr, res) = do
  case res of
    Qed -> pure () -- ignore unreachable branches
    Error e -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn $ "Error during SMT solving, cannot check branch " <> e
    Unknown reason -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn $ "Unable to produce a model for the following end state due to '" <> reason <> "' :"
      T.putStrLn $ indent 2 $ formatExpr expr
      putStrLn ""
    Cex cex -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn "Inputs:"
      T.putStrLn $ indent 2 $ formatCex cd Nothing cex
      putStrLn "End State:"
      T.putStrLn $ indent 2 $ formatExpr expr

showBuffer :: (Expr Buf) -> SMTCex -> Text
showBuffer buf cex = case Map.lookup buf cex.buffers of
  Nothing -> internalError "buffer missing in the counterexample"
  Just buffer -> case SMT.collapse buffer of
    Nothing -> T.pack $ show buffer
    Just (Flat bs) -> T.pack $ show bs
    Just (EVM.Types.Comp _) -> internalError "CompressedBuf returned from collapse"

formatCex :: Expr Buf -> Maybe Sig -> SMTCex -> Text
formatCex cd sig m@(SMTCex _ addrs _ store blockContext txContext) = T.unlines $
  [ "Calldata:", indent 2 cd' ]
  <> storeCex
  <> txCtx
  <> blockCtx
  <> addrsCex
  where
    -- we attempt to produce a model for calldata by substituting all variables
    -- and buffers provided by the model into the original calldata expression.
    -- If we have a concrete result then we display it, otherwise we display
    -- `Any`. This is a little bit of a hack (and maybe unsound?), but we need
    -- it for branches that do not refer to calldata at all (e.g. the top level
    -- callvalue check inserted by solidity in contracts that don't have any
    -- payable functions).
    cd' = case sig of
      Nothing -> case (defaultSymbolicValues $ subModel m cd) of
        Right k -> prettyBuf $ Expr.concKeccakSimpExpr k
        Left err -> T.pack err
      Just (Sig n ts) -> prettyCalldata m cd n ts

    storeCex :: [Text]
    storeCex
      | Map.null store = []
      | otherwise =
          [ "Storage:"
          , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
              ("Addr " <> (T.pack . show $ key)
                <> ": " <> (T.pack $ show (Map.toList val))) : acc
            ) mempty store
          ]

    txCtx :: [Text]
    txCtx
      | Map.null txContext = []
      | otherwise =
        [ "Transaction Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
            (showTxCtx key <> ": " <> (T.pack $ show val)) : acc
          ) mempty (filterSubCtx txContext)
        ]

    addrsCex :: [Text]
    addrsCex
      | Map.null addrs = []
      | otherwise =
          [ "Addrs:"
          , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
              ((T.pack . show $ key) <> ": " <> (T.pack $ show val)) : acc
            ) mempty addrs
          ]

    -- strips the frame arg from frame context vars to make them easier to read
    showTxCtx :: Expr EWord -> Text
    showTxCtx (TxValue) = "TxValue"
    showTxCtx x = T.pack $ show x

    -- strips all frame context that doesn't come from the top frame
    filterSubCtx :: Map (Expr EWord) W256 -> Map (Expr EWord) W256
    filterSubCtx = Map.filterWithKey go
      where
        go :: Expr EWord -> W256 -> Bool
        go (TxValue) _ = True
        go (Balance {}) _ = internalError "TODO: BALANCE"
        go (Gas {}) _ = internalError "TODO: Gas"
        go _ _ = False

    blockCtx :: [Text]
    blockCtx
      | Map.null blockContext = []
      | otherwise =
        [ "Block Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
            (T.pack $ show key <> ": " <> show val) : acc
          ) mempty txContext
        ]

prettyBuf :: Expr Buf -> Text
prettyBuf (ConcreteBuf "") = "Empty"
prettyBuf (ConcreteBuf bs) = formatBinary bs
prettyBuf b = internalError $ "Unexpected symbolic buffer:\n" <> T.unpack (formatExpr b)

calldataFromCex :: App m => SMTCex -> Expr Buf -> Sig -> m (Err ByteString)
calldataFromCex cex buf sig = do
  let sigKeccak = BS.take 4 $ keccakBytes $ encodeUtf8 (callSig sig)
  pure $ (sigKeccak <>) <$> body
  where
    cd = defaultSymbolicValues $ subModel cex buf
    argdata = case cd of
      Right cd' -> Right $ Expr.drop 4 (Expr.simplify cd')
      Left e -> Left e
    body = forceConcrete =<< argdata
    forceConcrete :: (Expr Buf) -> Err ByteString
    forceConcrete (ConcreteBuf k) = Right k
    forceConcrete _ = Left "Symbolic buffer in calldata, cannot produce concrete model"

prettyCalldata :: SMTCex -> Expr Buf -> Text -> [AbiType] -> Text
prettyCalldata cex buf sig types = headErr errSig (T.splitOn "(" sig) <> "(" <> body <> ")" <> T.pack finalErr
  where
    cd = defaultSymbolicValues $ subModel cex buf
    argdata :: Err (Expr Buf) = case cd of
      Right cd' -> Right $ Expr.drop 4 (Expr.simplify cd')
      Left e -> Left e
    (body, finalErr) = case argdata of
      Right argdata' -> case decodeBuf types argdata' of
        (CAbi v, "") -> (T.intercalate "," (fmap showVal v), "")
        (CAbi v, err) -> (T.intercalate "," (fmap showVal v), dash <> err)
        (NoVals, err) -> case argdata' of
            ConcreteBuf c -> (T.pack $ "ABI decode failed. hex calldata: 0x" <> (bsToHex c), dash <> err)
            _ -> (T.pack defaultText, dash <> err)
        (SAbi _, err) -> (T.pack defaultText, dash <> err)
      Left err -> (T.pack err, "")
    headErr e l = fromMaybe (T.pack e) $ listToMaybe l
    dash = " -- "
    defaultText = "Error: unable to produce a concrete model for calldata: " <> show buf
    errSig = "Error unable to split sig: " <> show sig

-- | If the expression contains any symbolic values, default them to some
-- concrete value The intuition here is that if we still have symbolic values
-- in our calldata expression after substituting in our cex, then they can have
-- any value and we can safely pick a random value. This is a bit unsatisfying,
-- we should really be doing smth like: https://github.com/argotorg/hevm/issues/334
-- but it's probably good enough for now
defaultSymbolicValues :: Err (Expr a) -> Err (Expr a)
defaultSymbolicValues = \case
    Right e -> subBufs (foldTerm symbufs mempty e)
               . subVars (foldTerm symwords mempty e)
               . subAddrs (foldTerm symaddrs mempty e) $ e
    Left err -> Left err
  where
    symaddrs :: Expr a -> Map (Expr EAddr) Addr
    symaddrs = \case
      a@(SymAddr _) -> Map.singleton a (Addr 0x1312)
      _ -> mempty
    symbufs :: Expr a -> Map (Expr Buf) BufModel
    symbufs = \case
      a@(AbstractBuf _) -> Map.singleton a (Flat BS.empty)
      _ -> mempty
    symwords :: Expr a -> Map (Expr EWord) W256
    symwords = \case
      a@(Var _) -> Map.singleton a 0
      a@Origin -> Map.singleton a 0
      a@Coinbase -> Map.singleton a 0
      a@Timestamp -> Map.singleton a 0
      a@BlockNumber -> Map.singleton a 0
      a@PrevRandao -> Map.singleton a 0
      a@GasLimit -> Map.singleton a 0
      a@ChainId -> Map.singleton a 0
      a@BaseFee -> Map.singleton a 0
      _ -> mempty

-- | Takes an expression and a Cex and replaces all abstract values in the buf with
-- concrete ones from the Cex.
subModel :: SMTCex -> Expr a -> Err (Expr a)
subModel c
  = subBufs c.buffers
  . subStores c.store
  . subVars c.vars
  . subVars c.blockContext
  . subVars c.txContext
  . subAddrs c.addrs

subVars :: Map (Expr EWord) W256 -> Expr a -> Expr a
subVars model b = Map.foldlWithKey subVar b model
  where
    subVar :: Expr a -> Expr EWord -> W256 -> Expr a
    subVar a var val = mapExpr go a
      where
        go :: Expr a -> Expr a
        go = \case
          v@(Var _) -> if v == var
                      then Lit val
                      else v
          e -> e

subAddrs :: Map (Expr EAddr) Addr -> Expr a -> Expr a
subAddrs model b = Map.foldlWithKey subAddr b model
  where
    subAddr :: Expr a -> Expr EAddr -> Addr -> Expr a
    subAddr a var val = mapExpr go a
      where
        go :: Expr a -> Expr a
        go = \case
          v@(SymAddr _) -> if v == var
                      then LitAddr val
                      else v
          e -> e

subBufs :: Map (Expr Buf) BufModel -> Expr a -> Err (Expr a)
subBufs model b = Map.foldlWithKey subBuf (Right b) model
  where
    subBuf :: Err (Expr a) -> Expr Buf -> BufModel -> Err (Expr a)
    subBuf x var val = case x of
      Right x' -> mapExprM go x'
      Left err -> Left err
      where
        go :: Expr a -> Err (Expr a)
        go = \case
          c@(AbstractBuf _) -> case c == var of
            True -> case forceFlattened val of
              Right bs -> Right $ ConcreteBuf bs
              Left err -> Left $ show c <> " --- cannot flatten buffer: " <> err
            False -> Right c
          e -> Right e
        forceFlattened :: BufModel -> Err ByteString
        forceFlattened (Flat bs) = Right bs
        forceFlattened buf@(EVM.Types.Comp _) =  case SMT.collapse buf of
          Just k -> forceFlattened k
          Nothing -> Left $ show buf

subStores :: Map (Expr EAddr) (Map W256 W256) -> Expr a -> Expr a
subStores model b = Map.foldlWithKey subStore b model
  where
    subStore :: Expr a -> Expr EAddr -> Map W256 W256 -> Expr a
    subStore x var val = mapExpr go x
      where
        go :: Expr a -> Expr a
        go = \case
          v@(AbstractStore a _)
            -> if a == var
               then ConcreteStore val
               else v
          e -> e

getCex :: ProofResult a b -> Maybe a
getCex (Cex c) = Just c
getCex _ = Nothing
