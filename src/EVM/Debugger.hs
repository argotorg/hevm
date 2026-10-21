{-# LANGUAGE DeriveAnyClass #-}

-- | Interactive debugging sessions. UI-agnostic: clients drive a 'Session'
-- with text commands and display the resulting 'View'.
module EVM.Debugger
  ( Session
  , Debuggable
  , newSession
  , setStepLimit
  , BranchMode(..)
  , setBranchMode
  , setMerge
  , runCommand
  , runCommandText
  , Command(..)
  , Breakpoint(..)
  , parseCommand
  , View(..)
  , CodeLine(..)
  , SourceView(..)
  , SourceLine(..)
  , BranchView(..)
  , mkView
  , renderView
  , commandHelp
  , sessionVM
  , sessionStep
  , hasPendingBranch
  , Stats(..)
  , StatsView(..)
  , sessionStats
  , renderStats
  , isHalted
  ) where

import Control.Monad (filterM, forM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.ST (ST, RealWorld, stToIO)
import Control.Monad.State.Strict (execStateT)
import Data.Aeson (ToJSON, (.=))
import Data.Aeson.Types (Pair)
import Data.ByteString qualified as BS
import Data.Char (isDigit)
import Data.List (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8With)
import Data.Text.Encoding.Error (lenientDecode)
import Data.Typeable (Typeable)
import Data.Vector qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Data.Word (Word8, Word64)
import GHC.Clock (getMonotonicTime)
import GHC.Generics (Generic)
import Hexdump (prettyHex)
import Numeric (showHex, showFFloat)
import Prettyprinter (layoutPretty, LayoutOptions(..), PageWidth(..), unAnnotate)
import Prettyprinter.Render.Text (renderStrict)
import Data.Tree.View (showTree)
import Text.Read (readMaybe)
import Witch (into, unsafeInto)

import EVM (exec1, currentContract, opSize)
import EVM.Dapp (DappInfo(..), srcMap, srcMapCode)
import EVM.Effects
import EVM.Expr (maybeLitByteSimp, maybeLitWordSimp)
import EVM.Expr qualified as Expr
import EVM.SymExec (staticBranch, checkStaticBranch, StaticCheck(..), askSat)
import EVM.Fetch qualified as Fetch
import EVM.Format (formatExpr, formatProp, traceDocForest)
import EVM.Op (intToOpName)
import EVM.Progress qualified as Progress
import EVM.Solidity (SourceCache(..), SrcMap(..))
import EVM.Types

-- | How symbolic branches are decided: by asking the solver which sides are
-- feasible, or as exploration does, by simplifying without the solver and
-- offering both sides when that is inconclusive. Checked is the latter, with
-- the solver confirming every decision.
data BranchMode = SolverBranches | ExplorerBranches | CheckedBranches
  deriving (Eq, Show)

data Breakpoint
  = BreakPc Int
  | BreakOp Text
  | BreakLine (Maybe FilePath) Int
  deriving (Eq, Show)

data Command
  = Step Int
  | Next
  | Over
  | Out
  | Continue
  | Back Int
  | BackLine
  | Restart
  | Choose Text
  | Break Breakpoint
  | Delete (Maybe Int)
  | ListBreakpoints
  | ShowMemory Int Int
  | ShowStorage
  | ShowCalldata
  | ShowTrace
  | ShowPathConds
  | ShowStats
  | SetSimplify Bool
  | SetBranches BranchMode
  | SetMerge Bool
  | Help
  | Refresh
  deriving (Eq, Show)

-- | A symbolic branch waiting for the user to pick a side
data Pending t where
  Pending :: Maybe (Expr EWord) -> BranchContext -> Pending Symbolic

class (VMOps t, Typeable t) => Debuggable t where
  splitEffect :: Maybe (Expr EWord) -> Effect t -> Either (Query t) (Pending t)
  gasLeft :: VM t -> Maybe Word64
  modeName :: VM t -> Text

instance Debuggable Concrete where
  splitEffect _ (Query q) = Left q
  gasLeft vm = Just vm.state.gas
  modeName _ = "concrete"

instance Debuggable Symbolic where
  splitEffect _ (Query q) = Left q
  splitEffect c (Branch b) = Right (Pending c b)
  gasLeft _ = Nothing
  modeName _ = "symbolic"

data Session t = Session
  { vm          :: VM t
  , curStep     :: Int
  -- | step -> VM after that step. Taken every 'snapshotInterval' steps and after
  -- every step that needed a query, so replaying from one never re-queries.
  , snapshots   :: Map Int (VM t)
  , pending     :: Maybe (Pending t)
  , lastCond    :: Maybe (Expr EWord)
  , taken       :: [(Int, Text)]
  , bps         :: [Breakpoint]
  , dapp        :: DappInfo
  , note        :: Text
  , out         :: Maybe Text
  , stepLimit   :: Int
  , stats       :: Stats
  -- | simplify the expressions shown
  , simp        :: Bool
  , branchMode  :: BranchMode
  -- | problems found by 'CheckedBranches', newest first
  , warnings    :: [Text]
  -- | merge both sides of short branches as exploration does, so a step may
  -- execute a whole if/else
  , merge       :: Bool
  -- | (step, merge): the steps after that step ran with that setting, newest
  -- first, so that going back replays them the same way
  , mergeFrom   :: [(Int, Bool)]
  }

-- | What a session has done so far. Going back in time does not undo these.
data Stats = Stats
  { commands        :: Int
  , commandSecs     :: Double
  , opcodes         :: Int
  -- | the part of 'opcodes' that re-executed steps to go back in time
  , replayedOpcodes :: Int
  , queries         :: Int
  , querySecs       :: Double
  , branchQueries   :: Int
  , solutionQueries :: Int
  , fetchQueries    :: Int
  , otherQueries    :: Int
  , branchesOffered :: Int
  , branchesTaken   :: Int
  -- | branches decided without the solver, in 'ExplorerBranches' mode
  , staticDecisions :: Int
  -- | in 'CheckedBranches' mode: static decisions the solver contradicts, and
  -- branches the solver could decide but simplification could not
  , staticWrong     :: Int
  , staticMissed    :: Int
  , staticInconclusive :: Int
  -- | values of multi-way branches not offered, as the solver finds them infeasible
  , infeasibleOptions :: Int
  , breakpointHits  :: Int
  }
  deriving (Eq, Show, Generic, ToJSON)

data StatsView = StatsView
  { step          :: Int
  , snapshotCount :: Int
  , counters      :: Stats
  }
  deriving (Show, Generic, ToJSON)

emptyStats :: Stats
emptyStats = Stats 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

addStats :: (Stats -> Stats) -> Session t -> Session t
addStats f s = s { stats = f s.stats }

sessionStats :: Session t -> StatsView
sessionStats s = StatsView s.curStep (Map.size s.snapshots) s.stats

renderStats :: StatsView -> Text
renderStats v = T.unlines
  [ "step " <> tshow v.step <> ", " <> tshow v.snapshotCount <> " snapshots"
  , "commands:  " <> tshow c.commands <> " in " <> secs c.commandSecs
  , "opcodes:   " <> tshow c.opcodes <> " executed, " <> tshow c.replayedOpcodes <> " of them to go back"
  , "queries:   " <> tshow c.queries <> " in " <> secs c.querySecs <> " (" <> tshow c.branchQueries <> " branch, "
      <> tshow c.solutionQueries <> " solutions, " <> tshow c.fetchQueries <> " fetch, " <> tshow c.otherQueries <> " other)"
  , "branches:  " <> tshow c.branchesOffered <> " offered, " <> tshow c.branchesTaken <> " taken, "
      <> tshow c.infeasibleOptions <> " infeasible values not offered, "
      <> tshow c.staticDecisions <> " decided without the solver"
  , "checked:   " <> tshow c.staticWrong <> " static decisions the solver contradicts, "
      <> tshow c.staticMissed <> " branches only the solver could decide, "
      <> tshow c.staticInconclusive <> " the solver could not check"
  , "breakpoint hits: " <> tshow c.breakpointHits
  ]
  where
    c = v.counters
    secs x = T.pack (showFFloat (Just 3) x "s")

snapshotInterval :: Int
snapshotInterval = 50

-- | Default bound on the steps a single command takes, so a server stays responsive
maxRunSteps :: Int
maxRunSteps = 5000000

-- | Largest memory dump a command returns
maxMemoryDump :: Int
maxMemoryDump = 65536

setStepLimit :: Int -> Session t -> Session t
setStepLimit n s = s { stepLimit = n }

setBranchMode :: BranchMode -> Session t -> Session t
setBranchMode m s = s { branchMode = m }

setMerge :: Bool -> Session t -> Session t
setMerge b s = s { merge = b, mergeFrom = (s.curStep, b) : s.mergeFrom }

-- | Whether the given step runs with merging
mergesAt :: Session t -> Int -> Bool
mergesAt s i = maybe False snd (find ((< i) . fst) s.mergeFrom)

sessionVM :: Session t -> VM t
sessionVM s = s.vm

sessionStep :: Session t -> Int
sessionStep s = s.curStep

hasPendingBranch :: Session t -> Bool
hasPendingBranch s = isJust s.pending

newSession :: Debuggable t => DappInfo -> VM t -> IO (Session t)
newSession dapp vm0 = do
  snap <- stToIO $ cloneVM vm0
  pure Session
    { vm = vm0, curStep = 0, snapshots = Map.singleton 0 snap, pending = Nothing
    , lastCond = Nothing, taken = [], bps = [], dapp = dapp
    , note = "Started. Type 'help' for commands.", out = Nothing, stepLimit = maxRunSteps
    , stats = emptyStats, simp = True, branchMode = SolverBranches, warnings = [], merge = False
    , mergeFrom = [(-1, False)] }

-- | Memory is a mutable vector, so a VM must be copied before it is kept around
cloneVM :: forall t. VM t -> ST RealWorld (VM t)
cloneVM vm = do
  st <- cloneState vm.state
  frames <- forM vm.frames $ \f -> do
    fs <- cloneState f.state
    pure (f :: Frame t) { state = fs }
  pure vm { state = st, frames = frames }
  where
    cloneState :: FrameState t -> ST RealWorld (FrameState t)
    cloneState s = case s.memory of
      ConcreteMemory m -> do
        m' <- VSM.clone m
        pure (s :: FrameState t) { memory = ConcreteMemory m' }
      SymbolicMemory _ -> pure s

isHalted :: Session t -> Bool
isHalted s = case s.vm.result of
  Just (HandleEffect _) -> False
  Just _ -> True
  Nothing -> False

-- * Stepping

stepOnce :: (App m, Debuggable t) => Fetch.Fetcher t m -> Session t -> m (Session t)
stepOnce fetcher s
  | isJust s.pending || isHalted s = pure s
  | otherwise = do
      conf <- readConfig
      vm' <- liftIO $ stToIO $ execStateT (exec1 conf { mergeMaxBudget = if mergesAt s (s.curStep + 1) then conf.mergeMaxBudget else 0 }) s.vm
      resolve fetcher False $ addStats (\st -> st { opcodes = st.opcodes + 1 }) s { vm = vm', curStep = s.curStep + 1 }

resolve :: (App m, Debuggable t) => Fetch.Fetcher t m -> Bool -> Session t -> m (Session t)
resolve fetcher queried s = case s.vm.result of
  Just (HandleEffect e) -> case splitEffect s.lastCond e of
    Left (PleaseAskSMT c pcs continue) | s.branchMode /= SolverBranches -> do
      let decision = case Expr.concKeccakSimpExpr c of
            Lit v -> Case (v > 0)
            _ -> staticBranch c pcs
      Progress.emit "debug-static-decision" $ where_ s <> ["decision" .= T.pack (show decision)]
      checked <- if s.branchMode /= CheckedBranches then pure s else checkStaticBranch fetcher s.vm c pcs decision >>= \case
        StaticOk -> pure s
        StaticMissed -> pure $ addStats (\st -> st { staticMissed = st.staticMissed + 1 }) s
        StaticInconclusive -> pure $ addStats (\st -> st { staticInconclusive = st.staticInconclusive + 1 }) s
        StaticWrong msg -> do
          Progress.emit "debug-static-decision-wrong" $ where_ s <> ["problem" .= T.pack msg]
          pure $ addStats (\st -> st { staticWrong = st.staticWrong + 1 })
            s { warnings = take 20 (("step " <> tshow s.curStep <> ": " <> T.pack msg) : s.warnings) }
      vm' <- liftIO $ stToIO $ execStateT (continue decision) checked.vm
      resolve fetcher True $ addStats (\st -> st { staticDecisions = st.staticDecisions + 1 }) checked { vm = vm', lastCond = Just c }
    Left q -> do
      let cond = case q of
            PleaseAskSMT c _ _ -> Just c
            _ -> s.lastCond
      -- tells /progress where the solver time goes
      Progress.setWorker [ "pc" .= s.vm.state.pc, "addr" .= T.pack (show s.vm.state.contract), "step" .= s.curStep ]
      t0 <- liftIO getMonotonicTime
      m <- fetcher q
      vm' <- liftIO $ stToIO $ execStateT m s.vm
      t1 <- liftIO getMonotonicTime
      let count st = case q of
            PleaseAskSMT {} -> st { branchQueries = st.branchQueries + 1 }
            PleaseGetSols {} -> st { solutionQueries = st.solutionQueries + 1 }
            PleaseFetchContract {} -> st { fetchQueries = st.fetchQueries + 1 }
            PleaseFetchSlot {} -> st { fetchQueries = st.fetchQueries + 1 }
            _ -> st { otherQueries = st.otherQueries + 1 }
      resolve fetcher True $ addStats (\st -> count st { queries = st.queries + 1, querySecs = st.querySecs + t1 - t0 })
        s { vm = vm', lastCond = cond }
    Right (Pending c ctx0) -> do
      -- forks over the values of a subterm do not check them against the path
      -- conditions: in solver mode only the feasible ones are offered
      (ctx, hidden) <- case ctx0 of
        PleaseRunAll vals k | s.branchMode == SolverBranches -> do
          feasible <- filterM (\v -> do
            vm0 <- liftIO $ stToIO $ cloneVM s.vm
            vmv <- liftIO $ stToIO $ execStateT (k v) (vm0 :: VM Symbolic) { result = Nothing }
            (/= Just False) <$> askSat fetcher vmv vmv.constraints) vals
          pure $ if null feasible then (ctx0, 0) else (PleaseRunAll feasible k, length vals - length feasible)
        _ -> pure (ctx0, 0)
      let s' = addStats (\st -> st { infeasibleOptions = st.infeasibleOptions + hidden }) s
      case ctx of
        PleaseRunAll [v] k -> do
          Progress.emit "debug-branch-decided" $ where_ s <> ["value" .= formatExpr v, "hidden" .= hidden]
          vm' <- liftIO $ stToIO $ execStateT (k v) s.vm { result = Nothing, exploreDepth = s.vm.exploreDepth + 1 }
          resolve fetcher True s' { vm = vm', taken = (s.curStep, formatExpr v) : s.taken }
        _ -> do
          Progress.emit "debug-branch-offered" $ where_ s <> ["options" .= branchOptionCount ctx, "hidden" .= hidden]
          Progress.emitExprs "debug-branch-condition" $ where_ s <> maybe [] (Progress.bigText "cond" . formatExpr) c
          pure $ addStats (\st -> st { branchesOffered = st.branchesOffered + 1 }) s' { pending = Just (Pending c ctx) }
  _ | queried || s.curStep `mod` snapshotInterval == 0 -> do
        snap <- liftIO $ stToIO $ cloneVM s.vm
        pure s { snapshots = Map.insert s.curStep snap s.snapshots }
    | otherwise -> pure s

choose :: (App m, Debuggable t) => Fetch.Fetcher t m -> Text -> Session t -> m (Session t)
choose fetcher arg s = case s.pending of
  Nothing -> pure s { note = "No branch is pending." }
  Just (Pending cond ctx) -> do
    let picked = case (ctx, T.toLower arg) of
          (PleaseRunBoth k, a) | a `elem` ["true", "t", "1", "jump"] -> Just (k True, "true")
                               | a `elem` ["false", "f", "0", "nojump"] -> Just (k False, "false")
          (PleaseRunAll vals k, a) | Just i <- readMaybe (T.unpack a), i >= 0, i < length vals ->
                                       Just (k (vals !! i), formatExpr (vals !! i))
          _ -> Nothing
    case picked of
      Nothing -> pure s { note = "Invalid choice '" <> arg <> "'. " <> branchHint ctx }
      Just (m, desc) -> do
        vm' <- liftIO $ stToIO $ execStateT m s.vm { result = Nothing, exploreDepth = s.vm.exploreDepth + 1 }
        let what = maybe "" (\c -> " for condition " <> clip 200 (formatExpr c)) cond
        Progress.emit "debug-branch-taken" $ where_ s <> ["choice" .= desc]
        s' <- resolve fetcher True $ addStats (\st -> st { branchesTaken = st.branchesTaken + 1 })
                s { vm = vm', pending = Nothing, taken = (s.curStep, desc) : s.taken }
        pure s' { note = "Took branch " <> desc <> what <> "." }

-- | An expression as the session shows it
shown :: Session t -> Expr a -> Expr a
shown s = if s.simp then Expr.simplify else id

-- | Where the session is, for the progress log
where_ :: Session t -> [Pair]
where_ s = ["step" .= s.curStep, "pc" .= s.vm.state.pc, "addr" .= T.pack (show s.vm.state.contract), "depth" .= length s.vm.frames]

branchOptionCount :: BranchContext -> Int
branchOptionCount = \case
  PleaseRunBoth _ -> 2
  PleaseRunAll vals _ -> length vals

branchHint :: BranchContext -> Text
branchHint = \case
  PleaseRunBoth _ -> "Use 'branch true' or 'branch false'."
  PleaseRunAll vals _ -> "Use 'branch <index>' with index 0.." <> tshow (length vals - 1) <> "."

data Stop = StopHalt | StopBranch | StopBreak Int | StopCond | StopLimit

-- | Step until the predicate (given the session before and after a step) holds,
-- or execution halts, or a branch needs choosing, or a breakpoint is hit
runUntil :: (App m, Debuggable t) => Fetch.Fetcher t m -> Int -> (Session t -> Bool) -> Session t -> m (Session t, Stop)
runUntil fetcher limit p = go 0
  where
    go n s
      | isHalted s = pure (s, StopHalt)
      | isJust s.pending = pure (s, StopBranch)
      | n >= limit = pure (s, StopLimit)
      | otherwise = do
          s' <- stepOnce fetcher s
          case findBreak s' of
            Just i -> Progress.emit "debug-breakpoint" (where_ s' <> ["breakpoint" .= showBreak (s'.bps !! i)])
                      >> pure (addStats (\st -> st { breakpointHits = st.breakpointHits + 1 }) s', StopBreak i)
            _ | p s' -> pure (s', StopCond)
              | otherwise -> go (n + 1) s'

findBreak :: Session t -> Maybe Int
findBreak s = fst <$> find (hits . snd) (zip [0..] s.bps)
  where
    hits = \case
      BreakPc pc -> s.vm.state.pc == pc
      BreakOp op -> T.pack (opNameAt s.vm.state.code s.vm.state.pc) == op
      BreakLine file line -> case srcPos s.dapp s.vm of
        Just (_, f, l, _) -> l == line && maybe True (`T.isSuffixOf` T.pack f) (T.pack <$> file)
        Nothing -> False

stopMessage :: Session t -> Stop -> Text
stopMessage s = \case
  StopHalt -> "Execution finished: " <> resultText s.vm
  StopBranch -> "Stopped at a symbolic branch. " <> maybe "" (\(Pending _ ctx) -> branchHint ctx) s.pending
  StopBreak i -> "Hit breakpoint " <> tshow i <> ": " <> showBreak (s.bps !! i)
  StopCond -> ""
  StopLimit -> "Stopped after " <> tshow s.stepLimit <> " steps."

backTo :: (App m, Debuggable t) => Fetch.Fetcher t m -> Int -> Session t -> m (Session t)
backTo fetcher target s = do
  -- a step that took a branch is snapshotted after the choice, so restoring
  -- it would skip the branch: replay that step to offer the branch again
  let chosenAt = target `elem` map fst s.taken
      snaps = Map.filterWithKey (\i _ -> i < target || (i == target && not chosenAt)) s.snapshots
      (k, snap) = fromMaybe (internalError "no initial snapshot") (Map.lookupMax snaps)
  vm <- liftIO $ stToIO $ cloneVM snap
  let s0 = s { vm = vm, curStep = k, snapshots = snaps, pending = Nothing, lastCond = Nothing
             , taken = filter ((< target) . fst) s.taken }
  s1 <- replay (target - k) s0
  -- the steps from here on are new, and run with the current setting
  let s' = s1 { mergeFrom = (target, s.merge) : filter ((< target) . fst) s.mergeFrom }
  Progress.emit "debug-back" ["from" .= s.curStep, "to" .= target, "snapshot" .= k, "replayed" .= (target - k), "branchAgain" .= chosenAt]
  pure $ addStats (\st -> st { replayedOpcodes = st.replayedOpcodes + st.opcodes - s.stats.opcodes }) s'
  where
    replay 0 s' = pure s'
    replay n s' = stepOnce fetcher s' >>= replay (n - 1)

-- * Commands

runCommandText :: (App m, Debuggable t) => Fetch.Fetcher t m -> Text -> Session t -> m (Session t)
runCommandText fetcher line s = do
  t0 <- liftIO getMonotonicTime
  s' <- case parseCommand line of
    Left err -> pure s { note = err, out = Nothing }
    Right cmd -> runCommand fetcher cmd s
  t1 <- liftIO getMonotonicTime
  Progress.emit "debug-command" $
    [ "command" .= line, "from" .= s.curStep, "secs" .= (t1 - t0), "message" .= s'.note
    , "status" .= (if isHalted s' then "halted" else if isJust s'.pending then "branch" else "running" :: Text) ]
    <> where_ s'
  pure $ addStats (\st -> st { commands = st.commands + 1, commandSecs = st.commandSecs + t1 - t0 }) s'

-- | The session passed in stays valid: commands work on a copy of its VM, whose
-- memory would otherwise be mutated in place
runCommand :: (App m, Debuggable t) => Fetch.Fetcher t m -> Command -> Session t -> m (Session t)
runCommand fetcher cmd s0 = do
  vm <- liftIO $ stToIO $ cloneVM s0.vm
  runCommand' fetcher cmd s0 { vm = vm, note = "", out = Nothing }

runCommand' :: (App m, Debuggable t) => Fetch.Fetcher t m -> Command -> Session t -> m (Session t)
runCommand' fetcher cmd s = case cmd of
  Step n -> do
    (s', why) <- runUntil fetcher n (const False) s
    pure $ case why of
      StopLimit -> s'
      _ -> stopping (s', why)
  Next -> do
    let here = srcKey s
    stopping <$> runUntil fetcher s.stepLimit (\s' -> isJust (srcKey s') && srcKey s' /= here) s
  Over -> do
    let here = srcKey s
        depth = length s.vm.frames
    stopping <$> runUntil fetcher s.stepLimit (\s' -> isJust (srcKey s') && srcKey s' /= here
                                                     && length s'.vm.frames <= depth && not (boring s')) s
  Out -> do
    let depth = length s.vm.frames
    if depth == 0
      then stopping <$> runUntil fetcher s.stepLimit (const False) s
      else stopping <$> runUntil fetcher s.stepLimit (\s' -> length s'.vm.frames < depth) s
  Continue -> stopping <$> runUntil fetcher s.stepLimit (const False) s
  Back n
    | s.curStep == 0 -> pure s { note = "Already at the first step." }
    | otherwise -> do
        s' <- backTo fetcher (max 0 (s.curStep - n)) s
        pure s' { note = "Stepped back to step " <> tshow s'.curStep <> "." }
  BackLine
    | s.curStep == 0 -> pure s { note = "Already at the first step." }
    | otherwise -> do
        let here = srcKey s
            go t | t <= 0 = backTo fetcher 0 s
                 | otherwise = do
                     s' <- backTo fetcher t s
                     if isJust (srcKey s') && srcKey s' /= here then pure s' else go (t - 1)
        s' <- go (s.curStep - 1)
        pure s' { note = "Stepped back to step " <> tshow s'.curStep <> "." }
  Restart -> do
    s' <- backTo fetcher 0 s
    pure s' { note = "Restarted." }
  Choose arg -> choose fetcher arg s
  Break bp -> pure s { bps = s.bps <> [bp]
                     , note = "Breakpoint " <> tshow (length s.bps) <> " set: " <> showBreak bp }
  Delete Nothing -> pure s { bps = [], note = "All breakpoints deleted." }
  Delete (Just i)
    | i >= 0 && i < length s.bps ->
        pure s { bps = take i s.bps <> drop (i + 1) s.bps
               , note = "Breakpoint " <> tshow i <> " deleted." }
    | otherwise -> pure s { note = "No breakpoint " <> tshow i <> "." }
  ListBreakpoints -> pure s { out = Just $ if null s.bps then "No breakpoints."
                              else T.unlines [tshow i <> ": " <> showBreak b | (i, b) <- zip [0 :: Int ..] s.bps] }
  ShowMemory off len -> do
    t <- liftIO $ memoryText (shown s) s.vm off (min len maxMemoryDump)
    pure s { out = Just t }
  ShowStorage -> pure s { out = Just $ case currentContract s.vm of
                        Just c -> formatExpr (shown s c.storage)
                        Nothing -> "No contract." }
  ShowCalldata -> pure s { out = Just (bufText (shown s s.vm.state.calldata)) }
  ShowTrace -> pure s { out = Just (traceText s.dapp s.vm) }
  ShowPathConds -> pure s { out = Just $ if null s.vm.constraints then "No path conditions."
                        else T.unlines (map (formatProp . (if s.simp then Expr.simplifyProp else id)) (reverse s.vm.constraints)) }
  ShowStats -> pure s { out = Just (renderStats (sessionStats s)) }
  SetSimplify b -> pure s { simp = b, note = "Expressions are shown " <> (if b then "simplified." else "as they are.") }
  SetMerge b -> pure (setMerge b s) { note = if b
    then "Short branches are merged as exploration does: a step may run a whole if/else."
    else "Branches are not merged: every step is one instruction." }
  SetBranches m -> pure s { branchMode = m, note = case m of
    SolverBranches -> "Branches are decided by the solver: only feasible sides are offered."
    ExplorerBranches -> "Branches are decided as exploration does, without the solver: sides that may be infeasible are offered too."
    CheckedBranches -> "Branches are decided as exploration does, and the solver checks every decision: see 'stats'." }
  Help -> pure s { out = Just commandHelp }
  Refresh -> pure s
  where
    stopping (s', why) = s' { note = stopMessage s' why }
    boring s' = case srcPos s'.dapp s'.vm of
      Just (_, _, _, sm) -> maybe True (BS.isPrefixOf "contract ") (srcMapCode s'.dapp.sources sm)
      Nothing -> True

srcKey :: Session t -> Maybe (Int, Int)
srcKey s = (\(fid, _, l, _) -> (fid, l)) <$> srcPos s.dapp s.vm

parseCommand :: Text -> Either Text Command
parseCommand line = case T.words (T.strip line) of
  [] -> Right Refresh
  (c : args) -> case (T.toLower c, args) of
    (w, []) | w `elem` ["s", "step"] -> Right (Step 1)
    (w, [n]) | w `elem` ["s", "step"] -> Step <$> num n
    (w, []) | w `elem` ["n", "next"] -> Right Next
    (w, []) | w `elem` ["o", "over"] -> Right Over
    ("out", []) -> Right Out
    (w, []) | w `elem` ["c", "continue", "e", "end"] -> Right Continue
    (w, []) | w `elem` ["b", "back"] -> Right (Back 1)
    (w, [n]) | w `elem` ["b", "back"] -> Back <$> num n
    (w, []) | w `elem` ["bl", "back-line"] -> Right BackLine
    (w, []) | w `elem` ["r", "restart"] -> Right Restart
    (w, [a]) | w `elem` ["branch", "choose"] -> Right (Choose a)
    ("break", ["pc", n]) -> Break . BreakPc <$> num n
    ("break", ["op", o]) -> Right (Break (BreakOp (T.toUpper o)))
    ("break", ["line", l]) -> case T.breakOnEnd ":" l of
      ("", n) -> Break . BreakLine Nothing <$> num n
      (f, n) -> Break . BreakLine (Just (T.unpack (T.dropEnd 1 f))) <$> num n
    ("delete", ["all"]) -> Right (Delete Nothing)
    ("delete", [n]) -> Delete . Just <$> num n
    (w, []) | w `elem` ["breakpoints", "bps"] -> Right ListBreakpoints
    (w, [o, l]) | w `elem` ["memory", "mem"] -> ShowMemory <$> num o <*> num l
    (w, [o]) | w `elem` ["memory", "mem"] -> (`ShowMemory` 256) <$> num o
    (w, []) | w `elem` ["memory", "mem"] -> Right (ShowMemory 0 256)
    ("storage", []) -> Right ShowStorage
    ("calldata", []) -> Right ShowCalldata
    ("trace", []) -> Right ShowTrace
    ("stats", []) -> Right ShowStats
    ("simplify", ["on"]) -> Right (SetSimplify True)
    ("simplify", ["off"]) -> Right (SetSimplify False)
    ("branches", ["solver"]) -> Right (SetBranches SolverBranches)
    ("branches", ["explorer"]) -> Right (SetBranches ExplorerBranches)
    ("branches", ["checked"]) -> Right (SetBranches CheckedBranches)
    ("merge", ["on"]) -> Right (SetMerge True)
    ("merge", ["off"]) -> Right (SetMerge False)
    (w, []) | w `elem` ["pathconds", "pc", "constraints"] -> Right ShowPathConds
    (w, []) | w `elem` ["h", "help", "?"] -> Right Help
    (w, []) | w `elem` ["show", "state"] -> Right Refresh
    _ -> Left $ "Unknown command '" <> T.strip line <> "'. Type 'help' for commands."
  where
    num :: Text -> Either Text Int
    num t = case T.stripPrefix "0x" t of
      Just h | [(v, "")] <- reads ("0x" <> T.unpack h) -> inRange v
      _ | T.all isDigit t, not (T.null t) -> inRange (read (T.unpack t))
      _ -> Left $ "Not a number: " <> t
      where
        -- parsed as Integer, as Int would silently wrap around
        inRange :: Integer -> Either Text Int
        inRange v
          | v <= 1000000000000 = Right (fromInteger v)
          | otherwise = Left $ "Number too large: " <> t

commandHelp :: Text
commandHelp = T.unlines
  [ "step [n]         (s)  execute n opcodes (default 1)"
  , "next             (n)  run to the next source line, entering calls"
  , "over             (o)  run to the next source line without entering calls"
  , "out                   run until the current call frame returns"
  , "continue         (c)  run until a breakpoint, a symbolic branch, or the end"
  , "back [n]         (b)  step back n opcodes (default 1)"
  , "back-line        (bl) step back to the previous source line"
  , "restart          (r)  go back to the first step"
  , "branch true|false     pick a side of a pending symbolic branch"
  , "branch <i>            pick the i-th value of a pending multi-way branch"
  , "break pc <n>          break when pc is n (decimal or 0x-hex)"
  , "break op <NAME>       break before an opcode, e.g. 'break op SSTORE'"
  , "break line [file:]<n> break at a source line"
  , "breakpoints           list breakpoints"
  , "delete <i>|all        delete breakpoint(s)"
  , "memory [off] [len]    hexdump of memory (default 0 256, at most 65536 bytes)"
  , "storage               storage of the current contract"
  , "calldata              calldata of the current frame"
  , "trace                 call trace so far"
  , "pathconds             path conditions so far"
  , "stats                 what the session has done: commands, opcodes, solver queries, branches"
  , "simplify on|off       show expressions simplified (default) or as they are"
  , "branches solver|explorer|checked  decide symbolic branches with the solver (default), or as"
  , "                      exploration does: without the solver, offering sides that may be"
  , "                      infeasible. 'checked' also has the solver confirm each decision"
  , "merge on|off          merge short branches as exploration does (default off): a step"
  , "                      may then run a whole if/else"
  , "show                  just show the current state"
  , "quit             (q)  stop the debugger (hevm-debug; 'detach' leaves it running)"
  ]

showBreak :: Breakpoint -> Text
showBreak = \case
  BreakPc pc -> "pc " <> hex pc
  BreakOp op -> "op " <> op
  BreakLine f l -> "line " <> maybe "" (\x -> T.pack x <> ":") f <> tshow l

-- * Views

data CodeLine = CodeLine { pc :: Int, op :: Text, current :: Bool }
  deriving (Show, Generic, ToJSON)

data SourceLine = SourceLine { line :: Int, text :: Text, current :: Bool }
  deriving (Show, Generic, ToJSON)

data SourceView = SourceView { file :: Text, line :: Int, lines :: [SourceLine] }
  deriving (Show, Generic, ToJSON)

data BranchView = BranchView { condition :: Maybe Text, options :: [Text] }
  deriving (Show, Generic, ToJSON)

data View = View
  { mode           :: Text
  , step           :: Int
  , status         :: Text
  , result         :: Maybe Text
  , pc             :: Int
  , op             :: Text
  , contract       :: Text
  , codeContract   :: Text
  , depth          :: Int
  , gas            :: Maybe Word64
  , code           :: [CodeLine]
  , stack          :: [Text]
  , memorySize     :: Word64
  , memory         :: Text
  , source         :: Maybe SourceView
  , pathConditions :: Int
  , branch         :: Maybe BranchView
  , choices        :: [Text]
  , breakpoints    :: [Text]
  , message        :: Text
  , output         :: Maybe Text
  , branchMode     :: Text
  , simplified     :: Bool
  , warnings       :: [Text]
  , merging        :: Bool
  }
  deriving (Show, Generic, ToJSON)

mkView :: Debuggable t => Session t -> IO View
mkView s = do
  mem <- memoryText (shown s) vm 0 (min 128 (unsafeInto vm.state.memorySize))
  pure View
    { mode = modeName vm
    , step = s.curStep
    , status = if isHalted s then "halted" else if isJust s.pending then "branch" else "running"
    , result = if isHalted s then Just (resultText vm) else Nothing
    , pc = vm.state.pc
    , op = T.pack (opNameAt vm.state.code vm.state.pc)
    , contract = formatExpr vm.state.contract
    , codeContract = formatExpr vm.state.codeContract
    , depth = length vm.frames
    , gas = gasLeft vm
    , code = codeWindow vm.state.code vm.state.pc
    , stack = map (clip 300 . formatWord . shown s) vm.state.stack
    , memorySize = vm.state.memorySize
    , memory = mem
    , source = sourceView s.dapp vm
    , pathConditions = length vm.constraints
    , branch = (\(Pending c ctx) -> BranchView (clip 1000 . formatExpr . shown s <$> c) (branchOptions ctx)) <$> s.pending
    , branchMode = case s.branchMode of
        SolverBranches -> "solver"
        ExplorerBranches -> "explorer"
        CheckedBranches -> "checked"
    , simplified = s.simp
    , warnings = s.warnings
    , merging = s.merge
    , choices = [ "step " <> tshow st <> ": " <> clip 100 d | (st, d) <- reverse s.taken ]
    , breakpoints = map showBreak s.bps
    , message = s.note
    , output = s.out
    }
  where
    vm = s.vm
    branchOptions = \case
      PleaseRunBoth _ -> ["true", "false"]
      PleaseRunAll vals _ -> map (clip 200 . formatExpr) vals

renderView :: View -> Text
renderView v = T.unlines $
  [ "== step " <> tshow v.step <> " | " <> v.mode <> " | " <> v.status
    <> " | pc " <> hex v.pc <> " " <> v.op <> " | depth " <> tshow v.depth
    <> maybe "" (\g -> " | gas " <> tshow g) v.gas
    <> (if v.branchMode == "solver" then "" else " | branches " <> v.branchMode)
    <> (if v.simplified then "" else " | not simplified")
    <> (if v.merging then " | merging" else "")
  , "contract " <> v.contract <> (if v.codeContract /= v.contract then " (code of " <> v.codeContract <> ")" else "")
  , ""
  , "-- code"
  ] <> [ (if c.current then " > " else "   ") <> hex c.pc <> "  " <> c.op | c <- v.code ]
  <> [ "", "-- stack (top first)" ]
  <> (if null v.stack then ["   <empty>"] else [ "   " <> tshow i <> ": " <> e | (i, e) <- zip [0 :: Int ..] v.stack ])
  <> maybe [] (\sv -> ["", "-- source " <> sv.file <> ":" <> tshow sv.line]
                      <> [ (if l.current then " > " else "   ") <> T.justifyRight 5 ' ' (tshow l.line) <> " | " <> l.text | l <- sv.lines ]) v.source
  <> [ "", "-- memory (" <> tshow v.memorySize <> " bytes)" ]
  <> (if v.memorySize == 0 then [] else T.lines v.memory)
  <> [ "\npath conditions: " <> tshow v.pathConditions <> " (see 'pathconds')" | v.pathConditions > 0 ]
  <> [ "branches taken: " <> T.intercalate ", " v.choices | not (null v.choices) ]
  <> [ "breakpoints: " <> T.intercalate ", " [ tshow i <> ": " <> b | (i, b) <- zip [0 :: Int ..] v.breakpoints ] | not (null v.breakpoints) ]
  <> maybe [] (\b -> [ "", "-- symbolic branch pending" ]
                     <> maybe [] (\c -> ["   condition: " <> c]) b.condition
                     <> [ "   options: " <> T.intercalate " | " [ tshow i <> ": " <> o | (i, o) <- zip [0 :: Int ..] b.options ] ]) v.branch
  <> (if null v.warnings then [] else ["", "-- warnings"] <> map ("   " <>) v.warnings)
  <> maybe [] (\r -> ["", "result: " <> r]) v.result
  <> maybe [] (\o -> ["", o]) v.output
  <> [ "\n" <> v.message | not (T.null v.message) ]

-- * Helpers

srcPos :: DappInfo -> VM t -> Maybe (Int, FilePath, Int, SrcMap)
srcPos dapp vm = do
  c <- currentContract vm
  i <- c.opIxMap VS.!? vm.state.pc
  sm <- srcMap dapp c i
  (path, contents) <- Map.lookup sm.file dapp.sources.files
  pure (sm.file, path, BS.count 0xa (BS.take sm.offset contents) + 1, sm)

sourceView :: DappInfo -> VM t -> Maybe SourceView
sourceView dapp vm = do
  (fid, path, line, _) <- srcPos dapp vm
  ls <- Map.lookup fid dapp.sources.lines
  let from = max 1 (line - 4)
      to = min (V.length ls) (line + 4)
  pure $ SourceView (T.pack path) line
    [ SourceLine n (decode (ls V.! (n - 1))) (n == line) | n <- [from .. to] ]
  where decode = T.stripEnd . decodeUtf8With lenientDecode

codeBytes :: ContractCode -> [Maybe Word8]
codeBytes = \case
  UnknownCode _ -> []
  InitCode bs _ -> map Just (BS.unpack bs)
  RuntimeCode (ConcreteRuntimeCode bs) -> map Just (BS.unpack bs)
  RuntimeCode (SymbolicRuntimeCode ops) -> map maybeLitByteSimp (V.toList ops)

disassemble :: ContractCode -> [(Int, Text)]
disassemble = go 0 . codeBytes
  where
    go _ [] = []
    go i (Nothing : rest) = (i, "<symbolic>") : go (i + 1) rest
    go i (Just b : rest) =
      let n = opSize b - 1
          imm = take n rest
          txt = T.pack (opName b) <> if n > 0 then " 0x" <> T.pack (concatMap (maybe "??" byteHex) imm) else ""
      in (i, txt) : go (i + 1 + n) (drop n rest)

codeWindow :: ContractCode -> Int -> [CodeLine]
codeWindow code pc =
  let ops = disassemble code
      (before, after) = span ((< pc) . fst) ops
  in [ CodeLine i o (i == pc) | (i, o) <- reverse (take 8 (reverse before)) <> take 12 after ]

opNameAt :: ContractCode -> Int -> String
opNameAt code pc = case drop pc (codeBytes code) of
  Just b : _ -> opName b
  Nothing : _ -> "<symbolic>"
  [] -> "STOP"

opName :: Word8 -> String
opName b = case intToOpName (fromIntegral b) of
  "" -> "UNKNOWN_0x" <> byteHex b
  n -> n

byteHex :: Word8 -> String
byteHex b = let h = showHex b "" in if length h < 2 then '0' : h else h

formatWord :: Expr EWord -> Text
formatWord e = case maybeLitWordSimp e of
  Just w -> T.pack ("0x" <> showHex w "") <> (if w < 0x10000 && w > 9 then " (" <> tshow (into w :: Integer) <> ")" else "")
  Nothing -> formatExpr e

memoryText :: (Expr Buf -> Expr Buf) -> VM t -> Int -> Int -> IO Text
memoryText display vm off len = case vm.state.memory of
  ConcreteMemory m -> do
    let avail = max 0 (min len (VSM.length m - off))
    bytes <- if avail <= 0 || off < 0 then pure VS.empty
             else stToIO $ VS.freeze (VSM.slice off avail m)
    let bs = BS.pack (VS.toList bytes) <> BS.replicate (max 0 len - avail) 0
    pure $ T.pack (prettyHexAt off bs)
  SymbolicMemory buf -> pure $ clip 4000 (formatExpr (display buf))

prettyHexAt :: Int -> BS.ByteString -> String
prettyHexAt off bs
  | off == 0 = prettyHex bs
  | otherwise = "offset " <> "0x" <> showHex off "" <> ":\n" <> prettyHex bs

bufText :: Expr Buf -> Text
bufText = \case
  ConcreteBuf bs -> T.pack (prettyHex bs)
  b -> clip 4000 (formatExpr b)

traceText :: DappInfo -> VM t -> Text
traceText dapp vm =
  T.pack $ concatMap (showTree . fmap (T.unpack . renderStrict . layoutPretty (LayoutOptions Unbounded) . unAnnotate)) (traceDocForest dapp vm)

resultText :: VM t -> Text
resultText vm = case vm.result of
  Just (VMSuccess buf) -> "success, returned " <> clip 500 (retText buf)
  Just (VMFailure e) -> "failure: " <> clip 500 (T.pack (show e))
  Just (Unfinished p) -> "unfinished: " <> clip 500 (T.pack (show p))
  Just (HandleEffect _) -> "waiting on an effect"
  Nothing -> "running"
  where
    retText = \case
      ConcreteBuf bs -> if BS.null bs then "nothing" else "0x" <> T.pack (concatMap byteHex (BS.unpack bs))
      b -> formatExpr b

hex :: Int -> Text
hex i = T.pack ("0x" <> showHex i "")

tshow :: Show a => a -> Text
tshow = T.pack . show

clip :: Int -> Text -> Text
clip n t
  | T.length t <= n = t
  | otherwise = T.take n t <> "… (" <> tshow (T.length t) <> " chars)"
