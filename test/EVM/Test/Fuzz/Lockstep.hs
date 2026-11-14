{-|
Module      : EVM.Test.Fuzz.Lockstep
Description : Concrete and symbolic debugger sessions stepped side by side

After every step, the symbolic state with the concrete inputs substituted must
be the concrete one. Forward jumps are merged on the side and compared where
the concrete run reaches the jump target. Also steps along solver-chosen paths,
and checks a concrete session moving back and forth against geth.
-}
module EVM.Test.Fuzz.Lockstep
  ( DebuggerVsGeth(..), Deferred(..), Lockstep(..), debuggerVsGeth, lockstepCase, modelGuided
  ) where

import Control.Monad (foldM, forM, void, when, zipWithM)
import Control.Monad.IO.Unlift
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (execStateT)
import Data.Aeson qualified as JSON
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Either (isLeft)
import Data.IORef (newIORef, readIORef, atomicModifyIORef')
import Data.List (isInfixOf, tails)
import Data.Map.Strict qualified as Map
import Data.Monoid (Any(..))
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Tree (Forest, flatten, rootLabel, subForest)
import Data.Vector.Storable qualified as VS
import Optics.Core hiding (pre, elements)
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Witch (unsafeInto)
import EVM (exec1, traceForest)
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Op (intToOpName)
import EVM.Progress qualified as Progress
import EVM.SMT qualified as SMT
import EVM.Solvers
import EVM.Traversals (foldProp)
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Dapp (emptyDapp)
import EVM.Debugger (Session, newSession, setSnapshotInterval, sessionWarnings, runCommand, Command(..), mkView, View(..), BranchView(..), sessionVM, sessionStep, isHalted, hasPendingBranch, BranchMode(..), setBranchMode, sessionStats, StatsView(..), Stats(..))
import EVM.Tracing (vmTraceStep, VMTraceStep(..))
import EVM.Test.Fuzz.Program
import EVM.Test.Fuzz.Geth
import EVM.Test.Fuzz.Hevm
import EVM.Test.Fuzz.Case
import EVM.Test.Fuzz.Check

-- * Lockstep

-- | What a lockstep run covered, for the coverage tables
data Lockstep = Lockstep
  { stopped  :: String
  , steps    :: Int
  , compared :: Int -- ^ stack words, memory and storage that concretized and matched
  , opaque   :: Int -- ^ stack words that stayed symbolic after substituting the inputs
  , branches :: Int -- ^ branches offered, and taken the concrete run's way
  , retries  :: Int -- ^ sides tried that the concrete run did not take
  , trail    :: [String] -- ^ the latest steps, newest first, for failure reports
  , static   :: Int -- ^ branches decided without the solver
  , ended    :: Maybe (Int, Int, String) -- ^ pc, depth and kind of result, when both runs halted
  , ops      :: Set String -- ^ the opcodes stepped and compared after
  , deferred :: Maybe Deferred
  , deferredChecked :: Int
  }

emptyLockstep :: Lockstep
emptyLockstep = Lockstep
  { stopped = "", steps = 0, compared = 0, opaque = 0, branches = 0, retries = 0, trail = []
  , static = 0, ended = Nothing, ops = mempty, deferred = Nothing, deferredChecked = 0 }

-- | A symbolic state ahead of the concrete run, e.g. after merging a forward
-- jump, compared when the concrete run reaches its pc at its depth, which it
-- must by step 'deadline'
data Deferred = Deferred
  { what     :: String
  , pc       :: Int
  , depth    :: Int
  , deadline :: Int
  , vm       :: VM Symbolic
  }

maxLockstepSteps :: Int
maxLockstepSteps = 2000

-- | Steps a concrete and a symbolic debugging session of the case side by side,
-- taking the concrete run's side at every symbolic branch. After every step the
-- symbolic state, with the concrete inputs substituted, must be the concrete one.
-- The sessions do not merge forward jumps, so at a symbolic JUMPI the merged
-- state is computed on the side, and compared when the concrete run reaches the
-- jump target.
lockstepCase :: App m => SolverGroup -> BranchMode -> TestCase -> m (Either String Lockstep)
lockstepCase solvers mode c = Progress.withProgressLogFromEnv "lockstep" $ do
  sc0 <- liftIO $ stToIO (concreteTestVm c) >>= newSession emptyDapp
  ss0 <- liftIO $ setBranchMode mode <$> (stToIO (symbolicTestVm c) >>= newSession emptyDapp)
  r <- go sc0 ss0 emptyLockstep Nothing
  Progress.emit "lockstep-end" $ case r of
    Left err -> ["failure" JSON..= T.pack err]
    Right l -> ["stopped" JSON..= T.pack l.stopped, "steps" JSON..= l.steps, "compared" JSON..= l.compared, "branches" JSON..= l.branches]
  pure r
  where
    fetcher :: Fetch.Fetcher t m
    fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
    go :: App m => Session Concrete -> Session Symbolic -> Lockstep -> Maybe String -> m (Either String Lockstep)
    go sc ss acc prevOp = do
      let vc = sessionVM sc
          vs = sessionVM ss
          where_ = "after " <> show acc.steps <> " steps, at pc " <> show vc.state.pc <> maybe "" (" after " <>) prevOp <> ": "
          stopWith why = pure (Right acc { stopped = why })
          mismatch = mismatchAt vc
          mismatchAt now msg
            | gasDependentRun now = stopWith "gas-dependent"
            | otherwise = pure (Left (where_ <> msg <> "\nlast steps, oldest first:\n" <> unlines (reverse acc.trail)))
      cmp <- liftIO $ compareStates c prevOp vc vs
      deferredCmp <- case acc.deferred of
        Just d | vc.state.pc == d.pc, length vc.frames == d.depth -> Just <$> liftIO (compareStates c Nothing vc d.vm)
        _ -> pure Nothing
      case cmp of
        _ | Just (Unfinished p) <- vs.result -> stopWith ("symbolic unfinished: " <> unfinishedReason p)
        Left msg -> mismatch msg
        _ | Just d <- acc.deferred, Just (Left msg) <- deferredCmp -> mismatch ("against " <> d.what <> ", " <> msg)
          | Just d <- acc.deferred, isNothing deferredCmp, acc.steps > d.deadline || isHalted sc ->
              mismatch ("the concrete run did not reach the pc of " <> d.what)
        Right (n, o) -> do
          let acc' = acc { compared = acc.compared + n, opaque = acc.opaque + o
                         , deferredChecked = acc.deferredChecked + length deferredCmp
                         , deferred = if isJust deferredCmp then Nothing else acc.deferred }
          case (isHalted sc, isHalted ss) of
            (True, True) -> either mismatch (const (pure (Right acc' { stopped = "halted", ended = Just (endOf vs) }))) (compareEnds c vc vs)
            (True, False) -> mismatch $ "only the concrete run halted: " <> show vc.result
            (False, True) -> mismatch $ "only the symbolic run halted: " <> show vs.result
            _ | acc.steps >= maxLockstepSteps -> stopWith "step limit"
              | otherwise -> do
                  let opName' = intToOpName (fromIntegral (getOpW8' vc))
                  deferred' <- if opName' == "JUMPI" && isNothing acc'.deferred then mergeAt acc'.steps vs else pure acc'.deferred
                  sc' <- runCommand fetcher (Step 1) sc >>= settle (4 :: Int) vc
                  ss1 <- runCommand fetcher (Step 1) ss
                  picked <- pickSide vs (sessionVM sc') ss1
                  case picked of
                    -- a call to an address that stays symbolic goes to unknown code, which is
                    -- over-approximated rather than run
                    Left _ | opName' `elem` ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"]
                           , target : _ <- drop 1 vs.state.stack
                           , Nothing <- Expr.maybeLitWordSimp (Expr.simplify target)
                           , length (sessionVM sc').frames > length vs.frames -> stopWith "call to a symbolic address"
                    Left msg -> mismatchAt (sessionVM sc') msg
                    Right (ss'', _, _) | not (null (sessionWarnings ss'')) ->
                      pure $ Left $ where_ <> "the solver contradicts a branch decided by simplification:\n"
                        <> unlines (map T.unpack (sessionWarnings ss''))
                    Right (ss'', tried, took) -> case concretizeProps c c.inputs (sessionVM ss'').constraints of
                      Just False -> mismatch $ "the concrete inputs violate the path conditions after " <> opName'
                        <> ": " <> show (sessionVM ss'').constraints
                      _ -> do
                        let vs' = sessionVM ss''
                            entry = "  " <> show acc.steps <> ": pc " <> show vc.state.pc <> " " <> opName'
                              <> " depth " <> show (length vc.frames)
                              <> (if took > 0 then ", took the branch side that leads to pc " <> show vs'.state.pc
                                                   <> " after trying " <> show tried <> " other sides" else "")
                        Progress.emit "lockstep-step" $
                          [ "step" JSON..= acc.steps, "pc" JSON..= vc.state.pc, "op" JSON..= T.pack opName', "depth" JSON..= length vc.frames
                          , "compared" JSON..= n, "symbolic" JSON..= o ]
                          <> [ "branchesTaken" JSON..= took | took > 0 ] <> [ "sidesRetried" JSON..= tried | tried > 0 ]
                        let counters = (sessionStats ss'').counters
                        go sc' ss'' acc' { steps = acc.steps + 1, branches = acc.branches + took, retries = acc.retries + tried
                                         , ops = Set.insert opName' acc.ops
                                         , trail = take 30 (entry : acc.trail)
                                         , static = counters.staticDecisions, deferred = deferred' } (Just opName')
    mergeAt :: App m => Int -> VM Symbolic -> m (Maybe Deferred)
    mergeAt step vs = case (vs.state.stack, vs.state.memory) of
      (Lit t : cond : _, SymbolicMemory _)
        | t < 0x10000, unsafeInto t > vs.state.pc
        , isNothing (Expr.maybeLitWordSimp (Expr.simplify cond)) -> do
            conf <- readConfig
            vm <- liftIO $ stToIO $ execStateT (exec1 conf) vs
            pure $ if isNothing vm.result && vm.state.pc == unsafeInto t
              then Just Deferred { what = "the merged state of the latest JUMPI", pc = vm.state.pc, depth = length vs.frames
                                 , deadline = step + conf.mergeMaxBudget + 1, vm }
              else Nothing
      _ -> pure Nothing
    -- an instruction may take several steps, e.g. when it is re-executed after
    -- a query, but always ends at another pc or depth, or halts
    midInstruction :: VM t -> VM t -> Bool
    midInstruction before now = isNothing now.result && now.state.pc == before.state.pc
                                  && length now.frames == length before.frames
    settle :: App m => Int -> VM Concrete -> Session Concrete -> m (Session Concrete)
    settle n before s
      | n > 0, midInstruction before (sessionVM s) = runCommand fetcher (Step 1) s >>= settle (n - 1) before
      | otherwise = pure s
    -- The branch sides and further steps that reach the concrete state: same pc
    -- and depth, and path conditions the inputs satisfy. One instruction may
    -- branch several times, e.g. a symbolic jump target is first checked to be
    -- in range, then resolved.
    pickSide :: App m => VM Symbolic -> VM Concrete -> Session Symbolic -> m (Either String (Session Symbolic, Int, Int))
    pickSide start vc ss0 = do
      (found, tried) <- search ss0 (6 :: Int) []
      pure $ maybe (Left (failure tried)) Right found
      where
        failure tried = "no sides of the branches reach the concrete pc " <> show vc.state.pc
          <> " at depth " <> show (length vc.frames) <> ", the sides lead to:\n" <> unlines (reverse tried)
        pathOk s = concretizeProps c c.inputs (sessionVM s).constraints /= Just False
        -- or the side gives up on this path: incomplete, but not wrong
        unfinished s = case (sessionVM s).result of
          Just (Unfinished _) -> True
          _ -> False
        reached s = (sessionVM s).state.pc == vc.state.pc && length (sessionVM s).frames == length vc.frames
        describe path s = "  " <> path <> ": pc " <> show (sessionVM s).state.pc <> ", depth " <> show (length (sessionVM s).frames)
          <> ", result " <> show (sessionVM s).result
          <> ", inputs satisfy the path conditions: " <> show (concretizeProps c c.inputs (sessionVM s).constraints)
          <> "\n    violated: " <> show [ p | p <- (sessionVM s).constraints, concretizeProps c c.inputs [p] == Just False ]
        search s fuel tried
          | fuel == 0 = pure (Nothing, describe "out of fuel" s : tried)
          | hasPendingBranch s = do
              v <- liftIO $ mkView s
              let opts = maybe [] (.options) v.branch
                  sides = if opts == ["false", "true"] then ["true", "false"] else map (T.pack . show) [0 .. length opts - 1]
                  tryEach _ [] tr = pure (Nothing, tr)
                  tryEach n (side : rest) tr = do
                    s1 <- runCommand fetcher (Choose side) s
                    (found, tr') <- search s1 (fuel - 1) tr
                    case found of
                      Just (s2, t, took) -> pure (Just (s2, t + n, took + 1), tr')
                      Nothing -> tryEach (n + 1) rest (describe (show (opts, side)) s1 : tr')
              tryEach 0 sides tried
          | not (pathOk s) = pure (Nothing, describe "the inputs violate the path conditions" s : tried)
          | unfinished s || reached s = pure (Just (s, 0, 0), tried)
          | midInstruction start (sessionVM s) = runCommand fetcher (Step 1) s >>= \s' -> search s' (fuel - 1) tried
          | otherwise = pure (Nothing, describe "elsewhere" s : tried)
    getOpW8' vm = case vm.state.code of
      RuntimeCode (ConcreteRuntimeCode bs) | vm.state.pc < BS.length bs -> BS.index bs vm.state.pc
      InitCode bs _ | vm.state.pc < BS.length bs -> BS.index bs vm.state.pc
      _ -> 0

-- | Why a symbolic run gave up, briefly
unfinishedReason :: PartialExec -> String
unfinishedReason = \case
  UnexpectedSymbolicArg { opcode, msg } -> opcode <> ": " <> msg
  p -> takeWhile (/= ' ') (show p)

-- | Where a run halted, and how
endOf :: VM t -> (Int, Int, String)
endOf vm = (vm.state.pc, length vm.frames, case vm.result of
  Just (VMSuccess _) -> "success"
  Just (VMFailure (Revert _)) -> "revert"
  Just (VMFailure e) -> hevmErrorKind e
  r -> show r)

-- | Follows a random path of a symbolic session, picking a random feasible side
-- at every branch, until it halts
randomPath :: App m => SolverGroup -> TestCase -> [Int] -> m (Session Symbolic)
randomPath solvers c picks0 = do
  s0 <- liftIO $ stToIO (symbolicTestVm c) >>= newSession emptyDapp
  go s0 (cycle (0 : picks0)) (0 :: Int)
  where
    fetcher :: Fetch.Fetcher Symbolic m
    fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
    go s picks n
      | isHalted s || n >= maxLockstepSteps = pure s
      | hasPendingBranch s = do
          v <- liftIO $ mkView s
          let opts = maybe [] (.options) v.branch
              pick = fromMaybe 0 (headMay picks)
              side = if opts == ["false", "true"] then (["true", "false"] !! (pick `mod` 2))
                     else T.pack (show (pick `mod` max 1 (length opts)))
          s' <- runCommand fetcher (Choose side) s
          go s' (drop 1 picks) n
      | otherwise = runCommand fetcher (Step 1) s >>= \s' -> go s' picks (n + 1)

-- | Gas is not tracked symbolically, so after it ran out anywhere the runs may differ
gasDependentRun :: VM Concrete -> Bool
gasDependentRun vm = any isGas (concatMap flatten (traceForest vm)) || resultIsGas
  where
    isGas t = case t.tracedata of
      ErrorTrace e -> gasError e
      _ -> False
    resultIsGas = case vm.result of
      Just (VMFailure e) -> gasError e
      _ -> False
    -- memory this large costs more gas than any run has
    gasError e = "gas" `isInfixOf` hevmErrorKind e || case e of
      IllegalOverflow -> True
      _ -> False

-- | Ops that change balances, nonces, storage or code
accountOps :: [String]
accountOps = ["SSTORE", "TSTORE", "SELFDESTRUCT"] <> callOps

memWriters, callOps :: [String]
memWriters = ["MSTORE", "MSTORE8", "MCOPY", "CALLDATACOPY", "CODECOPY", "RETURNDATACOPY", "EXTCODECOPY"] <> callOps
callOps = ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "CREATE", "CREATE2"]

-- | Compares where the runs are, their stacks, and what the previous op may have
-- changed. Returns how many values matched and how many stayed symbolic.
-- | 'compareStates'' on the symbolic state as it is, and simplified: the
-- simplifier must not change what any value is
compareStates :: TestCase -> Maybe String -> VM Concrete -> VM Symbolic -> IO (Either String (Int, Int))
compareStates c prevOp vc vs = compareStates' id c prevOp vc vs >>= \case
  Left err -> pure (Left err)
  Right counts -> compareStates' Expr.simplify c prevOp vc vs <&> \case
    Left err -> Left ("only after Expr.simplify, " <> err)
    Right _ -> Right counts

compareStates' :: (forall a. Expr a -> Expr a) -> TestCase -> Maybe String -> VM Concrete -> VM Symbolic -> IO (Either String (Int, Int))
compareStates' pre c prevOp vc vs
  | vc.state.pc /= vs.state.pc = pure $ Left $ "pc differs: symbolic " <> show vs.state.pc
  | length vc.frames /= length vs.frames = pure $ Left $ "depth differs: concrete " <> show (length vc.frames) <> ", symbolic " <> show (length vs.frames)
  | vc.state.codeContract /= vs.state.codeContract = pure $ Left $ "code address differs: " <> show (vc.state.codeContract, vs.state.codeContract)
  | length vc.state.stack /= length vs.state.stack = pure $ Left $ "stack heights differ: " <> show (length vc.state.stack, length vs.state.stack)
  | otherwise = do
      let words' = zip3 [0 :: Int ..] vc.state.stack (map (concretize c c.inputs . pre) vs.state.stack)
          badWords = [ (i, a, b) | (i, a@(Lit _), b@(Lit _)) <- words', a /= b ]
          nWords = length [ () | (_, Lit _, Lit _) <- words' ]
      mem <- if maybe True (`elem` memWriters) prevOp then compareMemory pre c vc vs else pure (Right 0)
      let ret = if maybe False (`elem` callOps) prevOp then compareBufs "return data" c vc.state.returndata (pre vs.state.returndata) else Right 0
          store = if maybe False (`elem` accountOps) prevOp then compareStorage pre c vc vs else Right 0
          traces = compareCallTraces pre c vc vs
      pure $ case badWords of
        (i, a, b) : _ -> Left $ "stack word " <> show i <> " differs: concrete " <> show a <> ", symbolic " <> show b
          <> "\nsymbolic, before substituting: " <> show (pre (vs.state.stack !! i))
        [] -> (\m r st tr -> (nWords + m + r + st + tr, length words' - nWords)) <$> mem <*> ret <*> store <*> traces

-- | The traces, node by node, where the symbolic one is concrete once the inputs are substituted
compareCallTraces :: (forall a. Expr a -> Expr a) -> TestCase -> VM Concrete -> VM Symbolic -> Either String Int
compareCallTraces pre c vc vs
  | length tc /= length ts = Left $ "traces differ in length: concrete " <> show (length tc) <> ", symbolic " <> show (length ts)
      <> "\nconcrete: " <> show (map (kind . snd) tc) <> "\nsymbolic: " <> show (map (kind . snd) ts)
  | otherwise = sum <$> zipWithM node [0 :: Int ..] (zip tc ts)
  where
    tc = nodes 0 (traceForest vc)
    ts = nodes 0 (traceForest vs)
    nodes :: Int -> Forest Trace -> [(Int, Trace)]
    nodes d = concatMap (\t -> (d, t.rootLabel) : nodes (d + 1) t.subForest)
    node i ((dc, a), (ds, b))
      | dc /= ds || kind a /= kind b || a.opIx /= b.opIx =
          Left $ "trace node " <> show i <> " differs: concrete " <> show (dc, a.opIx, kind a) <> ", symbolic " <> show (ds, b.opIx, kind b)
      | otherwise = case same (a.tracedata, b.tracedata) of
          Just False -> Left $ "trace node " <> show i <> " differs: concrete " <> show a.tracedata <> "\nsymbolic " <> show b.tracedata
          Just True -> Right 1
          Nothing -> Right 0
    kind t = case t.tracedata of
      EventTrace {} -> "event"
      FrameTrace (CallContext {}) -> "call"
      FrameTrace (CreationContext {}) -> "create"
      ErrorTrace e -> "error " <> hevmErrorKind e
      EntryTrace e -> "entry " <> T.unpack e
      ReturnTrace {} -> "return"
      ConsoleLog {} -> "console"
    -- Nothing when some part stays symbolic and every concrete part agrees
    same :: (TraceData, TraceData) -> Maybe Bool
    same = \case
      (EventTrace a d ts1, EventTrace a' d' ts2) -> allOf' ([eq a a', eq d d'] <> zipWith eq ts1 ts2)
      (FrameTrace x, FrameTrace y) -> frame x y
      (ReturnTrace d x, ReturnTrace d' y) -> allOf' [eq d d', frame x y]
      (ConsoleLog d, ConsoleLog d') -> eq d d'
      _ -> Just True
    frame (CallContext t ctx o sz _ _ cd _ _) (CallContext t' ctx' o' sz' _ _ cd' _ _) =
      allOf' [eq t t', eq ctx ctx', eq o o', eq sz sz', eq cd cd']
    frame (CreationContext a _ _ _) (CreationContext a' _ _ _) = eq a a'
    frame _ _ = Just False
    allOf' rs
      | Just False `elem` rs = Just False
      | all (== Just True) rs = Just True
      | otherwise = Nothing
    eq :: Expr a -> Expr a -> Maybe Bool
    eq x y = let y' = concretize c c.inputs (pre y) in
      if concrete x && concrete y' then Just (x == y') else Nothing
    concrete :: Expr a -> Bool
    concrete = \case
      Lit _ -> True
      ConcreteBuf _ -> True
      LitAddr _ -> True
      _ -> False

compareMemory :: (forall a. Expr a -> Expr a) -> TestCase -> VM Concrete -> VM Symbolic -> IO (Either String Int)
compareMemory pre c vc vs = do
  mc <- memoryBytes id vc.state.memory
  ms <- memoryBytes pre vs.state.memory
  let size = fromIntegral vc.state.memorySize
      symSize = maybe (Just (fromIntegral vs.state.memorySize)) (fmap fromIntegral . Expr.maybeLitWordSimp . concretize c c.inputs) vs.state.symMemorySize
  pure $ case (mc, ms) of
    _ | Just size /= symSize && isJust symSize -> Left $ "memory sizes differ: concrete " <> show size <> ", symbolic " <> show symSize
    (Just a, Just b) | pad size a /= pad size b ->
      Left $ "memory differs:\nconcrete: " <> bsToHex (pad size a) <> "\nsymbolic: " <> bsToHex (pad size b)
    (Just _, Just _) -> Right 1
    _ -> Right 0
  where
    pad n b = BS.take n (b <> BS.replicate n 0)
    memoryBytes :: (Expr Buf -> Expr Buf) -> Memory -> IO (Maybe ByteString)
    memoryBytes f = \case
      ConcreteMemory m -> Just . BS.pack . VS.toList <$> stToIO (VS.freeze m)
      SymbolicMemory b -> pure $ case concretize c c.inputs (f b) of
        ConcreteBuf bs -> Just bs
        _ -> Nothing

compareBufs :: String -> TestCase -> Expr Buf -> Expr Buf -> Either String Int
compareBufs what c a b = case (concretize c c.inputs a, concretize c c.inputs b) of
  (ConcreteBuf x, ConcreteBuf y) | x /= y -> Left $ what <> " differs: concrete " <> bsToHex x <> ", symbolic " <> bsToHex y
                                 | otherwise -> Right 1
  _ -> Right 0

-- | Balances, nonces, storage, transient storage and code of the accounts both
-- runs have
compareStorage :: (forall a. Expr a -> Expr a) -> TestCase -> VM Concrete -> VM Symbolic -> Either String Int
compareStorage pre c vc vs = sum <$> forM common (\(a, cc, sc) -> do
  let what :: String -> String
      what x = x <> " of " <> show a <> " differs: concrete "
      conc :: Expr b -> Expr b
      conc = concretize c c.inputs . pre
      stores :: String -> Expr Storage -> Expr Storage -> Either String Int
      stores name x y = case (x, conc y) of
        (ConcreteStore m, ConcreteStore m')
          | nonZero m /= nonZero m' -> Left $ what name <> show m <> ", symbolic " <> show m'
          | otherwise -> Right 1
        _ -> Right 0
  balance <- case (cc.balance, conc sc.balance) of
    -- they pay for and are paid the gas, which is not tracked symbolically
    _ | a `elem` [fromAddress, coinbaseAddr] -> Right 0
    (Lit x, Lit y) | x /= y -> Left $ what "balance" <> show x <> ", symbolic " <> show y
                   | otherwise -> Right 1
    _ -> Right 0
  nonce <- if cc.nonce /= sc.nonce then Left $ what "nonce" <> show cc.nonce <> ", symbolic " <> show sc.nonce else Right 1
  code <- case (cc.code, sc.code) of
    (RuntimeCode (ConcreteRuntimeCode x), RuntimeCode (ConcreteRuntimeCode y))
      | x /= y -> Left $ what "code" <> bsToHex x <> ", symbolic " <> bsToHex y
      | otherwise -> Right 1
    _ -> Right 0
  st <- stores "storage" cc.storage sc.storage
  tst <- stores "transient storage" cc.tStorage sc.tStorage
  pure (balance + nonce + code + st + tst))
  where
    common = [ (a, cc, sc) | (LitAddr a, cc) <- Map.toList vc.env.contracts, Just sc <- [Map.lookup (LitAddr a) vs.env.contracts] ]

-- | Both runs halted: the same way, with the same output, logs and storage
compareEnds :: TestCase -> VM Concrete -> VM Symbolic -> Either String ()
compareEnds c vc vs = do
  case (vc.result, vs.result) of
    (Just (VMSuccess a), Just (VMSuccess b)) -> do
      void $ compareBufs "output" c a b
      void $ compareBufs "output, simplified" c a (Expr.simplify b)
    (Just (VMFailure (Revert a)), Just (VMFailure (Revert b))) -> do
      void $ compareBufs "revert data" c a b
      void $ compareBufs "revert data, simplified" c a (Expr.simplify b)
    (Just (VMFailure a), Just (VMFailure b)) | hevmErrorKind a == hevmErrorKind b -> pure ()
    (a, b) -> Left $ "the runs ended differently: concrete " <> show a <> ", symbolic " <> show b
  let logs = map (concretize c c.inputs) vs.logs
  when (all concreteLog logs && logs /= vc.logs) $ Left $ "logs differ: concrete " <> show vc.logs <> ", symbolic " <> show logs
  void $ compareStorage id c vc vs
  void $ compareStorage Expr.simplify c vc vs
  void $ compareCallTraces id c vc vs
  void $ compareCallTraces Expr.simplify c vc vs
  where
    concreteLog = \case
      LogEntry (WAddr (LitAddr _)) (ConcreteBuf _) ts -> all (isJust . Expr.maybeLitWordSimp) ts
      _ -> False

-- | Lockstep along a random path: the inputs a model of its path conditions
-- gives must take the concrete run along it, to where it ended
modelGuided :: App m => SolverGroup -> BranchMode -> TestCase -> [Int] -> m Property
modelGuided solvers mode c picks = Progress.withProgressLogFromEnv "model-guided" $ do
  sp <- randomPath solvers c picks
  let vs = sessionVM sp
      skip why = pure $ label why (property True)
  case vs.result of
    Nothing -> skip "random path too long"
    Just (Unfinished _) -> skip "random path unfinished"
    _ | any mentionsBlockHash vs.constraints -> skip "path conditions on a symbolic blockhash"
      | PBool False `elem` vs.constraints -> skip "path ends in a failed assumption"
      | otherwise -> checkSatWithProps solvers vs.constraints >>= \case
          -- a branch query the solver could not encode offers both sides
          -- the solver may have had no say at some branch: with path conditions it cannot
          -- encode, as they were before a later one made them plainly false, both sides are offered
          Qed | any (isLeft . SMT.assertProps defaultConfig) (tails vs.constraints) ->
                skip "infeasible, after path conditions the solver cannot take"
          Qed -> liftIO $ failWith c c.inputs $ "the random path offered only feasible sides, but is infeasible:\n"
                   <> unlines (map show vs.constraints)
          Unknown _ -> skip "unknown"
          Error e -> skip ("solver error: " <> take 40 e)
          Cex cex -> case modelInputs c.inputs cex of
            Left e -> skip ("model: " <> takeWhile (/= ':') e)
            Right i -> do
              let c' = c { inputs = i }
              lockstepCase solvers mode c' >>= \case
                Left err -> liftIO $ failWith c' i err
                Right l -> case l.ended of
                  -- the solver may pick any hash of symbolic data, which the concrete run does not get
                  Just e | e /= endOf vs, any mentionsSymbolicKeccak vs.constraints ->
                    consistentHashes solvers c' i vs.constraints >>= \case
                      Just False -> liftIO $ failWith c' i $ "the model gives one keccak input two hashes\npath conditions:\n"
                        <> unlines (map show vs.constraints)
                      _ -> skip "model via symbolic keccak"
                  Just e | e /= endOf vs -> liftIO $ failWith c' i $
                    "the inputs from a model of the path conditions end at " <> show e
                    <> ", the path ends at " <> show (endOf vs) <> "\npath conditions:\n" <> unlines (map show vs.constraints)
                  Just _ -> pure $ label "followed the path" (property True)
                  Nothing -> skip l.stopped
  where
    mentionsBlockHash = getAny . foldProp (\case BlockHash _ -> Any True; _ -> Any False) mempty
    mentionsSymbolicKeccak = getAny . foldProp (\case
      Keccak (ConcreteBuf _) -> Any False
      Keccak _ -> Any True
      _ -> Any False) mempty

-- | A concrete debugger session must see the same state at a step however it
-- got there, and its forward run must match geth's
data DebuggerVsGeth = DebuggerVsGeth
  { steps :: Int, revisits :: Int, wentBack :: Int, acrossSnapshots :: Int, outcome :: String, depth :: Int, ops :: Set String }

debuggerVsGeth :: Int -> TestCase -> [Command] -> IO DebuggerVsGeth
debuggerVsGeth every c moves = do
  g <- withDir $ \dir -> runGeth dir c c.inputs
  revisits <- newIORef (0 :: Int)
  backs <- newIORef (0 :: Int)
  across <- newIORef (0 :: Int)
  h <- runEnv testEnv $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
    let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
        shown s = if isHalted s then "halted: " <> show (sessionVM s).result else show (vmTraceStep (sessionVM s))
        visit seen s how = case Map.lookup (sessionStep s) seen of
          Just before
            | before /= shown s -> liftIO $ failWith c c.inputs $ "debugger: step " <> show (sessionStep s) <> " after " <> how
                <> " is\n" <> shown s <> "\nbut was\n" <> before <> "\nmoves: " <> show moves
            | otherwise -> liftIO (atomicModifyIORef' revisits (\n -> (n + 1, ()))) >> pure seen
          Nothing -> pure (Map.insert (sessionStep s) (shown s) seen)
        move (s, seen) m = do
          s' <- runCommand fetcher m s
          when (sessionStep s' < sessionStep s) $ liftIO $ do
            atomicModifyIORef' backs (\n -> (n + 1, ()))
            when (sessionStep s' `div` every /= sessionStep s `div` every) $ atomicModifyIORef' across (\n -> (n + 1, ()))
          (s',) <$> visit seen s' (show m)
        forward seen s acc
          | isHalted s || sessionStep s > 100_000 = pure (s, reverse acc)
          | otherwise = do
              s' <- runCommand fetcher (Step 1) s
              seen' <- visit seen s' "stepping forward"
              forward seen' s' (vmTraceStep (sessionVM s) : acc)
    s0 <- liftIO $ setSnapshotInterval every <$> (stToIO (concreteTestVm c) >>= newSession emptyDapp)
    seen0 <- visit mempty s0 "the start"
    (sEnd, seen) <- foldM move (s0, seen0) moves
    (sStart, seen') <- move (sEnd, seen) Restart
    (sLast, trace) <- forward seen' sStart []
    let vm = sessionVM sLast
    pure $ case vm.result of
      Just (VMSuccess b) -> hevmRun False c c.inputs (Right b) vm trace
      -- as in hevm's own traces, the failing step carries the error
      Just (VMFailure e) -> hevmRun False c c.inputs (Left e) vm (failedLast e trace)
      r -> internalError $ "the debugger stopped with " <> show r
  checkConcrete "debugger" c c.inputs g h
  DebuggerVsGeth (length h.trace) <$> readIORef revisits <*> readIORef backs <*> readIORef across
    <*> pure (either (errorKind . evmErrToString) (const "success") h.result)
    <*> pure (maximum (1 : map (.depth) h.trace))
    <*> pure (Set.fromList [intToOpName t.op | t <- h.trace])
  where
    failedLast e t = case reverse t of
      VMTraceStep p o gas m d st _ : rest -> reverse (VMTraceStep p o gas m d st (Just (evmErrToString e)) : rest)
      [] -> []
