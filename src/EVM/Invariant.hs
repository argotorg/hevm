{-# LANGUAGE DataKinds #-}

-- | Stateful invariant testing: the states reachable by sequences of calls to
-- target functions with symbolic arguments
module EVM.Invariant
  ( Target(..)
  , Call(..)
  , InvState(..)
  , Senders(..)
  , Probe(..)
  , CallConfig(..)
  , ValueTransfer(..)
  , defaultCallConfig
  , Transition(..)
  , StateKey
  , stateKey
  , startCall
  , startCallWithValue
  , startNoCall
  , nextStates
  , nextStatesWith
  , nextStatesWithProgress
  , CallProgress(..)
  , simplifyDisjunction
  ) where

import Control.Concurrent.STM.TVar (newTVarIO)
import Control.Monad (forM, forM_)
import Control.Monad.ST (stToIO)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Control.Monad.State.Strict (execStateT, execState, get, put, liftIO, modify)
import Data.List (partition, sortOn)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import Data.Tree.Zipper qualified as Zipper
import Optics.Core
import Optics.State
import Optics.State.Operators
import Witch (into)

import EVM (clearTStorages, loadContract, resetState, pushTrace)
import EVM.ABI (Sig(..), callSig)
import EVM.Effects
import EVM.Expr (simplifyProp)
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Keccak.Preimages qualified as Preimages
import EVM.Solvers (SolverGroup, checkSatWithProps, checkBranchSat)
import EVM.SymExec (IterConfig, Postcondition, interpretVMAbortable, runExpr, extractProps, verifyResult)
import EVM.SymExec.Calldata (symCalldataNamed)
import EVM.Transaction (accountAt, initTx)
import EVM.Traversals (foldExpr, foldProp)
import EVM.Types

-- | A function that a sequence may call
data Target = Target
  { addr :: Expr EAddr
  , contractName :: Text
  , sig :: Sig
  }

data Call = Call
  { target :: Target
  , caller :: Expr EAddr
  , calldata :: Expr Buf
  , timestamp :: Expr EWord
  , blockNumber :: Expr EWord
  , origin :: Expr EAddr
  , value :: Expr EWord
  , valueTransfer :: ValueTransfer
  -- | Relative to the state before this call, which may have been changed by
  -- warp/roll cheatcodes in the preceding call.
  , delay :: (Expr EWord, Expr EWord)
  }
  -- | Advance block context without executing code or touching accounts.
  | NoCall
  { timestamp :: Expr EWord
  , blockNumber :: Expr EWord
  , delay :: (Expr EWord, Expr EWord)
  }

-- | Context for generated transactions. Bounds are per transaction. With no
-- number bound the block number stays fixed; time is always monotone and below
-- 2^64. Caller-as-origin requires a finite sender list
-- so account lookup during transaction initialization stays concrete.
data CallConfig = CallConfig
  { gas :: Word64
  , maxTimeDelay :: Maybe W256
  , maxBlockDelay :: Maybe W256
  , callerIsOrigin :: Bool
  , maxValue :: W256
  , valueTransfer :: ValueTransfer
  -- | Include context-only steps. Each consumes one exploration depth.
  , allowNoCalls :: Bool
  }

-- | Normal transactions debit the origin and require sufficient funds.
-- Some testing frameworks instead credit the target without debiting the
-- sender. Keep this policy in the call so concrete replay uses the same model.
data ValueTransfer = TransferValue | MintValue
  deriving (Eq, Show)

defaultCallConfig :: Word64 -> CallConfig
defaultCallConfig gas = CallConfig gas Nothing Nothing False 0 TransferValue False

-- | Outcomes of expanding a frontier. Inconclusive solver results must not
-- be mistaken for successfully checked paths.
data Transition = Transition
  { states :: [InvState]
  , partials :: [Expr End]
  , probes :: [Probe]
  , issues :: [Text]
  }

instance Semigroup Transition where
  a <> b = Transition (a.states <> b.states) (a.partials <> b.partials)
    (a.probes <> b.probes) (a.issues <> b.issues)

instance Monoid Transition where
  mempty = Transition [] [] [] []

-- | A call that can violate the client's postcondition, including successful
-- calls. The sequence includes the violating call, from the state before it.
data Probe = Probe
  { state :: InvState
  , leaf :: Expr End
  , cex :: SMTCex
  }

-- | Who may send the calls, from targetSender and excludeSender
data Senders = AnySender | OneOf [Addr] | NoneOf [Addr]

-- | The call about to be explored. Indices are one-based within the selected
-- functions, separately for each sender. Nothing denotes a context-only wait.
-- This deliberately carries no VM or symbolic calldata.
data CallProgress = CallProgress
  { target :: Maybe Target
  , functionIndex :: Int
  , functionCount :: Int
  , caller :: Maybe (Expr EAddr)
  }

-- | A state reached by successful calls and optional context-only steps.
data InvState = InvState
  { vm :: VM Symbolic
  , calls :: [Call]
  }

-- | What determines how a state continues: the accounts, and the path
-- conditions on their symbolic values
data StateKey = StateKey [(Expr EAddr, Expr EWord, Expr Storage, Expr EWord, Maybe W64)] (Set Prop)
  deriving (Eq, Ord)

type Account = (Expr EAddr, Expr EWord, Expr Storage, Expr EWord, Maybe W64)

accountsOf :: VM Symbolic -> [Account]
accountsOf vm =
  -- every transaction bumps the origin's nonce, which no contract can read
  [ (a, c.codehash, zeroless c.storage, c.balance, if a == vm.tx.origin then Nothing else c.nonce)
  | (a, c) <- Map.toList vm.env.contracts ]
  where
    -- a slot written back to zero is the same as one never written
    zeroless = \case
      ConcreteStore m -> ConcreteStore (Map.filter (/= 0) m)
      st -> st

stateKey :: VM Symbolic -> StateKey
stateKey vm = StateKey accounts (Set.fromList (connected (foldMap accountAtoms accounts) conds))
  where
    accounts = accountsOf vm
    accountAtoms (a, h, st, b, _) = foldExpr atom mempty a <> foldExpr atom mempty h
      <> foldExpr atom mempty st <> foldExpr atom mempty b
    conds = [(p, foldProp atom mempty p) | p <- vm.constraints]
    -- conditions linked to the state through any chain of shared variables
    connected vars cs = case partition (not . Set.disjoint vars . snd) cs of
      ([], _) -> []
      (linked, rest) -> map fst linked <> connected (vars <> foldMap snd linked) rest
    atom :: Expr a -> Set Text
    atom = \case
      Var n -> Set.singleton ("var " <> n)
      SymAddr n -> Set.singleton ("addr " <> n)
      AbstractBuf n -> Set.singleton ("buf " <> n)
      e@AbstractStore {} -> Set.singleton (T.pack (show e))
      e@Balance {} -> Set.singleton (T.pack (show e))
      e@Gas {} -> Set.singleton (T.pack (show e))
      TxValue -> Set.singleton "txvalue"
      _ -> mempty

-- | Sets up a new transaction calling the given contract
startCall :: VMOps t => Expr EAddr -> Expr EAddr -> Word64 -> Text -> (Expr Buf, [Prop]) -> EVM t ()
startCall target caller gas = startCallWithValue target caller gas (Lit 0) TransferValue

-- | A context-only step does not initialize a transaction: balances, nonces,
-- origin and persistent storage are unchanged, and no bytecode is executed.
startNoCall :: VMOps t => Expr EWord -> Expr EWord -> EVM t ()
startNoCall timestamp blockNumber = do
  resetState
  assign (#block % #timestamp) timestamp
  assign (#block % #number) blockNumber

-- | Initialize call value before transferring funds. The caller must ensure
-- a normal transfer is affordable; symbolic transitions add that constraint.
startCallWithValue :: VMOps t => Expr EAddr -> Expr EAddr -> Word64 -> Expr EWord -> ValueTransfer -> Text -> (Expr Buf, [Prop]) -> EVM t ()
startCallWithValue target caller gas value transfer entry (cd, props) = do
  resetState
  clearTStorages
  -- loop bounds count visits within one transaction
  assign #iterations mempty
  assign #pathsVisited mempty
  assign #exploreDepth 0
  assign (#tx % #subState) (SubState mempty mempty mempty mempty mempty mempty)
  assign (#tx % #isCreate) False
  execState (loadContract target) <$> get >>= put
  assign (#state % #calldata) cd
  #constraints %= (<> props)
  assign (#state % #caller) caller
  assign (#state % #callvalue) value
  assign (#state % #gas) (toGas gas)
  pushTrace (EntryTrace entry)
  modify $ \vm -> case transfer of
    TransferValue -> initTx vm
    -- Restore the debited value after initTx. Its reversion snapshot remains
    -- untouched, so reverting a mint does not leave extra funds in the origin.
    MintValue -> initTx vm & over (#env % #contracts % ix vm.tx.origin % #balance) (`Expr.add` value)

-- | What of a VM at the end of a successful call the next call can see
endState :: VM Symbolic -> VM Symbolic
endState vm = vm
  & set #result Nothing
  & set #frames []
  & set (#state % #memory) (SymbolicMemory mempty)
  & set (#state % #stack) []
  & set (#state % #returndata) mempty
  & set #traces (Zipper.fromForest [])
  & set #iterations mempty
  & set #pathsVisited mempty
  & set #logs []

-- | Merges the end states of paths that differ only in their path conditions,
-- such as the branches of an assertion: the paths of one state continue alike
mergeStates :: [VM Symbolic] -> [VM Symbolic]
mergeStates vms = map (merge . snd) $ sortOn fst $ Map.elems $
  Map.fromListWith (\(_, new) (i, old) -> (i, old <> new)) [(sameAs vm, (i, [vm])) | (i, vm) <- zip [0 :: Int ..] vms]
  where
    sameAs vm = (accountsOf vm, vm.block.timestamp, vm.block.number, vm.env.callWorld,
                 vm.env.callCounts, vm.env.freshAddresses, vm.freshVar)
    merge [vm] = vm
    merge group@(vm:_) =
      let conds = map (Set.fromList . (.constraints)) group
          common = foldr1 Set.intersection conds
          rest = simplifyDisjunction $ map (`Set.difference` common) conds
          shared = filter (`Set.member` common) vm.constraints
      in vm & set #constraints (if any Set.null rest then shared else shared <> [por (map (pand . Set.toList) rest)])
            & set #keccakPreImgs (foldMap (.keccakPreImgs) group)
    merge [] = internalError "empty group"

-- | Shortens a disjunction of conjunctions: two that differ only in one
-- condition and its negation become one without it, and a conjunction that
-- implies another is dropped
simplifyDisjunction :: [Set Prop] -> [Set Prop]
simplifyDisjunction = untilFixpoint (absorb . resolve) . mapMaybe simp
  where
    simp r = let ps = Set.delete (PBool True) (Set.map simplifyProp r)
             in if Set.member (PBool False) ps then Nothing else Just ps
    resolve rs = case [ (i, j, Set.delete p r) | (i, r) <- zip [0 :: Int ..] rs, (j, r') <- zip [0..] rs, i < j
                      , p <- Set.toList r, let q = simplifyProp (PNeg p)
                      , Set.member q r', Set.delete p r == Set.delete q r' ] of
      (i, j, s):_ -> s : [r | (k, r) <- zip [0..] rs, k /= i, k /= j]
      [] -> rs
    -- of equal conjunctions, the first one stays
    absorb rs = [ r | (i, r) <- zip [0 :: Int ..] rs
                , not (or [r' `Set.isSubsetOf` r && (r' /= r || j < i) | (j, r') <- zip [0..] rs, j /= i]) ]

-- | The feasible states not in @visited@ after one more call to any of the
-- targets, the partially explored paths of those calls, and the calls that
-- can fail the postcondition
nextStates :: App m
  => SolverGroup -> Postcondition -> Fetch.Fetcher Symbolic m -> IterConfig -> Word64 -> Senders -> [Target]
  -> IORef (Set StateKey) -> InvState
  -> m ([InvState], [Expr End], [Probe])
nextStates solvers post fetcher iterConf gas senders targets visited st = do
  result <- nextStatesWith solvers post fetcher iterConf (defaultCallConfig gas)
    senders targets (Just visited) st
  pure (result.states, result.partials, result.probes)

-- | Configurable transition execution. Passing 'Nothing' for the visited set
-- disables state pruning, which is needed when checks observe transaction or
-- block context not captured by 'stateKey'. The legacy 'nextStates' wrapper
-- retains its original pruning policy and result type.
nextStatesWith :: App m
  => SolverGroup -> Postcondition -> Fetch.Fetcher Symbolic m -> IterConfig -> CallConfig -> Senders -> [Target]
  -> Maybe (IORef (Set StateKey)) -> InvState -> m Transition
nextStatesWith = nextStatesWithProgress (const $ pure ())

-- | Report each call before transaction setup, interpretation and SMT queries.
-- The callback must return promptly; clients can publish periodic updates from
-- the latest event while a call is still being explored.
nextStatesWithProgress :: App m
  => (CallProgress -> IO ())
  -> SolverGroup -> Postcondition -> Fetch.Fetcher Symbolic m -> IterConfig -> CallConfig -> Senders -> [Target]
  -> Maybe (IORef (Set StateKey)) -> InvState -> m Transition
nextStatesWithProgress progress solvers post fetcher iterConf conf senders targets visitedStates st = do
  called <- if null targets then pure mempty
    else if conf.callerIsOrigin then case senders of
      OneOf as -> mconcat <$> mapM (expand . OneOf . pure) as
      _ -> pure $ mempty { issues = ["caller-as-origin requires OneOf senders"] }
    else expand senders
  waited <- if conf.allowNoCalls then noCall else pure mempty
  pure $ called <> waited
  where
  -- Storage-only keys cannot distinguish the contexts reached by waiting.
  visited = if conf.allowNoCalls then Nothing else visitedStates
  n = T.pack (show (length st.calls + 1))
  timestamp = Var ("timestamp" <> n)
  blockNumber = maybe st.vm.block.number (const $ Var ("blockNumber" <> n)) conf.maxBlockDelay
  delay = (Sub timestamp st.vm.block.timestamp, Sub blockNumber st.vm.block.number)
  timeProps = [PLEq st.vm.block.timestamp timestamp, PLT timestamp (Lit (2 ^ (64 :: Int)))]
    <> maybe [] (\limit -> [PLEq (fst delay) (Lit limit)]) conf.maxTimeDelay
  numberProps = maybe [] (\limit -> [PLEq st.vm.block.number blockNumber,
    PLEq (snd delay) (Lit limit)]) conf.maxBlockDelay

  noCall
    | conf.maxTimeDelay == Just 0 && maybe True (== 0) conf.maxBlockDelay = pure mempty
    | otherwise = do
        liftIO $ progress $ CallProgress Nothing 0 0 Nothing
        -- Zero-delay waits add no reachable context and need not be explored.
        let props = timeProps <> numberProps <>
              [POr (PLT st.vm.block.timestamp timestamp) (PLT st.vm.block.number blockNumber)]
        result <- checkBranchSat solvers (st.vm.constraints <> props <> Preimages.recordedProps st.vm.keccakPreImgs)
        next <- liftIO $ stToIO $ execStateT (startNoCall timestamp blockNumber) st.vm
        let reached = InvState
              (endState next & over #constraints (<> props))
              (st.calls <> [NoCall timestamp blockNumber delay])
        pure $ mempty { states = [reached | not (isQed result)], issues = solverIssues result }

  expand (OneOf []) = pure mempty
  expand allowed = fmap mconcat $ forM (zip [1..] targets) $ \(index, target) -> do
    let Sig _ types = target.sig
        anyCaller = SymAddr ("caller" <> n)
        (caller, callerProps) = case allowed of
          OneOf [a] -> (LitAddr a, [])
          OneOf as -> (anyCaller, [por [PEq anyCaller (LitAddr a) | a <- as]])
          NoneOf as -> (anyCaller, [PNeg (PEq anyCaller (LitAddr a)) | a <- as])
          AnySender -> (anyCaller, [])
        origin = if conf.callerIsOrigin then caller else st.vm.tx.origin
        value = if conf.maxValue == 0 then Lit 0 else Var ("value" <> n)
        balance = view (accountAt origin % #balance) st.vm.env.contracts
        gasCost = Lit (st.vm.tx.gasprice * into st.vm.tx.gaslimit)
        valueProps = [PLEq value (Lit conf.maxValue)] <>
          [p | conf.maxValue /= 0 && conf.valueTransfer == TransferValue
             , p <- [PLEq gasCost balance, PLEq value (Expr.sub balance gasCost)]]
    liftIO $ progress $ CallProgress (Just target) index (length targets) (Just caller)
    (cd, props, _) <- symCalldataNamed ("call" <> n <> "-") True (callSig target.sig) types [] (AbstractBuf ("txdata" <> n))
    let call = Call { target, caller, calldata = cd, timestamp, blockNumber, origin, value,
          valueTransfer = conf.valueTransfer,
          delay }
        entry = target.contractName <> "." <> callSig target.sig
    vm <- liftIO $ stToIO $ flip execStateT st.vm $ do
      assign (#block % #timestamp) timestamp
      assign (#block % #number) blockNumber
      assign (#tx % #origin) origin
      startCallWithValue target.addr caller conf.gas value conf.valueTransfer entry
        (cd, props <> callerProps <> timeProps <> numberProps <> valueProps)
    abort <- liftIO $ newTVarIO False
    issues <- liftIO $ newIORef []
    let checkPost :: App m => VM Symbolic -> Expr End -> m [Probe]
        checkPost endVm leaf = case post vm leaf of
          PBool True -> pure []
          p -> do
            res <- checkSatWithProps solvers (PNeg p : extractProps leaf <> Preimages.recordedProps endVm.keccakPreImgs)
            recordIssue issues res
            pure $ case snd (verifyResult vm (res, leaf)) of
              Cex (l, cex) -> [Probe { state = st { calls = st.calls <> [call] }, leaf = l, cex }]
              _ -> []
    leaves <- interpretVMAbortable abort fetcher iterConf vm runExpr $ \leaf endVm _ -> case leaf of
      Success {} -> do
        -- A successful EVM call can still violate a return-value or storage
        -- postcondition. Check it before pruning its successor state.
        probes <- checkPost endVm leaf
        known <- maybe (pure False) (liftIO . fmap (Set.member (stateKey endVm)) . readIORef) visited
        ends <- if known then pure [] else do
          -- branches were only decided by the simplifier
          res <- checkBranchSat solvers (extractProps leaf <> Preimages.recordedProps endVm.keccakPreImgs)
          recordIssue issues res
          pure $ case res of
            Qed -> []
            _ -> [endState endVm]
        pure $ Just (ends, [], probes)
      Partial {} -> pure $ Just ([], [leaf], [])
      Failure {} -> do
        probes <- checkPost endVm leaf
        pure $ Just ([], [], probes)
      _ -> pure Nothing
    let (ends, partials, probes) = mconcat (catMaybes leaves)
    states <- liftIO $ fmap catMaybes $ forM (mergeStates ends) $ \end -> do
      let k = stateKey end
          reached = InvState { vm = end, calls = st.calls <> [call] }
      maybe (pure $ Just reached) (\ref -> atomicModifyIORef' ref $ \seen ->
        (Set.insert k seen, if Set.member k seen then Nothing else Just reached)) visited
    -- a merged state covers each of its paths
    liftIO $ forM_ visited $ \ref -> atomicModifyIORef' ref $ \seen -> (seen <> Set.fromList (map stateKey ends), ())
    Transition states partials probes <$> liftIO (readIORef issues)

  recordIssue :: App m => IORef [Text] -> SMTResult -> m ()
  recordIssue ref result = liftIO $ atomicModifyIORef' ref $ \found -> (found <> solverIssues result, ())

  solverIssues :: SMTResult -> [Text]
  solverIssues = \case
    Unknown reason -> [T.pack $ getUnknownStr reason]
    Error err -> [T.pack err]
    _ -> []
