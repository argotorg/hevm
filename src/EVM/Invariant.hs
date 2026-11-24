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
  , defaultCallConfig
  , Transition(..)
  , StateKey
  , stateKey
  , startCall
  , nextStates
  , nextStatesWith
  , simplifyDisjunction
  ) where

import Control.Concurrent.STM.TVar (newTVarIO)
import Control.Monad (forM, forM_)
import Control.Monad.ST (stToIO)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Control.Monad.State.Strict (execStateT, execState, get, put, liftIO, modify)
import Data.Either (partitionEithers)
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

import EVM (clearTStorages, loadContract, resetState, pushTrace)
import EVM.ABI (Sig(..), callSig)
import EVM.Effects
import EVM.Expr (simplifyProp)
import EVM.Fetch qualified as Fetch
import EVM.Keccak.Preimages qualified as Preimages
import EVM.Solvers (SolverGroup, checkSatWithProps, checkBranchSat)
import EVM.SymExec (IterConfig, Postcondition, interpretVMAbortable, runExpr, extractProps, verifyResult)
import EVM.SymExec.Calldata (symCalldataNamed)
import EVM.Transaction (initTx)
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
  }

-- | Context for generated transactions. Bounds are per transaction. With no
-- number bound the block number stays fixed; time is always monotone and below
-- 2^64. Value is currently zero. Caller-as-origin requires a finite sender list
-- so account lookup during transaction initialization stays concrete.
data CallConfig = CallConfig
  { gas :: Word64
  , maxTimeDelay :: Maybe W256
  , maxBlockDelay :: Maybe W256
  , callerIsOrigin :: Bool
  }

defaultCallConfig :: Word64 -> CallConfig
defaultCallConfig gas = CallConfig gas Nothing Nothing False

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

-- | A call that can fail an assertion: the calls up to and including it, from the state before it
data Probe = Probe
  { state :: InvState
  , leaf :: Expr End
  , cex :: SMTCex
  }

-- | Who may send the calls, from targetSender and excludeSender
data Senders = AnySender | OneOf [Addr] | NoneOf [Addr]

-- | A state reached from the initial one by a sequence of successful calls
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
startCall target caller gas entry (cd, props) = do
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
  assign (#state % #gas) (toGas gas)
  pushTrace (EntryTrace entry)
  modify initTx

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
nextStatesWith solvers post fetcher iterConf conf senders targets visited st
  | conf.callerIsOrigin = case senders of
      OneOf as -> mconcat <$> mapM (expand . OneOf . pure) as
      _ -> pure $ mempty { issues = ["caller-as-origin requires OneOf senders"] }
  | otherwise = expand senders
  where
  expand (OneOf []) = pure mempty
  expand allowed = fmap mconcat $ forM targets $ \target -> do
    let Sig _ types = target.sig
        -- each call of a sequence needs its own variables, and they are on one path
        n = T.pack (show (length st.calls + 1))
        anyCaller = SymAddr ("caller" <> n)
        (caller, callerProps) = case allowed of
          OneOf [a] -> (LitAddr a, [])
          OneOf as -> (anyCaller, [por [PEq anyCaller (LitAddr a) | a <- as]])
          NoneOf as -> (anyCaller, [PNeg (PEq anyCaller (LitAddr a)) | a <- as])
          AnySender -> (anyCaller, [])
        -- time may pass between calls, as in halmos up to 2^64
        timestamp = Var ("timestamp" <> n)
        timeProps = [PLEq st.vm.block.timestamp timestamp, PLT timestamp (Lit (2 ^ (64 :: Int)))]
          <> maybe [] (\limit -> [PLEq (Sub timestamp st.vm.block.timestamp) (Lit limit)]) conf.maxTimeDelay
        blockNumber = maybe st.vm.block.number (const $ Var ("blockNumber" <> n)) conf.maxBlockDelay
        numberProps = maybe [] (\limit -> [PLEq st.vm.block.number blockNumber,
          PLEq (Sub blockNumber st.vm.block.number) (Lit limit)]) conf.maxBlockDelay
        origin = if conf.callerIsOrigin then caller else st.vm.tx.origin
    (cd, props, _) <- symCalldataNamed ("call" <> n <> "-") True (callSig target.sig) types [] (AbstractBuf ("txdata" <> n))
    let call = Call { target, caller, calldata = cd, timestamp, blockNumber, origin }
        entry = target.contractName <> "." <> callSig target.sig
    vm <- liftIO $ stToIO $ flip execStateT st.vm $ do
      assign (#block % #timestamp) timestamp
      assign (#block % #number) blockNumber
      assign (#tx % #origin) origin
      startCall target.addr caller conf.gas entry (cd, props <> callerProps <> timeProps <> numberProps)
    abort <- liftIO $ newTVarIO False
    issues <- liftIO $ newIORef []
    leaves <- interpretVMAbortable abort fetcher iterConf vm runExpr $ \leaf endVm _ -> case leaf of
      Success {} -> do
        known <- maybe (pure False) (liftIO . fmap (Set.member (stateKey endVm)) . readIORef) visited
        if known then pure Nothing else do
          -- branches were only decided by the simplifier
          res <- checkBranchSat solvers (extractProps leaf <> Preimages.recordedProps endVm.keccakPreImgs)
          recordIssue issues res
          pure $ case res of
            Qed -> Nothing
            _ -> Just $ Left (endState endVm)
      Partial {} -> pure $ Just $ Right (Left leaf)
      Failure {} -> case post vm leaf of
        PBool True -> pure Nothing
        p -> do
          res <- checkSatWithProps solvers (PNeg p : extractProps leaf <> Preimages.recordedProps vm.keccakPreImgs)
          recordIssue issues res
          pure $ case snd (verifyResult vm (res, leaf)) of
            Cex (l, cex) -> Just $ Right $ Right Probe { state = st { calls = st.calls <> [call] }, leaf = l, cex }
            _ -> Nothing
      _ -> pure Nothing
    let (ends, others) = partitionEithers (catMaybes leaves)
        (partials, probes) = partitionEithers others
    states <- liftIO $ fmap catMaybes $ forM (mergeStates ends) $ \end -> do
      let k = stateKey end
          reached = InvState { vm = end, calls = st.calls <> [call] }
      maybe (pure $ Just reached) (\ref -> atomicModifyIORef' ref $ \seen ->
        (Set.insert k seen, if Set.member k seen then Nothing else Just reached)) visited
    -- a merged state covers each of its paths
    liftIO $ forM_ visited $ \ref -> atomicModifyIORef' ref $ \seen -> (seen <> Set.fromList (map stateKey ends), ())
    Transition states partials probes <$> liftIO (readIORef issues)

  recordIssue :: App m => IORef [Text] -> SMTResult -> m ()
  recordIssue ref result = case result of
    Unknown reason -> add (getUnknownStr reason)
    Error err -> add err
    _ -> pure ()
    where add message = liftIO $ atomicModifyIORef' ref $ \found -> (found <> [T.pack message], ())
