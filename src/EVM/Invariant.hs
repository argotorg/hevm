{-# LANGUAGE DataKinds #-}

-- | Stateful invariant testing: the states reachable by sequences of calls to
-- target functions with symbolic arguments
module EVM.Invariant
  ( Target(..)
  , Call(..)
  , InvState(..)
  , Senders(..)
  , Probe(..)
  , StateKey
  , stateKey
  , startCall
  , nextStates
  , disjoin
  ) where

import Control.Concurrent.STM.TVar (newTVarIO)
import Control.Monad (forM)
import Control.Monad.ST (stToIO)
import Data.IORef (IORef, readIORef, atomicModifyIORef')
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

import EVM (loadContract, resetState, pushTrace)
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
  }

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
  -- loop bounds count visits within one transaction
  assign #iterations mempty
  assign #pathsVisited mempty
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
          rest = disjoin $ map (`Set.difference` common) conds
          shared = filter (`Set.member` common) vm.constraints
      in vm & set #constraints (if any Set.null rest then shared else shared <> [por (map (pand . Set.toList) rest)])
            & set #keccakPreImgs (foldMap (.keccakPreImgs) group)
    merge [] = internalError "empty group"

-- | Shortens a disjunction of conjunctions: two that differ only in one
-- condition and its negation become one without it, and a conjunction that
-- implies another is dropped
disjoin :: [Set Prop] -> [Set Prop]
disjoin = untilFixpoint (absorb . resolve) . mapMaybe simp
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
  results <- forM targets $ \target -> do
    let Sig _ types = target.sig
        -- each call of a sequence needs its own variables, and they are on one path
        n = T.pack (show (length st.calls + 1))
        anyCaller = SymAddr ("caller" <> n)
        (caller, callerProps) = case senders of
          OneOf [a] -> (LitAddr a, [])
          OneOf as -> (anyCaller, [foldr1 POr [PEq anyCaller (LitAddr a) | a <- as]])
          NoneOf as -> (anyCaller, [PNeg (PEq anyCaller (LitAddr a)) | a <- as])
          AnySender -> (anyCaller, [])
        -- time may pass between calls, as in halmos up to 2^64
        timestamp = Var ("timestamp" <> n)
        timeProps = [PLEq st.vm.block.timestamp timestamp, PLT timestamp (Lit (2 ^ (64 :: Int)))]
    (cd, props, _) <- symCalldataNamed ("call" <> n <> "-") True (callSig target.sig) types [] (AbstractBuf ("txdata" <> n))
    let call = Call { target, caller, calldata = cd, timestamp }
        entry = target.contractName <> "." <> callSig target.sig
    vm <- liftIO $ stToIO $ flip execStateT st.vm $ do
      assign (#block % #timestamp) timestamp
      startCall target.addr caller gas entry (cd, props <> callerProps <> timeProps)
    abort <- liftIO $ newTVarIO False
    leaves <- interpretVMAbortable abort fetcher iterConf vm runExpr $ \leaf endVm _ -> case leaf of
      Success {} -> do
        known <- liftIO $ Set.member (stateKey endVm) <$> readIORef visited
        if known then pure Nothing else do
          -- branches were only decided by the simplifier
          res <- checkBranchSat solvers (extractProps leaf <> Preimages.recordedProps endVm.keccakPreImgs)
          pure $ case res of
            Qed -> Nothing
            _ -> Just $ Left (endState endVm)
      Partial {} -> pure $ Just $ Right (Left leaf)
      Failure {} -> case post vm leaf of
        PBool True -> pure Nothing
        p -> do
          res <- checkSatWithProps solvers (PNeg p : extractProps leaf <> Preimages.recordedProps vm.keccakPreImgs)
          pure $ case snd (verifyResult vm (res, leaf)) of
            Cex (l, cex) -> Just $ Right $ Right Probe { state = st { calls = st.calls <> [call] }, leaf = l, cex }
            _ -> Nothing
      _ -> pure Nothing
    let (ends, others) = partitionEithers (catMaybes leaves)
        (partials, probes) = partitionEithers others
    states <- liftIO $ fmap catMaybes $ forM (mergeStates ends) $ \end -> do
      let k = stateKey end
      atomicModifyIORef' visited $ \seen ->
        (Set.insert k seen, if Set.member k seen then Nothing else Just InvState { vm = end, calls = st.calls <> [call] })
    -- a merged state covers each of its paths
    liftIO $ atomicModifyIORef' visited $ \seen -> (seen <> Set.fromList (map stateKey ends), ())
    pure (states, partials, probes)
  pure (concatMap (\(a, _, _) -> a) results, concatMap (\(_, b, _) -> b) results, concatMap (\(_, _, c) -> c) results)
