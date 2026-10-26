{-# LANGUAGE DataKinds #-}

-- | Stateful invariant testing: the states reachable by sequences of calls to
-- target functions with symbolic arguments
module EVM.Invariant
  ( Target(..)
  , Call(..)
  , InvState(..)
  , Senders(..)
  , StateKey
  , stateKey
  , startCall
  , nextStates
  ) where

import Control.Concurrent.STM.TVar (newTVarIO)
import Control.Monad (forM)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (execStateT, execState, get, put, liftIO, modify)
import Data.Either (partitionEithers)
import Data.List (partition)
import Data.Map qualified as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import Optics.Core
import Optics.State
import Optics.State.Operators

import EVM (loadContract, resetState, pushTrace)
import EVM.ABI (Sig(..), callSig)
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.SymExec (IterConfig, interpretVMAbortable, runExpr, symCalldataNamed, freezeVM)
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

stateKey :: VM Symbolic -> StateKey
stateKey vm = StateKey accounts (Set.fromList (connected (foldMap accountAtoms accounts) conds))
  where
    -- every transaction bumps the origin's nonce, which no contract can read
    accounts = [ (a, c.codehash, zeroless c.storage, c.balance, if a == vm.tx.origin then Nothing else c.nonce)
               | (a, c) <- Map.toList vm.env.contracts ]
    -- a slot written back to zero is the same as one never written
    zeroless = \case
      ConcreteStore m -> ConcreteStore (Map.filter (/= 0) m)
      st -> st
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

-- | The states after one more call to any of the targets, and the partially
-- explored paths of those calls
nextStates :: App m
  => Fetch.Fetcher Symbolic m -> IterConfig -> Word64 -> Senders -> [Target] -> InvState
  -> m ([InvState], [Expr End])
nextStates fetcher iterConf gas senders targets st = do
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
        frozen <- liftIO $ stToIO $ freezeVM endVm
        pure $ Just $ Left InvState { vm = frozen, calls = st.calls <> [call] }
      Partial {} -> pure $ Just $ Right leaf
      _ -> pure Nothing
    pure $ partitionEithers (catMaybes leaves)
  pure (concatMap fst results, concatMap snd results)
