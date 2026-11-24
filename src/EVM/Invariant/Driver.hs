-- | Bounded invariant exploration independent of a test framework. Clients
-- select targets and supply the semantics of their checks. Reaching the depth
-- limit is a bounded search result, not an inductive invariant proof.
module EVM.Invariant.Driver
  ( Exploration
  , ExplorationConfig(..)
  , newExploration
  , explorationStatus
  , exploreLevel
  , Check(..)
  , Counterexample(..)
  , CheckResult(..)
  , checkInvariant
  , searchInvariant
  , ConcreteCall(..)
  , concretizeCalls
  , concreteAddr
  , replayCall
  , replayCalls
  ) where

import Control.Monad (foldM, when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (execStateT, get)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe (listToMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import Optics.Core

import EVM.ABI (AbiValue, AbiVals(..), Sig(..), callSig, decodeBuf)
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Fetch (Fetcher)
import EVM.Invariant
import EVM.Solvers (SolverGroup)
import EVM.Stepper qualified as Stepper
import EVM.SymExec (IterConfig, Postcondition, VeriOpts(..), verify)
import EVM.SymExec.Cex (calldataFromCex, subModel)
import EVM.Types

data ExplorationConfig = ExplorationConfig
  { targets :: [Target]
  , senders :: Senders
  , callConfig :: CallConfig
  , postcondition :: Postcondition
  -- | Disable when checks observe context omitted by 'stateKey'.
  , pruneStates :: Bool
  }

-- | A single-threaded cache shared by all checks from the same initial state.
-- Solver settings and fetcher must stay the same throughout its lifetime.
data Exploration = Exploration
  { options :: ExplorationConfig
  , levels :: IORef [[InvState]]
  , visited :: Maybe (IORef (Set StateKey))
  , outcomes :: IORef Transition
  }

newExploration :: MonadIO m => ExplorationConfig -> VM Symbolic -> m Exploration
newExploration options vm = liftIO $ do
  levels <- newIORef [[InvState vm []]]
  visited <- if options.pruneStates then Just <$> newIORef (Set.singleton $ stateKey vm) else pure Nothing
  outcomes <- newIORef mempty
  pure Exploration { options, levels, visited, outcomes }

-- | Frontier sizes and accumulated transition diagnostics. Probe diagnostics
-- retain the first failing call to each target, as in the Foundry runner.
explorationStatus :: MonadIO m => Exploration -> m ([Int], Transition)
explorationStatus exploration = liftIO $
  (,) <$> (map length <$> readIORef exploration.levels) <*> readIORef exploration.outcomes

-- | States reached by exactly the requested number of successful calls.
-- A level is executed once, even when multiple properties search it.
exploreLevel :: App m => SolverGroup -> Fetcher Symbolic m -> IterConfig -> Exploration -> Int -> m [InvState]
exploreLevel solvers fetcher iterConf exploration depth
  | depth < 0 = pure []
  | otherwise = do
      known <- liftIO $ readIORef exploration.levels
      case drop depth known of
        states:_ -> pure states
        [] -> do
          previous <- exploreLevel solvers fetcher iterConf exploration (depth - 1)
          let opts = exploration.options
          result <- mconcat <$> mapM (nextStatesWith solvers opts.postcondition fetcher iterConf
            opts.callConfig opts.senders opts.targets exploration.visited) previous
          conf <- readConfig
          when conf.debug $ liftIO $ putStrLn $ "Invariant states after " <> show depth
            <> " calls: " <> show (length result.states) <> " new"
          liftIO $ do
            modifyIORef' exploration.levels (<> [result.states])
            modifyIORef' exploration.outcomes $ \old -> (old <> result)
              { states = [], probes = List.foldl' addProbe old.probes result.probes }
          pure result.states
  where
    addProbe :: [Probe] -> Probe -> [Probe]
    addProbe found p = if any (sameFunction p) found then found else found <> [p]
    sameFunction :: Probe -> Probe -> Bool
    sameFunction a b = case (reverse a.state.calls, reverse b.state.calls) of
      (x:_, y:_) -> x.target.addr == y.target.addr && callSig x.target.sig == callSig y.target.sig
      _ -> False

-- | A property call. An absent origin preserves the explored state's origin;
-- otherwise the supplied origin is used only for this check. Checks execute
-- on copies of reached states, so their writes cannot affect other checks.
data Check = Check
  { target :: Target
  , caller :: Expr EAddr
  , origin :: Maybe (Expr EAddr)
  , gas :: Word64
  , calldata :: (Expr Buf, [Prop])
  , postcondition :: Postcondition
  }

data Counterexample = Counterexample
  { state :: InvState
  , call :: Call
  , leaf :: Expr End
  , model :: SMTCex
  }

data CheckResult = CheckResult
  { counterexample :: Maybe Counterexample
  , partials :: [Expr End]
  , issues :: [Text]
  }

checkInvariant :: App m => SolverGroup -> Fetcher Symbolic m -> VeriOpts -> Check -> InvState -> m CheckResult
checkInvariant solvers fetcher opts check st = do
  let initial = maybe st.vm (\a -> st.vm & set (#tx % #origin) a) check.origin
      call = Call check.target check.caller (fst check.calldata) initial.block.timestamp
        initial.block.number initial.tx.origin (Lit 0, Lit 0)
  vm <- liftIO $ stToIO $ execStateT
    (startCall check.target.addr check.caller check.gas (callSig check.target.sig) check.calldata) initial
  (ends, results) <- verify solvers fetcher opts vm check.postcondition Nothing
  pure CheckResult
    { counterexample = listToMaybe [Counterexample st call leaf model | Cex (leaf, model) <- results]
    , partials = [p | p@Partial {} <- ends]
    , issues = [T.pack (getUnknownStr u) | Unknown u <- results] <> [T.pack e | Error e <- results]
    }

-- | Search an inclusive range of depths, stopping at the first counterexample
-- for this check. Exploration is cached across calls for other checks. Partial
-- paths and solver issues are returned even when a counterexample is found.
searchInvariant :: App m
  => SolverGroup -> Fetcher Symbolic m -> VeriOpts -> Exploration -> (Int, Int) -> Check -> m CheckResult
searchInvariant solvers fetcher opts exploration (first, lastDepth) check = go (max 0 first) [] []
  where
    go depth partials issues
      | depth > lastDepth = pure $ CheckResult Nothing partials issues
      | otherwise = exploreLevel solvers fetcher opts.iterConf exploration depth >>= \case
          [] -> pure $ CheckResult Nothing partials issues
          states -> visit depth partials issues states
    visit depth partials issues [] = go (depth + 1) partials issues
    visit depth partials issues (st:rest) = do
      result <- checkInvariant solvers fetcher opts check st
      let ps = partials <> result.partials
          es = issues <> result.issues
      case result.counterexample of
        Just cex -> pure $ CheckResult (Just cex) ps es
        Nothing -> visit depth ps es rest

-- | A replayable zero-value transaction, including decoded ABI arguments and
-- delays relative to the state before each call, including prior cheatcodes.
data ConcreteCall = ConcreteCall
  { target :: Addr
  , caller :: Addr
  , origin :: Addr
  , sig :: Sig
  , arguments :: [AbiValue]
  , calldata :: ByteString
  , timestamp :: W256
  , blockNumber :: W256
  , delay :: (W256, W256)
  }

concreteAddr :: SMTCex -> Expr EAddr -> Expr EAddr
concreteAddr model = \case
  a@(SymAddr _) -> LitAddr $ Map.findWithDefault 0xdeadbeef a model.addrs
  a -> a

-- | Materialize every call using the same model. Clients can replay these
-- through their own executor for coverage, shrinking and result validation.
concretizeCalls :: App m => Block -> SMTCex -> [Call] -> m (Err [ConcreteCall])
concretizeCalls block model = go (forceLit block.timestamp) (forceLit block.number)
  where
    go _ _ [] = pure $ Right []
    go time number (call:rest) = do
      bytes <- calldataFromCex model call.calldata call.target.sig
      let Sig _ types = call.target.sig
          timestamp = wordValue time call.timestamp
          blockNumber = wordValue number call.blockNumber
          address a = case concreteAddr model a of
            LitAddr value -> Right value
            _ -> Left "could not concretize invariant call address"
          materialized = do
            calldata <- bytes
            arguments <- case decodeBuf types (ConcreteBuf $ BS.drop 4 calldata) of
              (CAbi args, "") -> Right args
              _ -> Left "could not decode invariant counterexample"
            target <- address call.target.addr
            caller <- address call.caller
            origin <- address call.origin
            Right ConcreteCall { target, caller, origin, sig = call.target.sig, arguments, calldata,
              timestamp, blockNumber, delay = (wordValue 0 $ fst call.delay, wordValue 0 $ snd call.delay) }
      case materialized of
        Left err -> pure $ Left err
        Right concrete -> fmap (concrete :) <$> go timestamp blockNumber rest
    wordValue :: W256 -> Expr EWord -> W256
    wordValue fallback expression = case Expr.simplify <$> subModel model expression of
      Right (Lit value) -> value
      _ -> fallback

-- | Execute a materialized transaction. A failing last call is returned for
-- the client to classify; intermediate calls must succeed in 'replayCalls'.
replayCall :: App m
  => Fetcher Concrete m -> Word64 -> VM Concrete -> ConcreteCall
  -> m (VM Concrete, Either EvmError (Expr Buf))
replayCall fetcher gas vm call = Stepper.interpret fetcher initial $ do
  Stepper.evm $ startCall (LitAddr call.target) (LitAddr call.caller) gas
    (callSig call.sig) (ConcreteBuf call.calldata, [])
  result <- Stepper.execFully
  (, result) <$> Stepper.evm get
  where
    initial = vm & set (#block % #timestamp) (Lit call.timestamp)
      & set (#block % #number) (Lit call.blockNumber) & set (#tx % #origin) (LitAddr call.origin)

replayCalls :: App m
  => Fetcher Concrete m -> Word64 -> VM Concrete -> SMTCex -> [Call] -> m (Err (VM Concrete))
replayCalls fetcher gas initial model calls = concretizeCalls initial.block model calls >>= \case
  Left err -> pure $ Left err
  Right concrete -> foldM step (Right initial) (zip [1 :: Int ..] concrete)
  where
    step (Left err) _ = pure $ Left err
    step (Right vm) (i, call) = replayCall fetcher gas vm call >>= \case
      (next, Right _) -> pure $ Right next
      _ -> pure $ Left $ "call " <> show i <> " failed in the concrete replay"
