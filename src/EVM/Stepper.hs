{-# LANGUAGE ScopedTypeVariables #-}

module EVM.Stepper
  ( Action (..)
  , Stepper
  , exec
  , execFully
  , run
  , runFully
  , wait
  , fork
  , evm
  , enter
  , interpret
  )
where

-- This module is an abstract definition of EVM steppers.
-- Steppers can be run as TTY debuggers or as CLI test runners.
--
-- The implementation uses the operational monad pattern
-- as the framework for monadic interpretation.

import Control.Monad.IO.Class
import Control.Monad.Operational (Program, ProgramViewT(..), ProgramView, singleton, view)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (execStateT, get, StateT(..))
import Data.Text (Text)

import EVM qualified
import EVM.Effects
import EVM.Exec qualified
import EVM.Fetch qualified as Fetch
import EVM.Types

-- | The instruction type of the operational monad
data Action t a where
  -- | Keep executing until an intermediate result is reached
  Exec :: Action t (VMResult t)
  -- | Embed a VM state transformation
  EVM  :: EVM t a -> Action t a
  -- | Wait for a query to be resolved
  Wait :: Query t -> Action t ()
  -- | Two things can happen
  Fork :: RunBoth -> Action Symbolic ()
  -- | Many (>2) things can happen
  ForkMany :: RunAll -> Action Symbolic ()

-- | Type alias for an operational monad of @Action@
type Stepper t a = Program (Action t) a

-- Singleton actions

exec :: Stepper t (VMResult t)
exec = singleton Exec

run :: Stepper t (VM t)
run = exec >> evm get

wait :: Query t -> Stepper t ()
wait = singleton . Wait

fork :: RunBoth -> Stepper Symbolic ()
fork = singleton . Fork

forkMany :: RunAll -> Stepper Symbolic ()
forkMany = singleton . ForkMany

evm :: EVM t a -> Stepper t a
evm = singleton . EVM

-- | Run the VM until final result, resolving all queries
execFully :: Stepper Concrete (Either EvmError (Expr Buf))
execFully =
  exec >>= \case
    HandleEffect (Query q) ->
      wait q >> execFully
    VMFailure x ->
      pure (Left x)
    VMSuccess x ->
      pure (Right x)

-- | Run the VM until its final state
runFully :: Stepper t (VM t)
runFully = do
  vm <- run
  case vm.result of
    Nothing -> internalError "should not occur"
    Just (HandleEffect (Query q)) ->
      wait q >> runFully
    Just (HandleEffect (RunBoth q)) ->
      fork q >> runFully
    Just (HandleEffect (RunAll q)) ->
      forkMany q >> runFully
    Just _ ->
      pure vm

enter :: Text -> Stepper t ()
enter t = evm (EVM.pushTrace (EntryTrace t))

-- Concrete interpretation
interpret
  :: forall m a . (App m)
  => Fetch.Fetcher Concrete m
  -> VM Concrete
  -> Stepper Concrete a
  -> m a
interpret fetcher vm = eval . view
  where
    eval :: ProgramView (Action Concrete) a -> m a
    eval (Return x) = pure x
    eval (action :>>= k) =
      case action of
        Exec -> do
          conf <- readConfig
          (r, vm') <- liftIO $ stToIO $ runStateT (EVM.Exec.exec conf) vm
          interpret fetcher vm' (k r)
        Wait q -> do
          m <- fetcher q
          vm' <- liftIO $ stToIO $ execStateT m vm
          interpret fetcher vm' (k ())
        EVM m -> do
          (r, vm') <- liftIO $ stToIO $ runStateT m vm
          interpret fetcher vm' (k r)

