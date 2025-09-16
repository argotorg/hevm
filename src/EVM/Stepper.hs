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
import Control.Monad.ST (stToIO, RealWorld)
import Control.Monad.State.Strict (execStateT, get, StateT(..))
import Data.Text (Text)

import EVM qualified
import EVM.Effects
import EVM.Exec qualified
import EVM.Fetch qualified as Fetch
import EVM.Types

-- | The instruction type of the operational monad
data Action t s a where
  -- | Keep executing until an intermediate result is reached
  Exec :: Action t s (VMResult t s)
  -- | Embed a VM state transformation
  EVM  :: EVM t s a -> Action t s a
  -- | Wait for a query to be resolved
  Wait :: Query t s -> Action t s ()
  -- | Two things can happen
  Fork :: RunBoth s -> Action Symbolic s ()
  -- | Many (>2) things can happen
  ForkMany :: RunAll s -> Action Symbolic s ()

-- | Type alias for an operational monad of @Action@
type Stepper t s a = Program (Action t s) a

-- Singleton actions

exec :: Stepper t s (VMResult t s)
exec = singleton Exec

run :: Stepper t s (VM t s)
run = exec >> evm get

wait :: Query t s -> Stepper t s ()
wait = singleton . Wait

fork :: RunBoth s -> Stepper Symbolic s ()
fork = singleton . Fork

forkMany :: RunAll s -> Stepper Symbolic s ()
forkMany = singleton . ForkMany

evm :: EVM t s a -> Stepper t s a
evm = singleton . EVM

-- | Run the VM until final result, resolving all queries
execFully :: Stepper Concrete s (Either EvmError (Expr Buf))
execFully =
  exec >>= \case
    HandleEffect (Query q) ->
      wait q >> execFully
    VMFailure x ->
      pure (Left x)
    VMSuccess x ->
      pure (Right x)

-- | Run the VM until its final state
runFully :: Stepper t s (VM t s)
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

enter :: Text -> Stepper t s ()
enter t = evm (EVM.pushTrace (EntryTrace t))

-- Concrete interpretation
interpret
  :: forall m a . (App m)
  => Fetch.Fetcher Concrete m RealWorld
  -> VM Concrete RealWorld
  -> Stepper Concrete RealWorld a
  -> m a
interpret fetcher vm = eval . view
  where
    eval :: ProgramView (Action Concrete RealWorld) a -> m a
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

