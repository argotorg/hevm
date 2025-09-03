{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}

module EVM.Tracing
  ( interpretWithTrace
  , execWithTrace
  , vmTraceStep
  , VMTraceStep (..)
  )
where

-- This module allows stepping with tracing of the EVM.
import Optics.Core
import Optics.State

import Control.Monad.IO.Class
import Control.Monad.ST (stToIO, RealWorld)
import Data.Word (Word8, Word64)
import GHC.Generics (Generic)
import Control.Monad.State.Strict (StateT(..))
import Control.Monad.Operational qualified as Operational
import Control.Monad.Reader (lift)
import Control.Monad.State.Strict qualified as State
import Data.Maybe (fromJust)
import EVM (exec1)
import EVM.Op (intToOpName)
import Witch (into)
import Data.ByteString qualified as BS


import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Types
import EVM.Stepper

data VMTraceStep =
  VMTraceStep
  { tracePc      :: Int
  , traceOp      :: Int
  , traceGas     :: Data.Word.Word64
  , traceMemSize :: Data.Word.Word64
  , traceDepth   :: Int
  , traceStack   :: [W256]
  , traceError   :: Maybe String
  } deriving (Generic)

instance Show VMTraceStep where
  show (VMTraceStep pc op gas memSize depth stack err) =
    "VMTraceStep { "
    ++ "tracePc = " ++ show pc
    ++ ", Op = " ++ show (intToOpName op)
    ++ ", Gas = " ++ show gas
    ++ ", MemSize = " ++ show memSize
    ++ ", Depth = " ++ show depth
    ++ ", Stack = " ++ show stack
    ++ ", Error = " ++ show err
    ++ " }"

type TraceState s = (VM Concrete s, [VMTraceStep])

execWithTrace :: App m => StateT (TraceState RealWorld) m (VMResult Concrete RealWorld)
execWithTrace = do
  _ <- runWithTrace
  fromJust <$> use (_1 % #result)

runWithTrace :: App m => StateT (TraceState RealWorld) m (VM Concrete RealWorld)
runWithTrace = do
  -- This is just like `exec` except for every instruction evaluated,
  -- we also increment a counter indexed by the current code location.
  conf <- lift readConfig
  vm0 <- use _1
  case vm0.result of
    Nothing -> do
      State.modify' (\(a, b) -> (a, b ++ [vmTraceStep vm0]))
      vm' <- liftIO $ stToIO $ State.execStateT (exec1 conf) vm0
      assign _1 vm'
      runWithTrace
    Just (VMFailure _) -> do
      -- Update error text for last trace element
      (a, b) <- State.get
      let updatedElem = (last b) {traceError = (vmTraceStep vm0).traceError}
          updatedTraces = take (length b - 1) b ++ [updatedElem]
      State.put (a, updatedTraces)
      pure vm0
    Just _ -> pure vm0

interpretWithTrace
  :: forall m a . App m
  => Fetch.Fetcher Concrete m RealWorld
  -> Stepper Concrete RealWorld a
  -> StateT (TraceState RealWorld) m a
interpretWithTrace fetcher =
  eval . Operational.view
  where
    eval
      :: App m
      => Operational.ProgramView (Action Concrete RealWorld) a
      -> StateT (TraceState RealWorld) m a
    eval (Operational.Return x) = pure x
    eval (action Operational.:>>= k) =
      case action of
        Exec ->
          execWithTrace >>= interpretWithTrace fetcher . k
        Wait q -> do
          m <- State.lift $ fetcher q
          vm <- use _1
          vm' <- liftIO $ stToIO $ State.execStateT m vm
          assign _1 vm'
          interpretWithTrace fetcher (k ())
        EVM m -> do
          vm <- use _1
          (r, vm') <- liftIO $ stToIO $ State.runStateT m vm
          assign _1 vm'
          interpretWithTrace fetcher (k r)

vmTraceStep :: VM Concrete s -> VMTraceStep
vmTraceStep vm =
  let
    memsize = vm.state.memorySize
  in VMTraceStep { tracePc = vm.state.pc
             , traceOp = into $ getOpFromVM vm
             , traceGas = vm.state.gas
             , traceMemSize = memsize
             -- increment to match geth format
             , traceDepth = 1 + length (vm.frames)
             -- reverse to match geth format
             , traceStack = reverse $ forceLit <$> vm.state.stack
             , traceError = readoutError vm.result
             }
  where
    readoutError :: Maybe (VMResult t s) -> Maybe String
    readoutError (Just (VMFailure e)) = Just $ evmErrToString e
    readoutError _ = Nothing

getOpFromVM :: VM t s -> Word8
getOpFromVM vm =
  let pcpos  = vm ^. #state % #pc
      code' = vm ^. #state % #code
      xs = case code' of
        UnknownCode _ -> internalError "UnknownCode instead of RuntimeCode"
        InitCode bs _ -> BS.drop pcpos bs
        RuntimeCode (ConcreteRuntimeCode xs') -> BS.drop pcpos xs'
        RuntimeCode (SymbolicRuntimeCode _) -> internalError "RuntimeCode is symbolic"
  in if xs == BS.empty then 0
                       else BS.head xs
