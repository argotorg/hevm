module EVM.Exec
  ( ethrunAddress, vmForEthrunCreation, exec, run, execWhile, newConcreteExec
  ) where

import EVM hiding (createAddress)
import EVM.Concrete (createAddress)
import EVM.Concrete.Blocks (newProgramCache, newScratch, prepareProgram, runConcreteBlocks)
import EVM.Types

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (get, gets, put, State)
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)
import Optics.Core
import Control.Monad.ST (ST, RealWorld)
import EVM.Effects (Config)
import Data.Typeable (Typeable, eqT, (:~:)(Refl))
import GHC.IO (ioToST)

ethrunAddress :: Addr
ethrunAddress = Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

vmForEthrunCreation :: VMOps t => ByteString -> ST RealWorld (VM t)
vmForEthrunCreation creationCode =
  (makeVm $ defaultVMOpts
    { contract = initialContract (InitCode creationCode mempty)
    , address = createAddress ethrunAddress 1
    , caller = LitAddr ethrunAddress
    , origin = LitAddr ethrunAddress
    , blockGaslimit = 0
    , prevRandao = Lit 42069
    }) <&> set (#env % #contracts % at (LitAddr ethrunAddress))
             (Just (initialContract (RuntimeCode (ConcreteRuntimeCode ""))))

exec :: forall t. (VMOps t, Typeable t) => Config -> EVM t (VMResult t)
exec conf = case eqT @t @Concrete of
  Just Refl -> do
    execute <- lift (ioToST newConcreteExec)
    execute conf
  Nothing -> untilResult (exec1 conf)

-- | Reuse bytecode plans and scratch space when resuming after a query.
-- Allocate a separate executor for each concurrent interpreter.
newConcreteExec :: IO (Config -> EVM Concrete (VMResult Concrete))
newConcreteExec = do
  cache <- newProgramCache
  scratch <- newScratch
  let ignore _ () = pure ()
  pure $ \conf -> untilResult $ do
    vm <- get
    plan <- lift $ ioToST $ prepareProgram cache vm.state.code
    case plan of
      Nothing -> pure ()
      Just _ -> do
        (before, ()) <- lift $ ioToST $ runConcreteBlocks scratch plan ignore ignore vm ()
        put before
    -- A block stops immediately before an ordinary or exceptional instruction.
    exec1 conf

untilResult :: EVM t () -> EVM t (VMResult t)
untilResult step = go
  where go = gets (.result) >>= maybe (step >> go) pure

run :: (VMOps t, Typeable t) => Config -> EVM t (VM t)
run conf = exec conf >> get

execWhile :: (VM t -> Bool) -> State (VM t) Int
execWhile p = go 0
  where
    go i = do
      vm <- get
      if p vm && isNothing vm.result
        then do
          go $! (i + 1)
      else
        pure i
