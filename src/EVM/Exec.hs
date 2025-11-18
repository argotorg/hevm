module EVM.Exec where

import EVM hiding (createAddress)
import EVM.Concrete (createAddress)
import EVM.FeeSchedule (feeSchedule)
import EVM.Types

import Control.Monad.Trans.State.Strict (get, State)
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)
import Optics.Core
import Control.Monad.ST (ST, RealWorld)
import EVM.Effects (Config)
import Data.Data (Typeable)

ethrunAddress :: Addr
ethrunAddress = Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

vmForEthrunCreation :: VMOps t => ByteString -> ST RealWorld (VM t)
vmForEthrunCreation creationCode =
  (makeVm $ VMOpts
    { contract = initialContract (InitCode creationCode mempty)
    , otherContracts = []
    , calldata = mempty
    , value = Lit 0
    , baseState = EmptyBase
    , address = createAddress ethrunAddress 1
    , caller = LitAddr ethrunAddress
    , origin = LitAddr ethrunAddress
    , coinbase = LitAddr 0
    , number = Lit 0
    , timestamp = Lit 0
    , blockGaslimit = 0
    , gasprice = 0
    , prevRandao = 42069
    , gas = toGas 0xffffffffffffffff
    , gaslimit = 0xffffffffffffffff
    , baseFee = 0
    , priorityFee = 0
    , maxCodeSize = 0xffffffff
    , schedule = feeSchedule
    , chainId = 1
    , create = False
    , txAccessList = mempty
    , allowFFI = False
    , freshAddresses = 0
    , beaconRoot = 0
    }) <&> set (#env % #contracts % at (LitAddr ethrunAddress))
             (Just (initialContract (RuntimeCode (ConcreteRuntimeCode ""))))

exec :: (VMOps t, Typeable t) => Config -> EVM t (VMResult t)
exec conf = do
  vm <- get
  case vm.result of
    Nothing -> exec1 conf >> exec conf
    Just r -> pure r

run :: (VMOps t, Typeable t) => Config -> EVM t (VM t)
run conf = do
  vm <- get
  case vm.result of
    Nothing -> exec1 conf >> run conf
    Just _ -> pure vm

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
