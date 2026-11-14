module EVM.Fetch.FetchTests (tests) where

import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (execStateT, lift, liftIO)
import Data.Maybe (fromMaybe)
import Data.STRef
import Test.Tasty
import Test.Tasty.HUnit

import EVM (defaultVMOpts, makeVm, emptyContract, unknownContract)
import EVM.Effects (runApp)
import EVM.Fetch qualified as Fetch
import EVM.Types

tests :: TestTree
tests = testGroup "fetchers"
  [ testCase "local-empty-account" $
      answer (PleaseFetchContract addr EmptyBase) >>= (@?= emptyContract)
  , testCase "local-abstract-account" $
      answer (PleaseFetchContract addr AbstractBase) >>= (@?= unknownContract (LitAddr addr))
  , testCase "local-storage" $
      answer (PleaseFetchSlot addr 17) >>= (@?= 0)
  ]
  where addr = 0x123456789

-- Capture the value supplied to a query's continuation, without executing code.
answer :: ((a -> EVM Concrete ()) -> Query Concrete) -> IO a
answer query = runApp $ do
  vm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Concrete)
  ref <- liftIO $ stToIO $ newSTRef Nothing
  action <- Fetch.noRpcConcreteFetcher (query (lift . writeSTRef ref . Just))
  liftIO $ stToIO $ do
    _ <- execStateT action vm
    fromMaybe (internalError "fetcher did not invoke its continuation") <$> readSTRef ref
