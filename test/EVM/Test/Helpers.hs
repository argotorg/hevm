module EVM.Test.Helpers where

import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Control.Monad.Reader (ReaderT)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.Maybe
import Data.Text qualified as T
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Test.Tasty.HUnit

import Optics.Core hiding (pre, re, elements)
import Optics.State

import EVM
import EVM.ABI
import EVM.Exec
import EVM.Fetch qualified as Fetch
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.UnitTest (writeTrace)

testEnv :: Env
testEnv = Env { config = defaultConfig {
  dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , dumpTrace = False
  , decomposeStorage = True
  , verb = 1
  } }

assertEqualM :: (App m, Eq a, Show a, HasCallStack) => String -> a -> a -> m ()
assertEqualM a b c = liftIO $ assertEqual a b c

assertBoolM
  :: (MonadUnliftIO m, HasCallStack)
  => String -> Bool -> m ()
assertBoolM a b = liftIO $ assertBool a b

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv testEnv b

withDefaultSolver :: App m => (SolverGroup -> m a) -> m a
withDefaultSolver = withSolvers Z3 3 Nothing defMemLimit

withBitwuzlaSolver :: App m => (SolverGroup -> m a) -> m a
withBitwuzlaSolver = withSolvers Bitwuzla 3 Nothing defMemLimit

hex :: ByteString -> ByteString
hex s =
  case BS16.decodeBase16Untyped s of
    Right x -> x
    Left e -> internalError $ T.unpack e

-- | Takes a creation code and returns a vm with the result of executing the creation code
loadVM :: App m => ByteString -> m (Maybe (VM Concrete))
loadVM x = do
  vm <- liftIO $ stToIO $ vmForEthrunCreation x
  vm1 <- Stepper.interpret (Fetch.zero 0 Nothing 1024) vm Stepper.runFully
  case vm1.result of
    Just (VMSuccess (ConcreteBuf targetCode)) -> do
      let target = vm1.state.contract
      vm2 <- Stepper.interpret (Fetch.zero 0 Nothing 1024) vm1 (prepVm target targetCode)
      writeTrace vm2
      pure $ Just vm2
    _ -> pure Nothing
  where
    prepVm target targetCode = Stepper.evm $ do
      replaceCodeOfSelf (RuntimeCode $ ConcreteRuntimeCode targetCode)
      resetState
      assign (#state % #gas) 0xffffffffffffffff -- kludge
      execState (loadContract target) <$> get >>= put
      get

reachableUserAsserts :: App m => ByteString -> Maybe Sig -> m (Either [SMTCex] [Expr End])
reachableUserAsserts = checkPost (checkAssertions [0x01])

checkPost :: App m => Postcondition -> ByteString -> Maybe Sig -> m (Either [SMTCex] [Expr End])
checkPost post c sig = do
  (e, res) <- withDefaultSolver $ \s -> verifyContract s c sig [] defaultVeriOpts Nothing post
  let cexs = snd <$> mapMaybe getCex res
  case cexs of
    [] -> pure $ Right e
    cs -> pure $ Left cs

newtype Bytes = Bytes ByteString
  deriving Eq

instance Show Bytes where
  showsPrec _ (Bytes x) _ = show (BS.unpack x)

instance Arbitrary Bytes where
  arbitrary = fmap (Bytes . BS.pack) arbitrary
