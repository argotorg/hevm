-- | Running a case in hevm, concretely and symbolically
module EVM.Test.Fuzz.Hevm
  ( HevmRun(..), concreteTestVm, hevmRun, replayModel, runHevm, runSymbolic
  , symCalldataBuf, symbolicTestVm
  ) where

import Control.Monad (forM, when)
import Control.Monad.IO.Unlift
import Control.Monad.ST (ST, stToIO, RealWorld)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad.State.Strict (StateT(..), get, lift)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Optics.Core hiding (pre, elements)
import System.Timeout (timeout)
import Witch (into, unsafeInto)
import EVM (makeVm, initialContract, defaultVMOpts, exec1)
import EVM.Expr qualified as Expr
import EVM.Exec (ethrunAddress)
import EVM.Fetch qualified as Fetch
import EVM.Fetch.MockNode (Account(..))
import EVM.FeeSchedule
import EVM.Op (intToOpName)
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Transaction qualified
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Tracing (interpretWithTrace, VMTraceStep(..))
import EVM.Test.Fuzz.Program
import EVM.Test.Fuzz.Geth

-- * hevm

-- | How to set up a VM: concrete values for the concrete run, abstract ones for the symbolic run
data VMInputs = VMInputs
  { calldata :: Expr Buf
  , store :: Expr Storage
  , callvalue :: Expr EWord
  , timestamp :: Expr EWord
  }

concreteVMInputs :: Inputs -> VMInputs
concreteVMInputs i =
  VMInputs (ConcreteBuf i.calldata) (ConcreteStore i.store) (Lit i.callvalue) (Lit i.timestamp)

symCalldataBuf :: Expr Buf
symCalldataBuf = AbstractBuf "calldata"

symbolicVMInputs :: VMInputs
symbolicVMInputs = VMInputs symCalldataBuf (AbstractStore (LitAddr contractAddr) Nothing) TxValue Timestamp

-- | When fetching, only the code and balance of the contract are known up front: its storage
-- and every other account come from the mock node
mkVm :: forall t . VMOps t => Bool -> Gas t -> TestCase -> VMInputs -> ST RealWorld (VM t)
mkVm fetching gas c i = do
  let store = if fetching then ConcreteStore mempty else i.store
      contract = initialContract (RuntimeCode (ConcreteRuntimeCode (assembleItems c.prog.main)))
        & set #balance (Expr.add (Lit contractBalance) i.callvalue)
        & set #storage store
        & set #origStorage store
        & set #nonce (Just 0x48)
        & set #external fetching
      calleeContract = initialContract (RuntimeCode (ConcreteRuntimeCode (assembleItems c.prog.callee)))
        & set #nonce (Just 1)
  vm <- makeVm $ (defaultVMOpts :: VMOpts t)
    { contract = contract
    , otherContracts =
        (LitAddr ethrunAddress, initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty)))
        -- finalize pays the unused gas and the refund back to the origin
        : (LitAddr fromAddress, initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty))
            & set #balance (Lit originBalance) & set #nonce (Just 0xac))
        : if fetching then [] else
          (LitAddr calleeAddr, calleeContract)
          : [ (LitAddr a, initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty))
                & set #balance (Lit b) & set #nonce (Just (unsafeInto n))
                & set #storage (ConcreteStore st) & set #origStorage (ConcreteStore st))
            | (a, b, n, st) <- extraAccounts ]
    , calldata = (i.calldata, [])
    , value = i.callvalue
    , address = LitAddr contractAddr
    , caller = LitAddr fromAddress
    , origin = LitAddr fromAddress
    , coinbase = LitAddr coinbaseAddr
    , number = Lit c.number
    , timestamp = i.timestamp
    , gasprice = 1
    , gas = gas
    , gaslimit = unsafeInto c.gasLimit
    , blockGaslimit = unsafeInto c.gasLimit
    , prevRandao = Lit prevRandaoVal
    , baseFee = Lit 0
    , priorityFee = 1
    , maxCodeSize = 0xfffff
    , schedule = feeSchedule
    , chainId = 1
    -- only the concrete run tracks gas
    , txdataFloorGas = case i.calldata of
        ConcreteBuf cd -> EVM.Transaction.txdataFloorGas feeSchedule (mkTx c (Inputs cd mempty 0 0))
        _ -> 0
    }
  pure $ vm & set (#state % #calldata) i.calldata

data HevmRun = HevmRun
  { trace :: [VMTraceStep]
  , result :: Either EvmError ByteString
  , storage :: Map Addr (Map W256 W256)
  , logs :: [Expr Log]
  , gasUsed :: W256
  }

-- | With a node's URL, everything but the contract's code and balance is fetched from it
runHevm :: App m => SolverGroup -> Maybe Text -> TestCase -> Inputs -> m HevmRun
runHevm solvers url c i = do
  let txn = mkTx c i
      gas = unsafeInto c.gasLimit - EVM.Transaction.txGasCost feeSchedule txn
  fetcher <- case url of
    Nothing -> pure $ Fetch.oracle solvers Nothing Fetch.noRpc
    Just u -> do
      sess <- Fetch.mkSessionWithoutCache
      pure $ Fetch.oracle solvers (Just sess) (Fetch.RpcInfo (Just (Fetch.BlockNumber c.number, u)))
  vm0 <- liftIO $ stToIO $ mkVm (isJust url) gas c (concreteVMInputs i)
  (res, (vm, trace)) <- runStateT (interpretWithTrace fetcher Stepper.execFully) (vm0, [])
  pure $ hevmRun (isJust url) c i res vm trace

-- | How a concrete run ended, from its last VM
hevmRun :: Bool -> TestCase -> Inputs -> Either EvmError (Expr Buf) -> VM Concrete -> [VMTraceStep] -> HevmRun
hevmRun viaRpc c i res vm trace =
  -- slots never read or written were never fetched
  let pre a = if viaRpc then (.storage) (Map.findWithDefault (Account mempty 0 0 mempty) a (preState c i)) else mempty
      storageOf a = case (.storage) <$> Map.lookup (LitAddr a) vm.env.contracts of
        Just (ConcreteStore s) -> nonZero (Map.union s (pre a))
        Nothing -> nonZero (pre a)
        Just s -> internalError $ "non-concrete storage in concrete run: " <> show s
      out = case res of
        Right (ConcreteBuf b) -> Right b
        Right b -> internalError $ "non-concrete return data: " <> show b
        Left e -> Left e
      stores = Map.fromList [(a, storageOf a) | a <- [contractAddr, calleeAddr]]
      -- the run starts after the gas purchase, so the origin only gets the unused gas back
      gasUsed = case (.balance) <$> Map.lookup (LitAddr fromAddress) vm.env.contracts of
        Just (Lit b) -> unsafeInto c.gasLimit - (b - originBalance)
        b -> internalError $ "origin balance: " <> show b
  in HevmRun trace out stores (reverse vm.logs) gasUsed

-- | The VMs 'checkCase' starts from, for other fuzzers to run
concreteTestVm :: TestCase -> ST RealWorld (VM Concrete)
concreteTestVm c = mkVm False gas c (concreteVMInputs c.inputs)
  where gas = unsafeInto c.gasLimit - EVM.Transaction.txGasCost feeSchedule (mkTx c c.inputs)

symbolicTestVm :: TestCase -> ST RealWorld (VM Symbolic)
symbolicTestVm c = set #constraints symProps <$> mkVm False () c symbolicVMInputs

symIterConf :: IterConfig
symIterConf = IterConfig { maxIter = Just 6, askSmtIters = 1, loopHeuristic = Naive }

-- | Bounds that keep solver models replayable in geth
symProps :: [Prop]
symProps =
  [ PLEq (BufLength symCalldataBuf) (Lit 128)
  , PLEq TxValue (Lit 1000)
  , PLEq Timestamp (Lit (2 ^ (40 :: Int)))
  , PGEq Timestamp (Lit 1)
  ]

-- | Replays a model of the leaf as `hevm symbolic` does: Right True if the
-- concrete run fails exactly when the leaf does
replayModel :: App m => TestCase -> Expr End -> SMTCex -> m (Either Text Bool)
replayModel c leaf cex = do
  vm0 <- liftIO $ stToIO $ mkVm False () c symbolicVMInputs
  withSolvers Z3 1 (Just 10) defMemLimit $ \solvers ->
    replaySymCex solvers (\_ e -> PBool (isFailure e /= isFailure leaf)) (vm0 & set #constraints symProps) leaf cex
  where
    isFailure = \case Failure {} -> True; _ -> False

-- | The leaves, the opcodes that ran with a non-literal operand, and the
-- number of forward jumps merged
runSymbolic :: App m => SolverGroup -> TestCase -> m (Maybe ([Expr End], Set String, Int))
runSymbolic solvers c = do
  conf <- readConfig
  vm0 <- liftIO $ stToIO $ mkVm False () c symbolicVMInputs
  ref <- liftIO $ newIORef mempty
  merges <- liftIO $ newIORef 0
  let vm = vm0 & set #constraints symProps
  leaves <- withRunInIO $ \runInIO ->
    timeout 60_000_000 $ runInIO $
      interpret (Fetch.oracle solvers Nothing Fetch.noRpc) symIterConf vm (recording conf ref merges) noopPathHandler
  forM leaves $ \ls -> (ls,,) <$> liftIO (readIORef ref) <*> liftIO (readIORef merges)

-- | 'runExpr', stepping one opcode at a time to record those with a non-literal operand.
-- Loops on concrete conditions only end when gas runs out, which the symbolic
-- run does not track, so a path is cut short after 'maxSteps'.
recording :: Config -> IORef (Set String) -> IORef Int -> Stepper.Stepper Symbolic (Expr End)
recording conf ref merges = loop (0 :: Int)
  where
    maxSteps = 20000
    loop n = do
      vm <- Stepper.evm get
      case vm.result of
        Nothing
          | n >= maxSteps -> pure $ Partial vm.constraints (TraceContext mempty mempty mempty)
                                      (MaxIterationsReached vm.state.pc vm.state.contract)
          | otherwise -> Stepper.evm (record vm >> exec1 conf >> countMerge vm) >> loop (n + 1)
        Just (HandleEffect (Query q)) -> Stepper.wait q >> loop n
        Just (HandleEffect (Branch ctx)) -> Stepper.fork ctx >> loop n
        Just _ -> runExpr
    record vm = case vm.state.code of
      RuntimeCode (ConcreteRuntimeCode bs) | vm.state.pc < BS.length bs -> do
        let name = intToOpName (into (BS.index bs vm.state.pc))
            isLit = \case Lit _ -> True; _ -> False
        when (any (not . isLit) (take (Map.findWithDefault 0 name opPops) vm.state.stack)) $
          lift $ unsafeIOToST $ atomicModifyIORef' ref (\x -> (Set.insert name x, ()))
      _ -> pure ()
    -- a symbolic JUMPI that lands on its target without forking was merged
    countMerge vm = case (vm.state.code, vm.state.stack) of
      (RuntimeCode (ConcreteRuntimeCode bs), Lit t : cond : _)
        | vm.state.pc < BS.length bs, BS.index bs vm.state.pc == 0x57
        , t < 0x10000, unsafeInto t > vm.state.pc
        , isNothing (Expr.maybeLitWordSimp (Expr.simplify cond)) -> do
            vm' <- get
            when (isNothing vm'.result && vm'.state.pc == unsafeInto t) $
              lift $ unsafeIOToST $ atomicModifyIORef' merges (\x -> (x + 1, ()))
      _ -> pure ()
