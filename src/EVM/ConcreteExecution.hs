module EVM.ConcreteExecution (
exec,
execBytecode,
RuntimeCode(..),
CallData(..),
CallValue(..),
ExecutionResult,
VMSnapshot(..),
VMResult(..),
Transaction(..),
BlockHeader(..),
ExecutionContext(..),
Account(..),
Wei(..),
Gas(..),
Nonce(..),
Accounts,
Storage
) where

import Control.Monad (forM, when, unless, ap, liftM)
import Control.Monad.ST (ST, runST)
import Data.Bits ((.|.), (.&.), (.^.), shiftR, shiftL, testBit, complement, bit)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8 (pack)
import Data.DoubleWord (Int256)
import Data.Map.Strict qualified as StrictMap
import Data.Maybe (fromMaybe, isJust, fromJust, isNothing)
import Data.Set qualified as Set
import Data.STRef
import Data.Vector.Unboxed qualified as UVec
import Data.Vector.Unboxed.Mutable qualified as UMVec
import Data.Vector.Mutable qualified as MVec
import Data.Vector qualified as Vec
import Data.Word (Word8, Word64)
import Prelude hiding (exponent)

import EVM (allButOne64th, ceilDiv, log2)
import EVM.RLP
import EVM.Types (
  W256(..),
  W64(..),
  Word512,
  internalError,
  GenericOp(..),
  ByteStringS(..),
  word,
  keccak',
  toWord64,
  constructWord256FromWords,
  deconstructWord256ToWords,
  truncateToAddr,
  Addr(..),
  FunctionSelector,
  word256Bytes,
  word160Bytes
  )
import EVM.Op (getOp)
import EVM.FeeSchedule

-- import Debug.Trace qualified (traceM, trace)
-- import Numeric (showHex)


type VMWord = W256
type Data = BS.ByteString
newtype RuntimeCode = RuntimeCode {code :: Data}
data Instruction = GenericInst !(GenericOp Word8) | Push !Word8 !VMWord
newtype Instructions = Instructions (Vec.Vector Instruction)
type MStack s = MVec.MVector s VMWord
newtype CallData = CallData {calldata :: Data}
newtype CallValue = CallValue {callvalue :: W256}
type Storage = StrictMap.Map W256 W256
type Accounts = StrictMap.Map Addr Account
newtype Wei = Wei {value :: W256}
  deriving (Num, Eq, Ord)
newtype Nonce = Nonce {value :: W64}
  deriving (Num, Eq, Ord)

newtype Gas = Gas {value :: Word64}
  deriving (Num, Eq, Ord, Show)
data Account = Account {
  accCode :: RuntimeCode,
  accStorage :: Storage,
  accBalance :: Wei,
  accNonce :: Nonce
}

emptyAccount :: Account
emptyAccount = Account (RuntimeCode "") mempty (Wei 0) (Nonce 0)

instance Show Instruction where
    show (GenericInst op) =
        show op

    show (Push n w) =
        "PUSH" ++ show n ++ " " ++ show w


data VMSnapshot = VMSnapshot
  {
    code         :: RuntimeCode
  , pc           :: Int
  , stack        :: [W256]
  , memory :: BS.ByteString
  , worldState :: Accounts
  }

freezeVM :: MVM s -> ST s VMSnapshot
freezeVM vm = do
  frame <- getCurrentFrame vm
  stack <- freezeStack frame
  pc <- freezePC frame
  memory <- freezeMemory frame
  let accounts = frame.state.accounts
  pure $ VMSnapshot frame.context.code pc stack memory accounts

  where
    freezePC frame = readSTRef frame.state.pcRef
    freezeStack frame = do
      stackEnd <- readSTRef frame.state.spRef
      let vec = frame.state.stack
      forM [0 .. stackEnd - 1] (MVec.read vec)
    freezeMemory frame = do
      let (Memory memRef sizeRef) = frame.state.memory
      vec <- readSTRef memRef
      let vecsize = UMVec.length vec
      logicalSize <- readSTRef sizeRef
      let logicalSizeInt = fromIntegral logicalSize
      frozen <- UVec.freeze $ if logicalSizeInt > vecsize then vec else (UMVec.slice 0 logicalSizeInt) vec
      let bs = BS.pack (UVec.toList frozen) 
      pure $ if logicalSizeInt > vecsize then bs <> (BS.replicate (logicalSizeInt - vecsize) 0) else bs



type ExecutionResult = (VMResult, VMSnapshot)

data ReturnInfo = ReturnInfo {
  dataOffset :: VMWord,
  dataSize :: VMWord,
  stackValueOnSuccess :: VMWord
}

data MFrameState s = MFrameState {
  pcRef :: STRef s Int,
  stack :: MStack s,
  spRef :: STRef s Int,  -- stack pointer (beyond stack top slot)
  memory :: Memory s,
  accounts :: Accounts,
  gasRemainingRef :: STRef s Gas,
  gasRefundedRef :: STRef s Gas,
  retInfoRef :: STRef s (Maybe ReturnInfo)
}

newMFrameState :: Accounts -> Gas -> ST s (MFrameState s)
newMFrameState accounts gas = do
  pcRef <- newSTRef 0
  stackVec <- MVec.new 1024
  spRef <- newSTRef 0
  memory <- newMemory
  gasRemaining <- newSTRef gas
  gasRefunded <- newSTRef $ Gas 0
  retInfoRef <- newSTRef Nothing
  pure $ MFrameState pcRef stackVec spRef memory accounts gasRemaining gasRefunded retInfoRef

data ContextType = INIT | RUNTIME
  deriving Eq

data FrameContext = FrameContext {
  contextType :: ContextType,
  code :: RuntimeCode,
  instructions :: Instructions,
  callData :: CallData,
  callValue :: CallValue,
  accountsSnapshot :: Accounts,
  codeAddress :: Addr,
  storageAddress :: Addr,
  callerAddress :: Addr,
  isStatic :: Bool
}


data MFrame s = MFrame {
  context :: FrameContext,
  state :: MFrameState s
}

data MVM s = MVM
  {
    current :: STRef s (MFrame s),
    frames :: STRef s [MFrame s],
    fees :: FeeSchedule Word64,
    executionContext :: ExecutionContext,
    txsubstate :: STRef s TxSubState,
    terminationFlagRef :: TerminationFlag s
  }

pushFrame :: MVM s -> MFrame s -> ST s ()
pushFrame vm newFrame = do
  current <- readSTRef (vm.current)
  modifySTRef' (vm.frames) (current :)
  writeSTRef (vm.current) newFrame

data Transaction = Transaction {
  from :: Addr,
  to :: Maybe Addr,
  value :: CallValue,
  txdata :: CallData,
  gasLimit :: Gas,
  gasPrice :: W256,
  priorityFee :: W256
}

data BlockHeader = BlockHeader {
  coinbase :: Addr,
  timestamp :: W256,
  number :: W256,
  gaslimit :: Gas,
  prevRandao :: W256,
  baseFee :: W256
}

data ExecutionContext = ExecutionContext {
  transaction :: Transaction,
  blockHeader :: BlockHeader
}

newtype TxSubState = TxSubState {
  accessedAddresses :: StrictMap.Map Addr (Set.Set W256)
}

data EvmError
  = BalanceTooLow VMWord VMWord
  | UnrecognizedOpcode Word8
  | SelfDestruction
  | StackUnderrun
  | BadJumpDestination
  | Revert Data
  | OutOfGas Word64 Word64
  | StackLimitExceeded
  | IllegalOverflow
  | StateChangeWhileStatic
  | InvalidMemoryAccess
  | CallDepthLimitReached
  | MaxCodeSizeExceeded VMWord VMWord
  | MaxInitCodeSizeExceeded VMWord VMWord
  | InvalidFormat
  | PrecompileFailure
  | NonexistentPrecompile Addr
  | ReturnDataOutOfBounds
  | NonceOverflow
  | BadCheatCode String FunctionSelector
  | NonexistentFork Int
  deriving (Show, Eq, Ord)


data VMResult where
  VMFailure :: EvmError -> VMResult        -- ^ An operation failed
  VMSuccess :: Data -> VMResult            -- ^ Reached STOP, RETURN, or end-of-code

data FrameResult = FrameSucceeded Data | FrameReverted Data | FrameErrored EvmError
  deriving Show

frameToVMResult :: FrameResult -> VMResult
frameToVMResult (FrameSucceeded bs) = VMSuccess bs
frameToVMResult (FrameErrored err) = VMFailure err
frameToVMResult (FrameReverted bs) = VMFailure (Revert bs)


type TerminationFlag s = STRef s (Maybe FrameResult)
-- An operation in VM that either succeeds (and computes a result) or fails
newtype Step s a = Step (TerminationFlag s -> ST s a)

instance Functor (Step s) where
  fmap = liftM

instance Applicative (Step s) where
  pure x = Step $ \_ -> pure x
  (<*>) = ap
  (*>) :: Step s a -> Step s b -> Step s b
  Step sa *> Step sb = Step $ \flagRef -> do
      _ <- sa flagRef
      maybeResult <- readSTRef flagRef
      case maybeResult of
        Nothing -> sb flagRef
        Just _  -> pure (undefined)

instance Monad (Step s) where
  (>>=) :: Step s a -> (a -> Step s b) -> Step s b
  Step sa >>= f = Step $ \flagRef -> do
    a <- sa flagRef
    maybeResult <- readSTRef flagRef
    case maybeResult of
      Nothing -> let (Step sb) = (f a) in sb flagRef
      Just _ -> pure (undefined)
  (>>) = (*>)

liftST :: ST s a -> Step s a
liftST st = Step $ const st

stackUnderflow :: Step s a
stackUnderflow = vmError StackUnderrun

vmError :: EvmError -> Step s a
vmError err = stop $ FrameErrored err

vmError' :: MVM s -> EvmError -> ST s ()
vmError' vm err = stop' vm $ FrameErrored err


stop :: FrameResult -> Step s a
stop result = Step $ \resultRef -> writeSTRef resultRef (Just result) >> pure (internalError "Should never be executed")

stop' :: MVM s -> FrameResult -> ST s ()
stop' vm result = writeSTRef vm.terminationFlagRef (Just result)

checkNotStaticContext :: MVM s -> Step s ()
checkNotStaticContext vm = do
  frame <- liftST $ getCurrentFrame vm
  when (frame.context.isStatic) $ vmError StateChangeWhileStatic

isCreate :: Transaction -> Bool
isCreate tx = isNothing tx.to

execBytecode :: RuntimeCode -> CallData -> CallValue -> ExecutionResult
execBytecode code calldata value = exec executionContext worldState
  where
    artificialAddress = Addr 0xdeadbeef
    artificialAccount = Account code mempty (Wei (fromIntegral (maxBound :: Word64))) (Nonce 0)
    worldState = StrictMap.singleton artificialAddress artificialAccount
    transaction = Transaction (Addr 0) (Just artificialAddress ) value calldata (Gas maxBound) 0 0
    blockHeader = BlockHeader (Addr 0) 0 0 (Gas maxBound) 0 0
    executionContext = ExecutionContext transaction blockHeader

exec :: ExecutionContext -> Accounts -> ExecutionResult
exec executionContext accounts = runST $ do
  let tx = executionContext.transaction
      accountsAfterInitiatingTransaction = StrictMap.adjust (payForInitiatingTransaction tx) tx.from accounts
      (updatedAccounts, targetAddress) = initTransaction tx accountsAfterInitiatingTransaction
      availableGas = tx.gasLimit - (Gas $ txGasCost feeSchedule tx)
      targetAccount = fromMaybe (internalError "Target address not present in the known accounts") (StrictMap.lookup targetAddress updatedAccounts)
      contextType = if isCreate tx then INIT else RUNTIME
  -- let Transaction from _ (CallValue value) (CallData calldata) gasLimit gasPrice priorityFee = executionContext.transaction
  -- let RuntimeCode bs = targetAccount.accCode
  -- Debug.Trace.traceM $ "\nNew transaction!\n"
  -- Debug.Trace.traceM $ "From: " <> (show from)
  -- Debug.Trace.traceM $ "Value: " <> (show value)
  -- Debug.Trace.traceM $ "Calldata: " <> (show $ ByteStringS calldata)
  -- Debug.Trace.traceM $ "Code: " <> (show $ ByteStringS bs)
  -- Debug.Trace.traceM $ "Gas limit: " <> (show gasLimit)
  -- Debug.Trace.traceM $ "Gas price: " <> (show gasPrice)
  -- Debug.Trace.traceM $ "Priority fee: " <> (show priorityFee)
  -- Debug.Trace.traceM $ "Target address: " <> (show targetAddress)
  initialFrame <- mkFrame contextType tx.from targetAddress tx.value tx.txdata targetAccount.accCode availableGas accountsAfterInitiatingTransaction
  let frameAfterAccountsUpdate = initialFrame {state = initialFrame.state {accounts = updatedAccounts}}
  currentRef <- newSTRef frameAfterAccountsUpdate
  framesRef <- newSTRef []
  let warmAddresses = [tx.from, targetAddress, executionContext.blockHeader.coinbase] ++ [1..9]
        -- TODO: ++ (Map.keys txaccessList)
  substateRef <- newSTRef (TxSubState $ StrictMap.fromList [(address, mempty) | address <- warmAddresses])
  terminationFlagRef <- newSTRef Nothing
  let vm = MVM currentRef framesRef feeSchedule executionContext substateRef terminationFlagRef
  runLoop vm

  where
    initTransaction :: Transaction -> Accounts -> (Accounts, Addr)
    initTransaction tx accounts' =
      let (afterNewAccountCreation, targetAddress) = if isCreate tx then (createNewAccount tx accounts') else (accounts', fromJust tx.to)
          afterValueTransfer = uncheckedTransfer afterNewAccountCreation tx.from targetAddress tx.value
      in (afterValueTransfer, targetAddress)
    payForInitiatingTransaction tx account =
      let
        (Wei balance) = account.accBalance
        (Gas limit) = tx.gasLimit
        gasCost = tx.gasPrice * (fromIntegral limit)
        updatedBalance = Wei $ balance - gasCost -- TODO: Check if the balance is sufficient to execute Tx
        updatedNonce = account.accNonce + 1
      in
        account {accBalance = updatedBalance, accNonce = updatedNonce}

    createNewAccount tx accounts' =
      let senderAccount = fromJust $ StrictMap.lookup tx.from accounts'
          newAddress = createAddress tx.from (senderAccount.accNonce - 1) -- NOTE: We increment sender's nonce before we get here, so we need to subtract 1
      in (StrictMap.insert newAddress (emptyAccount {accNonce = 1, accCode = (asCode tx.txdata)}) accounts', newAddress)
    asCode (CallData txdata) = RuntimeCode txdata

    mkFrame :: ContextType -> Addr -> Addr -> CallValue -> CallData -> RuntimeCode -> Gas -> Accounts -> ST s (MFrame s)
    mkFrame contextType from to callvalue calldata code availableGas accounts' = do
      freshState <- newMFrameState accounts' availableGas
      let ctx = FrameContext contextType code (parseByteCode code) calldata callvalue accounts' to to from False
      pure $ MFrame ctx freshState


runLoop :: MVM s -> ST s ExecutionResult
runLoop vm = do
  maybeResult <- stepVM vm
  if (isJust maybeResult) then do
    let result = fromJust maybeResult
    finalizeTransaction vm result
    snapshot <- freezeVM vm
    pure (result, snapshot)
  else runLoop vm

  where
    finalizeTransaction :: MVM s -> VMResult -> ST s ()
    finalizeTransaction vm result = do
      let Gas limit = vm.executionContext.transaction.gasLimit
          gasPrice = vm.executionContext.transaction.gasPrice
      frame <- getCurrentFrame vm
      Gas remaining <- getAvailableGas frame
      -- Debug.Trace.traceM $ "Remaining gas at the end of transaction:" <> show remaining
      case result of
        VMFailure _ -> do
          let weiToRefund = Wei $ (fromIntegral remaining) * gasPrice
              addTo account = account {accBalance = account.accBalance + weiToRefund}
              accounts = frame.context.accountsSnapshot
              updatedAccounts = StrictMap.adjust addTo vm.executionContext.transaction.from accounts
              updatedFrame = frame {state = frame.state {accounts = updatedAccounts}}
          writeSTRef vm.current updatedFrame
        VMSuccess _ -> do
          Gas refunds <- getGasRefund frame
          let gasUsed = limit - remaining
              refundCap = gasUsed `div` 5
              finalRefund = Prelude.min refunds refundCap

              toRefund = remaining + finalRefund
              weiToRefund = Wei $ (fromIntegral toRefund) * gasPrice
              minerPay = Wei $ vm.executionContext.transaction.priorityFee * (fromIntegral gasUsed)

          let accounts = frame.state.accounts
              addTo account = account {accBalance = account.accBalance + weiToRefund}
              updatedAccounts = StrictMap.alter (rewardMiner minerPay) vm.executionContext.blockHeader.coinbase $ StrictMap.adjust addTo vm.executionContext.transaction.from accounts
              updatedFrame = frame {state = frame.state {accounts = updatedAccounts}}
          writeSTRef vm.current updatedFrame

    rewardMiner reward maybeAccount =
      case maybeAccount of
        Nothing -> Just $ emptyAccount {accBalance = reward}
        Just account -> Just $ account {accBalance = account.accBalance + reward}

stepVM :: MVM s -> ST s (Maybe VMResult)
stepVM vm = do
  let terminationFlagRef = vm.terminationFlagRef
  let (Step stAction) = runStep vm
  _ <- stAction terminationFlagRef
  maybeFrameResult <- readSTRef terminationFlagRef
  case maybeFrameResult of
    Nothing -> pure Nothing
    Just frameResult -> finishFrame vm frameResult

  where
  finishFrame :: MVM s -> FrameResult -> ST s (Maybe VMResult)
  finishFrame vm result = do
    frames <- readSTRef vm.frames
    finalizeInitIfSucceeded
    
    case frames of
      [] -> do
        case result of
          FrameErrored _ -> burnRemainingGas
          _ -> pure ()
        pure $ Just $ frameToVMResult result

      nextFrame:rest -> do
        finishingFrame <- getCurrentFrame vm
        let accounts = finishingFrame.state.accounts
        unspentGas <- getAvailableGas finishingFrame
        gasRefund <- getGasRefund finishingFrame
        (ReturnInfo retOffset retSize stackRetValue) <- getReturnInfo finishingFrame
        writeSTRef vm.current nextFrame
        writeSTRef vm.frames rest
        writeSTRef vm.terminationFlagRef Nothing
        case result of
          FrameSucceeded returnData -> do
            currentFrame <- getCurrentFrame vm
            unburn' currentFrame unspentGas
            addGasRefund currentFrame gasRefund
            let calleeContextType = finishingFrame.context.contextType
            let updatedFrame = currentFrame {state = currentFrame.state {accounts = accounts}}
            writeSTRef vm.current updatedFrame
            when (calleeContextType == RUNTIME) $ do 
              memory <- getMemory vm
              writeMemory memory (fromIntegral retOffset) (BS.take (fromIntegral retSize) returnData)
            uncheckedPush vm stackRetValue -- We can use uncheckedPush because call must have removed some arguments from the stack, so there is space

          FrameReverted returnData -> do
            currentFrame <- getCurrentFrame vm
            unburn' currentFrame unspentGas
            memory <- getMemory vm
            writeMemory memory (fromIntegral retOffset) (BS.take (fromIntegral retSize) returnData)
            uncheckedPush vm 0

          FrameErrored _ -> do
            uncheckedPush vm 0
        pure Nothing
    
    where
      burnRemainingGas = do
        frame <- getCurrentFrame vm
        writeSTRef frame.state.gasRemainingRef 0

      finalizeInitIfSucceeded = do
        finishingFrame <- getCurrentFrame vm
        let accounts = finishingFrame.state.accounts
        when (finishingFrame.context.contextType == INIT) $ do
          case result of
            FrameSucceeded returnData -> writeSTRef vm.current finishingFrame {state = finishingFrame.state {accounts = StrictMap.adjust (\acc -> acc{accCode = RuntimeCode returnData}) finishingFrame.context.codeAddress accounts}}
            _ -> pure ()


runStep :: MVM s -> Step s ()
runStep vm = do
  instruction <- liftST $ do
    pc <- readPC vm
    advancePC vm 1
    inst <- getInstruction vm pc
    -- Debug.Trace.traceM ("Executing op " <> (show inst))
    -- Debug.Trace.traceM ("PC is " <> (showHex pc ""))
    burnStaticGas vm inst
    pure inst
  -- frame <- liftST $ getCurrentFrame vm
  -- Gas gas <- liftST $ readSTRef frame.state.gasRemainingRef
  -- Debug.Trace.traceM ("Remaining gas is " <> (show gas))
  case instruction of
    GenericInst op -> case op of
      OpStop -> haltExecution vm
      OpReturn -> stepReturn vm
      OpRevert -> stepRevert vm
      OpAdd -> {-# SCC "OpAdd" #-} binOp vm (+)
      OpMul -> binOp vm (*)
      OpSub -> binOp vm (-)
      OpMod -> stepMod vm
      OpSmod -> stepSMod vm
      OpDiv -> stepDiv vm
      OpSdiv -> stepSDiv vm
      OpAddmod -> stepAddMod vm
      OpMulmod -> stepMulMod vm
      OpExp -> {-# SCC "stepExp" #-} stepExp vm
      OpAnd -> binOp vm (.&.)
      OpOr -> binOp vm (.|.)
      OpXor -> binOp vm (.^.)
      OpNot -> stepNot vm
      OpByte -> stepByte vm
      OpShr -> stepShr vm;
      OpShl -> stepShl vm
      OpSar -> stepSar vm
      OpSignextend -> stepSignExtend vm
      OpPush0 -> push vm 0
      OpPush _ -> internalError "PushN is handled in a special way"
      OpPop -> {-# SCC "OpPop" #-} do _ <- pop vm; pure ()
      OpDup n -> {-# SCC "OpDupN" #-} stepDupN vm n
      OpSwap n -> {-# SCC "OpSwapN" #-} stepSwapN vm n
      OpLt -> stepLt vm
      OpGt -> stepGt vm
      OpSlt -> stepSLt vm
      OpSgt -> stepSGt vm
      OpEq -> stepEq vm
      OpIszero -> {-# SCC "OpIsZero" #-} stepIsZero vm
      OpJump -> {-# SCC "OpJump" #-} stepJump vm
      OpJumpi -> {-# SCC "OpJumpI" #-} stepJumpI vm
      OpJumpdest -> pure ()
      OpMsize -> stepMSize vm
      OpMload -> stepMLoad vm
      OpMstore -> stepMStore vm
      OpMstore8 -> stepMStore8 vm
      OpMcopy -> stepMCopy vm
      OpSload -> stepSLoad vm
      OpSstore -> stepSStore vm
      OpCallvalue -> stepCallValue vm
      OpCalldataload -> stepCallDataLoad vm
      OpCalldatasize -> stepCallDataSize vm
      OpCalldatacopy -> stepCallDataCopy vm
      OpCall -> stepCall vm
      OpCallcode -> stepCallCode vm
      OpDelegatecall -> stepDelegateCall vm
      OpStaticcall -> stepStaticCall vm
      OpSha3 -> stepKeccak vm
      OpGas -> stepGas vm
      OpBlockhash -> stepBlockHash vm
      OpCoinbase -> stepCoinBase vm
      OpTimestamp -> stepTimeStamp vm
      OpNumber -> stepNumber vm
      OpPrevRandao -> stepPrevRandao vm
      OpGaslimit -> stepGasLimit vm
      OpAddress -> stepAddress vm
      OpBalance -> stepBalance vm
      OpCaller -> stepCaller vm
      OpOrigin -> stepOrigin vm
      OpCodesize -> stepCodeSize vm
      OpCodecopy -> stepCodeCopy vm
      OpGasprice -> stepGasPrice vm
      OpExtcodesize -> stepExtCodeSize vm
      OpExtcodecopy -> stepExtCodeCopy vm
      OpPc -> stepPC vm
      OpLog n -> stepLog vm n
      OpCreate -> stepCreate vm
      OpCreate2 -> stepCreate2 vm
      OpUnknown xxx -> vmError $ UnrecognizedOpcode xxx
      _ -> internalError ("Unknown opcode: " ++ show op)
    Push n payload -> stepPushN vm n payload
  where
    binOp vm' f = do
      x <- pop vm'
      y <- pop vm'
      push vm' (x `f` y)

stepPushN :: MVM s -> Word8 -> VMWord -> Step s ()
stepPushN vm n value = {-# SCC "PushN" #-} do
  push vm value
  liftST $ advancePC vm (fromIntegral n)

stepDupN :: MVM s -> Word8 -> Step s ()
stepDupN vm n = do
  val <- stackSlot vm (n - 1)
  push vm val

stepSwapN :: MVM s -> Word8 -> Step s ()
stepSwapN vm n = do
  topVal <- stackSlot vm 0
  otherVal <- stackSlot vm n
  stackPointer <- liftST $ getStackPointer vm
  stack <- liftST $ getStack vm
  let topSlot = stackPointer - 1
  let otherSlot = topSlot - (fromIntegral n)
  liftST $ MVec.write stack topSlot otherVal
  liftST $ MVec.write stack otherSlot topVal

stepSLt :: MVM s -> Step s ()
stepSLt vm = comparison vm slt
  where
    slt x y =
      let sx, sy :: Int256
          sx = fromIntegral x
          sy = fromIntegral y
      in if sx < sy then 1 else 0

stepSGt :: MVM s -> Step s ()
stepSGt vm = comparison vm sgt
  where
    sgt x y =
      let sx, sy :: Int256
          sx = fromIntegral x
          sy = fromIntegral y
      in if sx > sy then 1 else 0

stepLt :: MVM s -> Step s ()
stepLt vm = comparison vm (\x y -> if x < y then 1 else 0)

stepGt :: MVM s -> Step s ()
stepGt vm = comparison vm (\x y -> if x > y then 1 else 0)

stepEq :: MVM s -> Step s ()
stepEq vm = comparison vm (\x y -> if x == y then 1 else 0)

stepIsZero :: MVM s -> Step s ()
stepIsZero vm = do
  current <- pop vm
  let val = if current == 0 then 1 else 0
  push vm val


comparison :: MVM s -> (VMWord -> VMWord -> VMWord) -> Step s ()
comparison vm op = {-# SCC "Comparison" #-} do
  lhs <- pop vm
  rhs <- pop vm
  push vm (op lhs rhs)

-- top slot = 0, one below is 1, and so on
stackSlot :: MVM s -> Word8 -> Step s VMWord
stackSlot vm n = do
  stackPointer <- liftST $ getStackPointer vm
  stack <- liftST $ getStack vm
  let slotPointer = stackPointer - (fromIntegral (n + 1))
  if slotPointer < 0
    then stackUnderflow
    else liftST $ MVec.read stack slotPointer

push :: MVM s -> VMWord -> Step s ()
push vm val = do
  sp <- liftST $ getStackPointer vm
  if sp >= 1024
    then vmError StackLimitExceeded
    else liftST $ do
      stack <- getStack vm
      MVec.write stack sp val
      let !sp' = sp + 1
      writeStackPointer vm sp'

uncheckedPush :: MVM s -> VMWord -> ST s ()
uncheckedPush vm val = do
  frame <- getCurrentFrame vm
  sp <- readSTRef frame.state.spRef
  when (sp >= 1024) $ internalError "Stack overflow in uncheckedPush!"
  let stack = frame.state.stack
  MVec.write stack sp val
  let !sp' = sp + 1
  writeSTRef frame.state.spRef sp'

pop :: MVM s -> Step s VMWord
pop vm = {-# SCC "Pop" #-} do
  sp <- liftST $ getStackPointer vm
  if sp <= 0
    then stackUnderflow
    else liftST $ do
      stack <- getStack vm
      let !sp' = sp - 1
      writeStackPointer vm sp'
      MVec.read stack sp'

stepMod :: MVM s -> Step s ()
stepMod vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let res = if denumerator == 0 then 0 else numerator `Prelude.mod` denumerator
  push vm res

stepSMod :: MVM s -> Step s ()
stepSMod vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let snum, sden :: Int256
      snum = fromIntegral numerator
      sden = fromIntegral denumerator
  let res = if denumerator == 0 then 0 else fromIntegral (snum `rem` sden)
  push vm res


stepDiv :: MVM s -> Step s ()
stepDiv vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let res = if denumerator == 0 then 0 else numerator `Prelude.div` denumerator
  push vm res

stepSDiv :: MVM s -> Step s ()
stepSDiv vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let snum, sden :: Int256
      snum = fromIntegral numerator
      sden = fromIntegral denumerator
  let res = if denumerator == 0 then 0 else fromIntegral (snum `quot` sden)
  push vm res

stepAddMod :: MVM s -> Step s ()
stepAddMod vm = do
  a <- pop vm
  b <- pop vm
  n <- pop vm
  let res = if n == 0 then 0 else fromIntegral $ (((fromIntegral a) :: Word512) + (fromIntegral b)) `Prelude.mod` (fromIntegral n)
  push vm res

stepMulMod :: MVM s -> Step s ()
stepMulMod vm = do
  a <- pop vm
  b <- pop vm
  n <- pop vm
  let res = if n == 0 then 0 else fromIntegral $ (((fromIntegral a) :: Word512) * (fromIntegral b)) `Prelude.mod` (fromIntegral n)
  push vm res

stepExp :: MVM s -> Step s ()
stepExp vm = do
  base <- pop vm
  exponent <- pop vm
  unless (exponent == 0) $ liftST $ burn vm (extraExpGasCost exponent)
  let res = pow256 base exponent
  push vm res

pow256 :: W256 -> W256 -> W256
pow256 base exponent = go base exponent 1
  where
    go !b !e !acc
      | e == 0 = acc
      | testBit e 0 = go (b*b) (e `shiftR` 1) (acc*b)
      | otherwise   = go (b*b) (e `shiftR` 1) acc

stepNot :: MVM s -> Step s ()
stepNot vm = do
  arg <- pop vm
  push vm (complement arg)

capAsWord64 :: W256 -> Word64
capAsWord64 w256 = case deconstructWord256ToWords w256 of
  (0, 0, 0, w64) -> w64
  _ -> maxBound

capAsInt :: Word64 -> Int
capAsInt w64 = if w64 >= (fromIntegral (maxBound :: Int)) then (maxBound :: Int) else (fromIntegral w64)


stepByte :: MVM s -> Step s ()
stepByte vm = do
  byteOffset <- pop vm
  value <- pop vm
  let offset64 :: Word64 = capAsWord64 byteOffset
      result = if offset64 >= 32 then 0 else
                let shift = (31 - fromIntegral offset64) * 8
                in (value `shiftR` shift) .&. 0xFF
  push vm result

stepShr :: MVM s -> Step s ()
stepShr vm = do
  shift <- pop vm
  value <- pop vm
  let shifted = if shift > 255 then 0 else value `shiftR` (fromIntegral shift)
  push vm shifted

stepShl :: MVM s -> Step s ()
stepShl vm = do
  shift <- pop vm
  value <- pop vm
  let shifted = if shift > 255 then 0 else value `shiftL` (fromIntegral shift)
  push vm shifted

stepSar :: MVM s -> Step s ()
stepSar vm = do
  shift <- pop vm
  value <- pop vm
  let shift64 = capAsWord64 shift
      msb = testBit value 255
      asSigned = fromIntegral value :: Int256
      shifted = if shift64 >= 255 then
                if msb then maxBound else 0
              else
                fromIntegral $ shiftR asSigned (fromIntegral shift64)
  push vm shifted

stepSignExtend :: MVM s -> Step s ()
stepSignExtend vm = do
  byteIndex <- pop vm
  value <- pop vm
  let extended = case deconstructWord256ToWords byteIndex of
                  (0,0,0, byteIndexW64) ->
                    if byteIndexW64 >= 32 then value
                    else let signBit = fromIntegral $ byteIndexW64 * 8 + 7 in
                        if testBit value signBit
                        then value .|. complement (bit signBit - 1)
                        else value .&. (bit signBit - 1)
                  _ -> value
  push vm extended

advancePC :: MVM s -> Int -> ST s ()
advancePC vm n = do
  current <- readSTRef vm.current
  modifySTRef' (current.state.pcRef) (+ n)

readPC :: MVM s -> ST s Int
readPC vm = do
  current <- readSTRef vm.current
  readSTRef current.state.pcRef


writePC :: MVM s -> Int -> ST s ()
writePC vm pc = do
  current <- readSTRef vm.current
  writeSTRef current.state.pcRef pc

getStackPointer :: MVM s -> ST s Int
getStackPointer vm = do
  current <- readSTRef vm.current
  readSTRef current.state.spRef

writeStackPointer :: MVM s -> Int -> ST s ()
writeStackPointer vm sp = do
  current <- readSTRef vm.current
  writeSTRef current.state.spRef sp

getStack :: MVM s -> ST s (MStack s)
getStack vm = do
  current <- readSTRef vm.current
  pure current.state.stack

getMemory :: MVM s -> ST s (Memory s)
getMemory vm = do
  current <- readSTRef vm.current
  pure current.state.memory

getCurrentFrame :: MVM s -> ST s (MFrame s)
getCurrentFrame vm = readSTRef vm.current

getCurrentAccounts :: MVM s -> ST s Accounts
getCurrentAccounts vm = do
  frame <- getCurrentFrame vm
  pure frame.state.accounts

getCurrentInstructions :: MVM s -> ST s Instructions
getCurrentInstructions vm = do
  frame <- getCurrentFrame vm
  pure frame.context.instructions

stepJump :: MVM s -> Step s ()
stepJump vm = do
  jumpDest <- pop vm
  tryJump vm $ capAsWord64 jumpDest

stepJumpI :: MVM s -> Step s ()
stepJumpI vm = do
  jumpDest <- pop vm
  condition <- pop vm
  if condition == 0 then pure () else tryJump vm $ capAsWord64 jumpDest

tryJump :: MVM s -> Word64 -> Step s ()
tryJump vm dest = do
  Instructions instructions <- liftST $ getCurrentInstructions vm
  let instIndex = fromIntegral dest
  if isValidJumpDest instructions instIndex
  then do
    liftST $ writePC vm instIndex
  else vmError BadJumpDestination
  where
    isValidJumpDest instructions index = 
      case instructions Vec.!? index of
        Just (GenericInst OpJumpdest) -> True
        _ -> False

stepCallValue :: MVM s -> Step s ()
stepCallValue vm = do
  frame <- liftST $ getCurrentFrame vm
  let CallValue val = frame.context.callValue
  push vm val

stepCallDataSize :: MVM s -> Step s ()
stepCallDataSize vm = do
  frame <- liftST $ getCurrentFrame vm
  let CallData dataBS = frame.context.callData
  let size = BS.length dataBS
  push vm (fromIntegral size)

stepCallDataLoad :: MVM s -> Step s ()
stepCallDataLoad vm = do
  frame <- liftST $ getCurrentFrame vm
  offsetWord <- pop vm
  let CallData dataBS = frame.context.callData
  let offset = fromIntegral offsetWord
      -- Extract up to 32 bytes or fewer if out of bounds
      slice = BS.take 32 (BS.drop offset dataBS)
      -- Convert to big-endian W256
      sliceAsWord = BS.foldl' (\acc b -> (acc `shiftL` 8) .|. fromIntegral b) 0 slice
      callDataWord = if BS.length slice == 32 then sliceAsWord else (sliceAsWord `shiftL` (8 * (32 - BS.length slice)))
  push vm callDataWord

stepCallDataCopy :: MVM s -> Step s ()
stepCallDataCopy vm = do
  memoryOffset <- pop vm
  callDataOffset <- pop vm
  size <- pop vm
  let size64 = capAsWord64 size -- NOTE: We can cap it, larger numbers would cause of of gas anyway
  let callDataOffset64 = capAsWord64 callDataOffset
  let memoryOffset64 = capAsWord64 memoryOffset
  liftST $ do
    frame <- getCurrentFrame vm
    let CallData dataBS = frame.context.callData
    copyFromByteStringToMemory vm dataBS memoryOffset64 callDataOffset64 size64


stepCall :: MVM s -> Step s ()
stepCall vm = do
  gas <- pop vm
  address <- pop vm
  value <- pop vm
  argsOffset <- pop vm
  argsSize <- pop vm
  retOffset <- pop vm
  retSize <- pop vm
  when (value > 0) $ checkNotStaticContext vm
  makeCall vm REGULAR (Gas $ fromIntegral gas) (truncateToAddr address) (CallValue value) argsOffset argsSize retOffset retSize

stepDelegateCall :: MVM s -> Step s ()
stepDelegateCall vm = do
  gas <- pop vm
  address <- pop vm
  argsOffset <- pop vm
  argsSize <- pop vm
  retOffset <- pop vm
  retSize <- pop vm
  makeCall vm DELEGATE (Gas $ fromIntegral gas) (truncateToAddr address) (CallValue 0) argsOffset argsSize retOffset retSize

stepCallCode :: MVM s -> Step s ()
stepCallCode vm = do
  gas <- pop vm
  address <- pop vm
  value <- pop vm
  argsOffset <- pop vm
  argsSize <- pop vm
  retOffset <- pop vm
  retSize <- pop vm
  when (value > 0) $ checkNotStaticContext vm
  makeCall vm CODE (Gas $ fromIntegral gas) (truncateToAddr address) (CallValue value) argsOffset argsSize retOffset retSize

stepStaticCall :: MVM s -> Step s ()
stepStaticCall vm = do
  gas <- pop vm
  address <- pop vm
  argsOffset <- pop vm
  argsSize <- pop vm
  retOffset <- pop vm
  retSize <- pop vm
  makeCall vm STATIC (Gas $ fromIntegral gas) (truncateToAddr address) (CallValue 0) argsOffset argsSize retOffset retSize

data CallType = REGULAR | DELEGATE | CODE | STATIC
  deriving Eq

makeCall :: MVM s -> CallType -> Gas -> Addr -> CallValue -> VMWord -> VMWord -> VMWord -> VMWord -> Step s ()
makeCall vm callType gas to callValue@(CallValue cv') argsOffset argsSize retOffset retSize
  | isPrecompile to = internalError "Precompiles not supported yet!"
  | otherwise = do
    calldata <- readMemory vm argsOffset argsSize
    liftST $ do
      memory <- getMemory vm
      touchMemory vm memory (fromIntegral retOffset) (fromIntegral retSize) -- FIXME: Should gas be charged beforehand or only for actually used memory on return? See EIP - 5
    targetAccount <- liftST $ getOrCreateAccount vm to
    let targetCode = targetAccount.accCode
    -- let RuntimeCode bs = targetCode
    -- Debug.Trace.traceM ("Calling " <> (show $ ByteStringS bs))
    -- Debug.Trace.traceM ("With call data " <> (show $ ByteStringS calldata))
    currentFrame <- liftST $ getCurrentFrame vm
    isWarm <- liftST $ accessAccountForGas vm to
    let fees = vm.fees
    let accessCost = if isWarm then fees.g_warm_storage_read else fees.g_cold_account_access
        sendingValue = cv' /= 0
        positiveValueCost = if sendingValue then feeSchedule.g_callvalue else 0
        dynamicCost = accessCost + positiveValueCost
    liftST $ burn vm (Gas dynamicCost)
    availableGas <- liftST $ getAvailableGas currentFrame
    let accounts = currentFrame.state.accounts
        accountsAfterTransfer = uncheckedTransfer accounts currentFrame.context.codeAddress to callValue
        myGasToTransfer = computeGasToTransfer availableGas gas
        gasToTransfer = if sendingValue then myGasToTransfer + feeSchedule.g_callstipend else myGasToTransfer
    newFrameState <- liftST $ newMFrameState accountsAfterTransfer gasToTransfer
    liftST $ burn vm myGasToTransfer
    let
      callValue' = case callType of DELEGATE -> currentFrame.context.callValue; _ -> callValue
      storageAddress = case callType of ct | ct == REGULAR || ct == STATIC -> to; _ -> currentFrame.context.storageAddress
      caller = case callType of DELEGATE -> currentFrame.context.storageAddress; _ -> currentFrame.context.codeAddress
      shouldBeStatic = (callType == STATIC || currentFrame.context.isStatic)
      newFrameContext = FrameContext RUNTIME targetCode (parseByteCode targetCode) (CallData calldata) callValue' accounts to storageAddress caller shouldBeStatic
      newFrame = MFrame newFrameContext newFrameState
    liftST $ setReturnInfo newFrame (ReturnInfo retOffset retSize 1)
    liftST $ pushFrame vm newFrame

  where
    computeGasToTransfer (Gas availableGas) (Gas requestedGas) = Gas $ Prelude.min (EVM.allButOne64th availableGas) requestedGas


getOrCreateAccount :: MVM s -> Addr -> ST s Account
getOrCreateAccount vm address = do
  accounts <- getCurrentAccounts vm
  let maybeAccount = StrictMap.lookup address accounts
  case maybeAccount of
    Nothing -> do
      let accounts' = StrictMap.insert address emptyAccount accounts
      modifySTRef' vm.current (\frame -> frame {state = frame.state {accounts = accounts'}})
      pure emptyAccount
    Just account -> pure account

setReturnInfo :: MFrame s -> ReturnInfo -> ST s ()
setReturnInfo (MFrame _ state) retInfo = do
  writeSTRef state.retInfoRef (Just retInfo)

getReturnInfo :: MFrame s -> ST s ReturnInfo
getReturnInfo (MFrame _ state) = do
  retInfo <- readSTRef state.retInfoRef
  case retInfo of
    Nothing -> internalError "Return info not set!"
    Just info -> pure info

stepKeccak :: MVM s -> Step s ()
stepKeccak vm = do
  offset <- pop vm
  size <- pop vm
  liftST $ burnDynamicCost size
  bs <- readMemory vm offset size
  let hash = keccak' bs
  push vm hash

  where
    burnDynamicCost size =
      let cost = feeSchedule.g_sha3word * ceilDiv (fromIntegral size) 32 in
        burn vm $ Gas cost

stepGas :: MVM s -> Step s ()
stepGas vm = do
  frame <- liftST $ getCurrentFrame vm
  Gas gasRemaining <- liftST $ getAvailableGas frame
  push vm (fromIntegral gasRemaining)

stepReturn :: MVM s -> Step s ()
stepReturn vm = do
  offset <- pop vm
  size <- pop vm
  returnWithData vm offset size

returnWithData :: MVM s -> W256 -> W256 -> Step s a
returnWithData vm offset size = do
  bs <- readMemory vm offset size
  stop (FrameSucceeded bs)

stepRevert :: MVM s -> Step s ()
stepRevert vm = do
  offset <- pop vm
  size <- pop vm
  bs <- readMemory vm offset size
  stop (FrameReverted bs)

haltExecution :: MVM s -> Step s a
haltExecution vm = returnWithData vm 0 0

stepBlockHash :: MVM s -> Step s ()
stepBlockHash vm = do
  blockNumber <- pop vm
  let currentBlockNumber = vm.executionContext.blockHeader.number
  let hash = if blockNumber + 256 < currentBlockNumber || blockNumber >= currentBlockNumber
              then 0
              else fakeHash blockNumber
  push vm hash
  where
    fakeHash (W256 num) = keccak' $ Char8.pack $ show num

stepCoinBase :: MVM s -> Step s ()
stepCoinBase vm = do
  let (Addr val) = vm.executionContext.blockHeader.coinbase
  push vm (fromIntegral val)

stepTimeStamp :: MVM s -> Step s ()
stepTimeStamp vm = do
  let val = vm.executionContext.blockHeader.timestamp
  push vm val

stepNumber :: MVM s -> Step s ()
stepNumber vm = do
  let val = vm.executionContext.blockHeader.number
  push vm val

stepPrevRandao :: MVM s -> Step s ()
stepPrevRandao vm = do
  let val = vm.executionContext.blockHeader.prevRandao
  push vm val

stepGasLimit :: MVM s -> Step s ()
stepGasLimit vm = do
  let (Gas limit) = vm.executionContext.blockHeader.gaslimit
  push vm (fromIntegral limit)

stepAddress :: MVM s -> Step s ()
stepAddress vm = do
  frame <- liftST $ getCurrentFrame vm
  let (Addr addr) = frame.context.codeAddress
  push vm (fromIntegral addr)

stepBalance :: MVM s -> Step s ()
stepBalance vm = do
  address <- pop vm
  let address' = truncateToAddr address
  liftST $ do
    isWarm <- accessAccountForGas vm address'
    let fees = vm.fees
    burn vm (Gas $ if isWarm then fees.g_warm_storage_read else fees.g_cold_account_access)
  (Wei balance) <- liftST $ do
    frame <- getCurrentFrame vm
    let accounts = frame.state.accounts
    pure $ case StrictMap.lookup address' accounts of
            Nothing -> Wei 0
            Just account -> account.accBalance
  push vm (fromIntegral balance)

stepCaller :: MVM s -> Step s ()
stepCaller vm = do
  frame <- liftST $ getCurrentFrame vm
  let (Addr addr) = frame.context.callerAddress
  push vm (fromIntegral addr)

stepOrigin :: MVM s -> Step s ()
stepOrigin vm = do
  let (Addr addr) = vm.executionContext.transaction.from
  push vm (fromIntegral addr)

stepGasPrice :: MVM s -> Step s ()
stepGasPrice vm = do
  let price = vm.executionContext.transaction.gasPrice
  push vm price

stepCodeSize :: MVM s -> Step s ()
stepCodeSize vm = do
  frame <- liftST $ getCurrentFrame vm
  let (RuntimeCode bs) = frame.context.code
  push vm (fromIntegral $ BS.length bs)

stepCodeCopy :: MVM s -> Step s ()
stepCodeCopy vm = do
  memoryOffset <- pop vm
  codeOffset <- pop vm
  size <- pop vm
  let size64 = capAsWord64 size -- NOTE: We can cap it, larger numbers would cause of of gas anyway
  let codeOffset64 = capAsWord64 codeOffset
  let memoryOffset64 = capAsWord64 memoryOffset
  liftST $ do
    frame <- getCurrentFrame vm
    let RuntimeCode dataBS = frame.context.code
    copyFromByteStringToMemory vm dataBS memoryOffset64 codeOffset64 size64


stepExtCodeSize :: MVM s -> Step s ()
stepExtCodeSize vm = do
  address <- pop vm
  let address' = truncateToAddr address
  liftST $ do
    isWarm <- accessAccountForGas vm address'
    let fees = vm.fees
    burn vm (Gas $ if isWarm then fees.g_warm_storage_read else fees.g_cold_account_access)
  frame <- liftST $ getCurrentFrame vm
  let accounts = frame.state.accounts
  let account = StrictMap.findWithDefault emptyAccount address' accounts
  let (RuntimeCode bs) = account.accCode
  push vm (fromIntegral $ BS.length bs)

stepExtCodeCopy :: MVM s -> Step s ()
stepExtCodeCopy vm = do
  address <- pop vm
  memoryOffset <- pop vm
  codeOffset <- pop vm
  size <- pop vm
  let size64 = capAsWord64 size -- NOTE: We can cap it, larger numbers would cause of of gas anyway
  let codeOffset64 = capAsWord64 codeOffset
  let memoryOffset64 = capAsWord64 memoryOffset
  let address' = truncateToAddr address
  liftST $ do
    isWarm <- accessAccountForGas vm address'
    let fees = vm.fees
    burn vm (Gas $ if isWarm then fees.g_warm_storage_read else fees.g_cold_account_access)
  liftST $ do
    frame <- getCurrentFrame vm
    let accounts = frame.state.accounts
    let account = StrictMap.findWithDefault emptyAccount address' accounts
    let (RuntimeCode bs) = account.accCode
    copyFromByteStringToMemory vm bs memoryOffset64 codeOffset64 size64

copyFromByteStringToMemory :: MVM s -> BS.ByteString -> Word64 -> Word64 -> Word64 -> ST s ()
copyFromByteStringToMemory vm bs memOffset bsOffset size = do
  burnDynamicCost vm size
  maybeResult <- readSTRef vm.terminationFlagRef
  when (isNothing maybeResult) $ do
    let bs' = slicePadded bs (capAsInt bsOffset) (capAsInt size) -- NOTE: We cap to Int, larger values would cause error anyway
    memory <- getMemory vm
    touchMemory vm memory memOffset size
    writeMemory memory memOffset bs'

  where
    burnDynamicCost _ 0 = pure ()
    burnDynamicCost vm' size' =
      let cost = if size' > (maxBound - 32) then maxBound else feeSchedule.g_copy * ceilDiv size' 32 in
      burn vm' (Gas cost)

slicePadded :: BS.ByteString -> Int -> Int -> BS.ByteString
slicePadded _ _ 0 = BS.empty
slicePadded bs offset size =
    let len = BS.length bs
        slice | offset >= len = BS.replicate size 0
              | offset + size <= len = BS.take size (BS.drop offset bs)
              | otherwise =
                let available = BS.drop offset bs
                    missing   = size - BS.length available
                in available <> BS.replicate missing 0
    in
    slice

stepPC :: MVM s -> Step s ()
stepPC vm = do
  pcAfterThisInstruction <- liftST $ readPC vm
  push vm (fromIntegral pcAfterThisInstruction - 1)

stepLog :: MVM s -> Word8 -> Step s ()
stepLog vm n = do
  offset <- pop vm
  size <- pop vm
  bytes <- readMemory vm offset size
  topics <- getTopics vm n
  liftST $ burnLogGas n size
  -- TODO: keep logs?
  pure ()
  where
    burnLogGas n' size' = do
      let fees = feeSchedule
          size64 = capAsWord64 size'
          cost = Gas $ (fees.g_logdata * size64) + (fromIntegral n' * fees.g_logtopic)
      burn vm cost
    getTopics :: MVM s -> Word8 -> Step s [VMWord]
    getTopics vm' n' = do
      let i = fromIntegral n'
      sp <- liftST $ getStackPointer vm'
      if sp < i
        then stackUnderflow
        else liftST $ do
          stack <- getStack vm'
          let !sp' = sp - i
          writeStackPointer vm' sp'
          Vec.toList <$> Vec.freeze (MVec.slice sp' i stack)
  
stepCreate :: MVM s -> Step s ()
stepCreate _vm = internalError "CREATE not implemented yet!"

stepCreate2 :: MVM s -> Step s ()
stepCreate2 vm = do
  checkNotStaticContext vm
  value <- pop vm
  offset <- pop vm
  size <- pop vm
  salt <- pop vm
  
  initCode <- readMemory vm offset size
  -- memory <- liftST $ getMemory vm
  currentFrame <- liftST $ getCurrentFrame vm
  availableGas <- liftST $ getAvailableGas currentFrame
  let
    sender = currentFrame.context.storageAddress
    newAddress = create2Address sender salt initCode
    (createCost, initGas) = costOfCreate availableGas size True
  liftST $ burn vm createCost
  executeCreate vm sender initGas (CallValue value) newAddress initCode

  where
    costOfCreate :: Gas -> VMWord -> Bool -> (Gas, Gas)
    costOfCreate availableGas codeSize hashNeeded = (createCost, initGas)
      where
        fees = feeSchedule
        byteCost = if hashNeeded then fees.g_sha3word + fees.g_initcodeword else fees.g_initcodeword
        codeCost = byteCost * (ceilDiv codeSize 32)
        createCost = Gas . fromIntegral $ codeCost
        (Gas remaining) = availableGas - createCost
        initGas = Gas $ allButOne64th remaining



-- isRootFrame :: MVM s -> ST s Bool
-- isRootFrame vm = do
--   frames <- readSTRef vm.frames
--   pure (null frames)

stepMSize :: MVM s -> Step s ()
stepMSize vm = do
  (Memory _ wordSizeRef) <- liftST $ getMemory vm
  wordSize <- liftST $ readSTRef wordSizeRef
  push vm (fromIntegral $ wordSize * 32)

stepMCopy :: MVM s -> Step s ()
stepMCopy vm = do
  destOff <- pop vm
  sourceOff <- pop vm
  size <- pop vm
  let size' = capAsWord64 size
  let destOff' = capAsWord64 destOff
  when (size > 0) $ do
    buf <- readMemory vm sourceOff size
    liftST $ copyFromByteStringToMemory vm buf destOff' 0 size'

stepMLoad :: MVM s -> Step s ()
stepMLoad vm = {-# SCC "MLoad" #-} do
  offset <- pop vm
  v <- liftST $ do
     memory <- getMemory vm
     touchMemory vm memory (fromIntegral offset) 32 -- TODO: check size and error out if larger than 64-bit word?
     memLoad32 memory (fromIntegral offset)
  push vm v

stepMStore :: MVM s -> Step s ()
stepMStore vm = {-# SCC "MStore" #-} do
  off <- pop vm
  val <- pop vm
  liftST $ do
    memory <-getMemory vm
    touchMemory vm memory (fromIntegral off) 32 -- TODO: check size and error out if larger than 64-bit word?
    memStore32 memory off val

stepMStore8 :: MVM s -> Step s ()
stepMStore8 vm = do
  off <- pop vm
  val <- pop vm
  liftST $ do
    memory <-getMemory vm
    touchMemory vm memory (fromIntegral off) 1 -- TODO: check size and error out if larger than 64-bit word?
    memStore1 memory off val

stepSLoad :: MVM s -> Step s ()
stepSLoad vm = {-# SCC "SLoad" #-} do
  key <- pop vm
  val <- liftST $ do
    store <- getCurrentStorage vm
    isWarm <- touchCurrentStore vm key
    burn vm $ if isWarm then feeSchedule.g_warm_storage_read else feeSchedule.g_cold_sload
    pure $ sload store key
  push vm val

stepSStore :: MVM s -> Step s ()
stepSStore vm = {-# SCC "SStore" #-} do
  checkNotStaticContext vm
  ensureGas vm (Gas vm.fees.g_callstipend)
  key <- pop vm
  val <- pop vm
  liftST $ do
    isWarm <- touchCurrentStore vm key
    store <- getCurrentStorage vm
    let currentVal = sload store key
    originalVal <- getOriginalValue vm key
    let warmCost = warmStoreCost originalVal currentVal val
        totalGasCost = if isWarm then warmCost else warmCost + feeSchedule.g_cold_sload
    burn vm totalGasCost
    let refund = computeRefund originalVal currentVal val
    addRefund vm refund
    let updatedStore = sstore store key val
    setCurrentStorage vm updatedStore

  where
    warmStoreCost originalValue currentValue newValue
      | newValue == currentValue = sload'
      | currentValue == originalValue = if originalValue == 0 then sset else sreset
      | otherwise = sload'

    computeRefund originalValue currentValue newValue
      | currentValue == newValue                                             = 0
      | originalValue /= 0 && newValue == 0                                  = sreset + access_list_storage_key
      | originalValue /= 0 && currentValue == 0 && originalValue == newValue = sreset - sload' - (sreset + access_list_storage_key)
      | originalValue /= 0 && currentValue == 0                              = -(sreset + access_list_storage_key)
      | originalValue /= 0 && originalValue == newValue                      = sreset - sload'
      | originalValue == 0 && newValue == 0                                  = sset - sload'
      | otherwise = 0

    sreset = feeSchedule.g_sreset
    sset = feeSchedule.g_sset
    access_list_storage_key = feeSchedule.g_access_list_storage_key
    sload' = feeSchedule.g_sload

    addRefund vm' value = do
      frame <- getCurrentFrame vm'
      addGasRefund frame value

touchCurrentStore :: MVM s -> W256 -> ST s Bool
touchCurrentStore vm slot = do
  address <- getCurrentStorageAddress vm
  access vm address slot

  where
    access vm' address slot' = do
      substate <- readSTRef vm'.txsubstate
      let accessed = substate.accessedAddresses
          present = case StrictMap.lookup address accessed of
            Nothing -> False
            Just slots -> Set.member slot' slots
      unless present $ do
        let updatedAccessList = StrictMap.insertWith (\_ oldSet -> Set.insert slot' oldSet) address (Set.singleton slot') accessed
        writeSTRef vm'.txsubstate substate {accessedAddresses = updatedAccessList}
      pure present

    getCurrentStorageAddress vm' = do
      frame <- getCurrentFrame vm'
      pure frame.context.storageAddress

-- TODO: This could be pure if we store the original storages at the beginning of transaction
getOriginalValue :: MVM s -> VMWord  -> ST s VMWord
getOriginalValue vm key = do
  firstFrame <- getFirstFrame vm
  let accounts = firstFrame.context.accountsSnapshot
  currentFrame <- getCurrentFrame vm
  let storageAddress = currentFrame.context.storageAddress
  pure $ case StrictMap.lookup storageAddress accounts of
    Nothing -> 0
    Just account -> StrictMap.findWithDefault 0 key account.accStorage
  where
    getFirstFrame vm' = do
      frameStack <- readSTRef vm'.frames
      case frameStack of
        [] -> getCurrentFrame vm'
        fs -> pure $ last fs
      

getCurrentStorage :: MVM s -> ST s Storage
getCurrentStorage vm = do
  frame <- getCurrentFrame vm
  let maybeStorage = do
        account <- StrictMap.lookup frame.context.storageAddress frame.state.accounts
        pure account.accStorage
  pure $ fromMaybe mempty maybeStorage

setCurrentStorage :: MVM s -> Storage -> ST s ()
setCurrentStorage vm storage = do
  frame <- getCurrentFrame vm
  let currentAccount = fromMaybe (internalError "Current account is unknown!") $ StrictMap.lookup frame.context.storageAddress frame.state.accounts
  let updatedAccounts = StrictMap.insert frame.context.storageAddress (currentAccount {accStorage = storage}) frame.state.accounts
      updatedState = frame.state {accounts = updatedAccounts}
      updatedFrame = frame {state = updatedState}
  writeSTRef vm.current updatedFrame

------------- Storage Submodule --------------------------

sload :: Storage -> W256 -> W256
sload storage key = StrictMap.findWithDefault 0 key storage

sstore :: Storage -> W256 -> W256 -> Storage
sstore storage key val = if val == 0 then StrictMap.delete key storage else StrictMap.insert key val storage

------------- Memory Submodule ---------------------------
data Memory s = Memory {
  memRef :: STRef s (UMVec.MVector s Word8),
  wordSizeRef :: STRef s Word64
}

newMemory :: ST s (Memory s)
newMemory = do
    v <- UMVec.new 0
    ref <- newSTRef v
    size <- newSTRef 0
    pure (Memory ref size)

readMemory :: MVM s -> W256 -> W256 -> Step s BS.ByteString
readMemory vm offset size =
  case (,) <$> toWord64 offset <*> toWord64 size of
    Nothing -> vmError IllegalOverflow
    Just (offset64, size64) -> liftST $ do
      memory@(Memory memRef _) <- getMemory vm
      touchMemory vm memory offset64 size64
      memvec <- readSTRef memRef
      let vecsize = fromIntegral $ UMVec.length memvec
      if offset64 >= vecsize then
        -- reads past memory are all zeros
        pure $ BS.replicate (fromIntegral size) 0
      else if (vecsize - offset64) >= size64 then do
        -- whole read from memory
        let dataVec = UMVec.slice (fromIntegral offset64) (fromIntegral size64) memvec
        frozen <- UVec.freeze dataVec
        let dataBS = BS.pack (UVec.toList frozen) -- TODO: Consider using storable vector for memory?
        pure dataBS
      else do -- partially in bounds, partially zero
        let available = vecsize - offset64
            missing = size64 - available -- number of zero bytes

        -- read the part that exists
        prefixFrozen <- UVec.freeze (UMVec.slice (fromIntegral offset64) (fromIntegral available) memvec)
        let prefix = BS.pack (UVec.toList prefixFrozen)
        -- append missing zeros
        let suffix = BS.replicate (fromIntegral missing) 0
        pure (prefix <> suffix)

writeMemory :: Memory s -> Word64 -> BS.ByteString -> ST s ()
writeMemory (Memory memRef wordSizeRef) offset bs
  | BS.null bs = pure ()
  | otherwise = do
      vec <- readSTRef memRef
      let off64 = fromIntegral offset
          len = BS.length bs
          requiredSizeWords = bytesToWords $ off64 + (fromIntegral len)
          requiredSizeBytes = fromIntegral $ requiredSizeWords * 32
          vecSize = UMVec.length vec
      vec' <- if requiredSizeBytes <= vecSize
              then pure vec
              else do vec' <- grow vec requiredSizeBytes; writeSTRef memRef vec'; pure vec'
      actualSizeWords <- readSTRef wordSizeRef

      when (requiredSizeWords > actualSizeWords) $ writeSTRef wordSizeRef requiredSizeWords
      -- now write the bytes
      let off = fromIntegral off64
      let writeByte i
            | i == len  = pure ()
            | otherwise = do
                let b = BS.index bs i
                UMVec.unsafeWrite vec' (off + i) b
                writeByte (i + 1)
      writeByte 0

touchMemory :: MVM s -> Memory s -> Word64 -> Word64 -> ST s ()
touchMemory _ _ _ 0 = pure ()
touchMemory vm (Memory _ wordSizeRef) offset size = do
  currentSizeInWords <- readSTRef wordSizeRef
  let wordSizeAfterTouch = bytesToWords $ cappedSum offset size
  when (wordSizeAfterTouch > currentSizeInWords) $ do
    let memoryExpansionCost = memoryCost wordSizeAfterTouch - memoryCost currentSizeInWords
    when (memoryExpansionCost > 0) $ do
      burn vm memoryExpansionCost
      writeSTRef wordSizeRef wordSizeAfterTouch

bytesToWords :: Word64 -> Word64
bytesToWords b
  | b <= maxBound - 32 = ceilDiv b 32
  | otherwise = maxBound `div` 32

memoryCost :: Word64 -> Gas
memoryCost wordCount =
  let
    fees = feeSchedule
    linearCost = fees.g_memory * wordCount
    quadraticCost = div (wordCount * wordCount) 512
  in
    Gas $ linearCost + quadraticCost

memLoad32 :: Memory s -> W256 -> ST s W256
memLoad32 (Memory memRef _) offset = do
  vec <- readSTRef memRef
  let !len = UMVec.length vec
      !off = fromIntegral offset

      -- Read 8 bytes starting at `base` into a Word64
      load64 base = go (0 :: Word64) 0
        where
          go !acc !i
            | i == 8 = pure acc
            | otherwise = do
                let !idx = base + i
                !b <- if idx < len
                      then UMVec.unsafeRead vec idx
                      else pure 0
                let !acc' = (acc `shiftL` 8) .|. fromIntegral b
                go acc' (i + 1)

  !w0 <- load64 (off + 0)
  !w1 <- load64 (off + 8)
  !w2 <- load64 (off + 16)
  !w3 <- load64 (off + 24)

  pure $ constructWord256FromWords w0 w1 w2 w3

memStore32 :: Memory s -> W256 -> W256 -> ST s ()
memStore32 (Memory memRef sizeRef) offset value = do
  vec <- readSTRef memRef
  let off64 = fromIntegral offset
      requiredSizeWords = bytesToWords $ off64 + 32
      requiredSizeBytes = fromIntegral $ requiredSizeWords * 32
      vecSize = UMVec.length vec
  vec' <- if requiredSizeBytes <= vecSize
          then pure vec
          else do vec' <- grow vec requiredSizeBytes; writeSTRef memRef vec'; pure vec'
  actualWordSize <- readSTRef sizeRef

  when (requiredSizeWords > actualWordSize) $ writeSTRef sizeRef requiredSizeWords

  -- EVM stores big-endian
  let (w0, w1, w2, w3) = deconstructWord256ToWords value

  -- write 32 bytes using fast Word64 stores
  let off = fromIntegral off64
  writeWord64BE vec' (off     ) w0
  writeWord64BE vec' (off +  8) w1
  writeWord64BE vec' (off + 16) w2
  writeWord64BE vec' (off + 24) w3

  where
    writeWord64BE :: UMVec.MVector s Word8 -> Int -> Word64 -> ST s ()
    writeWord64BE vec off w = do
      UMVec.unsafeWrite vec (off    ) (fromIntegral (w `shiftR` 56))
      UMVec.unsafeWrite vec (off + 1) (fromIntegral (w `shiftR` 48))
      UMVec.unsafeWrite vec (off + 2) (fromIntegral (w `shiftR` 40))
      UMVec.unsafeWrite vec (off + 3) (fromIntegral (w `shiftR` 32))
      UMVec.unsafeWrite vec (off + 4) (fromIntegral (w `shiftR` 24))
      UMVec.unsafeWrite vec (off + 5) (fromIntegral (w `shiftR` 16))
      UMVec.unsafeWrite vec (off + 6) (fromIntegral (w `shiftR` 8))
      UMVec.unsafeWrite vec (off + 7) (fromIntegral w)


memStore1 :: Memory s -> W256 -> W256 -> ST s ()
memStore1 (Memory memRef wordSizeRef) offset value = do
  vec <- readSTRef memRef
  let off64 = fromIntegral offset
      requiredSizeWords = bytesToWords $ off64 + 1
      requiredSizeBytes = fromIntegral $ requiredSizeWords * 32
      vecSize = UMVec.length vec
  vec' <- if requiredSizeBytes <= vecSize
          then pure vec
          else do vec' <- grow vec requiredSizeBytes; writeSTRef memRef vec'; pure vec'
  actualSizeWords <- readSTRef wordSizeRef
  when (requiredSizeWords > actualSizeWords) $ writeSTRef wordSizeRef requiredSizeWords

  let byte = fromIntegral (value .&. 0xff)
      off = fromIntegral off64
  UMVec.write vec' off byte

-- NOTE: This assumes that required size is greater than current size, it does not check it!
grow :: UMVec.MVector s Word8 -> Int -> ST s (UMVec.MVector s Word8)
grow vec requiredSize = do
  let currentSize = UMVec.length vec
  let growthFactor = 2
  let targetSize = max requiredSize (currentSize * growthFactor)
  -- Always grow at least 8k
  let toGrow = max 8192 $ targetSize - currentSize
  UMVec.grow vec toGrow


------------------- GAS helpers --------------------------------

getAvailableGas :: MFrame s -> ST s Gas
getAvailableGas frame = readSTRef frame.state.gasRemainingRef

getGasRefund :: MFrame s -> ST s Gas
getGasRefund frame = readSTRef frame.state.gasRefundedRef

addGasRefund :: MFrame s -> Gas -> ST s ()
addGasRefund frame gas= modifySTRef' frame.state.gasRefundedRef (+gas)

burn :: MVM s -> Gas -> ST s ()
burn vm (Gas toBurn) = {-# SCC "Burn" #-} do
  frame <- getCurrentFrame vm
  let gasRef = frame.state.gasRemainingRef
  (Gas gasRemaining) <- readSTRef gasRef
  if toBurn > gasRemaining
    then vmError' vm (OutOfGas gasRemaining toBurn)
    else writeSTRef gasRef (Gas $ gasRemaining - toBurn)

ensureGas :: MVM s -> Gas -> Step s ()
ensureGas vm (Gas amount) = liftST $ do
  frame <- getCurrentFrame vm
  let gasRef = frame.state.gasRemainingRef
  (Gas gasRemaining) <- readSTRef gasRef
  -- NOTE: Here we are also out of gas when requested amount is equal to the remaining gas
  when (amount >= gasRemaining) $ vmError' vm (OutOfGas gasRemaining amount)


unburn' :: MFrame s -> Gas -> ST s ()
unburn' frame (Gas toReturn) = do
  let gasRef = frame.state.gasRemainingRef
  (Gas gasRemaining) <- readSTRef gasRef
  writeSTRef gasRef (Gas $ gasRemaining + toReturn)

extraExpGasCost :: W256 -> Gas
extraExpGasCost exponent =
    let fees = feeSchedule
        cost = if exponent == 0
          then 0
          else fees.g_expbyte * (fromIntegral $ ceilDiv (1 + log2 exponent) 8)
    in
      Gas cost

burnStaticGas :: MVM s -> Instruction -> ST s ()
burnStaticGas vm instruction = {-# SCC "BurnStaticGas" #-} do
  let FeeSchedule {..} = vm.fees
  let cost = case instruction of
        GenericInst op -> case op of
          OpStop -> g_zero
          OpAdd -> g_verylow
          OpMul -> g_low
          OpSub -> g_verylow
          OpDiv -> g_low
          OpSdiv -> g_low
          OpMod -> g_low
          OpSmod -> g_low
          OpAddmod -> g_mid
          OpMulmod -> g_mid
          OpExp -> g_exp
          OpSignextend -> g_low
          OpLt -> g_verylow
          OpGt -> g_verylow
          OpSlt -> g_verylow
          OpSgt -> g_verylow
          OpEq -> g_verylow
          OpIszero -> g_verylow
          OpAnd -> g_verylow
          OpOr -> g_verylow
          OpXor -> g_verylow
          OpNot -> g_verylow
          OpByte -> g_verylow
          OpShl -> g_verylow
          OpShr -> g_verylow
          OpSar -> g_verylow
          OpSha3 -> g_sha3
          OpAddress -> g_base
          OpBalance -> g_zero
          OpOrigin -> g_base
          OpCaller -> g_base
          OpCallvalue -> g_base
          OpCalldataload -> g_verylow
          OpCalldatasize -> g_base
          OpCalldatacopy -> g_verylow
          OpCodesize -> g_base
          OpCodecopy -> g_verylow
          OpGasprice -> g_base
          OpExtcodesize -> g_zero
          OpExtcodecopy -> g_zero
          OpBlockhash -> g_blockhash
          OpCoinbase -> g_base
          OpTimestamp -> g_base
          OpNumber -> g_base
          OpPrevRandao -> g_base
          OpGaslimit -> g_base
          OpPop -> g_base
          OpMload -> g_verylow
          OpMstore -> g_verylow
          OpMstore8 -> g_verylow
          OpSload -> g_zero -- Custom rules
          OpSstore -> g_zero -- Custom rules
          OpJump -> g_mid
          OpJumpi -> g_high
          OpPc -> g_base
          OpMsize -> g_base
          OpGas -> g_base
          OpJumpdest -> g_jumpdest
          OpMcopy -> g_verylow
          OpPush0 -> g_base
          OpPush _ -> g_verylow
          OpDup _ -> g_verylow
          OpSwap _ -> g_verylow
          OpLog _ -> g_log
          OpCreate -> g_create
          OpCall -> g_zero -- Cost for CALL depends on if we are accessing cold or warm address
          OpCallcode -> g_zero -- Cost for CALL depends on if we are accessing cold or warm address
          OpReturn -> g_zero
          OpDelegatecall -> g_zero
          OpCreate2 -> g_create
          OpStaticcall -> g_zero
          OpRevert -> g_zero
          OpUnknown _ -> g_zero
          _ -> internalError ("Unknown opcode: " ++ show op)
        Push _ _ -> g_verylow
  when (cost > 0) $ burn vm (Gas cost)


txGasCost :: FeeSchedule Word64 -> Transaction -> Word64
txGasCost fs tx =
  let CallData calldata = tx.txdata
      zeroBytes = BS.count 0 calldata
      nonZeroBytes = BS.length calldata - zeroBytes
      baseCost = fs.g_transaction
        + (if isNothing tx.to then fs.g_txcreate + initcodeCost else 0)
        -- TODO: + (accessListPrice fs tx.accessList )
      zeroCost = fs.g_txdatazero
      nonZeroCost = fs.g_txdatanonzero
      initcodeCost = fs.g_initcodeword * fromIntegral (ceilDiv (BS.length calldata) 32)
  in baseCost + zeroCost * (fromIntegral zeroBytes) + nonZeroCost * (fromIntegral nonZeroBytes)


----------------------- Balance transfers -------------------------------------

-- Assumes both sender are receiver are already in the map
uncheckedTransfer :: Accounts -> Addr -> Addr -> CallValue -> Accounts
uncheckedTransfer accounts from to (CallValue value) =
  if value == 0 then accounts else updatedAccounts
  where
    updatedAccounts =
      let
        addTo account = account {accBalance = account.accBalance + (Wei value)}
        subtractFrom account = account {accBalance = account.accBalance - (Wei value)}
      in
        StrictMap.adjust addTo to $ StrictMap.adjust subtractFrom from accounts


------------------------ Other --------------------------------------------------

parseByteCode :: RuntimeCode -> Instructions
parseByteCode (RuntimeCode bs) = Instructions $ runST $ do
  let len = BS.length bs
  vec <- Vec.thaw $ Vec.generate len (\_ -> GenericInst (OpUnknown 254)) -- 254 means invalid instruction
      -- single pass: write actual instruction starts (PUSH start -> Push; others -> decoded op)
  let go pc
        | pc >= len = pure ()
        | otherwise =
            let byte = BS.index bs pc in
            if isPush byte
              then
                let n = byte - 0x5f
                    n' = fromIntegral n
                    payloadStart = pc + 1
                    payloadEnd = min len (payloadStart + n')
                    payload = BS.take (payloadEnd - payloadStart)
                                      (BS.drop payloadStart bs)
                    w = word payload
                in do
                    MVec.write vec pc (Push n w)
                    go payloadEnd
              else do
                MVec.write vec pc (GenericInst (getOp byte))
                go (pc + 1)
  go 0
  Vec.freeze vec

  where
    isPush w = w >= 0x60 && w <= 0x7f

getInstruction :: MVM s -> Int -> ST s Instruction
getInstruction vm pc = do
  frame <- getCurrentFrame vm
  let (Instructions instructions) = frame.context.instructions
  let len = Vec.length instructions
  pure $ if pc >= len
    then GenericInst OpStop
    else Vec.unsafeIndex instructions pc

createAddress :: Addr -> Nonce -> Addr
createAddress sender (Nonce senderNonce) = Addr . fromIntegral . keccak' . rlpList $ [rlpAddrFull sender, rlpWord256 (fromIntegral senderNonce)]

create2Address :: Addr -> VMWord -> BS.ByteString -> Addr
create2Address sender salt initCode = 
  truncateToAddr $ keccak' $ mconcat [BS.singleton 0xff, word160Bytes sender, word256Bytes salt, word256Bytes $ keccak' initCode]

executeCreate :: MVM s -> Addr -> Gas -> CallValue -> Addr -> BS.ByteString -> Step s ()
executeCreate vm sender initGas value newAddress code = do
  -- TODO: check code size
  -- TODO: check nonce overflowing
  -- TODO: Check call stack overflowing
  -- TODO: Check account already exists on address
  -- TODO Check balance
  -- Debug.Trace.traceM $ "Executing create: with address " <> (show newAddress) <> " sender is " <> (show sender) <> " code is: " <> (show $ ByteStringS code)
  callerFrame <- liftST $ getCurrentFrame vm
  liftST $ burn vm initGas
  let initCode = RuntimeCode code
  let callerAccounts = callerFrame.state.accounts
      withCalleeAccounts = StrictMap.insert newAddress (emptyAccount {accCode = initCode, accNonce = 1}) callerAccounts
      withNonceIncremented = StrictMap.adjust (\acc -> acc{accNonce = acc.accNonce + 1})  sender withCalleeAccounts
      calleeAccounts = uncheckedTransfer withNonceIncremented sender newAddress value
  newFrameState <- liftST $ newMFrameState calleeAccounts initGas
  let newFrameContext = FrameContext INIT initCode (parseByteCode initCode) (CallData BS.empty) value calleeAccounts newAddress newAddress sender False
      newFrame = MFrame newFrameContext newFrameState
      (Addr addrVal) = newAddress
  liftST $ setReturnInfo newFrame (ReturnInfo 0 0 (fromIntegral addrVal))
  liftST $ pushFrame vm newFrame

cappedSum :: Word64 -> Word64 -> Word64
cappedSum a b = let s = a + b in if s < a then maxBound else s

accessAccountForGas :: MVM s -> Addr -> ST s Bool
accessAccountForGas vm address = do
  substate <- readSTRef vm.txsubstate
  let accessed = substate.accessedAddresses
      present = StrictMap.member address accessed
  unless present $ do
    let updatedAccessList = StrictMap.insert address mempty accessed
    writeSTRef vm.txsubstate substate {accessedAddresses = updatedAccessList}
  pure present

isPrecompile :: Addr -> Bool
isPrecompile addr = 0x0 < addr && addr <= 0x09
