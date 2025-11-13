module EVM.ConcreteExecution (
exec,
execBytecode,
RuntimeCode(..),
CallData(..),
CallValue(..),
ExecutionResult,
VMSnapshot(..),
Transaction(..),
Account(..),
Wei(..),
Gas(..),
Nonce(..)
) where

import Control.Monad (forM, when, unless)
import Control.Monad.ST (ST, runST)
import Data.Bits ((.|.), (.&.), (.^.), shiftR, shiftL, testBit, complement, bit)
import Data.ByteString qualified as BS
import Data.DoubleWord (Int256)
import Data.Map.Strict qualified as StrictMap
import Data.Maybe (fromMaybe, isJust, fromJust, isNothing)
import Data.Set qualified as Set
import Data.STRef
import Data.Vector.Unboxed qualified as UVec
import Data.Vector.Unboxed.Mutable qualified as UMVec
import Data.Vector.Mutable qualified as MVec
import Data.Word (Word8, Word64)
import Prelude hiding (exponent)

import EVM (allButOne64th, ceilDiv, log2)
import EVM.Types (
  W256(..),
  W64(..),
  Word512,
  EvmError (BadJumpDestination),
  internalError,
  GenericOp(..),
  word,
  -- ByteStringS(..),
  keccak',
  toWord64,
  constructWord256FromWords,
  deconstructWord256ToWords,
  truncateToAddr,
  Addr(..), ByteStringS (ByteStringS)
  )
import EVM.Op (getOp)
import EVM.FeeSchedule

-- import Debug.Trace qualified (traceM, trace)
-- import Numeric (showHex)


type VMWord = W256
type Data = BS.ByteString
newtype RuntimeCode = RuntimeCode {code :: Data}
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

data MFrameState s = MFrameState {
  pcRef :: STRef s Int,
  stack :: MStack s,
  spRef :: STRef s Int,  -- stack pointer (beyond stack top slot)
  memory :: Memory s,
  accounts :: Accounts,
  gasRemainingRef :: STRef s Gas,
  gasRefundedRef :: STRef s Gas,
  retInfoRef :: STRef s (Maybe (W256, W256))
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

newFrameFromTransaction :: Transaction -> Accounts -> ST s (MFrame s)
newFrameFromTransaction tx@(Transaction from maybeTo callvalue calldata maybeCode gasLimit _) accounts =
  case (maybeTo, maybeCode) of
    (Just to, Just code) -> do
      let availableGas = gasLimit - (Gas $ txGasCost feeSchedule tx) -- TODO: check if limit is at least transaction cost
      freshState <- newMFrameState accounts availableGas
      let frameState = freshState {accounts = accounts}
      let ctx = FrameContext code calldata callvalue accounts to to from
      pure $ MFrame ctx frameState
    _  -> internalError "Creation transaction not supported yet"


data FrameContext = FrameContext {
  code :: RuntimeCode,
  callData :: CallData,
  callValue :: CallValue,
  accountsSnapshot :: Accounts,
  codeAddress :: Addr,
  storageAddress :: Addr,
  callerAddress :: Addr
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
    transaction :: Transaction,
    txsubstate :: STRef s TxSubState
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
  code :: Maybe RuntimeCode,
  gasLimit :: Gas,
  gasPrice :: W256
}

newtype TxSubState = TxSubState {
  accessedAddresses :: StrictMap.Map Addr (Set.Set W256)
}


data VMResult where
  VMFailure :: EvmError -> VMResult        -- ^ An operation failed
  VMSuccess :: Data -> VMResult            -- ^ Reached STOP, RETURN, or end-of-code

execBytecode :: RuntimeCode -> CallData -> CallValue -> ExecutionResult
execBytecode code calldata value = exec transaction worldState
  where
    artificialAddress = Addr 0xdeadbeef
    artificialAccount = Account code mempty (Wei (fromIntegral (maxBound :: Word64))) (Nonce 0)
    worldState = StrictMap.singleton artificialAddress artificialAccount
    transaction = Transaction (Addr 0) (Just artificialAddress ) value calldata (Just code) (Gas maxBound) 0

exec :: Transaction -> Accounts -> ExecutionResult
exec tx accounts = runST $ do
  -- let Transaction from to (CallValue value) (CallData calldata) maybeCode gasLimit gasPrice = tx
  -- let RuntimeCode bs = fromJust maybeCode
  -- Debug.Trace.traceM $ "\nNew transaction!\n"
  -- Debug.Trace.traceM $ "Value: " <> (show value)
  -- Debug.Trace.traceM $ "Calldata: " <> (show $ ByteStringS calldata)
  -- Debug.Trace.traceM $ "Code: " <> (show $ ByteStringS bs)
  -- Debug.Trace.traceM $ "Gas limit: " <> (show gasLimit)
  -- Debug.Trace.traceM $ "Gas price: " <> (show gasPrice)
  let updatedAccounts = transferTxValue $ initTransaction accounts
  initialFrame <- newFrameFromTransaction tx updatedAccounts
  currentRef <- newSTRef initialFrame
  framesRef <- newSTRef []
  substateRef <- newSTRef (TxSubState mempty)
  let vm = MVM currentRef framesRef feeSchedule tx substateRef
  runLoop vm

  where
    initTransaction :: Accounts -> Accounts
    initTransaction accounts' = StrictMap.adjust initiatingTransaction tx.from accounts'
    initiatingTransaction account =
      let
        (Wei balance) = account.accBalance
        (Gas limit) = tx.gasLimit
        gasCost = tx.gasPrice * (fromIntegral limit)
        updatedBalance = Wei $ balance - gasCost -- TODO: Check if the balance is sufficient to execute Tx
        updatedNonce = account.accNonce + 1
      in
        account {accBalance = updatedBalance, accNonce = updatedNonce}
    transferTxValue :: Accounts -> Accounts
    transferTxValue accounts' =
      let
        (CallValue value) = tx.value
        addTo account = account {accBalance = account.accBalance + (Wei value)}
        subtractFrom account = account {accBalance = account.accBalance - (Wei value)}
      in
        if value == 0 then accounts' else StrictMap.adjust addTo (fromJust tx.to) $ StrictMap.adjust subtractFrom tx.from accounts'

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
      let Gas limit = vm.transaction.gasLimit
          gasPrice = vm.transaction.gasPrice
      frame <- getCurrentFrame vm
      Gas remaining <- getAvailableGas frame
      Gas refunds <- getGasRefund vm
      let gasUsed = limit - remaining
          refundCap = gasUsed `div` 5
          finalRefund = Prelude.min refunds refundCap

          toRefund = remaining + finalRefund
          weiToRefund = Wei $ (fromIntegral toRefund) * gasPrice

      -- TODO: gas that pays the miner (in Wei):
      -- minerGas = gasLimit - gasRemaining - finalRefund
      -- minerWei = minerGas * gasPrice

      let accounts = frame.state.accounts
          addTo account = account {accBalance = account.accBalance + weiToRefund}
          updatedAccounts = StrictMap.adjust addTo vm.transaction.from accounts
          updatedFrame = frame {state = frame.state {accounts = updatedAccounts}}
      writeSTRef vm.current updatedFrame


stepVM :: MVM s -> ST s (Maybe VMResult)
stepVM vm = do
  byte <- fetchByte vm
  -- pc <- readPC vm
  _ <- advancePC vm 1
  let op = getOp byte
  burnStaticGas vm op
  -- Debug.Trace.traceM ("Executing op " <> (show op) <> "\nPC: " <> showHex pc "")
  case op of
    OpStop -> returnWithData vm 0 0
    OpReturn -> stepReturn vm
    OpAdd -> binOp vm (+)
    OpMul -> binOp vm (*)
    OpSub -> binOp vm (-)
    OpMod -> do stepMod vm; pure Nothing
    OpSmod -> do stepSMod vm; pure Nothing
    OpDiv -> do stepDiv vm; pure Nothing
    OpSdiv -> do stepSDiv vm; pure Nothing
    OpAddmod -> do stepAddMod vm; pure Nothing
    OpMulmod -> do stepMulMod vm; pure Nothing
    OpExp -> do stepExp vm; pure Nothing
    OpAnd -> binOp vm (.&.)
    OpOr -> binOp vm (.|.)
    OpXor -> binOp vm (.^.)
    OpNot -> do stepNot vm; pure Nothing
    OpByte -> do stepByte vm; pure Nothing
    OpShr -> do stepShr vm; pure Nothing
    OpShl -> do stepShl vm; pure Nothing
    OpSar -> do stepSar vm; pure Nothing
    OpSignextend -> do stepSignExtend vm; pure Nothing
    OpPush0 -> do push vm 0; pure Nothing
    OpPush n -> do stepPushN vm n; pure Nothing
    OpPop -> do _ <- pop vm; pure Nothing
    OpDup n -> do stepDupN vm n; pure Nothing
    OpSwap n -> do stepSwapN vm n; pure Nothing
    OpLt -> do stepLt vm; pure Nothing
    OpGt -> do stepGt vm; pure Nothing
    OpSlt -> do stepSLt vm; pure Nothing
    OpSgt -> do stepSGt vm; pure Nothing
    OpEq -> do stepEq vm; pure Nothing
    OpIszero -> do stepIsZero vm; pure Nothing
    OpJump -> do stepJump vm
    OpJumpi -> do stepJumpI vm
    OpJumpdest -> pure Nothing
    OpMload -> stepMLoad vm
    OpMstore -> stepMStore vm
    OpMstore8 -> stepMStore8 vm
    OpSload -> stepSLoad vm
    OpSstore -> stepSStore vm
    OpCallvalue -> do stepCallValue vm; pure Nothing
    OpCalldatasize -> do stepCallDataSize vm; pure Nothing
    OpCalldataload -> do stepCallDataLoad vm; pure Nothing
    OpCall -> do stepCall vm; pure Nothing
    OpSha3 -> do stepKeccak vm; pure Nothing
    _ -> internalError ("Unknown opcode: " ++ show op)
  where
    binOp vm' f = do
      x <- pop vm'
      y <- pop vm'
      push vm' (x `f` y)
      pure Nothing

stepPushN :: MVM s -> Word8 -> ST s ()
stepPushN vm n = do
  pc <- readPC vm
  bs <- getCodeByteString vm
  let n' = fromIntegral n
  if pc + n' > BS.length bs
    then internalError "PUSH: not enough bytes"
    else do
      let pushValue = BS.take n' (BS.drop pc bs)
      push vm (word pushValue)
      advancePC vm n'

stepDupN :: MVM s -> Word8 -> ST s ()
stepDupN vm n = do
  val <- stackSlot vm (n - 1)
  push vm val

stepSwapN :: MVM s -> Word8 -> ST s ()
stepSwapN vm n = do
  topVal <- stackSlot vm 0
  otherVal <- stackSlot vm n
  stackPointer <- getStackPointer vm
  stack <- getStack vm
  let topSlot = stackPointer - 1
  let otherSlot = topSlot - (fromIntegral n)
  MVec.write stack topSlot otherVal
  MVec.write stack otherSlot topVal

stepSLt :: MVM s -> ST s ()
stepSLt vm = comparison vm slt
  where
    slt x y =
      let sx, sy :: Int256
          sx = fromIntegral x
          sy = fromIntegral y
      in if sx < sy then 1 else 0

stepSGt :: MVM s -> ST s ()
stepSGt vm = comparison vm sgt
  where
    sgt x y =
      let sx, sy :: Int256
          sx = fromIntegral x
          sy = fromIntegral y
      in if sx > sy then 1 else 0

stepLt :: MVM s -> ST s ()
stepLt vm = comparison vm (\x y -> if x < y then 1 else 0)

stepGt :: MVM s -> ST s ()
stepGt vm = comparison vm (\x y -> if x > y then 1 else 0)

stepEq :: MVM s -> ST s ()
stepEq vm = comparison vm (\x y -> if x == y then 1 else 0)

stepIsZero :: MVM s -> ST s ()
stepIsZero vm = do
  current <- pop vm
  let val = if current == 0 then 1 else 0
  push vm val


comparison :: MVM s -> (VMWord -> VMWord -> VMWord) -> ST s ()
comparison vm op = do
  lhs <- pop vm
  rhs <- pop vm
  push vm (op lhs rhs)

-- top slot = 0, one below is 1, and so on
stackSlot :: MVM s -> Word8 -> ST s VMWord
stackSlot vm n = do
  stackPointer <- getStackPointer vm
  stack <- getStack vm
  let slotPointer = stackPointer - (fromIntegral (n + 1))
  if slotPointer < 0
    then internalError "stack underflow"
    else MVec.read stack slotPointer


push :: MVM s -> VMWord -> ST s ()
push vm val = do
  current <- readSTRef vm.current
  sp <- readSTRef current.state.spRef
  stack <- getStack vm
  MVec.write stack sp val
  writeStackPointer vm (sp + 1)

pop :: MVM s -> ST s VMWord
pop vm = do
  sp <- getStackPointer vm
  if sp <= 0
    then internalError "Stack underflow"
    else do
      stack <- getStack vm
      let !sp' = sp - 1
      writeStackPointer vm sp'
      MVec.read stack sp'

stepMod :: MVM s -> ST s ()
stepMod vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let res = if denumerator == 0 then 0 else numerator `Prelude.mod` denumerator
  push vm res

stepSMod :: MVM s -> ST s ()
stepSMod vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let snum, sden :: Int256
      snum = fromIntegral numerator
      sden = fromIntegral denumerator
  let res = if denumerator == 0 then 0 else fromIntegral (snum `rem` sden)
  push vm res


stepDiv :: MVM s -> ST s ()
stepDiv vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let res = if denumerator == 0 then 0 else numerator `Prelude.div` denumerator
  push vm res

stepSDiv :: MVM s -> ST s ()
stepSDiv vm = do
  numerator <- pop vm
  denumerator <- pop vm
  let snum, sden :: Int256
      snum = fromIntegral numerator
      sden = fromIntegral denumerator
  let res = if denumerator == 0 then 0 else fromIntegral (snum `quot` sden)
  push vm res

stepAddMod :: MVM s -> ST s ()
stepAddMod vm = do
  a <- pop vm
  b <- pop vm
  n <- pop vm
  let res = if n == 0 then 0 else fromIntegral $ (((fromIntegral a) :: Word512) + (fromIntegral b)) `Prelude.mod` (fromIntegral n)
  push vm res

stepMulMod :: MVM s -> ST s ()
stepMulMod vm = do
  a <- pop vm
  b <- pop vm
  n <- pop vm
  let res = if n == 0 then 0 else fromIntegral $ (((fromIntegral a) :: Word512) * (fromIntegral b)) `Prelude.mod` (fromIntegral n)
  push vm res

stepExp :: MVM s -> ST s ()
stepExp vm = do
  base <- pop vm
  exponent <- pop vm
  unless (exponent == 0) $ burn vm (extraExpGasCost exponent)
  let res = base ^ exponent
  push vm res

stepNot :: MVM s -> ST s ()
stepNot vm = do
  arg <- pop vm
  push vm (complement arg)

capAsWord64 :: W256 -> Word64
capAsWord64 w256 = case deconstructWord256ToWords w256 of
  (0, 0, 0, w64) -> w64
  _ -> maxBound


stepByte :: MVM s -> ST s ()
stepByte vm = do
  byteOffset <- pop vm
  value <- pop vm
  let offset64 :: Word64 = capAsWord64 byteOffset
      result = if offset64 >= 32 then 0 else
                let shift = (31 - fromIntegral offset64) * 8
                in (value `shiftR` shift) .&. 0xFF
  push vm result

stepShr :: MVM s -> ST s ()
stepShr vm = do
  shift <- pop vm
  value <- pop vm
  let shifted = if shift > 255 then 0 else value `shiftR` (fromIntegral shift)
  push vm shifted

stepShl :: MVM s -> ST s ()
stepShl vm = do
  shift <- pop vm
  value <- pop vm
  let shifted = if shift > 255 then 0 else value `shiftL` (fromIntegral shift)
  push vm shifted

stepSar :: MVM s -> ST s ()
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

stepSignExtend :: MVM s -> ST s ()
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


fetchByte :: MVM s -> ST s Word8
fetchByte vm = do
  pc <- readPC vm
  code <- getCodeByteString vm
  if pc >= BS.length code
    then internalError "PC out of range"
    else pure (BS.index code pc)

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

getCodeByteString :: MVM s -> ST s BS.ByteString
getCodeByteString vm = do
  current <- readSTRef vm.current
  case current.context.code of (RuntimeCode bs) -> pure bs

getMemory :: MVM s -> ST s (Memory s)
getMemory vm = do
  current <- readSTRef vm.current
  pure current.state.memory

getCurrentFrame :: MVM s -> ST s (MFrame s)
getCurrentFrame vm = readSTRef vm.current

getAvailableGas :: MFrame s -> ST s Gas
getAvailableGas frame = readSTRef frame.state.gasRemainingRef

getCurrentAccounts :: MVM s -> ST s Accounts
getCurrentAccounts vm = do
  frame <- getCurrentFrame vm
  pure frame.state.accounts

stepJump :: MVM s -> ST s (Maybe VMResult)
stepJump vm = do
  jumpDest <- pop vm
  tryJump vm $ fromIntegral jumpDest

stepJumpI :: MVM s -> ST s (Maybe VMResult)
stepJumpI vm = do
  jumpDest <- pop vm
  condition <- pop vm
  if condition == 0 then pure Nothing else tryJump vm $ fromIntegral jumpDest

tryJump :: MVM s -> Int -> ST s (Maybe VMResult)
tryJump vm dest = do
  code <- getCodeByteString vm
  if isValidJumpDest code dest
  then do
    writePC vm dest
    pure Nothing
  else pure $ Just $ VMFailure BadJumpDestination
  where
    isValidJumpDest code jumpDest = (fromMaybe (0 :: Word8) $ BS.indexMaybe code jumpDest) == 0x5b

stepCallValue :: MVM s -> ST s ()
stepCallValue vm = do
  frame <- getCurrentFrame vm
  let CallValue val = frame.context.callValue
  push vm val

stepCallDataSize :: MVM s -> ST s ()
stepCallDataSize vm = do
  frame <- getCurrentFrame vm
  let CallData dataBS = frame.context.callData
  let size = BS.length dataBS
  push vm (fromIntegral size)

stepCallDataLoad :: MVM s -> ST s ()
stepCallDataLoad vm = do
  frame <- getCurrentFrame vm
  offsetWord <- pop vm
  let CallData dataBS = frame.context.callData
  let size = BS.length dataBS
      offset = fromIntegral offsetWord
  -- Extract up to 32 bytes or fewer if out of bounds
      slice | offset >= size = BS.replicate 32 0
            | offset + 32 <= size = BS.take 32 (BS.drop offset dataBS)
            | otherwise =
                let available = BS.drop offset dataBS
                    missing   = 32 - BS.length available
                in available <> BS.replicate missing 0

      -- Convert 32 bytes big-endian to W256
      callDataWord = BS.foldl' (\acc b -> (acc `shiftL` 8) .|. fromIntegral b) 0 slice
  push vm callDataWord

stepCall :: MVM s -> ST s ()
stepCall vm = do
  gas <- pop vm
  address <- pop vm
  value <- pop vm
  argsOffset <- pop vm
  argsSize <- pop vm
  retOffset <- pop vm
  retSize <- pop vm
  calldata <- readMemory vm argsOffset argsSize
  -- Debug.Trace.traceM $ "Call with value: " <> show value
  when (value /= 0) $ internalError "TODO: Handle calling with value"
  let to = truncateToAddr address
  targetCode <- lookupCode vm to
  -- let RuntimeCode bs = targetCode
  -- Debug.Trace.traceM ("Calling " <> (show $ ByteStringS bs))
  currentFrame <- getCurrentFrame vm
  let accessCost = vm.fees.g_cold_account_access -- TODO: maintain access lists
  burn' currentFrame (Gas accessCost)
  availableGas <- getAvailableGas currentFrame
  let accounts = currentFrame.state.accounts
      requestedGas = (Gas $ fromIntegral gas)
      gasToTransfer = computeGasToTransfer availableGas requestedGas
  newFrameState <- newMFrameState accounts gasToTransfer
  burn' currentFrame gasToTransfer
  let
      newFrameContext = FrameContext targetCode (CallData calldata) (CallValue value) accounts to to currentFrame.context.codeAddress -- TODO: code or sotrage address?
      newFrame = MFrame newFrameContext newFrameState
  setReturnInfo newFrame (retOffset, retSize)
  pushFrame vm newFrame

  where
    computeGasToTransfer (Gas availableGas) (Gas requestedGas) = Gas $ Prelude.min (EVM.allButOne64th availableGas) requestedGas

lookupCode :: MVM s -> Addr -> ST s RuntimeCode
lookupCode vm address = do
  accounts <- getCurrentAccounts vm
  let account = fromMaybe (internalError "Lookup of unknown address") $ StrictMap.lookup address accounts
  pure account.accCode

setReturnInfo :: MFrame s -> (W256, W256)-> ST s ()
setReturnInfo (MFrame _ state) retInfo = do
  writeSTRef state.retInfoRef (Just retInfo)

getReturnInfo :: MFrame s -> ST s (W256, W256)
getReturnInfo (MFrame _ state) = do
  retInfo <- readSTRef state.retInfoRef
  case retInfo of
    Nothing -> internalError "Return error not set!"
    Just info -> pure info

stepKeccak :: MVM s -> ST s ()
stepKeccak vm = do
  offset <- pop vm
  size <- pop vm
  bs <- readMemory vm offset size
  let hash = keccak' bs
  push vm hash

stepReturn :: MVM s -> ST s (Maybe VMResult)
stepReturn vm = do
  offset <- pop vm
  size <- pop vm
  returnWithData vm offset size

returnWithData :: MVM s -> W256 -> W256 -> ST s (Maybe VMResult)
returnWithData vm offset size = do
  bs <- readMemory vm offset size
  finishFrame vm (VMSuccess bs)

finishFrame :: MVM s -> VMResult -> ST s (Maybe VMResult)
finishFrame vm result = do
  frames <- readSTRef vm.frames
  case frames of
    [] -> pure $ Just result

    nextFrame:rest -> do
      finishingFrame <- getCurrentFrame vm
      accounts <- getCurrentAccounts vm
      unspentGas <- getAvailableGas finishingFrame
      (retOffset, retSize) <- getReturnInfo finishingFrame
      let updatedFrame = nextFrame {state = nextFrame.state {accounts = accounts}}
      writeSTRef vm.current updatedFrame
      writeSTRef vm.frames rest
      currentFrame <- getCurrentFrame vm
      unburn' currentFrame unspentGas
      case result of
        VMSuccess returnData -> do
          memory <- getMemory vm
          writeMemory memory retOffset (BS.take (fromIntegral retSize) returnData)
          push vm 1

        VMFailure _ -> do
          push vm 0
          internalError "TODO: Not implemented!"
      pure Nothing


-- isRootFrame :: MVM s -> ST s Bool
-- isRootFrame vm = do
--   frames <- readSTRef vm.frames
--   pure (null frames)

stepMLoad :: MVM s -> ST s (Maybe VMResult)
stepMLoad vm = {-# SCC "MLOAD" #-} do
  offset <- pop vm
  memory <- getMemory vm
  v <- memLoad32 memory (fromIntegral offset)
  push vm v
  pure Nothing

stepMStore :: MVM s -> ST s (Maybe VMResult)
stepMStore vm = {-# SCC "MSTORE" #-} do
  off <- pop vm
  val <- pop vm
  memory <- getMemory vm
  memStore32 memory off val
  pure Nothing

stepMStore8 :: MVM s -> ST s (Maybe VMResult)
stepMStore8 vm = do
  off <- pop vm
  val <- pop vm
  memory <- getMemory vm
  memStore1 memory off val
  pure Nothing

stepSLoad :: MVM s -> ST s (Maybe VMResult)
stepSLoad vm = do
  key <- pop vm
  store <- getCurrentStorage vm
  isWarm <- touchCurrentStore vm key
  burn vm $ if isWarm then feeSchedule.g_warm_storage_read else feeSchedule.g_cold_sload
  let val = sload store key
  push vm val
  pure Nothing

stepSStore :: MVM s -> ST s (Maybe VMResult)
stepSStore vm = do
  key <- pop vm
  val <- pop vm
  isWarm <- touchCurrentStore vm key
  let warmCost = warmStoreCost 0 0 val -- FIXME: get original and current value
      totalGasCost = if isWarm then warmCost else warmCost + feeSchedule.g_cold_sload
  burn vm totalGasCost
  store <- getCurrentStorage vm
  let updatedStore = sstore store key val
  setCurrentStorage vm updatedStore
  pure Nothing

  where
    warmStoreCost originalValue currentValue newValue
      | newValue == currentValue = feeSchedule.g_sload
      | currentValue == originalValue = if originalValue == 0 then feeSchedule.g_sset else feeSchedule.g_sreset
      | otherwise = feeSchedule.g_sload

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
  sizeRef :: STRef s Word64
}

newMemory :: ST s (Memory s)
newMemory = do
    v <- UMVec.new 0
    ref <- newSTRef v
    size <- newSTRef 0
    pure (Memory ref size)

readMemory :: MVM s -> W256 -> W256 -> ST s BS.ByteString
readMemory vm offset size =
  case (,) <$> toWord64 offset <*> toWord64 size of
    Nothing -> internalError "TODO: handle properly with VMError"
    Just (offset64, size64) -> do
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

writeMemory :: Memory s -> W256 -> BS.ByteString -> ST s ()
writeMemory (Memory memRef sizeRef) offset bs
  | BS.null bs = pure ()
  | otherwise = do
      vec <- readSTRef memRef
      let off = fromIntegral offset
          len = BS.length bs
          requiredSize = off + len
          vecSize = UMVec.length vec
      vec' <- if requiredSize <= vecSize
              then pure vec
              else do vec' <- grow vec requiredSize; writeSTRef memRef vec'; pure vec'
      actualSize <- readSTRef sizeRef

      let requiredSizeWord64 :: Word64 = fromIntegral requiredSize
      when (requiredSizeWord64 > actualSize) $ writeSTRef sizeRef requiredSizeWord64
      -- now write the bytes
      let writeByte i
            | i == len  = pure ()
            | otherwise = do
                let b = BS.index bs i
                UMVec.unsafeWrite vec' (off + i) b
                writeByte (i + 1)
      writeByte 0

touchMemory :: MVM s -> Memory s -> Word64 -> Word64 -> ST s ()
touchMemory _ _ _ 0 = pure ()
touchMemory vm (Memory _ sizeRef) offset size = do
  currentSizeInBytes <- readSTRef sizeRef
  let sizeAfterTouch = offset + size
  when (sizeAfterTouch > currentSizeInBytes) $ do
    let memoryExpansionCost = memoryCost sizeAfterTouch - memoryCost currentSizeInBytes
    when (memoryExpansionCost > 0) $ do 
      burn vm memoryExpansionCost
      writeSTRef sizeRef sizeAfterTouch

memoryCost :: Word64 -> Gas
memoryCost sizeInBytes =
  let
    fees = feeSchedule
    wordCount = ceilDiv sizeInBytes 32
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
  let off = fromIntegral offset
      requiredSize = off + 32
      vecSize = UMVec.length vec
  vec' <- if requiredSize <= vecSize
          then pure vec
          else do vec' <- grow vec requiredSize; writeSTRef memRef vec'; pure vec'
  actualSize <- readSTRef sizeRef

  let requiredSizeWord64 :: Word64 = fromIntegral requiredSize
  when (requiredSizeWord64 > actualSize) $ writeSTRef sizeRef requiredSizeWord64

  -- EVM stores big-endian
  let (w0, w1, w2, w3) = deconstructWord256ToWords value

  -- write 32 bytes using fast Word64 stores
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
memStore1 (Memory memRef sizeRef) offset value = do
  vec <- readSTRef memRef
  let off = fromIntegral offset
      requiredSize = off + 1
      vecSize = UMVec.length vec
  vec' <- if requiredSize <= vecSize
          then pure vec
          else do vec' <- grow vec requiredSize; writeSTRef memRef vec'; pure vec'
  actualSize <- readSTRef sizeRef
  let requiredSizeWord64 :: Word64 = fromIntegral requiredSize
  when (requiredSizeWord64 > actualSize) $ writeSTRef sizeRef requiredSizeWord64

  let byte = fromIntegral (value .&. 0xff)
  UMVec.write vec' off byte
  writeSTRef sizeRef (fromIntegral off + 1)

-- NOTE: This assumes that required size is greater than current size, it does not check it!
grow :: UMVec.MVector s Word8 -> Int -> ST s (UMVec.MVector s Word8)
grow vec requiredSize = {-# SCC "grow" #-} do
  let currentSize = UMVec.length vec
  let growthFactor = 2
  let targetSize = max requiredSize (currentSize * growthFactor)
  -- Always grow at least 8k
  let toGrow = max 8192 $ targetSize - currentSize
  UMVec.grow vec toGrow


------------------- GAS helpers --------------------------------

getGasRefund :: MVM s -> ST s Gas
getGasRefund vm = do
  frame <- getCurrentFrame vm
  readSTRef frame.state.gasRefundedRef

burn :: MVM s -> Gas -> ST s ()
burn vm gas = do
  frame <- getCurrentFrame vm
  burn' frame gas

burn' :: MFrame s -> Gas -> ST s ()
burn' frame (Gas toBurn) = do
  let gasRef = frame.state.gasRemainingRef
  (Gas gasRemaining) <- readSTRef gasRef
  if toBurn > gasRemaining then internalError "TODO: Handle insufficient gas!" else writeSTRef gasRef (Gas $ gasRemaining - toBurn)

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

burnStaticGas :: MVM s -> GenericOp Word8 -> ST s ()
burnStaticGas vm op = do
  let FeeSchedule {..} = vm.fees
  let cost = case op of
        OpStop -> g_zero
        OpReturn -> g_zero
        OpAdd -> g_verylow
        OpMul -> g_low
        OpSub -> g_verylow
        OpMod -> g_low
        OpSmod -> g_low
        OpDiv -> g_low
        OpSdiv -> g_low
        OpAddmod -> g_mid
        OpMulmod -> g_mid
        OpExp -> g_exp
        OpAnd -> g_verylow
        OpOr -> g_verylow
        OpXor -> g_verylow
        OpNot -> g_verylow
        OpByte -> g_verylow
        OpShr -> g_verylow
        OpShl -> g_verylow
        OpSar -> g_verylow
        OpSignextend -> g_low
        OpPush0 -> g_base
        OpPush _ -> g_verylow
        OpPop -> g_base
        OpDup _ -> g_verylow
        OpSwap _ -> g_verylow
        OpLt -> g_verylow
        OpGt -> g_verylow
        OpSlt -> g_verylow
        OpSgt -> g_verylow
        OpEq -> g_verylow
        OpIszero -> g_verylow
        OpJump -> g_mid
        OpJumpi -> g_high
        OpJumpdest -> g_jumpdest
        OpMload -> g_verylow
        OpMstore -> g_verylow
        OpMstore8 -> g_verylow
        OpSload -> g_zero -- Custom rules
        OpSstore -> g_zero -- Custom rules
        OpCallvalue -> g_base
        OpCalldatasize -> g_verylow
        OpCalldataload -> g_verylow
        OpCall -> g_zero -- Cost for CALL depends on if we are accessing cold or warm address
        OpSha3 -> g_sha3
        _ -> internalError ("Unknown opcode: " ++ show op)
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
