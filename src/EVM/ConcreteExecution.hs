module EVM.ConcreteExecution where

import Control.Monad.ST (ST, runST)
import Data.ByteString qualified as BS
import Data.Map
-- import Data.Map qualified as Map
-- import Data.Maybe (fromMaybe)
import Data.Set
import Data.STRef
import Data.Vector.Unboxed.Mutable qualified as MVec
import Data.Word (Word64, Word8)


import EVM.Types (Addr, W64, W256, EvmError, internalError, GenericOp(..))

type Gas = Word64
type VMWord = W256
type Data = BS.ByteString

data ConcreteVM = ConcreteVM
  { 
    code         :: RuntimeCode
  , pc           :: {-# UNPACK #-} !Int -- program counter in BYTES (not ops). PUSH ops will increment pc by more than 1
  , stack        :: [W256]
  }

data MVM s = MVM
  { pcRef    :: STRef s Int
  , stackRef :: MVec.MVector s W256
  , spRef    :: STRef s Int  -- stack pointer (top index)
  , code     :: Data
  }


newtype RuntimeCode = ConcreteRuntimeCode BS.ByteString
  deriving (Show)
newtype Memory = Vector Word8
type ConcreteStore = (Map W256 W256)

type ReturnValue = Data

data VMResult where
  VMFailure :: EvmError -> VMResult            -- ^ An operation failed
  VMSuccess :: ReturnValue -> VMResult         -- ^ Reached STOP, RETURN, or end-of-code

exec :: Data -> VMResult
exec bs = runST $ do 
  pcRef <- newSTRef 0
  stackRef <- MVec.new 1024
  spRef <- newSTRef 0
  let vm = MVM pcRef stackRef spRef bs
  runLoop vm

runLoop :: MVM s -> ST s VMResult
runLoop vm = do
  halted <- stepVM vm
  if halted then do
    sp <- readSTRef (vm.spRef)
    stack <- forM [0 .. sp - 1] (MVec.read (vm.stackRef))
    pure (VMSuccess (reverse stack))
  else runLoop vm


stepVM :: MVM s -> ST s Bool
stepVM vm = do
  byte <- fetchByte vm
  let op = getOp byte
  case op of
    OpStop -> pure True  -- STOP
    OpAdd -> binOp vm (+)
    OpMul -> binOp vm (*)
    OpSub -> binOp vm (-)
    OpPush n -> internalError "TODO"
    _ -> internalError ("Unknown opcode: " ++ show op)
  where
    binOp vm f = do
      y <- pop vm
      x <- pop vm
      push vm ((x `f` y) .&. ((1 `shiftL` 256) - 1)) -- EVM wraps to 256 bits
      pure False

fetchByte :: MVM s -> ST s Word8
fetchByte vm = do
  pc <- readSTRef (vm.pcRef)
  if pc >= BS.length (vm.code)
    then internalError "PC out of range"
    else pure (BS.index (vm.code) pc)

advancePC :: MVM s -> Int -> ST s ()
advancePC vm n = modifySTRef' (vm.pcRef) (+ n)


getOp :: Word8 -> GenericOp Word8
getOp x | x >= 0x80 && x <= 0x8f = OpDup (x - 0x80 + 1)
getOp x | x >= 0x90 && x <= 0x9f = OpSwap (x - 0x90 + 1)
getOp x | x >= 0xa0 && x <= 0xa4 = OpLog (x - 0xa0)
getOp x | x >= 0x60 && x <= 0x7f = OpPush (x - 0x60 + 1)
getOp x = case x of
  0x00 -> OpStop
  0x01 -> OpAdd
  0x02 -> OpMul
  0x03 -> OpSub
  0x04 -> OpDiv
  0x05 -> OpSdiv
  0x06 -> OpMod
  0x07 -> OpSmod
  0x08 -> OpAddmod
  0x09 -> OpMulmod
  0x0a -> OpExp
  0x0b -> OpSignextend
  _ -> internalError "TODO"
