{-# LANGUAGE GADTs #-}

-- | Predecode the stack effect of short stretches of concrete runtime code.
-- The input stack stays persistent across hevm frames. Only the slots that a
-- block reads and its arithmetic intermediates need indexed scratch storage.
module EVM.Concrete.Blocks.Plan
  ( Entry(..), StackBlock(..), Program(..), ProgramCache, newProgramCache, prepareProgram
  , Source(..), Action(..), scratchInputs, maxBlockLength
  ) where

import Data.ByteString qualified as BS
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import qualified Data.List as List
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import Data.Vector.Unboxed qualified as U
import Data.Word (Word64)
import Witch (into)

import EVM.Expr qualified as Expr
import EVM.HashCons (hashConsExpr)
import EVM.Op (getOp)
import EVM.Types (ContractCode(..), EType(EWord), Expr(Lit), GenericOp(..), RuntimeCode(..), internalError, word)

type Operand = Expr EWord

data Source = Input !Int | Constant !Operand | Temporary !Int

data Action
  = ApplyOne (Operand -> Operand) !Source
  | ApplyTwo (Operand -> Operand -> Operand) !Source !Source

data Fee = Base | VeryLow | Destination deriving Eq
data Instruction
  = Push !Operand | Duplicate !Int | Exchange !Int | Pop | DestinationMarker
  | Unary (Operand -> Operand) | Binary (Operand -> Operand -> Operand)

data StackBlock = StackBlock
  { endPC        :: !Int
  , required     :: !Int
  , peakGrowth   :: !Int
  , heightChange :: !Int
  , pcs          :: !(U.Vector Int)
  , baseCount    :: !Word64
  , veryLowCount :: !Word64
  , destCount    :: !Word64
  , actions      :: ![Action]
  , outputs      :: ![Source] -- deepest first, for rebuilding a shared list tail
  }

data Entry = Standard | StackRun !StackBlock

data Program = Program !BS.ByteString !(V.Vector Entry)
-- | A bounded, shareable cache of analysed runtime bytecode.
newtype ProgramCache = ProgramCache (IORef [(BS.ByteString, Program)])

newProgramCache :: IO ProgramCache
newProgramCache = ProgramCache <$> newIORef []

maxBlockLength, scratchInputs :: Int
maxBlockLength = 64
-- Each preceding instruction can remove at most one net slot. SWAP16
-- needs seventeen live operands at the final instruction.
scratchInputs = maxBlockLength - 1 + 17

-- | Look up or analyse concrete runtime code. Init code and symbolic code use exec1.
prepareProgram :: ProgramCache -> ContractCode -> IO (Maybe Program)
prepareProgram (ProgramCache cache) (RuntimeCode (ConcreteRuntimeCode bytes)) = do
  recentlyUsed <- readIORef cache
  case lookup bytes recentlyUsed of
    Just program -> pure (Just program)
    Nothing -> do
      -- Publish a single shared thunk. Concurrent workers can use the same
      -- analysis without holding the IORef while it scans the bytecode.
      program <- atomicModifyIORef' cache $ \entries ->
        case lookup bytes entries of
          Just shared -> (entries, shared)
          Nothing ->
            let shared = analyse bytes
            in ((bytes, shared) : take 15 entries, shared)
      pure (Just program)
prepareProgram _ _ = pure Nothing

decode :: BS.ByteString -> Int -> Maybe (Fee, Instruction, Int)
decode bytes pc = case getOp (BS.index bytes pc) of
  OpPush0 -> base (Push (Lit 0))
  OpPush width ->
    let size = into width
        value = word (BS.take size (BS.drop (pc + 1) bytes))
    in Just (VeryLow, Push (Lit value), pc + 1 + size)
  OpDup depth -> cheap (Duplicate (into depth - 1))
  OpSwap depth -> cheap (Exchange (into depth))
  OpPop -> base Pop
  OpJumpdest -> Just (Destination, DestinationMarker, pc + 1)
  OpAdd -> binary Expr.add
  OpSub -> binary Expr.sub
  OpLt -> binary Expr.lt
  OpGt -> binary Expr.gt
  OpSlt -> binary Expr.slt
  OpSgt -> binary Expr.sgt
  OpEq -> binary Expr.eq
  OpIszero -> cheap (Unary Expr.iszero)
  OpAnd -> binary Expr.and
  OpOr -> binary Expr.or
  OpXor -> binary Expr.xor
  OpNot -> cheap (Unary Expr.not)
  OpShl -> binary Expr.shl
  OpShr -> binary Expr.shr
  _ -> Nothing
  where
    base op = Just (Base, op, pc + 1)
    cheap op = Just (VeryLow, op, pc + 1)
    binary = cheap . Binary

data Analysis = Analysis
  { stack       :: [Source]
  , reverseOps  :: [Action]
  , temps       :: !Int
  , change      :: !Int
  , need        :: !Int
  , peak        :: !Int
  , baseFees    :: !Word64
  , veryLowFees :: !Word64
  , destFees    :: !Word64
  }

-- Start with symbolic slot numbers. Taking a prefix at the end reveals just
-- the outputs that differ from the untouched tail of the entry stack.
initial :: Analysis
initial = Analysis (map Input [0..]) [] 0 0 0 0 0 0 0

apply :: Analysis -> (Fee, Instruction) -> Analysis
apply state (fee, ins) =
  let (arity, adjustment, slots, op) = transform ins state.stack
      change = state.change + adjustment
      next = state
        { stack = slots, change = change, need = max state.need (arity - state.change)
        , peak = max state.peak change
        , baseFees = if fee == Base then state.baseFees + 1 else state.baseFees
        , veryLowFees = if fee == VeryLow then state.veryLowFees + 1 else state.veryLowFees
        , destFees = if fee == Destination then state.destFees + 1 else state.destFees
        }
  in case op of
    Nothing -> next
    Just action -> next { reverseOps = action : state.reverseOps, temps = state.temps + 1 }
  where
    transform (Push value) xs = (0, 1, Constant value : xs, Nothing)
    transform (Duplicate n) xs = (n+1, 1, (xs !! n) : xs, Nothing)
    transform (Exchange n) (top:xs) = case splitAt (n-1) xs of
      (prefix, old:rest) -> (n+1, 0, old : (prefix ++ (top : rest)), Nothing)
      _ -> internalError "finite stack during bytecode analysis"
    transform Pop (_:xs) = (1, -1, xs, Nothing)
    transform DestinationMarker xs = (0, 0, xs, Nothing)
    transform (Unary f) (Constant x:xs) = (1, 0, Constant (hashConsExpr (f x)) : xs, Nothing)
    transform (Unary f) (x:xs) = (1, 0, Temporary state.temps : xs, Just (ApplyOne f x))
    transform (Binary f) (Constant x:Constant y:xs) =
      (2, -1, Constant (hashConsExpr (f x y)) : xs, Nothing)
    transform (Binary f) (x:y:xs) = (2, -1, Temporary state.temps : xs, Just (ApplyTwo f x y))
    transform _ _ = internalError "finite stack during bytecode analysis"

analyse :: BS.ByteString -> Program
analyse bytes = Program bytes $ V.create $ do
  table <- MV.replicate (BS.length bytes) Standard
  let scan !pc
        | pc >= BS.length bytes = pure ()
        | otherwise = case collect pc 0 [] [] of
            (end, [], _) -> scan end
            (end, operations, positions) -> do
              let a = List.foldl' apply initial (reverse operations)
                  exposed = a.need + a.change
                  block = StackBlock end a.need a.peak a.change (U.fromList (reverse positions))
                            a.baseFees a.veryLowFees a.destFees (reverse a.reverseOps)
                            (reverse (take exposed a.stack))
              MV.write table pc (StackRun block)
              scan end
      collect pc count ops positions
        | pc >= BS.length bytes || count == maxBlockLength = (pc, ops, positions)
        -- A valid jump may enter at this instruction.
        | count > 0 && BS.index bytes pc == 0x5b = (pc, ops, positions)
        | otherwise = case decode bytes pc of
            Just (fee,op,next) -> collect next (count+1) ((fee,op):ops) (pc:positions)
            Nothing -> (if count == 0 then pc+1 else pc, ops, positions)
  scan 0
  pure table
