{-# LANGUAGE GADTs #-}

-- | Batched execution for concrete runtime bytecode. Clients observe the
-- original instruction offsets while the evaluator keeps stack, gas and PC
-- local across instructions. Unsupported or exceptional steps return to
-- the caller at the precise VM state where normal @exec1@ can resume.
module EVM.Concrete.Blocks
  ( Program, ProgramCache, newProgramCache, prepareProgram
  , Scratch, newScratch, runConcreteBlocks
  ) where

import Data.Bits ((.&.), complement, toIntegralSized)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSUnsafe
import Data.DoubleWord (Word128(..), Word256(..))
import Data.Maybe (fromMaybe, isNothing)
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import Data.Vector.Storable.Mutable qualified as SM
import Data.Vector.Unboxed qualified as U
import Data.Word (Word8, Word64)
import Foreign.Marshal.Alloc (allocaBytesAligned)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr, ptrToIntPtr)
import Foreign.Storable (peekByteOff, pokeByteOff)
import Witch (into, unsafeInto)

import EVM (currentContract, isOpStart, isPrecompileAddr', memoryCost)
import EVM.Concrete.Blocks.Plan
import EVM.Expr qualified as Expr
import EVM.FeeSchedule (FeeSchedule(..))
import EVM.HashCons (hashConsExpr)
import EVM.Types (ContractCode(..), EType(EWord), Expr(..), FrameState(..), RuntimeCode(..), VM(..), VMType(Concrete))
import EVM.Types qualified as EVM

-- | Scratch space for one executing thread. Allocate it independently per worker.
newtype Scratch = Scratch (MV.IOVector (Expr EWord))

newScratch :: IO Scratch
newScratch = Scratch <$> MV.new (scratchInputs + maxBlockLength)

-- The suffix that the block never reads remains a persistent list. Temporary
-- addresses are relative to a disjoint area of the same transaction-local vector.
applyBlock :: Scratch -> StackBlock -> [Expr EWord] -> IO [Expr EWord]
applyBlock (Scratch scratch) block stack = do
  tailStack <- loadInputs 0 stack
  runActions 0 block.actions
  buildOutput block.outputs tailStack
  where
    loadInputs !i xs | i == block.required = pure xs
    loadInputs i (x:xs) = MV.write scratch i x >> loadInputs (i+1) xs
    loadInputs _ [] = EVM.internalError "validated stack is shorter than the block inputs"

    readSource (Input i) = MV.read scratch i
    readSource (Temporary i) = MV.read scratch (scratchInputs + i)
    readSource (Constant word) = pure word

    runActions _ [] = pure ()
    runActions !i (op:ops) = do
      value <- case op of
        ApplyOne f a -> hashConsExpr . f <$> readSource a
        ApplyTwo f a b -> do
          x <- readSource a
          y <- readSource b
          pure (hashConsExpr (f x y))
      MV.write scratch (scratchInputs + i) value
      runActions (i+1) ops

    buildOutput [] xs = pure xs
    buildOutput (source:rest) xs = do
      x <- readSource source
      buildOutput rest (x:xs)

-- | Run only complete, affordable stack transitions. The original interpreter
-- handles the next instruction at its exact PC, including out-of-gas,
-- underflow/overflow, invalid jumps, precompiles and nonconcrete code.
-- Both callbacks run in execution order. The vector callback receives the
-- PCs of one affordable block and is equivalent to visiting each PC in it.
-- On return, execute one normal VM step to make progress if the PC is
-- unsupported or a guard failed.
runConcreteBlocks
  :: Scratch -> Maybe Program -> (Int -> a -> IO a) -> (U.Vector Int -> a -> IO a)
  -> VM Concrete -> a -> IO (VM Concrete, a)
runConcreteBlocks scratch (Just (Program bytes entries)) visit visitBlock vm initialContext
  | Nothing <- vm.result
  , RuntimeCode (ConcreteRuntimeCode current) <- frame.code
  , current == bytes
  , LitAddr address <- frame.contract
  , not (isPrecompileAddr' address)
  , frame.pc >= 0 && frame.pc < V.length entries =
      case V.unsafeIndex entries frame.pc of
        Standard -> pure (vm, initialContext)
        _ -> loop False frame.pc frame.gas frame.memorySize (length frame.stack) frame.stack initialContext
  where
    frame = vm.state
    fees = vm.block.schedule
    -- Contract lookup is invariant across the instructions in this run.
    jumpMap = (\contract -> contract.opIxMap) <$> currentContract vm
    maxWordEnd = fromMaybe maxBound (intOffset Expr.maxBytes)
    jumpTarget w
      | Just pc <- intOffset w
      , pc < BS.length bytes
      , BSUnsafe.unsafeIndex bytes pc == 0x5b
      , Just opMap <- jumpMap, isOpStart opMap pc = Just pc
      | otherwise = Nothing

    -- A custom schedule could overflow Word64 when fees are added together.
    affordableSchedule = maximum [fees.g_base, fees.g_verylow, fees.g_jumpdest]
                         <= maxBound `div` unsafeInto maxBlockLength

    loop !changed !pc !gas !memorySize !height stack !context =
      let finish
            | changed =
                let next = frame { pc = pc, gas = gas, memorySize = memorySize, stack = stack }
                in pure (vm { state = next, burned = vm.burned + (frame.gas - gas) }, context)
            | otherwise = pure (vm, context)

          jump cost target consumed rest = do
            context' <- visit pc context
            loop True target (gas-cost) memorySize (height-consumed) rest context'

          -- Stay on the fast path only while the backing vector still fits.
          -- hevm handles allocation, symbolic accesses and every fault.
          wordAccess offset action = case frame.memory of
            EVM.ConcreteMemory mem
              | isNothing frame.symMemorySize
              , Just off <- intOffset offset
              , off < unsafeInto EVM.memoryAccessLimit
              , off <= maxWordEnd - 32
              , off <= SM.length mem - 32
              , memorySize .&. 31 == 0
              , gas >= fees.g_verylow ->
                  let end = unsafeInto off + 32
                      size = max memorySize ((end + 31) .&. complement 31)
                      expansion = if size == memorySize then 0 else
                        memoryCost fees size - memoryCost fees memorySize
                  in if expansion <= gas - fees.g_verylow
                    then action mem off size (gas - fees.g_verylow - expansion)
                    else finish
            _ -> finish

      in if pc < 0 || pc >= V.length entries then finish else
        case V.unsafeIndex entries pc of
          StackRun block
            | height >= block.required
            , height + block.peakGrowth <= 1024
            , affordableSchedule
            , let cost = block.baseCount * fees.g_base + block.veryLowCount * fees.g_verylow
                         + block.destCount * fees.g_jumpdest
            , cost <= gas -> do
                stack' <- applyBlock scratch block stack
                context' <- visitBlock block.pcs context
                loop True block.endPC (gas-cost) memorySize (height+block.heightChange) stack' context'
          ReadField field | height < 1024 && gas >= fees.g_base ->
            let remaining = gas - fees.g_base
                pushField value = do
                  context' <- visit pc context
                  loop True (pc+1) remaining memorySize (height+1) (value:stack) context'
            in case field of
              Caller -> case frame.caller of
                LitAddr addr -> pushField (Expr.litAddr addr)
                _ -> finish
              CallValue -> pushField frame.callvalue
              CallDataSize -> pushField (Expr.bufLength frame.calldata)
              ReturnDataSize -> pushField (Expr.bufLength frame.returndata)
              RemainingGas -> pushField (Lit (into remaining))
          LoadCallData -> case (stack, frame.calldata) of
            (index@(Lit off):rest, buf@(ConcreteBuf bytes'))
              | gas >= fees.g_verylow -> do
                  -- Compare the full-width offset before narrowing it. Reading
                  -- at/past the end yields a zero word, even near 2^256.
                  value <- case intOffset off of
                    Just n | n < BS.length bytes' ->
                      if BS.length bytes' - n >= 32
                        then Lit <$> BSUnsafe.unsafeUseAsCString bytes'
                               (\p -> readWordAt (castPtr p `plusPtr` n))
                        else pure (hashConsExpr (Expr.readWord index buf))
                    _ -> pure (Lit 0)
                  context' <- visit pc context
                  loop True (pc+1) (gas-fees.g_verylow) memorySize height (value:rest) context'
            _ -> finish
          LoadWord -> case stack of
            Lit offset:xs -> wordAccess offset $ \mem off size remaining -> do
              value <- SM.unsafeWith mem $ \p -> readWordAt (p `plusPtr` off)
              context' <- visit pc context
              loop True (pc+1) remaining size height (Lit value:xs) context'
            _ -> finish
          StoreWord -> case stack of
            Lit offset:Lit value:xs -> wordAccess offset $ \mem off size remaining -> do
              SM.unsafeWith mem $ \p -> writeWordAt (p `plusPtr` off) value
              context' <- visit pc context
              loop True (pc+1) remaining size (height-2) xs context'
            _ -> finish
          Jump -> case stack of
            Lit w:xs | gas >= fees.g_mid, Just target <- jumpTarget w ->
              jump fees.g_mid target 1 xs
            _ -> finish
          JumpIf -> case stack of
            Lit _:Lit 0:xs | gas >= fees.g_high -> jump fees.g_high (pc+1) 2 xs
            Lit w:Lit condition:xs | condition /= 0 && gas >= fees.g_high, Just target <- jumpTarget w ->
              jump fees.g_high target 2 xs
            _ -> finish
          _ -> finish
runConcreteBlocks _ _ _ _ vm context = pure (vm, context)

-- Reject oversized offsets before narrowing them to a machine word.
wordOffset :: EVM.W256 -> Maybe Word64
wordOffset (EVM.W256 (Word256 (Word128 0 0) (Word128 0 lo))) = Just lo
wordOffset _ = Nothing
{-# INLINE wordOffset #-}

intOffset :: EVM.W256 -> Maybe Int
intOffset w = wordOffset w >>= toIntegralSized
{-# INLINE intOffset #-}

-- hevm's words use four big-endian limbs. Typed loads require an aligned
-- address. The byte-copy path also handles unaligned slices on strict targets.
readWordAt :: Ptr Word8 -> IO EVM.W256
readWordAt ptr
  | ptrToIntPtr ptr .&. 7 /= 0 = allocaBytesAligned 32 8 $ \aligned -> do
      copyBytes aligned ptr 32
      readAligned aligned
  | otherwise = readAligned ptr

readAligned :: Ptr Word8 -> IO EVM.W256
readAligned ptr = do
  let limb offset = EVM.hton64 <$> peekByteOff ptr offset
  a <- limb 0
  b <- limb 8
  c <- limb 16
  d <- limb 24
  pure (EVM.W256 (Word256 (Word128 a b) (Word128 c d)))

writeWordAt :: Ptr Word8 -> EVM.W256 -> IO ()
writeWordAt ptr value
  | ptrToIntPtr ptr .&. 7 /= 0 = allocaBytesAligned 32 8 $ \aligned -> do
      writeAligned aligned value
      copyBytes ptr aligned 32
  | otherwise = writeAligned ptr value

writeAligned :: Ptr Word8 -> EVM.W256 -> IO ()
writeAligned ptr (EVM.W256 (Word256 (Word128 a b) (Word128 c d))) = do
  pokeByteOff ptr 0 (EVM.hton64 a)
  pokeByteOff ptr 8 (EVM.hton64 b)
  pokeByteOff ptr 16 (EVM.hton64 c)
  pokeByteOff ptr 24 (EVM.hton64 d)
