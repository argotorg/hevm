{-# LANGUAGE GADTs #-}

-- | Batched execution for concrete runtime bytecode. Clients observe the
-- original instruction offsets while the evaluator keeps stack, gas and PC
-- local across instructions. Unsupported or exceptional steps return to
-- the caller at the precise VM state where normal @exec1@ can resume.
module EVM.Concrete.Blocks
  ( Program, ProgramCache, newProgramCache, prepareProgram
  , Scratch, newScratch, runConcreteBlocks
  ) where

import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import Data.Vector.Unboxed qualified as U
import Witch (unsafeInto)

import EVM (isPrecompileAddr')
import EVM.Concrete.Blocks.Plan
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
runConcreteBlocks scratch (Just (Program bytes entries)) _visit visitBlock vm initialContext
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
    -- A custom schedule could overflow Word64 when fees are added together.
    affordableSchedule = maximum [fees.g_base, fees.g_verylow, fees.g_jumpdest]
                         <= maxBound `div` unsafeInto maxBlockLength

    loop !changed !pc !gas !memorySize !height stack !context =
      let finish
            | changed =
                let next = frame { pc = pc, gas = gas, memorySize = memorySize, stack = stack }
                in pure (vm { state = next, burned = vm.burned + (frame.gas - gas) }, context)
            | otherwise = pure (vm, context)

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
          _ -> finish
runConcreteBlocks _ _ _ _ vm context = pure (vm, context)
