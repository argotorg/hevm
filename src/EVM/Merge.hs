{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | State merging for symbolic execution
--
-- This module provides functions for merging execution paths during symbolic
-- execution. Instead of forking on every JUMPI, we can speculatively execute
-- both paths and merge them using ITE (If-Then-Else) expressions when:
--
-- 1. Both paths converge to the same PC (forward jump pattern)
-- 2. Neither path has side effects (storage, memory, logs unchanged)
-- 3. Both paths have the same stack depth
--
-- This reduces path explosion from 2^N to linear in many common patterns.

module EVM.Merge
  ( tryMergeForwardJump
  ) where

import Control.Monad (when)
import Control.Monad.State.Strict (get, put)
import Debug.Trace (traceM)
import Optics.Core
import Optics.State

import EVM.Effects (Config(..))
import EVM.Expr qualified as Expr
import EVM.Types

-- | Execute instructions speculatively until target PC is reached or
-- we hit budget limit/SMT query/RPC call/revert/error.
speculateLoopOuter
  :: Config
  -> EVM Symbolic ()  -- ^ Single-step executor
  -> Int              -- ^ Target PC
  -> EVM Symbolic (Maybe (VM Symbolic))
speculateLoopOuter conf exec1Step targetPC = do
    -- Initialize merge state for this speculation
    let budget = conf.mergeMaxBudget
    modifying #mergeState $ \ms -> ms { msActive = True , msRemainingBudget = budget }
    res <- speculateLoop conf exec1Step targetPC
    -- Reset merge state
    assign #mergeState defaultMergeState
    pure res

-- | Inner loop for speculative execution with budget tracking
speculateLoop
  :: Config
  -> EVM Symbolic ()  -- ^ Single-step executor
  -> Int              -- ^ Target PC
  -> EVM Symbolic (Maybe (VM Symbolic))
speculateLoop conf exec1Step targetPC = do
    ms <- use #mergeState
    if ms.msRemainingBudget <= 0
      then pure Nothing  -- Budget exhausted
      else do
        pc <- use (#state % #pc)
        result <- use #result
        case result of
          Just _ -> pure Nothing  -- Hit RPC call/revert/SMT query/etc.
          Nothing
            | pc == targetPC -> Just <$> get  -- Reached target
            | otherwise -> do
                -- Decrement budget and execute one instruction
                modifying #mergeState $ \s -> s { msRemainingBudget = subtract 1 s.msRemainingBudget }
                exec1Step
                speculateLoop conf exec1Step targetPC

-- | Try to merge a forward jump (skip block pattern) for Symbolic execution
-- Returns True if merge succeeded, False if we should fall back to forking
-- SOUNDNESS: Both paths (jump and fall-through) must converge to the same PC,
-- have the same stack depth, and have no side effects. Only then can we merge.
tryMergeForwardJump
  :: Config
  -> EVM Symbolic ()  -- ^ Single-step executor
  -> Int              -- ^ Current PC
  -> Int              -- ^ Jump target PC
  -> Expr EWord       -- ^ Branch condition
  -> [Expr EWord]     -- ^ Stack after popping JUMPI args
  -> EVM Symbolic Bool
tryMergeForwardJump conf exec1Step currentPC jumpTarget cond stackAfterPop = do
  -- Only handle forward jumps (skip block pattern)
  if jumpTarget <= currentPC
  then pure False  -- Not a forward jump
  else do
    vm0 <- get

    -- Skip merge if memory is mutable (ConcreteMemory)
    case vm0.state.memory of
      ConcreteMemory _ -> pure False
      SymbolicMemory _ -> do
        -- True branch (jump taken): Just sets PC to target, no execution needed
        let trueStack = stackAfterPop  -- Stack after popping JUMPI args

        -- False branch (fall through): Execute until we reach jump target
        assign' (#state % #stack) stackAfterPop
        modifying' (#state % #pc) (+ 1)  -- Move past JUMPI
        maybeVmFalse <- speculateLoopOuter conf exec1Step jumpTarget

        case maybeVmFalse of
          Nothing -> put vm0 >> pure False -- restore, can't merge
          Just vmFalse -> do
            let falseStack = vmFalse.state.stack
                soundnessOK = checkNoSideEffects vm0 vmFalse

            -- Check merge conditions: same stack depth AND no side effects
            if length trueStack == length falseStack && soundnessOK
              then do
                -- Merge stacks using ITE expressions, simplifying to prevent growth
                let condSimp = Expr.simplify cond
                    mergeExpr t f
                      | t == f    = t
                      | otherwise = Expr.simplify (ITE condSimp t f)
                    mergedStack = zipWith mergeExpr trueStack falseStack
                -- Use vm0 as base and update only PC and stack
                when conf.debug $ traceM $ "Merged forward jump"
                  ++ runSrcLookup vm0.config.srcLookup vm0.env.contracts vm0.state.contract jumpTarget
                put vm0
                assign (#state % #pc) jumpTarget
                assign (#state % #stack) mergedStack
                assign #result Nothing
                assign (#mergeState % #msActive) False
                pure True
              else do
                -- Can't merge: stack depth or state differs
                put vm0
                pure False

-- | Check that execution had no side effects (storage, memory, logs, etc.)
checkNoSideEffects :: VM Symbolic -> VM Symbolic -> Bool
checkNoSideEffects vm0 vmAfter =
  let memoryUnchanged = case (vm0.state.memory, vmAfter.state.memory) of
        (SymbolicMemory m1, SymbolicMemory m2) -> m1 == m2
        _ -> False
      memorySizeUnchanged = vm0.state.memorySize == vmAfter.state.memorySize
      returndataUnchanged = vm0.state.returndata == vmAfter.state.returndata
      storageUnchanged = vm0.env.contracts == vmAfter.env.contracts
      logsUnchanged = vm0.logs == vmAfter.logs
      constraintsUnchanged = vm0.constraints == vmAfter.constraints
      keccakUnchanged = vm0.keccakPreImgs == vmAfter.keccakPreImgs
      freshVarUnchanged = vm0.freshVar == vmAfter.freshVar
      framesUnchanged = length vm0.frames == length vmAfter.frames
      subStateUnchanged = vm0.tx.subState == vmAfter.tx.subState
  in memoryUnchanged && memorySizeUnchanged && returndataUnchanged
     && storageUnchanged && logsUnchanged && constraintsUnchanged
     && keccakUnchanged && freshVarUnchanged
     && framesUnchanged && subStateUnchanged
