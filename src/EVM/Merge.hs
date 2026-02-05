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
  ( exploreNestedBranch
  , tryMergeForwardJump
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
    modifying #mergeState $ \ms -> ms
      { msActive = True
      , msTargetPC = targetPC
      , msRemainingBudget = budget
      , msNestingDepth = 0
      }
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
                modifying #mergeState $ \s -> s { msRemainingBudget = s.msRemainingBudget - 1 }
                exec1Step
                speculateLoop conf exec1Step targetPC

-- | When hitting nested JUMPI during speculation, try both paths
-- Returns Just vmState if BOTH paths converge to targetPC, Nothing otherwise
-- SOUNDNESS: We MUST require both paths to converge and merge them with ITE.
-- Picking one path arbitrarily would lose path constraint information.
exploreNestedBranch
  :: Config
  -> EVM Symbolic ()  -- ^ Single-step executor
  -> Int              -- ^ Nested jump target
  -> Int              -- ^ Target PC we're trying to reach
  -> Expr EWord       -- ^ Branch condition
  -> [Expr EWord]     -- ^ Stack after popping JUMPI args
  -> EVM Symbolic (Maybe (VM Symbolic))
exploreNestedBranch conf exec1Step nestedJumpTarget targetPC cond stackAfterPop = do
    ms <- use #mergeState
    let maxDepth = conf.mergeMaxDepth

    -- Check limits
    if ms.msRemainingBudget <= 0 || ms.msNestingDepth >= maxDepth
      then pure Nothing
      else do
        vm0 <- get

        -- CRITICAL: Skip if memory is mutable (ConcreteMemory)
        -- Mutable memory is not properly restored by `put vm0`
        case vm0.state.memory of
          ConcreteMemory _ -> pure Nothing  -- Can't safely explore with mutable memory
          SymbolicMemory _ -> do
            -- Save original merge state for proper backtracking
            let originalDepth = ms.msNestingDepth
                originalBudget = ms.msRemainingBudget
                halfBudget = max 10 (originalBudget `div` 2)

            -- Try fall-through path (cond == 0)
            put vm0
            assign' (#state % #stack) stackAfterPop
            modifying' (#state % #pc) (+ 1)  -- Move past JUMPI
            modifying #mergeState $ \s -> s
              { msNestingDepth = s.msNestingDepth + 1, msRemainingBudget = halfBudget }

            resultFallThrough <- speculateLoop conf exec1Step targetPC

            -- Restore state for jump path
            put vm0
            assign (#state % #pc) nestedJumpTarget
            assign' (#state % #stack) stackAfterPop
            modifying #mergeState $ const ms
              { msNestingDepth = originalDepth + 1, msRemainingBudget = halfBudget }

            -- Try jump path (cond != 0)
            resultJump <- speculateLoop conf exec1Step targetPC

            -- SOUNDNESS: Both paths MUST converge for merge to be valid
            case (resultFallThrough, resultJump) of
              (Just vmFalse, Just vmTrue) -> do
                -- Both paths converged - merge them using ITE
                let falseStack = vmFalse.state.stack
                    trueStack = vmTrue.state.stack
                -- Check that stacks have same depth and no side effects
                if length falseStack == length trueStack
                   && checkNoSideEffects vm0 vmFalse
                   && checkNoSideEffects vm0 vmTrue
                  then do
                    -- Merge stacks using ITE with the branch condition
                    -- Simplify merged expressions to prevent unbounded growth
                    -- (e.g. Mul (Lit 0) (ITE ...) must reduce to Lit 0)
                    let condSimp = Expr.simplify cond
                        mergeExpr t f
                          | t == f    = t
                          | otherwise = Expr.simplify (ITE condSimp t f)
                        mergedStack = zipWith mergeExpr trueStack falseStack
                    -- Use vm0 as base and update PC and stack
                    put vm0
                    assign (#state % #pc) targetPC
                    assign (#state % #stack) mergedStack
                    assign #result Nothing
                    modifying #mergeState $ const ms
                      { msNestingDepth = originalDepth, msRemainingBudget = originalBudget - (originalBudget - halfBudget) * 2}
                    Just <$> get
                  else do
                    -- Side effects or stack mismatch - can't merge
                    put vm0
                    pure Nothing
              _ -> do
                -- One or both paths didn't converge - can't merge
                put vm0
                pure Nothing

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

      -- CRITICAL: Skip merge if memory is mutable (ConcreteMemory)
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
            Nothing -> do
              -- Couldn't converge - restore and pure False
              put vm0
              pure False
            Just vmFalse -> do
              let falseStack = vmFalse.state.stack
                  soundnessOK = checkNoSideEffects vm0 vmFalse

              -- Check merge conditions: same stack depth AND no side effects
              if length trueStack == length falseStack && soundnessOK
                then do
                  -- Merge stacks using ITE expressions
                  -- Simplify merged expressions to prevent unbounded growth
                  -- (e.g. Mul (Lit 0) (ITE ...) must reduce to Lit 0)
                  let condSimp = Expr.simplify cond
                      mergeExpr t f
                        | t == f    = t
                        | otherwise = Expr.simplify (ITE condSimp t f)
                      mergedStack = zipWith mergeExpr trueStack falseStack
                  -- Use vm0 as base and update only PC and stack
                  when conf.debug $ traceM $ "Merged forward jump at PC " ++ show jumpTarget
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
