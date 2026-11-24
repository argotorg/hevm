{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | State merging for symbolic execution
--
-- This module provides functions for merging execution paths during symbolic
-- execution. Instead of forking on every JUMPI, we can speculatively execute
-- both paths and merge them using ITE (If-Then-Else) expressions when:
--
-- 1. Both paths reach the same PC at the same stack depth: the jump target
--    (skip block) or a later join point (if/else, ternary)
-- 2. Neither path has side effects (storage, memory, logs unchanged)
--
-- This reduces path explosion from 2^N to linear in many common patterns.

module EVM.Merge
  ( tryMergeForwardJump
  , decide
  ) where

import Control.Monad (when)
import Control.Monad.State.Strict (get, put)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Debug.Trace (traceM)
import Optics.Core
import Optics.State
import Witch (tryInto)

import EVM.Effects (Config(..))
import EVM.Expr qualified as Expr
import EVM.Types

-- | Executes instructions speculatively until @f@ is done, or until the budget
-- runs out or execution stops (RPC call, revert, SMT query, nested branch)
speculate :: Config -> EVM Symbolic () -> Prop -> s -> (s -> VM Symbolic -> Either a s) -> EVM Symbolic (Either a s)
speculate conf exec1Step assume s0 f = do
  assign #mergeState (MergeState True [Expr.simplifyProp assume])
  res <- go conf.mergeMaxBudget s0
  assign #mergeState defaultMergeState
  pure res
  where
    go budget s = do
      vm <- get
      if isJust vm.result || budget <= 0 then pure (Right s)
      else case f s vm of
        Left a -> pure (Left a)
        Right s' -> exec1Step >> go (budget - 1 :: Int) s'

-- | Try to merge a forward jump for Symbolic execution
-- Returns True if merge succeeded, False if we should fall back to forking
-- SOUNDNESS: Both paths (jump and fall-through) must reach the same PC with
-- the same stack depth and no side effects. Only then can we merge.
tryMergeForwardJump
  :: Config
  -> EVM Symbolic ()  -- ^ Single-step executor
  -> (Int -> Bool)    -- ^ Is this a valid jump destination
  -> Int              -- ^ Current PC
  -> Int              -- ^ Jump target PC
  -> Expr EWord       -- ^ Branch condition
  -> [Expr EWord]     -- ^ Stack after popping JUMPI args
  -> EVM Symbolic Bool
tryMergeForwardJump conf exec1Step isJumpDest currentPC jumpTarget cond stackAfterPop = do
  -- Only merge forward jumps whose conditions remain symbolic.
  if jumpTarget <= currentPC || isJust (Expr.maybeLitWordSimp cond)
  then pure False
  else do
    vm0 <- get

    -- Skip merge if memory is mutable (ConcreteMemory)
    case vm0.state.memory of
      ConcreteMemory _ -> pure False
      SymbolicMemory _ -> do
        let place vm = (vm.state.pc, length vm.state.stack)
            -- the fall-through may reach the join only after calling a helper
            -- that the jump also calls: there the return addresses differ
            mergeable vf vt = checkNoSideEffects vm0 vf && checkNoSideEffects vm0 vt
              && not (or (zipWith returnsDiffer vt.state.stack vf.state.stack))
            returnsDiffer (Lit a) (Lit b) = a /= b && jumpDest a && jumpDest b
            returnsDiffer _ _ = False
            jumpDest = either (const False) isJumpDest . tryInto

        -- False branch (fall through): every state it reaches
        assign' (#state % #stack) stackAfterPop
        modifying' (#state % #pc) (+ 1)
        -- the jump target is the earliest point where the branches can meet
        reached <- either id id <$> speculate conf exec1Step (PEq (Lit 0) cond) Map.empty (\seen vm ->
          let seen' = Map.insertWith (\_ old -> old) (place vm) vm seen
          in if vm.state.pc == jumpTarget then Left seen' else Right seen')

        -- True branch (jump taken): until it meets the false branch
        put vm0
        assign' (#state % #stack) stackAfterPop
        assign' (#state % #pc) jumpTarget
        met <- speculate conf exec1Step (PNeg (PEq (Lit 0) cond)) () $ \() vt -> case Map.lookup (place vt) reached of
          Just vf | mergeable vf vt -> Left (vt, vf)
          _ -> Right ()

        put vm0
        case met of
          Right () -> pure False -- can't merge: no common point, EVM error, SMT/RPC query, over-budget
          Left (vmTrue, vmFalse) -> do
            -- Merge stacks using ITE expressions, simplifying to prevent growth
            let condSimp = Expr.simplify cond
                mergeExpr t f
                  | t == f = t
                  | otherwise = Expr.simplify $ ITE condSimp t f
                mergedStack = zipWith mergeExpr vmTrue.state.stack vmFalse.state.stack
            when conf.debug $ traceM $ "Merged forward jump"
              <> runSrcLookup vm0.srcLookup vm0.env.contracts vm0.state.contract jumpTarget
            assign (#state % #pc) vmTrue.state.pc
            assign (#state % #stack) mergedStack
            assign #result Nothing
            pure True

-- | Whether a branch condition holds, if a literal or the assumptions of the
-- speculated branch decide it
decide :: [Prop] -> Expr EWord -> Maybe Bool
decide assumed cond = case Expr.maybeLitWordSimp cond of
  Just c -> Just (c /= 0)
  Nothing
    | implied (Expr.simplifyProp (PNeg (PEq (Lit 0) cond))) -> Just True
    | implied (Expr.simplifyProp (PEq (Lit 0) cond)) -> Just False
    | otherwise -> Nothing
  where
    implied p = p `elem` assumed || case p of
      PLEq a b -> PLT a b `elem` assumed
      _ -> False

-- | Check that execution had no side effects (storage, memory, logs, etc.)
checkNoSideEffects :: VM Symbolic -> VM Symbolic -> Bool
checkNoSideEffects vm0 vmAfter =
  let memoryUnchanged = case (vm0.state.memory, vmAfter.state.memory) of
        (SymbolicMemory m1, SymbolicMemory m2) -> m1 == m2
        _ -> False
      memorySizeUnchanged = vm0.state.memorySize == vmAfter.state.memorySize
                            && vm0.state.symMemorySize == vmAfter.state.symMemorySize
      returndataUnchanged = vm0.state.returndata == vmAfter.state.returndata
      storageUnchanged = vm0.env.contracts == vmAfter.env.contracts
      logsUnchanged = vm0.logs == vmAfter.logs
      constraintsUnchanged = vm0.constraints == vmAfter.constraints
      keccakUnchanged = vm0.keccakPreImgs == vmAfter.keccakPreImgs
      freshVarUnchanged = vm0.freshVar == vmAfter.freshVar
      framesUnchanged = length vm0.frames == length vmAfter.frames
      subStateUnchanged = vm0.tx.subState == vmAfter.tx.subState
      -- the merge restores vm0, so a GAS reading, CREATE or unknown call in the
      -- merged segment would leave these counters rolled back
      envCountersUnchanged = vm0.env.freshGasVals == vmAfter.env.freshGasVals
                             && vm0.env.freshAddresses == vmAfter.env.freshAddresses
                             && vm0.env.callWorld == vmAfter.env.callWorld
                             && vm0.env.callCounts == vmAfter.env.callCounts
                             && vm0.state.lastGasReading == vmAfter.state.lastGasReading
  in memoryUnchanged && memorySizeUnchanged && returndataUnchanged
     && storageUnchanged && logsUnchanged && constraintsUnchanged
     && keccakUnchanged && freshVarUnchanged
     && framesUnchanged && subStateUnchanged && envCountersUnchanged
