-- | Detect SLOAD->MSTORE copy loops in bytecode so the symbolic executor can
-- short-circuit them via StorageCopySlice.
module EVM.GetterDetection
  ( detectCopyLoops
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector qualified as V

import EVM.Types (CopyLoop(..), StorageLoopStackInfo(..), Op, GenericOp(..))
import EVM.Expr (maybeLitWordSimp)

-- | Scan op vector for copy loops, keyed by condJumpiPC.
-- Pattern A: backward JUMPI (condition at bottom), exitBranch=False.
-- Pattern B: backward JUMP + forward exit JUMPI, exitBranch=True.
detectCopyLoops :: V.Vector (Int, Op) -> Map Int CopyLoop
detectCopyLoops ops =
  let jumpdests  = buildJumpdestSet ops
      candidates = findBackwardJumps ops jumpdests
      loops      = [loop | (p, q) <- candidates, Just loop <- [analyseBody ops p q]]
  in Map.fromList [(l.condJumpiPC, l) | l <- loops]

-- | All JUMPDEST PCs.
buildJumpdestSet :: V.Vector (Int, Op) -> Set Int
buildJumpdestSet ops = Set.fromList [pc | (pc, OpJumpdest) <- V.toList ops]

-- | (target, jumpPC) pairs where a PUSH <Lit target> immediately precedes a
-- JUMP/JUMPI that jumps backward (target < jumpPC) to a known JUMPDEST.
findBackwardJumps :: V.Vector (Int, Op) -> Set Int -> [(Int, Int)]
findBackwardJumps ops jumpdests =
  [ (t, q)
  | i <- [1 .. V.length ops - 1]
  , let (q, op) = ops V.! i
  , isJumpOp op
  , OpPush w <- [snd (ops V.! (i - 1))]
  , Just target <- [maybeLitWordSimp w]
  , let t = fromIntegral target
  , t < q
  , Set.member t jumpdests
  ]

-- | Analyse body [p..q]; returns 'CopyLoop' when structural checks pass.
analyseBody :: V.Vector (Int, Op) -> Int -> Int -> Maybe CopyLoop
analyseBody ops p q = do
  let body          = V.filter (\(pc, _) -> pc >= p && pc <= q) ops
      opcodes       = fmap snd body
      hasSload      = V.elem OpSload opcodes
      hasMload      = V.elem OpMload opcodes
      hasMstore     = V.any (\op -> op == OpMstore || op == OpMstore8) opcodes
      hasSideEffect = V.any isSideEffect opcodes
      jumpsOK       = noEscapingJumps body p q
      isStackNeutral = case traverse stackDelta (V.toList opcodes) of
        Just deltas -> sum deltas == 0
        Nothing     -> False
      isStorageCopy = hasSload && hasMstore && not hasMload

  if not (isStorageCopy && not hasSideEffect && jumpsOK && isStackNeutral)
    then Nothing
    else do
      -- Layout extraction must succeed; otherwise the runtime would silently
      -- skip the loop body via a no-op summary.
      layout <- extractStorageStackLayout ops p q

      let mkLoop cjPC exitB exitPC = CopyLoop
            { loopHeadPC         = p
            , condJumpiPC        = cjPC
            , exitBranch         = exitB
            , loopExitPC         = exitPC
            , storageStackLayout = layout
            }


      case snd (V.last body) of
        -- Pattern A: backward JUMPI at q -- exit by falling through.
        OpJumpi -> Just (mkLoop q False (q + 1))
        -- Pattern B: backward JUMP at q; the loop condition is a forward
        -- JUMPI in the body whose exit target is the PUSH right before it.
        OpJump -> do
          (cpc, _) <- V.find (\(_, op) -> op == OpJumpi) body
          idx      <- V.findIndex (\(pc, _) -> pc == cpc) body
          if idx == 0 then Nothing else
            case snd (body V.! (idx - 1)) of
              OpPush w -> do
                target <- maybeLitWordSimp w
                let exitPC = fromIntegral target
                if exitPC > q then Just (mkLoop cpc True exitPC) else Nothing
              _ -> Nothing
        _ -> Nothing

-- | Every body JUMP/JUMPI must have a statically known target inside [p..].
noEscapingJumps :: V.Vector (Int, Op) -> Int -> Int -> Bool
noEscapingJumps body p q = V.all ok (V.indexed body)
  where
    ok (i, (pc, op))
      | isJumpOp op = pc == q || hasKnownTarget i
      | otherwise   = True
    hasKnownTarget i
      | i == 0    = False
      | otherwise = case snd (body V.! (i - 1)) of
          OpPush w -> case maybeLitWordSimp w of
            Just target -> fromIntegral target >= p
            Nothing     -> False
          _ -> False

-- | JUMP or JUMPI.
isJumpOp :: Op -> Bool
isJumpOp op = op == OpJump || op == OpJumpi

-- | A binary comparison opcode (pops two words, pushes one).
isCmpOp :: Op -> Bool
isCmpOp op = op `elem` [OpLt, OpGt, OpSlt, OpSgt, OpEq]

-- | Storage writes, calls, logs, etc.
isSideEffect :: Op -> Bool
isSideEffect = \case
  OpSstore       -> True
  OpTstore       -> True
  OpLog _        -> True
  OpCall         -> True
  OpCallcode     -> True
  OpDelegatecall -> True
  OpStaticcall   -> True
  OpCreate       -> True
  OpCreate2      -> True
  OpSelfdestruct -> True
  _              -> False

-- | Net stack effect (push - pop), Nothing if indeterminate.
stackDelta :: Op -> Maybe Int
stackDelta = \case
  OpStop -> Just 0; OpAdd -> Just (-1); OpMul -> Just (-1); OpSub -> Just (-1)
  OpDiv -> Just (-1); OpSdiv -> Just (-1); OpMod -> Just (-1); OpSmod -> Just (-1)
  OpAddmod -> Just (-2); OpMulmod -> Just (-2); OpExp -> Just (-1)
  OpSignextend -> Just (-1)
  OpLt -> Just (-1); OpGt -> Just (-1); OpSlt -> Just (-1); OpSgt -> Just (-1)
  OpEq -> Just (-1); OpIszero -> Just 0
  OpAnd -> Just (-1); OpOr -> Just (-1); OpXor -> Just (-1); OpNot -> Just 0
  OpByte -> Just (-1); OpShl -> Just (-1); OpShr -> Just (-1); OpSar -> Just (-1)
  OpClz -> Just 0
  OpSha3 -> Just (-1)
  OpAddress -> Just 1; OpBalance -> Just 0; OpOrigin -> Just 1; OpCaller -> Just 1
  OpCallvalue -> Just 1; OpCalldataload -> Just 0; OpCalldatasize -> Just 1
  OpCalldatacopy -> Just (-3); OpCodesize -> Just 1; OpCodecopy -> Just (-3)
  OpGasprice -> Just 1; OpExtcodesize -> Just 0; OpExtcodecopy -> Just (-4)
  OpReturndatasize -> Just 1; OpReturndatacopy -> Just (-3); OpExtcodehash -> Just 0
  OpBlockhash -> Just 0; OpCoinbase -> Just 1; OpTimestamp -> Just 1
  OpNumber -> Just 1; OpPrevRandao -> Just 1; OpGaslimit -> Just 1
  OpChainid -> Just 1; OpSelfbalance -> Just 1; OpBaseFee -> Just 1
  OpBlobhash -> Just 0; OpBlobBaseFee -> Just 1
  OpPop -> Just (-1); OpMcopy -> Just (-3)
  OpMload -> Just 0; OpMstore -> Just (-2); OpMstore8 -> Just (-2)
  OpSload -> Just 0; OpSstore -> Just (-2)
  OpTload -> Just 0; OpTstore -> Just (-2)
  OpJump -> Just (-1); OpJumpi -> Just (-2)
  OpPc -> Just 1; OpMsize -> Just 1; OpGas -> Just 1
  OpJumpdest -> Just 0
  OpPush0 -> Just 1; OpPush _ -> Just 1
  OpDup _ -> Just 1; OpSwap _ -> Just 0
  OpLog n -> Just (negate (fromIntegral n + 2))
  OpCreate -> Just (-2); OpCall -> Just (-6); OpStaticcall -> Just (-5)
  OpCallcode -> Just (-6); OpReturn -> Nothing; OpDelegatecall -> Just (-5)
  OpCreate2 -> Just (-3); OpRevert -> Nothing; OpSelfdestruct -> Nothing
  OpUnknown _ -> Nothing

-- Abstract stack simulation for extracting loop-variable positions ------------

-- | An abstract stack value: either a slot inherited unchanged from the loop
-- entry stack, or a value computed within the loop body.
data AV = Orig Int | Computed deriving (Eq, Show)

type AbstractStack = [AV]

-- | Simulate a storage-to-mem loop body; returns SLOAD slot, loop bound, MSTORE dst.
extractStorageStackLayout :: V.Vector (Int, Op) -> Int -> Int -> Maybe StorageLoopStackInfo
extractStorageStackLayout ops p q = do
  (slot, end, dst) <- extractStackLayout OpSload ops p q
  pure StorageLoopStackInfo { slotDepth = slot, endSlotDepth = end, dstOffDepth = dst }

-- | Abstractly execute the loop body and recover the entry-stack depths of
-- the three loop variables, as @(loadAddr, loopBound, storeAddr)@. @loadOp@
-- is the opcode (SLOAD) that reads the copied value; depths are relative
-- to the loop entry stack (see 'StorageLoopStackInfo').
extractStackLayout :: Op -> V.Vector (Int, Op) -> Int -> Int -> Maybe (Int, Int, Int)
extractStackLayout loadOp ops p q =
  let body    = V.toList $ V.filter (\(pc, _) -> pc >= p && pc <= q) ops
      -- drop the trailing PUSH<loopHead> and JUMP/JUMPI
      bodyOps = map snd $ if length body >= 2 then init (init body) else []
      initStk = map Orig [0 .. 1023]
  in go bodyOps initStk Nothing Nothing Nothing
  where
    go :: [Op] -> AbstractStack
       -> Maybe AV        -- ^ load address (consumed by loadOp)
       -> Maybe AV        -- ^ store address (consumed by MSTORE)
       -> Maybe (AV, AV)  -- ^ operands of the comparison opcode
       -> Maybe (Int, Int, Int)
    go [] _ loadAddr storeAddr cmpOps = do
      loadAV     <- loadAddr
      storeAV    <- storeAddr
      (c1, c2)   <- cmpOps
      loadDepth  <- getOrig loadAV
      storeDepth <- getOrig storeAV
      -- the loop bound is the comparison operand that is not the load address
      boundDepth <- case (c1, c2) of
        (Orig a, Orig b)
          | a == loadDepth -> Just b
          | b == loadDepth -> Just a
          | otherwise      -> Nothing
        (Computed, Orig b) -> Just b
        (Orig a, Computed) -> Just a
        _                  -> Nothing
      pure (loadDepth, boundDepth, storeDepth)
    go _ [] _ _ _ = Nothing
    -- stk is non-empty below (the empty case is caught by the clause above),
    -- so the single-element matches here are total.
    go (op:rest) stk loadAddr storeAddr cmpOps
      -- the value-loading opcode: pop the address, push the loaded value
      | op == loadOp = case stk of
          (addr:rest') -> go rest (Computed : rest') (Just addr) storeAddr cmpOps
      -- a comparison: record its two operands, push the boolean result
      | isCmpOp op = case stk of
          (a:b:rest') -> go rest (Computed : rest') loadAddr storeAddr (Just (a, b))
          _           -> Nothing
      | otherwise = case op of
          OpJumpdest -> go rest stk loadAddr storeAddr cmpOps
          OpPush _   -> go rest (Computed : stk) loadAddr storeAddr cmpOps
          OpPush0    -> go rest (Computed : stk) loadAddr storeAddr cmpOps
          OpDup n ->
            let idx = fromIntegral n - 1
            in if idx < length stk
               then go rest (stk !! idx : stk) loadAddr storeAddr cmpOps
               else Nothing
          OpSwap n ->
            let idx = fromIntegral n
            in case stk of
                 (top:rest') | idx < length stk ->
                   case splitAt (idx - 1) rest' of
                     (before, target:after) ->
                       go rest (target : before ++ [top] ++ after) loadAddr storeAddr cmpOps
                     _ -> Nothing
                 _ -> Nothing
          OpPop -> case stk of
            (_:rest') -> go rest rest' loadAddr storeAddr cmpOps
          OpMstore  -> recordStore
          OpMstore8 -> recordStore
          -- 0-output bulk-copy opcodes
          OpCalldatacopy   -> dropN 3
          OpCodecopy       -> dropN 3
          OpReturndatacopy -> dropN 3
          OpMcopy          -> dropN 3
          OpExtcodecopy    -> dropN 4
          -- default: treat as a 1-output opcode
          _ -> case stackDelta op of
                 Just d ->
                   let pops = 1 - d
                   in if pops > length stk
                      then Nothing
                      else go rest (Computed : drop pops stk) loadAddr storeAddr cmpOps
                 Nothing -> Nothing
      where
        recordStore = case stk of
          (addr:_) -> go rest (drop 2 stk) loadAddr (Just addr) cmpOps
        dropN n
          | n > length stk = Nothing
          | otherwise      = go rest (drop n stk) loadAddr storeAddr cmpOps

getOrig :: AV -> Maybe Int
getOrig (Orig i) = Just i
getOrig Computed = Nothing
