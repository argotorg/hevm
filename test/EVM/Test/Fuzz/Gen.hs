{-|
Module      : EVM.Test.Fuzz.Gen
Description : QuickCheck generators of fuzzed programs and inputs

Programs are blocks of straight-line code, branches, loops, calls, creates and
precompile calls that keep the stack deep enough. Some blocks target one hevm
feature, e.g. forward jumps that path merging joins. Also generates debugger
moves.
-}
module EVM.Test.Fuzz.Gen
  ( genMove, genSnapEvery
  ) where

import Control.Monad.State.Strict (StateT(..), evalStateT, gets, modify, lift)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Witch (into, unsafeInto)
import EVM.Types hiding (Env)
import EVM.Debugger (Command(..))
import EVM.Test.Fuzz.Program

-- * Generators

data GS = GS { sdepth :: Int, nextLabel :: Int, nextLoop :: Int }
type G = StateT GS Gen

liftG :: Gen a -> G a
liftG = lift

minWidth :: W256 -> Int
minWidth 0 = 0
minWidth v = length (takeWhile (> 0) (iterate (`div` 256) v))

genWord :: Gen W256
genWord = frequency
  [ (60, chooseBoundedIntegral (0, 10))
  , (10, chooseBoundedIntegral (0, 0x80))
  , (2, elements [ 0x1f, 0x20, 0x21, 0x3f, 0x40, 0xff, 0x100
                 , 2^(64::Int)-1, 2^(64::Int), 2^(128::Int)
                 , 2^(255::Int)-1, 2^(255::Int), maxBound - 1, maxBound ])
  , (1, chooseBoundedIntegral (0, maxBound))
  ]

push :: W256 -> G [Item]
push v = do
  modify (\s -> s { sdepth = s.sdepth + 1 })
  wide <- liftG $ chooseInt (0, 9)
  w <- if wide == 0 then liftG (chooseInt (max 1 (minWidth v), 32)) else pure (minWidth v)
  pure [IPush w v]

-- | Emit an op with fixed stack effect, keeping the tracked depth up to date
op :: Int -> Int -> Op -> G [Item]
op pops pushed o = do
  modify (\s -> s { sdepth = max 0 (s.sdepth - pops) + pushed })
  pure [IOp o]

genStraightOp :: G [Item]
genStraightOp = do
  d <- gets (.sdepth)
  usePush <- liftG $ chooseInt (0, 2)
  if usePush == 0 then liftG genWord >>= push else do
    (_, pops, pushed, o) <- liftG $ frequency [(w, pure e) | e@(w, _, _, _) <- opTable]
    -- rarely let it underflow, which ends the run
    underflow <- liftG $ chooseInt (0, 99)
    if pops > d && underflow /= 0 then liftG genWord >>= push else op pops pushed o

genStraight :: G [Item]
genStraight = do
  n <- liftG $ chooseInt (2, 12)
  concat <$> sequence (replicate n genStraightOp)

-- | A condition on calldata, pushing one word
genCalldataCond :: G [Item]
genCalldataCond = do
  off <- liftG $ frequency [(3, elements [0, 4, 32, 36]), (1, chooseBoundedIntegral (0, 70))]
  load <- (<>) <$> push off <*> op 1 1 OpCalldataload
  shape <- liftG $ chooseInt (0, 2)
  rest <- case shape of
    0 -> do m <- liftG $ elements [1, 2, 0xff, 0x8000, maxBound]
            (<>) <$> push m <*> op 2 1 OpAnd
    1 -> do k <- liftG genWord
            (<>) <$> push k <*> (liftG (elements [OpLt, OpGt, OpEq, OpSlt]) >>= op 2 1)
    _ -> pure []
  pure (load <> rest)

genBranch :: G [Item]
genBranch = do
  d <- gets (.sdepth)
  onCalldata <- liftG $ chooseInt (0, 3)
  cond <- if onCalldata == 3 then genStorageCond
          else if onCalldata > 0 || d == 0 then genCalldataCond else pure []
  modify (\s -> s { sdepth = s.sdepth - 1 })
  pure (cond <> [IJumpFwd True])

genHalt :: G [Item]
genHalt = do
  kind <- liftG $ frequency [(4, pure OpReturn), (3, pure OpRevert), (1, pure OpStop)]
  case kind of
    OpStop -> pure [IOp OpStop]
    _ -> do size <- liftG $ frequency [(3, elements [0x20, 0x40, 0x60]), (1, chooseBoundedIntegral (0, 0x41))]
            off <- liftG $ frequency [(3, pure 0), (1, chooseBoundedIntegral (0, 0x40))]
            items <- concat <$> mapM maybeFromCalldata [size, off]
            (items <>) <$> op 2 0 kind

-- | Push the value, or sometimes a calldata word masked to its bit width, so
-- that the operand is symbolic but stays as small as the value
maybeFromCalldata :: W256 -> G [Item]
maybeFromCalldata v = do
  sym <- liftG $ chooseInt (0, 3)
  if sym /= 0 then push v else do
    off <- liftG $ elements [0, 4, 32, 36]
    let bits = length (takeWhile (> 0) (iterate (`div` 2) v))
        mask = if bits >= 256 then maxBound else 2 ^ bits - 1
    concat <$> sequence [push off, op 1 1 OpCalldataload, push mask, op 2 1 OpAnd]

-- | A Solidity storage slot: of a mapping entry, keccak(key . p), or of an array
-- element, keccak(p) + i, for a small slot p. Exercises storage decomposition.
genStorageSlot :: G [Item]
genStorageSlot = do
  p <- liftG $ elements [0, 1, 2]
  isMap <- liftG arbitrary
  if isMap then do
    key <- liftG (chooseInt (0, 2)) >>= \case
      0 -> liftG (elements [0, 1, 7]) >>= push
      _ -> do off <- liftG $ elements [0, 4, 32, 36]
              (<>) <$> push off <*> op 1 1 OpCalldataload
    concat <$> sequence
      [ pure key, push 0, op 2 0 OpMstore, push p, push 0x20, op 2 0 OpMstore
      , push 0x40, push 0, op 2 1 OpSha3 ]
  else do
    base <- concat <$> sequence [push p, push 0, op 2 0 OpMstore, push 0x20, push 0, op 2 1 OpSha3]
    i <- maybeFromCalldata =<< liftG (elements [0, 1, 3])
    concat <$> sequence [pure base, pure i, op 2 1 OpAdd]

-- | Whether a storage slot holds a small value, pushing one word
genStorageCond :: G [Item]
genStorageCond = do
  slot <- genStorageSlot
  v <- liftG $ elements [0, 3, 4]
  concat <$> sequence [pure slot, op 1 1 OpSload, push v, op 2 1 OpEq]

genStorageWrite :: G [Item]
genStorageWrite = do
  v <- maybeFromCalldata =<< liftG (elements [3, 4, 0xff])
  slot <- genStorageSlot
  ((v <> slot) <>) <$> op 2 0 OpSstore

-- | Enough stack for the deep DUPs and SWAPs
genDeepStack :: G [Item]
genDeepStack = do
  n <- liftG $ chooseInt (8, 16)
  concat <$> sequence (replicate n (liftG genWord >>= push))

-- | A few ops run many times, so that runs are long: the debugger snapshots every 50 steps
genSmallLoop :: G [Item]
genSmallLoop = do
  l <- gets (.nextLabel)
  n <- gets (.nextLoop)
  modify (\s -> s { nextLabel = l + 1, nextLoop = n + 1 })
  k <- liftG $ chooseInt (1, 3)
  body <- concat <$> sequence (replicate k (do
    w <- liftG genWord
    liftG (chooseInt (0, 2)) >>= \case
      0 -> concat <$> sequence [push w, liftG (elements [0, 0x20, 0x41]) >>= push, op 2 0 OpMstore]
      1 -> concat <$> sequence [push w, liftG (chooseBoundedIntegral (0, 3)) >>= push, op 2 0 OpTstore]
      _ -> concat <$> sequence [push w, op 0 1 OpCalldatasize, liftG (elements [OpAdd, OpMul, OpXor]) >>= op 2 1, op 1 0 OpPop]))
  let ctr = 0xc0de0000 + unsafeInto n
  count <- concat <$> sequence
    [ push ctr, op 1 1 OpTload, push 1, op 2 1 OpAdd
    , op 1 2 (OpDup 1), push ctr, op 2 0 OpTstore ]
  bound <- liftG (chooseBoundedIntegral (5, 40)) >>= push
  cmp <- op 2 1 OpGt
  modify (\s -> s { sdepth = s.sdepth - 1 })
  pure $ [ILabel l] <> body <> count <> bound <> cmp <> [IJump True l]

-- | A loop whose trip count is kept in transient storage, bounded by a constant or by calldata
genLoop :: G [Item]
genLoop = do
  l <- gets (.nextLabel)
  n <- gets (.nextLoop)
  modify (\s -> s { nextLabel = l + 1, nextLoop = n + 1 })
  body <- genStraight
  let ctr = 0xc0de0000 + unsafeInto n
  count <- concat <$> sequence
    [ push ctr, op 1 1 OpTload, push 1, op 2 1 OpAdd
    , op 1 2 (OpDup 1), push ctr, op 2 0 OpTstore ]
  symBound <- liftG $ chooseInt (0, 1)
  bound <- if symBound == 0
    then liftG (chooseBoundedIntegral (1, 3)) >>= push
    else do off <- liftG $ elements [0, 4, 32]
            concat <$> sequence [push off, op 1 1 OpCalldataload, push 3, op 2 1 OpAnd]
  cmp <- op 2 1 OpGt
  modify (\s -> s { sdepth = s.sdepth - 1 })
  pure $ [ILabel l] <> body <> count <> bound <> cmp <> [IJump True l]

-- | BALANCE, EXTCODESIZE, EXTCODEHASH or EXTCODECOPY of an account in or out of the pre-state
genAccountOp :: G [Item]
genAccountOp = do
  a <- liftG $ elements accountTargets
  kind <- liftG $ elements [OpBalance, OpExtcodesize, OpExtcodehash, OpExtcodecopy]
  case kind of
    OpExtcodecopy -> do
      args <- concat <$> mapM (\g -> liftG g >>= push)
        [elements [0, 1, 0x20], elements [0, 2, 0x40], elements [0, 0x20, 0x40]]
      (args <>) <$> ((<>) <$> push (into a) <*> op 4 0 OpExtcodecopy)
    _ -> (<>) <$> push (into a) <*> op 1 1 kind

-- | CREATE or CREATE2 of 'createInitCode' or 'sizedInitCode', written to memory first
genCreate :: G [Item]
genCreate = do
  off <- liftG $ elements [0, 0x20, 0x41]
  value <- liftG $ frequency [(3, pure 0), (1, elements [1, 7])]
  salt <- liftG $ oneof [pure Nothing, Just <$> elements [0, 1]]
  code <- liftG $ elements [createInitCode, sizedInitCode]
  initCode <- concat <$> sequence
    [ concat <$> sequence [push (into b), push (off + fromIntegral i), op 2 0 OpMstore8]
    | (i, b) <- zip [0 :: Int ..] (BS.unpack code) ]
  saltItems <- maybe (pure []) push salt
  valueItems <- maybeFromCalldata value
  args <- (<>) <$> (concat <$> mapM push [fromIntegral (BS.length code), off]) <*> pure valueItems
  create <- maybe (op 3 1 OpCreate) (const (op 4 1 OpCreate2)) salt
  pure (initCode <> saltItems <> args <> create)

genCall :: G [Item]
genCall = do
  kind <- liftG $ elements [OpCall, OpCall, OpStaticcall, OpDelegatecall, OpCallcode]
  -- precompiles 0x5 and 0x9 can take huge time or gas on junk input
  addr <- liftG $ frequency [(3, pure (into calleeAddr)), (2, elements [1, 2, 3, 4, 6, 7, 8])]
  -- geth does not trace precompiles, so one running out of gas would go unnoticed
  let toCallee = addr == into calleeAddr
  retSize <- liftG $ elements [0, 0x20, 0x40]
  retOff <- liftG $ elements [0, 0x20, 0x40]
  argSize <- liftG $ elements [0, 0x20, 0x40, 0x80]
  argOff <- liftG $ elements [0, 0x20]
  value <- liftG $ frequency [(3, pure 0), (1, elements [1, 7])]
  gas <- liftG $ frequency [(4, pure 0xffffff), (if toCallee then 1 else 0, elements [0, 3000, 30000])]
  let withValue = kind == OpCall || kind == OpCallcode
  -- a symbolic target is a call to unknown code, which the inputs cannot decide
  args <- (<>) <$> (concat <$> mapM maybeFromCalldata ([retSize, retOff, argSize, argOff] <> [value | withValue]))
               <*> (concat <$> mapM push [addr, gas])
  (args <>) <$> op (if withValue then 7 else 6) 1 kind

-- | A call to a precompile with well-formed or nearly well-formed input, then
-- RETURNDATASIZE and the first output word, so that the result shows on the stack
genPrecompileCall :: G [Item]
genPrecompileCall = do
  (addr, ws, size) <- liftG $ oneof
    [ do h <- elements [0, 1, sigHash]
         v <- elements [27, 28, 29, 30, 0, 27 + 256]
         r <- elements [0, 1, 2, sigR, secpN - 1, secpN]
         s' <- elements [1, sigS, secpN - 1, secpN]
         pure (1, [h, v, r, s'], 0x80)
    , do ws <- vectorOf 2 genWord
         (,ws,) <$> elements [2, 3, 4] <*> elements [0, 1, 0x20, 0x21, 0x40]
    , do lens' <- vectorOf 3 (elements [0, 1, 0x20])
         vals <- vectorOf 3 genWord
         pure (5, lens' <> vals, 0x60 + sum lens')
    , do p1 <- elements bnPoints
         p2 <- elements bnPoints
         pure (6, p1 <> p2, 0x80)
    , do p <- elements bnPoints
         k <- elements [0, 1, 2, bnP, maxBound]
         pure (7, p <> [k], 0x60)
    , do size <- elements [0, 0xc0, 0xbf]
         pure (8, replicate 6 0, size)
    , do rounds <- elements [0, 1, 12]
         ws <- vectorOf 6 genWord
         f <- elements [0, 1, 2]
         -- the final-block flag is byte 212, byte 20 of the last word
         let flagUnit = 256 ^ (11 :: Int)
             w = ws !! 5
             lastWord = w - (w `div` flagUnit `mod` 256) * flagUnit + f * flagUnit
         pure (9, rounds * 256 ^ (28 :: Int) : take 5 ws <> [lastWord], 0xd5)
    ]
  let argOff = 0x100
      retOff = 0x400
  stores <- concat <$> sequence
    [ (<>) <$> ((<>) <$> push w <*> push (argOff + 0x20 * unsafeInto j)) <*> op 2 0 OpMstore
    | (j, w) <- zip [0 :: Int ..] ws ]
  call <- concat <$> mapM push [0x40, retOff, size, argOff, addr, 0xffffff]
  callOp <- op 6 1 OpStaticcall
  results <- concat <$> sequence [op 0 1 OpReturndatasize, push retOff, op 1 1 OpMload]
  pure (stores <> call <> callOp <> results)
  where
    secpN = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
    bnP = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
    sigHash = 0x513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31
    sigR = 0xc84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4732
    sigS = 0x1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d
    bnPoints = [[0, 0], [1, 2], [1, 3], [bnP, 0]]

-- | Clear two slots and restore the first, which earns refunds and then takes
-- one back (EIP-2200)
genRefund :: G [Item]
genRefund = do
  k1 <- liftG $ chooseBoundedIntegral (0, 3)
  k2 <- liftG $ chooseBoundedIntegral (0, 3)
  concat <$> sequence
    [ push k1, op 1 1 OpSload
    , push 0, push k1, op 2 0 OpSstore
    , push 0, push k2, op 2 0 OpSstore
    , push k1, op 2 0 OpSstore ]

-- | if (a calldata condition) { arithmetic on stack values }, which exploration
-- merges into ITE values: memory must already be symbolic, the skipped code
-- must have no side effects and leave the stack as high as it was
genMergeable :: G [Item]
genMergeable = do
  symMem <- concat <$> sequence [push 0, op 1 1 OpCalldataload, push 0x40, op 2 0 OpMstore]
  vals <- liftG (chooseInt (1, 3)) >>= \n -> concat <$> sequence (replicate n (liftG genWord >>= push))
  cond <- liftG (chooseInt (0, 5)) >>= \case
    0 -> genConcreteCond
    _ -> genCalldataCond
  modify (\s -> s { sdepth = s.sdepth - 1 })
  l <- gets (.nextLabel)
  modify (\s -> s { nextLabel = l + 1 })
  k <- liftG $ chooseInt (0, 4)
  body <- concat <$> sequence (replicate k genMergeableStep)
  pure (symMem <> vals <> cond <> [IJump True l] <> body <> [ILabel l])
  where
    -- operands of 0, 1 and maxBound give identities, and stack shuffles leave
    -- some or all slots equal on both sides of the merge
    genMergeableStep = do
      d <- gets (.sdepth)
      liftG (chooseInt (0, 3)) >>= \case
        0 | d >= 2 -> do
          j <- liftG $ chooseInt (1, min 4 (d - 1))
          op (j + 1) (j + 1) (OpSwap (unsafeInto j))
        1 | d >= 1 -> do
          j <- liftG $ chooseInt (1, min 4 d)
          (<>) <$> op j (j + 1) (OpDup (unsafeInto j)) <*> op 1 0 OpPop
        2 -> (<>) <$> (liftG genWord >>= push) <*> op 1 0 OpPop
        _ -> do
          o <- liftG $ elements [OpAdd, OpXor, OpMul, OpSub, OpAnd, OpShl]
          w <- liftG $ frequency [(3, genWord), (1, elements [0, 1, maxBound])]
          (<>) <$> push w <*> op 2 1 o
    -- a literal, or a comparison with the keccak of a word in memory, which
    -- simplification folds to a literal
    genConcreteCond = liftG (chooseInt (0, 1)) >>= \case
      0 -> liftG (elements [0, 1, maxBound]) >>= push
      _ -> do
        v <- liftG genWord
        h <- liftG $ elements [keccak' (word256Bytes v), keccak' (word256Bytes v) + 1]
        concat <$> sequence
          [ push v, push 0x80, op 2 0 OpMstore, push 0x20, push 0x80, op 2 1 OpSha3
          , push h, op 2 1 OpEq ]

-- | Weighted block generators, and those only the main contract gets
blockGens, mainBlockGens :: [(Int, G [Item])]
blockGens =
  [ (10, genStraight), (4, genBranch), (2, genMergeable), (1, pure [IJumpFwd False]), (1, genHalt)
  , (1, genDeepStack), (2, genStorageWrite) ]
mainBlockGens =
  [ (2, genLoop), (2, genSmallLoop), (2, genCall), (2, genAccountOp), (1, genCreate)
  , (1, genPrecompileCall), (1, genRefund) ]

genBlock :: Bool -> G [Item]
genBlock isMain = do
  inner <- liftG $ frequency [(w, pure g) | (w, g) <- blockGens <> (if isMain then mainBlockGens else [])]
  items <- inner
  addLabel <- liftG $ chooseInt (0, 1)
  if addLabel == 0 then pure items else do
    l <- gets (.nextLabel)
    modify (\s -> s { nextLabel = l + 1 })
    pure (items <> [ILabel l])

genProg :: Bool -> Int -> Gen [Item]
genProg isMain n = do
  items <- flip evalStateT (GS 0 0 0) $ do
    pre <- concat <$> (liftG (chooseInt (1, 4)) >>= \k -> sequence (replicate k (liftG genWord >>= push)))
    blocks <- concat <$> sequence (replicate n (genBlock isMain))
    end <- gets (.nextLabel)
    epilogue <- liftG (chooseInt (0, 9)) >>= \e -> if e == 0 then pure [] else genHalt
    pure (pre <> blocks <> [ILabel end] <> epilogue)
  resolveJumps items

resolveJumps :: [Item] -> Gen [Item]
resolveJumps items = go (reverse items) [] []
  where
    go :: [Item] -> [Int] -> [Item] -> Gen [Item]
    go [] _ acc = pure acc
    go (i:is) later acc = case i of
      ILabel l -> go is (l : later) (i : acc)
      IJumpFwd c -> do l <- elements later
                       go is later (IJump c l : acc)
      _ -> go is later (i : acc)

genInputs :: Gen Inputs
genInputs = do
  len <- frequency [(1, pure 0), (3, chooseInt (1, 40)), (3, elements [4, 32, 36, 64, 68, 100])]
  cd <- BS.pack <$> vectorOf len (frequency [(3, pure 0), (3, chooseBoundedIntegral (0, 10)), (4, chooseAny)])
  nslots <- chooseInt (0, 4)
  slots <- Map.fromList <$> vectorOf nslots ((,) <$> frequency [(3, chooseBoundedIntegral (0, 3)), (1, chooseBoundedIntegral (0, 10))] <*> genWord)
  cv <- frequency [(1, pure 0), (1, chooseBoundedIntegral (1, 1000))]
  ts <- chooseBoundedIntegral (1, 2 ^ (40 :: Int))
  pure $ Inputs cd slots cv ts

instance Arbitrary TestCase where
  arbitrary = sized $ \n -> do
    mainProg <- genProg True (n `div` 4 + 3)
    calleeProg <- genProg False 3
    inputs <- genInputs
    gasLimit <- chooseInt (60000, 0xfffff)
    number <- elements [0, 1, 100, 256, 257, 300]
    pure $ TestCase (Prog mainProg calleeProg) inputs gasLimit number
  shrink c =
    [ c { prog = c.prog { main = m } } | m <- shrinkItems c.prog.main ] <>
    [ c { prog = c.prog { callee = m } } | m <- shrinkItems c.prog.callee ] <>
    [ c { inputs = c.inputs { calldata = BS.take k c.inputs.calldata } }
    | k <- shrinkIntegral (BS.length c.inputs.calldata) ] <>
    [ c { inputs = c.inputs { store = s } } | s <- shrinkStore c.inputs.store ]
    where
      shrinkStore s = [Map.deleteAt i s | i <- [0 .. Map.size s - 1]]

-- | Drop plain ops and pushes, keeping labels and jumps so targets stay valid
shrinkItems :: [Item] -> [[Item]]
shrinkItems items =
  [ take i items <> drop (i + k) items
  | k <- [8, 4, 2, 1], i <- [0, k .. length items - k]
  , all droppable (take k (drop i items)) ]
  where
    droppable = \case
      IOp _ -> True
      IPush _ _ -> True
      _ -> False


-- | How often a debugger session snapshots: rarely, every step, or often enough that going back crosses snapshots
genSnapEvery :: Gen Int
genSnapEvery = frequency [(1, pure 1), (4, chooseInt (2, 10)), (1, chooseInt (11, 60))]

genMove :: Gen Command
genMove = frequency
  [ (4, Step <$> chooseInt (1, 120)), (4, Back <$> chooseInt (1, 120)), (1, pure Restart), (1, pure Continue) ]
