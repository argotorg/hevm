{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : FuzzSymExec
Description : Differential fuzzing of concrete and symbolic execution against geth's evm

Random programs are run in geth's evm, and in hevm both concretely (comparing
traces step by step) and symbolically, with calldata, storage, callvalue and
timestamp left abstract. Substituting the concrete inputs into the symbolic
leaves must select exactly one leaf, whose outcome must match geth's. For other
leaves, the solver's model of their path condition is replayed in geth, and
must reach that leaf.
-}
module EVM.Test.FuzzSymExec (tests, lockstepTests, TestCase, concreteTestVm, symbolicTestVm) where

import Control.Monad (forM, forM_, unless, void, when)
import Control.Monad.IO.Unlift
import Control.Monad.ST (ST, stToIO, RealWorld)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad.State.Strict (StateT(..), evalStateT, get, gets, modify, lift)
import Control.Monad.Reader (ReaderT)
import Data.Aeson ((.:), (.:?))
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.Char (isDigit, toLower)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Data.List (intercalate, isInfixOf, isPrefixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Monoid (Any(..))
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text, unpack)
import Data.Text qualified as T
import Data.Tree (flatten)
import Data.Vector.Storable qualified as VS
import Data.Vector qualified as Vector
import Data.Word (Word8)
import GHC.Clock (getMonotonicTime)
import GHC.Generics (Generic)
import GHC.IO.Exception (ExitCode(ExitSuccess))
import Numeric (showHex)
import Optics.Core hiding (pre, elements)
import System.Directory (removeDirectoryRecursive)
import System.Environment (lookupEnv)
import System.FilePath ((</>))
import System.IO.Temp (getCanonicalTemporaryDirectory, createTempDirectory)
import System.Process (readCreateProcessWithExitCode, proc, CreateProcess(..))
import System.Timeout (timeout)
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty (testGroup, after, withResource, TestTree, TestName, DependencyType(..))
import Test.Tasty.HUnit (assertFailure, testCase)
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Witch (into, unsafeInto)

import EVM (makeVm, initialContract, defaultVMOpts, exec1, traceForest)
import EVM.Assembler (assemble)
import EVM.Concrete qualified as Concrete
import EVM.Expr qualified as Expr
import EVM.Exec (ethrunAddress)
import EVM.Fetch qualified as Fetch
import EVM.Fetch.MockNode (Account(..), World, Node(..), withMockNode)
import EVM.FeeSchedule
import EVM.Format (hexByteString)
import EVM.Op (intToOpName)
import EVM.Progress qualified as Progress
import EVM.Sign (deriveAddr)
import EVM.SMT qualified as SMT
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Traversals (foldProp, mapExpr, mapProp)
import EVM.Transaction qualified
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Dapp (emptyDapp)
import EVM.Debugger (Session, newSession, runCommand, Command(..), mkView, View(..), BranchView(..), sessionVM, isHalted, hasPendingBranch
                    , BranchMode(..), setBranchMode, setMerge, sessionStats, StatsView(..), Stats(..))
import EVM.Tracing (interpretWithTrace, VMTraceStep(..))

-- * Programs

data Item
  = IOp Op
  | IPush Int W256 -- ^ byte width (0 is PUSH0) and value
  | ILabel Int
  | IJump Bool Int -- ^ conditional?, target label
  | IJumpFwd Bool  -- ^ resolved by 'resolveJumps' to an 'IJump' to a later label
  | IRaw ByteString
  deriving (Show, Eq)

data Prog = Prog
  { main :: [Item]
  , callee :: [Item]
  } deriving (Show, Eq)

-- | Everything that the symbolic run leaves abstract
data Inputs = Inputs
  { calldata :: ByteString
  , store :: Map W256 W256
  , callvalue :: W256
  , timestamp :: W256
  } deriving (Show, Eq)

data TestCase = TestCase
  { prog :: Prog
  , inputs :: Inputs
  , gasLimit :: Int
  , number :: W256
  } deriving (Show, Eq)

opByte :: Op -> Word8
opByte o = case Vector.toList (assemble [o]) of
  [LitByte b] -> b
  _ -> internalError $ "not a single-byte op: " <> show o

itemSize :: Item -> Int
itemSize = \case
  IOp _ -> 1
  IPush w _ -> 1 + w
  ILabel _ -> 1
  IJump _ _ -> 4
  IJumpFwd _ -> 4
  IRaw b -> BS.length b

assembleItems :: [Item] -> ByteString
assembleItems items = BS.pack $ concatMap go items
  where
    labels = Map.fromList [(l, pos) | (ILabel l, pos) <- zip items (scanl (+) 0 (map itemSize items))]
    pushBytes :: Int -> W256 -> [Word8]
    pushBytes 0 _ = [0x5f]
    pushBytes w v = (0x5f + unsafeInto w) : [byteAt i v | i <- [w-1, w-2 .. 0]]
    byteAt :: Int -> W256 -> Word8
    byteAt i v = unsafeInto ((v `div` (256 ^ i)) `mod` 256)
    go = \case
      IOp o -> [opByte o]
      IPush w v -> pushBytes w v
      ILabel _ -> [opByte OpJumpdest]
      IJump c l -> pushBytes 2 (unsafeInto (labels Map.! l)) <> [opByte (if c then OpJumpi else OpJump)]
      IJumpFwd _ -> internalError "unresolved jump"
      IRaw b -> BS.unpack b

contractAddr, calleeAddr :: Addr
contractAddr = 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192
calleeAddr = 0xca11ee

contractBalance :: W256
contractBalance = 0xa493d65e20984bc

-- | Accounts besides the contract and the callee: (address, balance, nonce, storage)
extraAccounts :: [(Addr, W256, W256, Map W256 W256)]
extraAccounts =
  [ (0xe0a1, 0x1234, 3, mempty)
  , (0xe0a2, 0, 1, mempty)  -- EIP-161 nonempty by nonce only
  , (0xe0a3, 7, 0, mempty)  -- and by balance only
  , (0xe0a4, 0, 0, mempty)  -- EIP-161 empty
  , (createdAt 0x48, 0, 0, Map.singleton 1 1) -- storage only: the first CREATE collides (EIP-7610)
  , (createdAt 0x49, 5, 0, mempty)            -- funded before the second CREATE
  , (create2At 0, 9, 0, mempty)
  , (create2At 1, 0, 0, Map.singleton 2 3)
  ]
  where
    createdAt n = case Concrete.createAddress contractAddr n of
      LitAddr a -> a
      a -> internalError $ "symbolic create address: " <> show a
    create2At salt = case Concrete.create2Address contractAddr salt createInitCode of
      LitAddr a -> a
      a -> internalError $ "symbolic create2 address: " <> show a

-- | A single STOP
createInitCode :: ByteString
createInitCode = BS.singleton 0

-- | RETURNs and(callvalue, 0xf) bytes: the deployed code size is symbolic when
-- the CREATE value is
sizedInitCode :: ByteString
sizedInitCode = BS.pack [0x60, 0x0f, 0x34, 0x16, 0x5f, 0xf3]

-- | Addresses the account opcodes query, including one that does not exist. No 0x100:
-- the evm in nixpkgs (1.16.1) predates its P256VERIFY precompile (EIP-7951).
accountTargets :: [Addr]
accountTargets = [a | (a, _, _, _) <- extraAccounts] <> [0xe0a5, contractAddr, calleeAddr, coinbaseAddr, 1, 4, 0x0a, 0x11]

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

-- | (weight, pops, pushes, op)
opTable :: [(Int, Int, Int, Op)]
opTable = concat
  [ [(w, 2, 1, o) | (w, o) <- binary]
  , [(2, 3, 1, OpAddmod), (2, 3, 1, OpMulmod)]
  , [(w, 1, 1, o) | (w, o) <- unary]
  , [(1, 0, 1, o) | o <- env]
  , [(w, 2, 0, o) | (w, o) <- stores]
  , [(w, 3, 0, o) | (w, o) <- copies]
  , [(3, 1, 0, OpPop), (1, 1, 0, OpJump), (1, 2, 0, OpJumpi)]
  , [(1, 2 + n, 0, OpLog (unsafeInto n)) | n <- [0 .. 4 :: Int]]
  , [(1, n, n + 1, OpDup (unsafeInto n)) | n <- [1 .. 16 :: Int]]
  , [(1, n + 1, n + 1, OpSwap (unsafeInto n)) | n <- [1 .. 16 :: Int]]
  ]
  where
    binary =
      [ (4, OpAdd), (4, OpMul), (2, OpSub), (3, OpDiv), (2, OpSdiv)
      , (3, OpMod), (2, OpSmod), (2, OpExp), (2, OpSignextend)
      , (3, OpLt), (3, OpGt), (3, OpSlt), (3, OpSgt), (3, OpEq)
      , (3, OpAnd), (3, OpOr), (3, OpXor), (3, OpByte)
      , (3, OpShl), (3, OpShr), (3, OpSar), (3, OpSha3)
      ]
    -- no CLZ: the evm in nixpkgs (1.16.1) does not implement it yet
    unary =
      [ (3, OpIszero), (3, OpNot), (25, OpCalldataload), (2, OpBlockhash)
      , (1, OpBlobhash), (8, OpMload), (8, OpSload), (4, OpTload)
      ]
    env =
      [ OpAddress, OpOrigin, OpCaller, OpCallvalue, OpCalldatasize
      , OpCodesize, OpGasprice, OpReturndatasize, OpCoinbase, OpTimestamp
      , OpNumber, OpPrevRandao, OpGaslimit, OpChainid, OpSelfbalance
      , OpBaseFee, OpBlobBaseFee, OpPc, OpMsize
      ]
    stores = [(8, OpMstore), (8, OpMstore8), (5, OpSstore), (4, OpTstore)]
    copies = [(3, OpMcopy), (8, OpCalldatacopy), (2, OpCodecopy), (3, OpReturndatacopy)]

-- | Stack items each generated opcode consumes
opPops :: Map String Int
opPops = Map.fromList $
  [(opName o, pops) | (_, pops, _, o) <- opTable] <>
  [ ("CALL", 7), ("CALLCODE", 7), ("DELEGATECALL", 6), ("STATICCALL", 6)
  , ("BALANCE", 1), ("EXTCODESIZE", 1), ("EXTCODEHASH", 1), ("EXTCODECOPY", 4), ("CREATE", 3), ("CREATE2", 4)
  , ("RETURN", 2), ("REVERT", 2), ("JUMP", 1), ("JUMPI", 2) ]

opName :: Op -> String
opName = intToOpName . into . opByte

-- | Every opcode that the generator can emit
genOps :: [String]
genOps = Map.keys opPops <> ["STOP", "JUMPDEST"] <> ["PUSH" <> show n | n <- [0 .. 32 :: Int]]

-- | The opcodes in some bytecode, skipping push data
codeOps :: ByteString -> Set String
codeOps bs = case BS.uncons bs of
  Nothing -> mempty
  Just (b, rest) ->
    let skip = if b >= 0x60 && b <= 0x7f then into (b - 0x5f) else 0
    in Set.insert (intToOpName (into b)) (codeOps (BS.drop skip rest))

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
  cond <- genCalldataCond
  modify (\s -> s { sdepth = s.sdepth - 1 })
  l <- gets (.nextLabel)
  modify (\s -> s { nextLabel = l + 1 })
  k <- liftG $ chooseInt (1, 4)
  body <- concat <$> sequence (replicate k (do
    o <- liftG $ elements [OpAdd, OpXor, OpMul, OpSub, OpAnd, OpShl]
    w <- liftG genWord
    (<>) <$> push w <*> op 2 1 o))
  pure (symMem <> vals <> cond <> [IJump True l] <> body <> [ILabel l])

genBlock :: Bool -> G [Item]
genBlock isMain = do
  inner <- liftG $ frequency $
    [ (10, pure genStraight), (4, pure genBranch), (2, pure genMergeable), (1, pure (pure [IJumpFwd False])), (1, pure genHalt)
    , (1, pure genDeepStack), (2, pure genStorageWrite) ] <>
    (if isMain then [ (2, pure genLoop), (2, pure genCall), (2, pure genAccountOp), (1, pure genCreate)
                    , (1, pure genPrecompileCall), (1, pure genRefund) ] else [])
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

-- * geth

data EVMToolTrace =
  EVMToolTrace
    { pc :: Int
    , op :: Int
    , gas :: W256
    , memSize :: Integer
    , depth :: Int
    , stack :: [W256]
    , error :: Maybe String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolTrace where
  parseJSON = JSON.withObject "EVMToolTrace" $ \v -> EVMToolTrace
    <$> v .: "pc"
    <*> v .: "op"
    <*> v .: "gas"
    <*> v .: "memSize"
    <*> v .: "depth"
    <*> v .: "stack"
    <*> v .:? "error"

data EVMToolOutput =
  EVMToolOutput
    { output :: ByteStringS
    , error :: Maybe String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolOutput where
  parseJSON = JSON.withObject "EVMToolOutput" $ \v -> EVMToolOutput
    <$> v .: "output"
    <*> v .:? "error"

data GethLog = GethLog { address :: String, topics :: [W256], logData :: ByteStringS }
  deriving (Show, Eq)

instance JSON.FromJSON GethLog where
  parseJSON = JSON.withObject "GethLog" $ \v -> GethLog
    <$> (map toLower <$> v .: "address")
    <*> v .: "topics"
    <*> v .: "data"

data GethRun = GethRun
  { trace :: [EVMToolTrace]
  , output :: ByteString
  , error :: Maybe String
  , storage :: Map Addr (Map W256 W256)
  , logs :: [GethLog]
  , gasUsed :: W256
  } deriving (Show)

headMay :: [a] -> Maybe a
headMay = \case [] -> Nothing; x:_ -> Just x

hexW :: W256 -> String
hexW w = "0x" <> showHex w ""

hexHash :: W256 -> String
hexHash w = "0x" <> replicate (64 - length h) '0' <> h
  where h = showHex w ""

addrKey :: Addr -> String
addrKey a = "0x" <> replicate (40 - length h) '0' <> h
  where h = showHex (into a :: Integer) ""

secretKey :: Integer
secretKey = 0xDC38EE117CAE37750EB1ECC5CFD3DE8E85963B481B93E732C5D0CB66EE6B0C9D

fromAddress :: Addr
fromAddress = fromJust $ deriveAddr secretKey

originBalance :: W256
originBalance = 0x5ffd4878be161d74

mkTx :: TestCase -> Inputs -> EVM.Transaction.Transaction
mkTx c i = EVM.Transaction.Transaction
  { txdata     = i.calldata
  , gasLimit = unsafeInto c.gasLimit
  , gasPrice = Just 1
  , nonce    = 172
  , toAddr   = Just contractAddr
  , r        = 0
  , s        = 0
  , v        = 0
  , value    = i.callvalue
  , txtype     = EVM.Transaction.EIP1559Transaction
  , accessList = []
  , maxPriorityFeeGas =  Just 1
  , maxFeePerGas = Just 1
  , chainId = 1
  }

blockHash :: W256 -> W256
blockHash n = keccak' (Char8.pack (show (into n :: Integer)))

coinbaseAddr :: Addr
coinbaseAddr = 0xff

prevRandaoVal :: W256
prevRandaoVal = 42

-- | The state before the transaction, as geth gets it and as the mock node serves it
preState :: TestCase -> Inputs -> World
preState c i = Map.fromList $
  [ (fromAddress, Account mempty 0xac originBalance mempty)
  , (contractAddr, Account (assembleItems c.prog.main) 0x48 contractBalance i.store)
  , (calleeAddr, Account (assembleItems c.prog.callee) 1 0 mempty) ]
  <> [(a, Account mempty (unsafeInto n) b st) | (a, b, n, st) <- extraAccounts]

runGeth :: FilePath -> TestCase -> Inputs -> IO GethRun
runGeth dir c i = do
  let account acc = JSON.object
        [ ("balance", JSON.toJSON (hexW acc.balance))
        , ("code", JSON.toJSON (ByteStringS acc.code))
        , ("nonce", JSON.toJSON (hexW (into acc.nonce)))
        , ("storage", JSON.toJSON (Map.fromList [(hexHash k, hexHash v) | (k, v) <- Map.toList acc.storage])) ]
      alloc = fmap account (preState c i)
      oldest = if c.number > 256 then c.number - 256 else 0
      hashes = Map.fromList [(into n :: Integer, blockHash n) | c.number > 0, n <- [oldest .. c.number - 1]]
      env = JSON.object
        [ ("currentCoinbase", JSON.toJSON coinbaseAddr)
        , ("currentGasLimit", JSON.toJSON ("0x" <> showHex c.gasLimit ""))
        , ("currentNumber", JSON.toJSON (hexW c.number))
        , ("currentTimestamp", JSON.toJSON (hexW i.timestamp))
        , ("currentBaseFee", JSON.toJSON (hexW 0))
        , ("blockHashes", JSON.toJSON hashes)
        , ("withdrawals", JSON.toJSON ([] :: [Int]))
        , ("currentRandom", JSON.toJSON (hexHash prevRandaoVal))
        , ("parentBeaconBlockRoot", JSON.toJSON (hexHash 5))
        , ("currentExcessBlobGas", JSON.toJSON (hexW 0)) ]
  JSON.encodeFile (dir </> "txs.json") [EVM.Transaction.sign secretKey (mkTx c i)]
  JSON.encodeFile (dir </> "alloc.json") alloc
  JSON.encodeFile (dir </> "env.json") env
  let cmd = (proc "evm" [ "transition"
                        , "--state.fork", "Osaka"
                        , "--input.alloc", "alloc.json"
                        , "--input.env", "env.json"
                        , "--input.txs", "txs.json"
                        , "--output.alloc", "alloc-out.json"
                        , "--trace.returndata=true"
                        , "--trace", "trace.json"
                        , "--output.result", "result.json"
                        ]) { cwd = Just dir }
  (exitCode, out, err) <- readCreateProcessWithExitCode cmd ""
  when (exitCode /= ExitSuccess) $ assertFailure $ "evm failed: " <> show exitCode <> "\n" <> out <> err
  result <- fromJust <$> JSON.decodeFileStrict (dir </> "result.json")
  let receipt :: Maybe (String, [GethLog], W256)
      receipt = flip JSON.parseMaybe result $ JSON.withObject "result" $ \v -> do
        rs <- v .: "receipts"
        gasUsed <- v .: "gasUsed"
        case rs of
          [r] -> (,,) <$> r .: "transactionHash" <*> (fromMaybe [] <$> r .:? "logs") <*> pure gasUsed
          _ -> fail "expected one receipt"
  (txHash, logs, gasUsed) <- maybe (assertFailure $ "cannot parse evm result: " <> show result) pure receipt
  -- as a String, a trace with deep stacks on every line takes tens of GB
  traceLines <- Char8.lines <$> BS.readFile (dir </> ("trace-0-" <> txHash <> ".jsonl"))
  let decode :: JSON.FromJSON a => ByteString -> Maybe a
      decode = JSON.decodeStrict
      -- every call, including to precompiles, ends with an output line of its own
      step l = maybe (Left <$> (decode l :: Maybe EVMToolOutput)) (Just . Right) (decode l)
      steps = mapM step (init traceLines) <&> \xs -> [t | Right t <- xs]
      final :: Maybe EVMToolOutput
      final = decode (last traceLines)
  allocOut :: Map String JSON.Value <- fromJust <$> JSON.decodeFileStrict (dir </> "alloc-out.json")
  let storageOf a = fromMaybe mempty $ do
        acc <- Map.lookup (addrKey a) (Map.mapKeys (map toLower) allocOut)
        JSON.parseMaybe (JSON.withObject "account" (\v -> fromMaybe mempty <$> v .:? "storage")) acc
      readStore :: Map String W256 -> Map W256 W256
      readStore = Map.fromList . map (\(k, v) -> (read k, v)) . Map.toList
  case (steps, final) of
    (Just s, Just f) -> pure $ GethRun s (bssToBs f.output) f.error
      (Map.fromList [(a, nonZero (readStore (storageOf a))) | a <- [contractAddr, calleeAddr]]) logs gasUsed
    _ -> assertFailure $ "cannot parse evm trace: "
           <> show [l | l <- traceLines, isNothing (decode l :: Maybe EVMToolTrace)]

nonZero :: Map W256 W256 -> Map W256 W256
nonZero = Map.filter (/= 0)

-- * hevm

-- | How to set up a VM: concrete values for the concrete run, abstract ones for the symbolic run
data VMInputs = VMInputs
  { calldata :: Expr Buf
  , store :: Expr Storage
  , callvalue :: Expr EWord
  , timestamp :: Expr EWord
  }

concreteVMInputs :: Inputs -> VMInputs
concreteVMInputs i =
  VMInputs (ConcreteBuf i.calldata) (ConcreteStore i.store) (Lit i.callvalue) (Lit i.timestamp)

symCalldataBuf :: Expr Buf
symCalldataBuf = AbstractBuf "calldata"

symbolicVMInputs :: VMInputs
symbolicVMInputs = VMInputs symCalldataBuf (AbstractStore (LitAddr contractAddr) Nothing) TxValue Timestamp

-- | When fetching, only the code and balance of the contract are known up front: its storage
-- and every other account come from the mock node
mkVm :: forall t . VMOps t => Bool -> Gas t -> TestCase -> VMInputs -> ST RealWorld (VM t)
mkVm fetching gas c i = do
  let store = if fetching then ConcreteStore mempty else i.store
      contract = initialContract (RuntimeCode (ConcreteRuntimeCode (assembleItems c.prog.main)))
        & set #balance (Expr.add (Lit contractBalance) i.callvalue)
        & set #storage store
        & set #origStorage store
        & set #nonce (Just 0x48)
        & set #external fetching
      calleeContract = initialContract (RuntimeCode (ConcreteRuntimeCode (assembleItems c.prog.callee)))
        & set #nonce (Just 1)
  vm <- makeVm $ (defaultVMOpts :: VMOpts t)
    { contract = contract
    , otherContracts =
        (LitAddr ethrunAddress, initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty)))
        -- finalize pays the unused gas and the refund back to the origin
        : (LitAddr fromAddress, initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty))
            & set #balance (Lit originBalance) & set #nonce (Just 0xac))
        : if fetching then [] else
          (LitAddr calleeAddr, calleeContract)
          : [ (LitAddr a, initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty))
                & set #balance (Lit b) & set #nonce (Just (unsafeInto n))
                & set #storage (ConcreteStore st) & set #origStorage (ConcreteStore st))
            | (a, b, n, st) <- extraAccounts ]
    , calldata = (i.calldata, [])
    , value = i.callvalue
    , address = LitAddr contractAddr
    , caller = LitAddr fromAddress
    , origin = LitAddr fromAddress
    , coinbase = LitAddr coinbaseAddr
    , number = Lit c.number
    , timestamp = i.timestamp
    , gasprice = 1
    , gas = gas
    , gaslimit = unsafeInto c.gasLimit
    , blockGaslimit = unsafeInto c.gasLimit
    , prevRandao = Lit prevRandaoVal
    , baseFee = Lit 0
    , priorityFee = 1
    , maxCodeSize = 0xfffff
    , schedule = feeSchedule
    , chainId = 1
    -- only the concrete run tracks gas
    , txdataFloorGas = case i.calldata of
        ConcreteBuf cd -> EVM.Transaction.txdataFloorGas feeSchedule (mkTx c (Inputs cd mempty 0 0))
        _ -> 0
    }
  pure $ vm & set (#state % #calldata) i.calldata

data HevmRun = HevmRun
  { trace :: [VMTraceStep]
  , result :: Either EvmError ByteString
  , storage :: Map Addr (Map W256 W256)
  , logs :: [Expr Log]
  , gasUsed :: W256
  }

-- | With a node's URL, everything but the contract's code and balance is fetched from it
runHevm :: App m => SolverGroup -> Maybe Text -> TestCase -> Inputs -> m HevmRun
runHevm solvers url c i = do
  let txn = mkTx c i
      gas = unsafeInto c.gasLimit - EVM.Transaction.txGasCost feeSchedule txn
  fetcher <- case url of
    Nothing -> pure $ Fetch.oracle solvers Nothing Fetch.noRpc
    Just u -> do
      sess <- Fetch.mkSessionWithoutCache
      pure $ Fetch.oracle solvers (Just sess) (Fetch.RpcInfo (Just (Fetch.BlockNumber c.number, u)))
  vm0 <- liftIO $ stToIO $ mkVm (isJust url) gas c (concreteVMInputs i)
  (res, (vm, trace)) <- runStateT (interpretWithTrace fetcher Stepper.execFully) (vm0, [])
  -- slots never read or written were never fetched
  let pre a = if isJust url then (.storage) (Map.findWithDefault (Account mempty 0 0 mempty) a (preState c i)) else mempty
      storageOf a = case (.storage) <$> Map.lookup (LitAddr a) vm.env.contracts of
        Just (ConcreteStore s) -> nonZero (Map.union s (pre a))
        Nothing -> nonZero (pre a)
        Just s -> internalError $ "non-concrete storage in concrete run: " <> show s
      out = case res of
        Right (ConcreteBuf b) -> Right b
        Right b -> internalError $ "non-concrete return data: " <> show b
        Left e -> Left e
      stores = Map.fromList [(a, storageOf a) | a <- [contractAddr, calleeAddr]]
      -- the run starts after the gas purchase, so the origin only gets the unused gas back
      gasUsed = case (.balance) <$> Map.lookup (LitAddr fromAddress) vm.env.contracts of
        Just (Lit b) -> unsafeInto c.gasLimit - (b - originBalance)
        b -> internalError $ "origin balance: " <> show b
  pure $ HevmRun trace out stores (reverse vm.logs) gasUsed

-- | The VMs 'checkCase' starts from, for other fuzzers to run
concreteTestVm :: TestCase -> ST RealWorld (VM Concrete)
concreteTestVm c = mkVm False gas c (concreteVMInputs c.inputs)
  where gas = unsafeInto c.gasLimit - EVM.Transaction.txGasCost feeSchedule (mkTx c c.inputs)

symbolicTestVm :: TestCase -> ST RealWorld (VM Symbolic)
symbolicTestVm c = set #constraints symProps <$> mkVm False () c symbolicVMInputs

symIterConf :: IterConfig
symIterConf = IterConfig { maxIter = Just 6, askSmtIters = 1, loopHeuristic = Naive }

-- | Bounds that keep solver models replayable in geth
symProps :: [Prop]
symProps =
  [ PLEq (BufLength symCalldataBuf) (Lit 128)
  , PLEq TxValue (Lit 1000)
  , PLEq Timestamp (Lit (2 ^ (40 :: Int)))
  , PGEq Timestamp (Lit 1)
  ]

-- | Replays a model of the leaf as `hevm symbolic` does: Right True if the
-- concrete run fails exactly when the leaf does
replayModel :: App m => TestCase -> Expr End -> SMTCex -> m (Either Text Bool)
replayModel c leaf cex = do
  vm0 <- liftIO $ stToIO $ mkVm False () c symbolicVMInputs
  withSolvers Z3 1 (Just 10) defMemLimit $ \solvers ->
    replaySymCex solvers (\_ e -> PBool (isFailure e /= isFailure leaf)) (vm0 & set #constraints symProps) leaf cex
  where
    isFailure = \case Failure {} -> True; _ -> False

-- | The leaves, and the opcodes that ran with a non-literal operand
runSymbolic :: App m => SolverGroup -> TestCase -> m (Maybe ([Expr End], Set String))
runSymbolic solvers c = do
  conf <- readConfig
  vm0 <- liftIO $ stToIO $ mkVm False () c symbolicVMInputs
  ref <- liftIO $ newIORef mempty
  let vm = vm0 & set #constraints symProps
  leaves <- withRunInIO $ \runInIO ->
    timeout 60_000_000 $ runInIO $
      interpret (Fetch.oracle solvers Nothing Fetch.noRpc) symIterConf vm (recording conf ref) noopPathHandler
  forM leaves $ \ls -> (ls,) <$> liftIO (readIORef ref)

-- | 'runExpr', stepping one opcode at a time to record those with a non-literal operand.
-- Loops on concrete conditions only end when gas runs out, which the symbolic
-- run does not track, so a path is cut short after 'maxSteps'.
recording :: Config -> IORef (Set String) -> Stepper.Stepper Symbolic (Expr End)
recording conf ref = loop (0 :: Int)
  where
    maxSteps = 20000
    loop n = do
      vm <- Stepper.evm get
      case vm.result of
        Nothing
          | n >= maxSteps -> pure $ Partial vm.constraints (TraceContext mempty mempty mempty)
                                      (MaxIterationsReached vm.state.pc vm.state.contract)
          | otherwise -> Stepper.evm (record vm >> exec1 conf) >> loop (n + 1)
        Just (HandleEffect (Query q)) -> Stepper.wait q >> loop n
        Just (HandleEffect (Branch ctx)) -> Stepper.fork ctx >> loop n
        Just _ -> runExpr
    record vm = case vm.state.code of
      RuntimeCode (ConcreteRuntimeCode bs) | vm.state.pc < BS.length bs -> do
        let name = intToOpName (into (BS.index bs vm.state.pc))
            isLit = \case Lit _ -> True; _ -> False
        when (any (not . isLit) (take (Map.findWithDefault 0 name opPops) vm.state.stack)) $
          lift $ unsafeIOToST $ atomicModifyIORef' ref (\x -> (Set.insert name x, ()))
      _ -> pure ()

-- * Checking

data Outcome
  = OSuccess ByteString (Map Addr (Map W256 W256))
  | ORevert ByteString
  | OError String
  deriving (Show, Eq)

gethOutcome :: GethRun -> Outcome
gethOutcome g = case g.error of
  Nothing -> OSuccess g.output g.storage
  Just "execution reverted" -> ORevert g.output
  Just e -> OError (errorKind e)

-- | An error message without its details, e.g. "stack underflow" for geth's "stack underflow (0 <=> 2)"
errorKind :: String -> String
errorKind e = case unwords (takeWhile (not . any isDigit) (words (takeWhile (`notElem` ("(:" :: String)) (map toLower e)))) of
  "attempting to modify state while in static context" -> "write protection"
  k -> k

hevmErrorKind :: EvmError -> String
hevmErrorKind = errorKind . evmErrToString

-- | Symbolic execution does not track gas, so its outcome is unknown when gas ran out anywhere
gasDependent :: GethRun -> Bool
gasDependent g = any isGas (g.error : map (.error) g.trace) || any lowGasPrecompile (zip g.trace (drop 1 g.trace)) || callsModexp g
  where
    isGas = maybe False (\e -> "out of gas" `isInfixOf` e || "gas uint64 overflow" `isInfixOf` e)
    -- geth does not trace precompiles, and one that fails burns its gas whether it ran out or not.
    -- Generated precompile calls get plenty of gas, so a failing one with little may have run out.
    lowGasPrecompile (a, b) = case reverse a.stack of
      gas : target : _ -> a.op `elem` [0xf1, 0xf2, 0xf4, 0xfa] && target >= 1 && target <= 0x11
        && b.depth == a.depth && headMay (reverse b.stack) == Just 0 && min gas a.gas < 0x100000
      _ -> False

callsModexp :: GethRun -> Bool
callsModexp g = any (\t -> t.op `elem` [0xf1, 0xf2, 0xf4, 0xfa] && take 1 (drop 1 (reverse t.stack)) == [5]) g.trace

compareTraces :: [VMTraceStep] -> [EVMToolTrace] -> Either String ()
compareTraces hs gs = go hs (dedup gs)
  where
    -- geth traces a failing step once more, with its error
    dedup (a:b:rest) | isJust b.error, a.pc == b.pc, a.op == b.op, a.depth == b.depth = dedup (a : rest)
    dedup (a:rest) = a : dedup rest
    dedup [] = []
    go [] [] = Right ()
    -- hevm steps into code-less accounts, geth does not
    go (a:ax) bs
      | a.op == 0, a.pc == 0, a.depth > 1
      , maybe True (\b -> b.depth < a.depth) (headMay bs) = go ax bs
    go (a:ax) (b:bx)
      | a.op /= b.op || a.pc /= b.pc =
          Left $ "op/pc mismatch: hevm " <> step a <> ", geth " <> intToOpName b.op <> " pc " <> show b.pc
      | a.stack /= b.stack = mismatch "stack" a.stack b.stack
      | into a.gas /= b.gas = mismatch "gas" a.gas b.gas
      | into a.memSize /= b.memSize = mismatch "memSize" a.memSize b.memSize
      | a.depth /= b.depth = mismatch "depth" a.depth b.depth
      | otherwise = go ax bx
      where
        mismatch :: (Show x, Show y) => String -> x -> y -> Either String ()
        mismatch what x y = Left $ what <> " mismatch at " <> step a
          <> "\nhevm: " <> show x <> "\ngeth: " <> show y
    go a b = Left $ "trace lengths differ, hevm has " <> show (length a)
                 <> " more, geth has " <> show (length b) <> " more"
    step a = intToOpName a.op <> " pc " <> show a.pc

hevmOutcome :: HevmRun -> Outcome
hevmOutcome h = case h.result of
  Right b -> OSuccess b h.storage
  Left (Revert (ConcreteBuf b)) -> ORevert b
  Left e -> OError (hevmErrorKind e)

logsMatch :: [Expr Log] -> [GethLog] -> Bool
logsMatch hs gs = length hs == length gs && and (zipWith same hs gs)
  where
    same :: Expr Log -> GethLog -> Bool
    same (LogEntry (WAddr (LitAddr a)) (ConcreteBuf d) ts) g =
      addrKey a == g.address && d == bssToBs g.logData && map forceLit ts == g.topics
    same _ _ = False

failWith :: TestCase -> Inputs -> String -> IO a
failWith c i msg = assertFailure $ msg
  <> "\ninputs: " <> show i
  <> "\nmain: " <> bsToHex (assembleItems c.prog.main)
  <> "\ncallee: " <> bsToHex (assembleItems c.prog.callee)
  <> "\nreproduce with: " <> reproduction c i

-- | Environment variables that 'caseFromEnv' reads back
reproduction :: TestCase -> Inputs -> String
reproduction c i = unwords
  [ "HEVM_FUZZ_MAIN=" <> hex (assembleItems c.prog.main), "HEVM_FUZZ_CALLEE=" <> hex (assembleItems c.prog.callee)
  , "HEVM_FUZZ_CALLDATA=" <> hex i.calldata, "HEVM_FUZZ_CALLVALUE=" <> show i.callvalue
  , "HEVM_FUZZ_TIMESTAMP=" <> show i.timestamp, "HEVM_FUZZ_STORE=" <> intercalate "," [ show k <> ":" <> show v | (k, v) <- Map.toList i.store ]
  , "HEVM_FUZZ_GASLIMIT=" <> show c.gasLimit, "HEVM_FUZZ_NUMBER=" <> show c.number ]
  where hex = bsToHex

-- | Records the case a property runs in HEVM_FUZZ_CASE_FILE, suffixed with the
-- property's name as properties run concurrently, to find one that crashes or hangs
writeCaseFile :: String -> String -> IO ()
writeCaseFile name content = lookupEnv "HEVM_FUZZ_CASE_FILE" >>= mapM_ (\f -> writeFile (f <> "." <> name) content)

splitOn' :: Char -> String -> [String]
splitOn' d str = case break (== d) str of
  (a, []) -> [a]
  (a, _ : rest) -> a : splitOn' d rest

modeOf :: String -> BranchMode
modeOf = \case
  "ExplorerBranches" -> ExplorerBranches
  "CheckedBranches" -> CheckedBranches
  _ -> SolverBranches

-- | The case 'reproduction' describes, if HEVM_FUZZ_MAIN is set
caseFromEnv :: IO (Maybe TestCase)
caseFromEnv = lookupEnv "HEVM_FUZZ_MAIN" >>= \case
  Nothing -> pure Nothing
  Just m -> do
    let var k d = fromMaybe d <$> lookupEnv ("HEVM_FUZZ_" <> k)
        bytes = fromJust . hexByteString . Char8.pack
        w256 :: String -> W256
        w256 = fromInteger . read
    callee <- var "CALLEE" ""
    cd <- var "CALLDATA" ""
    cv <- var "CALLVALUE" "0"
    ts <- var "TIMESTAMP" "1"
    st <- var "STORE" ""
    gl <- var "GASLIMIT" "300000"
    n <- var "NUMBER" "1"
    let store = Map.fromList [ (w256 k, w256 (drop 1 v)) | kv <- splitOn' ',' st, not (null kv), let (k, v) = break (== ':') kv ]
    pure $ Just $ TestCase (Prog [IRaw (bytes m)] [IRaw (bytes callee)]) (Inputs (bytes cd) store (w256 cv) (w256 ts)) (read gl) (w256 n)

-- | Concrete hevm against geth, howling failures with how hevm ran
checkConcrete :: String -> TestCase -> Inputs -> GethRun -> HevmRun -> IO ()
checkConcrete how c i g h = do
  let fails :: String -> IO a
      fails = failWith c i . ((how <> ": ") <>)
      ops :: [(Int, String)] -> String
      ops xs = unwords (map (\(p, o) -> show p <> ":" <> o) (take 40 xs))
        <> (if length xs > 40 then " ... " <> unwords (map (\(p, o) -> show p <> ":" <> o) (lastN 15 xs)) else "")
      lastN n xs = drop (length xs - n) xs
      traces = "\nhevm trace: " <> ops [(t.pc, intToOpName t.op) | t <- h.trace]
            <> "\ngeth trace: "
            <> ops [(t.pc, intToOpName t.op <> maybe "" withParens t.error) | t <- g.trace]
      withParens e = "(" <> e <> ")"
  -- geth 1.16.1 prices modexp before EIP-7883 was final, so gas and what depends on it differ
  unless (callsModexp g) $ do
    either (fails . (<> traces)) pure (compareTraces h.trace g.trace)
    let ho = hevmOutcome h
        go = gethOutcome g
    unless (ho == go || gasDependent g && failed ho && failed go) $
      fails $ "concrete outcome mismatch\nhevm: " <> show ho <> "\ngeth: " <> show go
    when (succeeded go && not (logsMatch h.logs g.logs)) $
      fails $ "logs mismatch\nhevm: " <> show h.logs <> "\ngeth: " <> show g.logs
    when (h.gasUsed /= g.gasUsed) $
      fails $ "gas used mismatch\nhevm: " <> show h.gasUsed <> "\ngeth: " <> show g.gasUsed
  where
    failed = \case OSuccess {} -> False; _ -> True
    succeeded = \case OSuccess {} -> True; _ -> False

-- | Substitute concrete inputs into a symbolic expression and evaluate it
concretize :: TestCase -> Inputs -> Expr a -> Expr a
concretize c i = untilFixpointN 4 (Expr.concKeccakSimpExpr . mapExpr blockHashes) . mapExpr inputs
  where
    inputs :: Expr b -> Expr b
    inputs = \case
      AbstractBuf "calldata" -> ConcreteBuf i.calldata
      AbstractStore (LitAddr a) Nothing | a == contractAddr -> ConcreteStore i.store
      TxValue -> Lit i.callvalue
      Timestamp -> Lit i.timestamp
      e -> e
    blockHashes :: Expr b -> Expr b
    blockHashes = \case
      BlockHash (Lit n) -> Lit $ if n + 256 < c.number || n >= c.number then 0 else blockHash n
      e -> e
    untilFixpointN :: Int -> (Expr b -> Expr b) -> Expr b -> Expr b
    untilFixpointN 0 _ e = e
    untilFixpointN k f e = let e' = f e in if e' == e then e else untilFixpointN (k - 1) f e'

concretizeProps :: TestCase -> Inputs -> [Prop] -> Maybe Bool
concretizeProps c i ps = case Expr.concKeccakSimpProps (map (mapProp (concretize c i)) ps) of
  [] -> Just True
  [PBool False] -> Just False
  _ -> Nothing

leafOutcome :: TestCase -> Inputs -> Expr End -> Either String (Maybe Outcome)
leafOutcome c i = \case
  Success _ _ buf contracts -> do
    out <- concreteBuf (concretize c i buf)
    stores <- forM [contractAddr, calleeAddr] $ \a -> case Map.lookup (LitAddr a) contracts of
      Just (C { storage = s }) -> case concretize c i s of
        ConcreteStore m -> Right (a, nonZero m)
        s' -> Left $ "storage of " <> show a <> " did not concretize: " <> show s'
      _ -> Left $ "missing contract " <> show a
    Right $ Just $ OSuccess out (Map.fromList stores)
  Failure _ _ (Revert buf) -> Just . ORevert <$> concreteBuf (concretize c i buf)
  Failure _ _ e -> Right $ Just $ OError (hevmErrorKind e)
  Partial {} -> Right Nothing
  e -> Left $ "unexpected leaf: " <> show e
  where
    concreteBuf :: Expr Buf -> Either String ByteString
    concreteBuf (ConcreteBuf b) = Right b
    concreteBuf b = Left $ "buffer did not concretize: " <> show b

-- | Select the leaf that the concrete inputs reach, and check it against geth.
-- Returns a label for coverage.
checkLeaves :: TestCase -> Inputs -> [Expr End] -> Maybe Int -> GethRun -> IO String
checkLeaves c i leaves expected g = do
  let fails :: String -> IO a
      fails msg = failWith c i (msg <> "\nleaves: " <> show leaves)
      evals = map (concretizeProps c i . extractProps) leaves
      concProps = Expr.concKeccakSimpProps . map (mapProp (concretize c i))
      undecided = [n | (n, Nothing) <- zip [0 :: Int ..] evals]
      taken = [n | (n, Just True) <- zip [0 :: Int ..] evals]
  -- past where gas runs out, the symbolic paths can e.g. hash huge buffers
      unknownCall = any (\case PCall {} -> True; _ -> False) . extractProps
  if gasDependent g && not (null undecided) && length taken <= 1 then pure "gas-dependent, undecided path"
  -- a call to a symbolic target gets fresh results, which the inputs cannot decide
  else if not (null undecided) && all (unknownCall . (leaves !!)) undecided && length taken <= 1
    then pure "call to unknown code, undecided path" else do
    unless (null undecided) $ fails $ "path conditions of leaves " <> show undecided <> " did not concretize: "
      <> show [concProps (extractProps (leaves !! n)) | n <- undecided]
    n <- case taken of
      [n] -> pure n
      _ -> fails $ "concrete inputs reach leaves " <> show taken <> " instead of exactly one"
    -- keccak of a symbolic buffer is only bounded, so a model may pick a hash no input has
    let spurious = maybe False (\e -> e /= n && hashesSymbolic (leaves !! e)) expected
        -- decomposition replaces mapping and array slots by their keys, and then
        -- the model's storage must be exact
        hashesSymbolic l = let ps = Expr.simplifyProps (extractProps l)
          in getAny $ foldMap (foldProp symKeccak mempty) (fromMaybe ps (Expr.decomposeStorageProps ps))
        symKeccak :: Expr b -> Any
        symKeccak = \case Keccak (ConcreteBuf _) -> Any False; Keccak _ -> Any True; _ -> Any False
    forM_ expected $ \e -> when (e /= n && not spurious) $ fails $ "model of leaf " <> show e <> " reaches leaf " <> show n
    if spurious then pure "model via symbolic keccak reaches another leaf"
    else if gasDependent g then pure "gas-dependent" else case leafOutcome c i (leaves !! n) of
      Left err -> fails err
      Right Nothing -> pure $ leafKind (leaves !! n)
      Right (Just o)
        | o == gethOutcome g -> pure $ case o of
            OSuccess {} -> "success"
            ORevert _ -> "revert"
            OError e -> "error: " <> e
        | otherwise -> fails $ "symbolic outcome mismatch\nsymbolic: " <> show o
                             <> "\ngeth: " <> show (gethOutcome g)

-- | Inputs from a model of a leaf's path condition
modelInputs :: Inputs -> SMTCex -> Either String Inputs
modelInputs orig cex = do
  cd <- case Map.lookup symCalldataBuf cex.buffers of
    Nothing -> Right orig.calldata
    Just m -> case SMT.collapse m of
      Just (Flat bs) -> Right bs
      _ -> Left $ "cannot flatten calldata model: " <> show m
  pure $ Inputs
    { calldata = cd
    , store = maybe orig.store (Map.filter (/= 0)) (Map.lookup (LitAddr contractAddr) cex.store)
    , callvalue = Map.findWithDefault orig.callvalue TxValue cex.txContext
    , timestamp = Map.findWithDefault orig.timestamp Timestamp cex.blockContext
    }

withDir :: (FilePath -> IO a) -> IO a
withDir f = do
  tmp <- getCanonicalTemporaryDirectory
  dir <- createTempDirectory tmp "evm-trace"
  r <- f dir
  removeDirectoryRecursive dir
  pure r

data Report = Report
  { tables :: [(String, String)] -- ^ (table, label) for 'tabulate'
  , generated :: Set String
  , executed :: Set String       -- ^ by geth, on any of the inputs
  , symbolic :: Set String       -- ^ with a non-literal operand
  }

leafKind :: Expr End -> String
leafKind = \case
  Success {} -> "success"
  Failure _ _ (Revert _) -> "revert"
  Failure _ _ e -> "error: " <> hevmErrorKind e
  Partial _ _ p -> "partial: " <> takeWhile (/= ' ') (show p)
  _ -> "other"

-- | Concrete hevm against geth, then the symbolic leaves against geth on the
-- concrete inputs and on models of up to 'maxReplays' other leaves
checkCase :: App m => Int -> TestCase -> m Report
checkCase maxReplays c = Progress.withProgressLogFromEnv "fuzz-symexec" $
  withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
  let phase name = liftIO $ lookupEnv "HEVM_FUZZ_CASE_FILE" >>= mapM_ (\f -> appendFile (f <> ".random-contract-concrete-call") ("\nphase: " <> name))
      runBoth i = do
        phase "geth"
        g <- liftIO $ withDir $ \dir -> runGeth dir c i
        phase "hevm"
        h <- runHevm solvers Nothing c i
        liftIO $ checkConcrete "hevm" c i g h
        phase "hevm via RPC"
        hr <- withRunInIO $ \run -> withMockNode c.number (preState c i) $ \node ->
          run (runHevm solvers (Just node.url) c i)
        liftIO $ checkConcrete "hevm via RPC" c i g hr
        pure g
      ran g = Set.fromList [intToOpName t.op | t <- g.trace]
      generated = codeOps (assembleItems c.prog.main) <> codeOps (assembleItems c.prog.callee)
  g <- runBoth c.inputs
  let gethTables = [("geth outcome", maybe "success" errorKind g.error)]
  phase "symbolic"
  runSymbolic solvers c >>= \case
    Nothing -> pure $ Report (("symbolic", "timeout") : gethTables) generated (ran g) mempty
    Just (leaves, symOps) -> do
      phase $ "leaves: " <> show (length leaves)
      first <- liftIO $ checkLeaves c c.inputs leaves Nothing g
      let candidates = take maxReplays [ (n, l) | (n, l) <- zip [0 ..] leaves
                                                , concretizeProps c c.inputs (extractProps l) /= Just True
                                                , not (isPartial l) ]
      replays <- forM candidates $ \(n, l) -> if mentionsBlockHash l
        -- BLOCKHASH of a symbolic number is uninterpreted, so a model can pick any hash
        then pure ("skipped: symbolic blockhash", Nothing, Nothing)
        else phase ("replay " <> show n) >> checkSatWithProps solvers (extractProps l) >>= \case
          Cex cex -> case modelInputs c.inputs cex of
            Left err -> pure ("model: " <> err, Nothing, Nothing)
            Right i -> do
              g' <- runBoth i
              r <- liftIO (checkLeaves c i leaves (Just n) g')
              phase ("hevm replay " <> show n)
              replayed <- replayModel c l cex
              -- where geth confirms the model reaches the leaf, so must `hevm symbolic`'s replay
              let confirmed = not (any (`isPrefixOf` r) ["gas-dependent", "model via symbolic keccak", "call to unknown code"])
              when (confirmed && replayed == Right False) $ liftIO $ failWith c i $
                "hevm symbolic's replay does not reproduce leaf " <> show n <> " that geth reaches\nleaf: " <> show l
              pure (r, Just g', Just (either (("cannot replay: " <>) . unpack) (\b -> if b then "validated" else "not reproducible") replayed))
          -- outside loops, branches are not checked for feasibility
          Qed -> pure ("unsat leaf", Nothing, Nothing)
          Unknown _ -> pure ("unknown", Nothing, Nothing)
          Error e
            | any (`isInfixOf` e) ["not currently implemented", "Cannot encode"] -> pure ("unsupported by SMT", Nothing, Nothing)
            | otherwise -> liftIO $ assertFailure $ "solver error: " <> show e
      pure $ Report
        { tables = gethTables
            <> [("leaves", bucket (length leaves)), ("concrete inputs reach", first)]
            <> [("replayed model reaches", r) | (r, _, _) <- replays]
            <> [("hevm symbolic replay", h) | (_, _, Just h) <- replays]
            <> [("leaf kinds", leafKind l) | l <- leaves]
        , generated
        , executed = Set.unions (ran g : [ran g' | (_, Just g', _) <- replays])
        , symbolic = symOps
        }
  where
    mentionsBlockHash l = getAny $ foldMap (foldProp isBlockHash mempty) (extractProps l)
    isBlockHash :: Expr a -> Any
    isBlockHash = \case BlockHash _ -> Any True; _ -> Any False
    bucket :: Int -> String
    bucket n | n <= 1 = show n
             | n <= 4 = "2-4"
             | n <= 16 = "5-16"
             | otherwise = ">16"

-- | For each opcode: how many cases generated it, ran it in geth, and ran it
-- symbolically with a non-literal operand
type Coverage = Map String (Int, Int, Int)

addCoverage :: IO (IORef Coverage) -> Report -> IO ()
addCoverage cov r = do
  ref <- cov
  let new = Map.unionsWith add3
        [Map.fromSet (const (1, 0, 0)) r.generated, Map.fromSet (const (0, 1, 0)) r.executed, Map.fromSet (const (0, 0, 1)) r.symbolic]
      add3 (a, b, x) (a', b', x') = (a + a', b + b', x + x')
  atomicModifyIORef' ref (\m -> (Map.unionWith add3 m new, ()))

printCoverage :: IORef Coverage -> IO ()
printCoverage ref = do
  m <- readIORef ref
  let counts o = Map.findWithDefault (0, 0, 0) o m
      missing f = unwords [o | o <- genOps, f (counts o) == 0]
      takesOperands o = Map.findWithDefault 0 o opPops > 0
      fst3 (a, _, _) = a
      snd3 (_, b, _) = b
      thd3 (_, _, x) = x
  unless (Map.null m) $ do
    putStrLn "fuzz-symexec opcode coverage, in cases (generated/ran in geth/ran with a symbolic operand):"
    putStrLn $ "  never generated: " <> missing fst3
    putStrLn $ "  never ran in geth: " <> missing snd3
    putStrLn $ "  never ran with a symbolic operand: "
      <> unwords [o | o <- genOps, takesOperands o, thd3 (counts o) == 0]
    forM_ (chunksOf 6 (Map.toList m)) $ \row ->
      putStrLn $ "  " <> unwords [pad 20 (o <> " " <> show a <> "/" <> show b <> "/" <> show x) | (o, (a, b, x)) <- row]
  where
    pad n t = t <> replicate (n - length t) ' '
    chunksOf _ [] = []
    chunksOf n xs = take n xs : chunksOf n (drop n xs)

-- * Lockstep

-- | What a lockstep run covered, for the coverage tables
data Lockstep = Lockstep
  { stopped  :: String
  , steps    :: Int
  , compared :: Int -- ^ stack words, memory and storage that concretized and matched
  , opaque   :: Int -- ^ stack words that stayed symbolic after substituting the inputs
  , branches :: Int -- ^ branches offered, and taken the concrete run's way
  , retries  :: Int -- ^ sides tried that the concrete run did not take
  , trail    :: [String] -- ^ the latest steps, newest first, for failure reports
  , static   :: (Int, Int) -- ^ branches decided without the solver, and those it could have decided
  , ended    :: Maybe (Int, Int, String) -- ^ pc, depth and kind of result, when both runs halted
  , ops      :: Set String -- ^ the opcodes stepped and compared after
  , merges   :: Int -- ^ symbolic steps that merged a branch
  }

maxLockstepSteps :: Int
maxLockstepSteps = 2000

-- | Steps a concrete and a symbolic debugging session of the case side by side,
-- taking the concrete run's side at every symbolic branch. After every step the
-- symbolic state, with the concrete inputs substituted, must be the concrete one.
lockstepCase :: App m => SolverGroup -> BranchMode -> Bool -> TestCase -> m (Either String Lockstep)
lockstepCase solvers mode merging c = Progress.withProgressLogFromEnv "lockstep" $ do
  sc0 <- liftIO $ stToIO (concreteTestVm c) >>= newSession emptyDapp
  ss0 <- liftIO $ setMerge merging . setBranchMode mode <$> (stToIO (symbolicTestVm c) >>= newSession emptyDapp)
  r <- go sc0 ss0 (Lockstep "" 0 0 0 0 0 [] (0, 0) Nothing mempty 0) Nothing
  Progress.emit "lockstep-end" $ case r of
    Left err -> ["failure" JSON..= T.pack err]
    Right l -> ["stopped" JSON..= T.pack l.stopped, "steps" JSON..= l.steps, "compared" JSON..= l.compared, "branches" JSON..= l.branches]
  pure r
  where
    fetcher :: Fetch.Fetcher t m
    fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
    go :: App m => Session Concrete -> Session Symbolic -> Lockstep -> Maybe String -> m (Either String Lockstep)
    go sc ss acc prevOp = do
      let vc = sessionVM sc
          vs = sessionVM ss
          where_ = "after " <> show acc.steps <> " steps, at pc " <> show vc.state.pc <> maybe "" (" after " <>) prevOp <> ": "
          stopWith why = pure (Right acc { stopped = why })
          mismatch = mismatchAt vc
          mismatchAt now msg
            | gasDependentRun now = stopWith "gas-dependent"
            | otherwise = pure (Left (where_ <> msg <> "\nlast steps, oldest first:\n" <> unlines (reverse acc.trail)))
      cmp <- liftIO $ compareStates c prevOp vc vs
      case cmp of
        _ | Just (Unfinished p) <- vs.result -> stopWith ("symbolic unfinished: " <> unfinishedReason p)
        Left msg -> mismatch msg
        Right (n, o) -> do
          let acc' = acc { compared = acc.compared + n, opaque = acc.opaque + o }
          case (isHalted sc, isHalted ss) of
            (True, True) -> either mismatch (const (pure (Right acc' { stopped = "halted", ended = Just (endOf vs) }))) (compareEnds c vc vs)
            (True, False) -> mismatch $ "only the concrete run halted: " <> show vc.result
            (False, True) -> mismatch $ "only the symbolic run halted: " <> show vs.result
            _ | acc.steps >= maxLockstepSteps -> stopWith "step limit"
              | otherwise -> do
                  let opName' = intToOpName (fromIntegral (getOpW8' vc))
                  sc1 <- runCommand fetcher (Step 1) sc >>= settle (4 :: Int) vc
                  ss1 <- runCommand fetcher (Step 1) ss
                  -- a merged branch runs one side's instructions in the symbolic step: the
                  -- concrete run catches up to where the merge ended
                  (sc', merged) <- if merging && not (hasPendingBranch ss1) && not (isHalted ss1) && not (atSame sc1 ss1)
                    then catchUp (200 :: Int) ss1 sc1 <&> \sc2 -> if atSame sc2 ss1 then (sc2, True) else (sc1, False)
                    else pure (sc1, False)
                  picked <- if merged then pure (Right (ss1, 0, 0)) else pickSide vs (sessionVM sc') ss1
                  case picked of
                    -- a call to an address that stays symbolic goes to unknown code, which is
                    -- over-approximated rather than run
                    Left _ | opName' `elem` ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"]
                           , target : _ <- drop 1 vs.state.stack
                           , Nothing <- Expr.maybeLitWordSimp (Expr.simplify target)
                           , length (sessionVM sc').frames > length vs.frames -> stopWith "call to a symbolic address"
                    Left msg -> mismatchAt (sessionVM sc') msg
                    Right (ss'', _, _) | (sessionStats ss'').counters.staticWrong > 0 -> do
                      v <- liftIO $ mkView ss''
                      pure $ Left $ where_ <> "the solver contradicts a branch decided by simplification:\n"
                        <> unlines (map T.unpack v.warnings)
                    Right (ss'', tried, took) -> case concretizeProps c c.inputs (sessionVM ss'').constraints of
                      Just False -> mismatch $ "the concrete inputs violate the path conditions after " <> opName'
                        <> ": " <> show (sessionVM ss'').constraints
                      _ -> do
                        let vs' = sessionVM ss''
                            entry = "  " <> show acc.steps <> ": pc " <> show vc.state.pc <> " " <> opName'
                              <> " depth " <> show (length vc.frames)
                              <> (if took > 0 then ", took the branch side that leads to pc " <> show vs'.state.pc
                                                   <> " after trying " <> show tried <> " other sides" else "")
                        Progress.emit "lockstep-step" $
                          [ "step" JSON..= acc.steps, "pc" JSON..= vc.state.pc, "op" JSON..= T.pack opName', "depth" JSON..= length vc.frames
                          , "compared" JSON..= n, "symbolic" JSON..= o ]
                          <> [ "branchesTaken" JSON..= took | took > 0 ] <> [ "sidesRetried" JSON..= tried | tried > 0 ]
                        let counters = (sessionStats ss'').counters
                        go sc' ss'' acc' { steps = acc.steps + 1, branches = acc.branches + took, retries = acc.retries + tried
                                         , merges = acc.merges + if merged then 1 else 0
                                         , ops = Set.insert opName' acc.ops
                                         , trail = take 30 (entry : acc.trail)
                                         , static = (counters.staticDecisions, counters.staticMissed) } (Just opName')
    -- an instruction may take several steps, e.g. when it is re-executed after
    -- a query, but always ends at another pc or depth, or halts
    midInstruction :: VM t -> VM t -> Bool
    midInstruction before now = isNothing now.result && now.state.pc == before.state.pc
                                  && length now.frames == length before.frames
    atSame :: Session Concrete -> Session Symbolic -> Bool
    atSame a b = (sessionVM a).state.pc == (sessionVM b).state.pc && length (sessionVM a).frames == length (sessionVM b).frames
    catchUp :: App m => Int -> Session Symbolic -> Session Concrete -> m (Session Concrete)
    catchUp n target s
      | n <= 0 || isHalted s || atSame s target = pure s
      | otherwise = runCommand fetcher (Step 1) s >>= catchUp (n - 1) target
    settle :: App m => Int -> VM Concrete -> Session Concrete -> m (Session Concrete)
    settle n before s
      | n > 0, midInstruction before (sessionVM s) = runCommand fetcher (Step 1) s >>= settle (n - 1) before
      | otherwise = pure s
    -- The branch sides and further steps that reach the concrete state: same pc
    -- and depth, and path conditions the inputs satisfy. One instruction may
    -- branch several times, e.g. a symbolic jump target is first checked to be
    -- in range, then resolved.
    pickSide :: App m => VM Symbolic -> VM Concrete -> Session Symbolic -> m (Either String (Session Symbolic, Int, Int))
    pickSide start vc ss0 = do
      (found, tried) <- search ss0 (6 :: Int) []
      pure $ maybe (Left (failure tried)) Right found
      where
        failure tried = "no sides of the branches reach the concrete pc " <> show vc.state.pc
          <> " at depth " <> show (length vc.frames) <> ", the sides lead to:\n" <> unlines (reverse tried)
        pathOk s = concretizeProps c c.inputs (sessionVM s).constraints /= Just False
        -- or the side gives up on this path: incomplete, but not wrong
        unfinished s = case (sessionVM s).result of
          Just (Unfinished _) -> True
          _ -> False
        reached s = (sessionVM s).state.pc == vc.state.pc && length (sessionVM s).frames == length vc.frames
        describe path s = "  " <> path <> ": pc " <> show (sessionVM s).state.pc <> ", depth " <> show (length (sessionVM s).frames)
          <> ", result " <> show (sessionVM s).result
          <> ", inputs satisfy the path conditions: " <> show (concretizeProps c c.inputs (sessionVM s).constraints)
          <> "\n    violated: " <> show [ p | p <- (sessionVM s).constraints, concretizeProps c c.inputs [p] == Just False ]
        search s fuel tried
          | fuel == 0 = pure (Nothing, describe "out of fuel" s : tried)
          | hasPendingBranch s = do
              v <- liftIO $ mkView s
              let opts = maybe [] (.options) v.branch
                  sides = if opts == ["false", "true"] then ["true", "false"] else map (T.pack . show) [0 .. length opts - 1]
                  tryEach _ [] tr = pure (Nothing, tr)
                  tryEach n (side : rest) tr = do
                    s1 <- runCommand fetcher (Choose side) s
                    (found, tr') <- search s1 (fuel - 1) tr
                    case found of
                      Just (s2, t, took) -> pure (Just (s2, t + n, took + 1), tr')
                      Nothing -> tryEach (n + 1) rest (describe (show (opts, side)) s1 : tr')
              tryEach 0 sides tried
          | not (pathOk s) = pure (Nothing, describe "the inputs violate the path conditions" s : tried)
          | unfinished s || reached s = pure (Just (s, 0, 0), tried)
          | midInstruction start (sessionVM s) = runCommand fetcher (Step 1) s >>= \s' -> search s' (fuel - 1) tried
          | otherwise = pure (Nothing, describe "elsewhere" s : tried)
    getOpW8' vm = case vm.state.code of
      RuntimeCode (ConcreteRuntimeCode bs) | vm.state.pc < BS.length bs -> BS.index bs vm.state.pc
      InitCode bs _ | vm.state.pc < BS.length bs -> BS.index bs vm.state.pc
      _ -> 0

-- | Why a symbolic run gave up, briefly
unfinishedReason :: PartialExec -> String
unfinishedReason = \case
  UnexpectedSymbolicArg { opcode, msg } -> opcode <> ": " <> msg
  p -> takeWhile (/= ' ') (show p)

-- | Where a run halted, and how
endOf :: VM t -> (Int, Int, String)
endOf vm = (vm.state.pc, length vm.frames, case vm.result of
  Just (VMSuccess _) -> "success"
  Just (VMFailure (Revert _)) -> "revert"
  Just (VMFailure e) -> hevmErrorKind e
  r -> show r)

-- | Follows a random path of a symbolic session, picking a random feasible side
-- at every branch, until it halts
randomPath :: App m => SolverGroup -> TestCase -> [Int] -> m (Session Symbolic)
randomPath solvers c picks0 = do
  s0 <- liftIO $ stToIO (symbolicTestVm c) >>= newSession emptyDapp
  go s0 (cycle (0 : picks0)) (0 :: Int)
  where
    fetcher :: Fetch.Fetcher Symbolic m
    fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
    go s picks n
      | isHalted s || n >= maxLockstepSteps = pure s
      | hasPendingBranch s = do
          v <- liftIO $ mkView s
          let opts = maybe [] (.options) v.branch
              pick = fromMaybe 0 (headMay picks)
              side = if opts == ["false", "true"] then (["true", "false"] !! (pick `mod` 2))
                     else T.pack (show (pick `mod` max 1 (length opts)))
          s' <- runCommand fetcher (Choose side) s
          go s' (drop 1 picks) n
      | otherwise = runCommand fetcher (Step 1) s >>= \s' -> go s' picks (n + 1)

-- | Gas is not tracked symbolically, so after it ran out anywhere the runs may differ
gasDependentRun :: VM Concrete -> Bool
gasDependentRun vm = any isGas (concatMap flatten (traceForest vm)) || resultIsGas
  where
    isGas t = case t.tracedata of
      ErrorTrace e -> gasError e
      _ -> False
    resultIsGas = case vm.result of
      Just (VMFailure e) -> gasError e
      _ -> False
    -- memory this large costs more gas than any run has
    gasError e = "gas" `isInfixOf` hevmErrorKind e || case e of
      IllegalOverflow -> True
      _ -> False

-- | Ops that change balances, nonces, storage or code
accountOps :: [String]
accountOps = ["SSTORE", "TSTORE", "SELFDESTRUCT"] <> callOps

memWriters, callOps :: [String]
memWriters = ["MSTORE", "MSTORE8", "MCOPY", "CALLDATACOPY", "CODECOPY", "RETURNDATACOPY", "EXTCODECOPY"] <> callOps
callOps = ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "CREATE", "CREATE2"]

-- | Compares where the runs are, their stacks, and what the previous op may have
-- changed. Returns how many values matched and how many stayed symbolic.
-- | 'compareStates'' on the symbolic state as it is, and simplified: the
-- simplifier must not change what any value is
compareStates :: TestCase -> Maybe String -> VM Concrete -> VM Symbolic -> IO (Either String (Int, Int))
compareStates c prevOp vc vs = compareStates' id c prevOp vc vs >>= \case
  Left err -> pure (Left err)
  Right counts -> compareStates' Expr.simplify c prevOp vc vs <&> \case
    Left err -> Left ("only after Expr.simplify, " <> err)
    Right _ -> Right counts

compareStates' :: (forall a. Expr a -> Expr a) -> TestCase -> Maybe String -> VM Concrete -> VM Symbolic -> IO (Either String (Int, Int))
compareStates' pre c prevOp vc vs
  | vc.state.pc /= vs.state.pc = pure $ Left $ "pc differs: symbolic " <> show vs.state.pc
  | length vc.frames /= length vs.frames = pure $ Left $ "depth differs: concrete " <> show (length vc.frames) <> ", symbolic " <> show (length vs.frames)
  | vc.state.codeContract /= vs.state.codeContract = pure $ Left $ "code address differs: " <> show (vc.state.codeContract, vs.state.codeContract)
  | length vc.state.stack /= length vs.state.stack = pure $ Left $ "stack heights differ: " <> show (length vc.state.stack, length vs.state.stack)
  | otherwise = do
      let words' = zip3 [0 :: Int ..] vc.state.stack (map (concretize c c.inputs . pre) vs.state.stack)
          badWords = [ (i, a, b) | (i, a@(Lit _), b@(Lit _)) <- words', a /= b ]
          nWords = length [ () | (_, Lit _, Lit _) <- words' ]
      mem <- if maybe True (`elem` memWriters) prevOp then compareMemory pre c vc vs else pure (Right 0)
      let ret = if maybe False (`elem` callOps) prevOp then compareBufs "return data" c vc.state.returndata (pre vs.state.returndata) else Right 0
          store = if maybe False (`elem` accountOps) prevOp then compareStorage pre c vc vs else Right 0
      pure $ case badWords of
        (i, a, b) : _ -> Left $ "stack word " <> show i <> " differs: concrete " <> show a <> ", symbolic " <> show b
          <> "\nsymbolic, before substituting: " <> show (pre (vs.state.stack !! i))
        [] -> (\m r st -> (nWords + m + r + st, length words' - nWords)) <$> mem <*> ret <*> store

compareMemory :: (forall a. Expr a -> Expr a) -> TestCase -> VM Concrete -> VM Symbolic -> IO (Either String Int)
compareMemory pre c vc vs = do
  mc <- memoryBytes id vc.state.memory
  ms <- memoryBytes pre vs.state.memory
  let size = fromIntegral vc.state.memorySize
      symSize = maybe (Just (fromIntegral vs.state.memorySize)) (fmap fromIntegral . Expr.maybeLitWordSimp . concretize c c.inputs) vs.state.symMemorySize
  pure $ case (mc, ms) of
    _ | Just size /= symSize && isJust symSize -> Left $ "memory sizes differ: concrete " <> show size <> ", symbolic " <> show symSize
    (Just a, Just b) | pad size a /= pad size b ->
      Left $ "memory differs:\nconcrete: " <> bsToHex (pad size a) <> "\nsymbolic: " <> bsToHex (pad size b)
    (Just _, Just _) -> Right 1
    _ -> Right 0
  where
    pad n b = BS.take n (b <> BS.replicate n 0)
    memoryBytes :: (Expr Buf -> Expr Buf) -> Memory -> IO (Maybe ByteString)
    memoryBytes f = \case
      ConcreteMemory m -> Just . BS.pack . VS.toList <$> stToIO (VS.freeze m)
      SymbolicMemory b -> pure $ case concretize c c.inputs (f b) of
        ConcreteBuf bs -> Just bs
        _ -> Nothing

compareBufs :: String -> TestCase -> Expr Buf -> Expr Buf -> Either String Int
compareBufs what c a b = case (concretize c c.inputs a, concretize c c.inputs b) of
  (ConcreteBuf x, ConcreteBuf y) | x /= y -> Left $ what <> " differs: concrete " <> bsToHex x <> ", symbolic " <> bsToHex y
                                 | otherwise -> Right 1
  _ -> Right 0

-- | Balances, nonces, storage, transient storage and code of the accounts both
-- runs have
compareStorage :: (forall a. Expr a -> Expr a) -> TestCase -> VM Concrete -> VM Symbolic -> Either String Int
compareStorage pre c vc vs = sum <$> forM common (\(a, cc, sc) -> do
  let what :: String -> String
      what x = x <> " of " <> show a <> " differs: concrete "
      conc :: Expr b -> Expr b
      conc = concretize c c.inputs . pre
      stores :: String -> Expr Storage -> Expr Storage -> Either String Int
      stores name x y = case (x, conc y) of
        (ConcreteStore m, ConcreteStore m')
          | nonZero m /= nonZero m' -> Left $ what name <> show m <> ", symbolic " <> show m'
          | otherwise -> Right 1
        _ -> Right 0
  balance <- case (cc.balance, conc sc.balance) of
    -- they pay for and are paid the gas, which is not tracked symbolically
    _ | a `elem` [fromAddress, coinbaseAddr] -> Right 0
    (Lit x, Lit y) | x /= y -> Left $ what "balance" <> show x <> ", symbolic " <> show y
                   | otherwise -> Right 1
    _ -> Right 0
  nonce <- if cc.nonce /= sc.nonce then Left $ what "nonce" <> show cc.nonce <> ", symbolic " <> show sc.nonce else Right 1
  code <- case (cc.code, sc.code) of
    (RuntimeCode (ConcreteRuntimeCode x), RuntimeCode (ConcreteRuntimeCode y))
      | x /= y -> Left $ what "code" <> bsToHex x <> ", symbolic " <> bsToHex y
      | otherwise -> Right 1
    _ -> Right 0
  st <- stores "storage" cc.storage sc.storage
  tst <- stores "transient storage" cc.tStorage sc.tStorage
  pure (balance + nonce + code + st + tst))
  where
    common = [ (a, cc, sc) | (LitAddr a, cc) <- Map.toList vc.env.contracts, Just sc <- [Map.lookup (LitAddr a) vs.env.contracts] ]

-- | Both runs halted: the same way, with the same output, logs and storage
compareEnds :: TestCase -> VM Concrete -> VM Symbolic -> Either String ()
compareEnds c vc vs = do
  case (vc.result, vs.result) of
    (Just (VMSuccess a), Just (VMSuccess b)) -> do
      void $ compareBufs "output" c a b
      void $ compareBufs "output, simplified" c a (Expr.simplify b)
    (Just (VMFailure (Revert a)), Just (VMFailure (Revert b))) -> do
      void $ compareBufs "revert data" c a b
      void $ compareBufs "revert data, simplified" c a (Expr.simplify b)
    (Just (VMFailure a), Just (VMFailure b)) | hevmErrorKind a == hevmErrorKind b -> pure ()
    (a, b) -> Left $ "the runs ended differently: concrete " <> show a <> ", symbolic " <> show b
  let logs = map (concretize c c.inputs) vs.logs
  when (all concreteLog logs && logs /= vc.logs) $ Left $ "logs differ: concrete " <> show vc.logs <> ", symbolic " <> show logs
  void $ compareStorage id c vc vs
  void $ compareStorage Expr.simplify c vc vs
  where
    concreteLog = \case
      LogEntry (WAddr (LitAddr _)) (ConcreteBuf _) ts -> all (isJust . Expr.maybeLitWordSimp) ts
      _ -> False

-- | Lockstep along a random path: the inputs a model of its path conditions
-- gives must take the concrete run along it, to where it ended
modelGuided :: App m => SolverGroup -> BranchMode -> TestCase -> [Int] -> m Property
modelGuided solvers mode c picks = Progress.withProgressLogFromEnv "model-guided" $ do
  sp <- randomPath solvers c picks
  let vs = sessionVM sp
      skip why = pure $ label why (property True)
  case vs.result of
    Nothing -> skip "random path too long"
    Just (Unfinished _) -> skip "random path unfinished"
    _ | any mentionsBlockHash vs.constraints -> skip "path conditions on a symbolic blockhash"
      | PBool False `elem` vs.constraints -> skip "path ends in a failed assumption"
      | otherwise -> checkSatWithProps solvers vs.constraints >>= \case
          Qed -> liftIO $ failWith c c.inputs $ "the random path offered only feasible sides, but is infeasible:\n"
                   <> unlines (map show vs.constraints)
          Unknown _ -> skip "unknown"
          Error e -> skip ("solver error: " <> take 40 e)
          Cex cex -> case modelInputs c.inputs cex of
            Left e -> skip ("model: " <> takeWhile (/= ':') e)
            Right i -> do
              let c' = c { inputs = i }
              lockstepCase solvers mode False c' >>= \case
                Left err -> liftIO $ failWith c' i err
                Right l -> case l.ended of
                  -- the solver may pick any hash of symbolic data, which the concrete run does not get
                  Just e | e /= endOf vs, any mentionsSymbolicKeccak vs.constraints -> skip "model via symbolic keccak"
                  Just e | e /= endOf vs -> liftIO $ failWith c' i $
                    "the inputs from a model of the path conditions end at " <> show e
                    <> ", the path ends at " <> show (endOf vs) <> "\npath conditions:\n" <> unlines (map show vs.constraints)
                  Just _ -> pure $ label "followed the path" (property True)
                  Nothing -> skip l.stopped
  where
    mentionsBlockHash = getAny . foldProp (\case BlockHash _ -> Any True; _ -> Any False) mempty
    mentionsSymbolicKeccak = getAny . foldProp (\case
      Keccak (ConcreteBuf _) -> Any False
      Keccak _ -> Any True
      _ -> Any False) mempty

lockstepTests :: TestTree
lockstepTests = testGroup "lockstep-fuzz"
  [ -- the case from HEVM_FUZZ_* with HEVM_FUZZ_PICKS and HEVM_FUZZ_MODE, that model-guided-lockstep prints
    test "model-guided-from-env" $ liftIO caseFromEnv >>= mapM_ (\c -> do
      picks <- liftIO $ maybe [] (map read . splitOn' ',') <$> lookupEnv "HEVM_FUZZ_PICKS"
      mode <- liftIO $ maybe SolverBranches modeOf <$> lookupEnv "HEVM_FUZZ_MODE"
      -- failures are raised; what is returned only labels the case
      void $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> modelGuided solvers mode c picks)
  , testProperty "model-guided-lockstep" $ \(c :: TestCase) -> forAll (vectorOf 50 (chooseInt (0, 7))) $ \picks ->
      forAll (elements [SolverBranches, ExplorerBranches, CheckedBranches]) $ \mode ->
      within 300_000_000 $ ioProperty $ runEnv testEnv $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
        liftIO $ writeCaseFile "model-guided-lockstep" $ show c <> "\nreproduce with: " <> reproduction c c.inputs
          <> " HEVM_FUZZ_PICKS=" <> intercalate "," (map show picks) <> " HEVM_FUZZ_MODE=" <> show mode
        modelGuided solvers mode c picks
  , -- the case from the HEVM_FUZZ_* variables that a failure prints, in every branch mode
    test "lockstep-from-env" $ liftIO caseFromEnv >>= mapM_ (\c ->
      withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> forM_ [(m, g) | m <- [SolverBranches, ExplorerBranches, CheckedBranches], g <- [False, True]] $ \(mode, merging) ->
        lockstepCase solvers mode merging c >>= \case
          Left err -> liftIO $ failWith c c.inputs (show mode <> (if merging then ", merging" else "") <> ": " <> err)
          Right r -> liftIO $ putStrLn $ show mode <> (if merging then ", merging" else "") <> ": " <> r.stopped <> " after " <> show r.steps <> " steps, "
                       <> show r.compared <> " values compared")
  , testProperty "symbolic-lockstep" $ \(c :: TestCase) -> forAll (elements [SolverBranches, ExplorerBranches, CheckedBranches]) $ \mode -> \merging ->
      within 300_000_000 $ ioProperty $ runEnv testEnv $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
        -- to find a case that crashes, hangs or runs out of memory
        liftIO $ writeCaseFile "symbolic-lockstep" $ show c <> "\nmode: " <> show mode <> ", merging: " <> show merging
          <> "\nreproduce with: " <> reproduction c c.inputs
        lockstepCase solvers mode merging c >>= \case
          Left err -> liftIO $ failWith c c.inputs err
          Right r -> pure $ tabulate "stopped" [r.stopped]
                          $ tabulate "merged branches" [bucket r.merges | merging]
                          $ tabulate "opcodes compared after, in cases" (Set.toList r.ops)
                          $ tabulate "branch mode" [show mode]
                          $ tabulate "decided by simplification" [bucket (fst r.static)]
                          $ tabulate "only the solver could decide" [bucket (snd r.static)]
                          $ tabulate "steps" [bucket r.steps]
                          $ tabulate "branches taken" [bucket r.branches]
                          $ tabulate "sides retried" [bucket r.retries]
                          $ tabulate "values compared" [bucket r.compared]
                          $ tabulate "stack words left symbolic" [bucket r.opaque] (property True)
  ]
  where
    bucket :: Int -> String
    bucket n | n == 0 = "0" | n < 10 = "1-9" | n < 100 = "10-99" | n < 1000 = "100-999" | otherwise = ">=1000"

testEnv :: Env
testEnv = Env { config = defaultConfig }

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv testEnv b

-- | A hand-written program as a 'TestCase' with the given calldata
fixedCase :: [Item] -> ByteString -> TestCase
fixedCase items cd = TestCase (Prog items []) (Inputs cd mempty 0 1000) 40000 0

pushOps :: [W256] -> [Item]
pushOps = map (\v -> IPush 32 v)

tests :: TestTree
tests = testGroup "contract-quickcheck-run"
    [ withResource (newIORef mempty) printCoverage $ \cov ->
      testProperty "random-contract-concrete-call" $ \(c :: TestCase, hashCons :: Bool) ->
      -- the flag is process-wide, so concurrent tests may flip it mid-run; results must not change either way
      within 120_000_000 $ ioProperty $ runEnv (Env { config = defaultConfig { hashConsExplore = hashCons } }) $ do
        -- to find a case that crashes or runs out of memory
        liftIO $ writeCaseFile "random-contract-concrete-call" $ show c
          <> "\nmain: " <> bsToHex (assembleItems c.prog.main) <> "\ncallee: " <> bsToHex (assembleItems c.prog.callee)
        t0 <- liftIO getMonotonicTime
        report <- checkCase 3 c
        t1 <- liftIO getMonotonicTime
        liftIO $ addCoverage cov report
        let secs = t1 - t0
            time | secs < 1 = "<1s" | secs < 5 = "1-5s" | secs < 20 = "5-20s" | otherwise = ">20s"
            tables = Map.fromListWith (flip (<>)) [(t, [l]) | (t, l) <- ("case time", time) : report.tables]
        pure $ foldr (uncurry tabulate) (property True) (Map.toList tables)
      -- runs only the symbolic phase on the bytecode in HEVM_FUZZ_MAIN and HEVM_FUZZ_CALLEE, to minimize crashes
      , test "symbolic-from-env" $ liftIO (lookupEnv "HEVM_FUZZ_MAIN") >>= mapM_ (\m -> do
          cl <- fromMaybe "" <$> liftIO (lookupEnv "HEVM_FUZZ_CALLEE")
          let hex = fromJust . hexByteString . Char8.pack
              c = TestCase (Prog [IRaw (hex m)] [IRaw (hex cl)]) (Inputs mempty mempty 0 1) 300000 1
          r <- withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> runSymbolic solvers c
          liftIO $ putStrLn $ "symbolic leaves: " <> show (length . fst <$> r))
      , after AllFinish "random-contract-concrete-call" $ test "symbolic-jump-calldata-length" $ do
        _ <- checkCase 0 (fixedCase [IOp OpCalldatasize, IOp OpJump] (BS.replicate 5 0))
        pure ()
      , after AllFinish "random-contract-concrete-call" $ test "calldata-wraparound-1" $ do
        let items = concat
              [ pushOps [0xff, 31] <> [IOp OpMstore8] -- value, offs
              , pushOps [0x3, maxBound, 0x0] <> [IOp OpCalldatacopy] -- size, offs, destOffs
              , pushOps [0x20, 0] <> [IOp OpReturn] -- datasize, offs
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5]))
        pure ()
      , after AllFinish "calldata-wraparound-1" $ test "calldata-wraparound-2" $ do
        let items = concat
              [ pushOps [0xff, 0] <> [IOp OpMstore8]
              , pushOps [0x10, maxBound, 0x0] <> [IOp OpCalldatacopy]
              , pushOps [0x20, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5]))
        pure ()
      , after AllFinish "calldata-wraparound-2" $ test "codecopy-symbolic-offset-wraparound" $ do
        let items = concat
              [ pushOps [4] <> [IOp OpCallvalue, IOp OpNot] <> pushOps [6] <> [IOp OpCodecopy] -- size, ~callvalue, destOffs
              , pushOps [0x60, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items mempty)
        pure ()
      , after AllFinish "codecopy-symbolic-offset-wraparound" $ test "calldata-overwrite-with-0-if-oversized" $ do
        -- supposed to copy 1...6 and then 0s, overwriting the 0xff with 0
        let items = concat
              [ pushOps [0xff, 1] <> [IOp OpMstore8]
              , pushOps [10, 0, 0] <> [IOp OpCalldatacopy]
              , pushOps [10, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5, 6]))
        pure ()
      , after AllFinish "calldata-overwrite-with-0-if-oversized" $ test "calldata-overwrite-correct-size" $ do
        let items = concat
              [ pushOps [0xff, 8] <> [IOp OpMstore8]
              , pushOps [10, 0, 0] <> [IOp OpCalldatacopy]
              , pushOps [10, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5, 6]))
        pure ()
      , after AllFinish "calldata-overwrite-correct-size" $ test "reverted-call-drops-logs" $ do
        let callee = pushOps [0, 0] <> [IOp (OpLog 0)] <> pushOps [0, 0] <> [IOp OpRevert]
            items = pushOps [0, 0, 0, 0, 0, into calleeAddr, 0xffffff] <> [IOp OpCall]
              <> pushOps [0, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items mempty) { prog = Prog items callee }
        pure ()
      , after AllFinish "reverted-call-drops-logs" $ test "precompile-copies-only-its-output" $ do
        -- ripemd160 returns 32 bytes, so the second word of the return buffer is kept
        let items = pushOps [maxBound, 0x20] <> [IOp OpMstore]
              <> pushOps [0x40, 0, 0x20, 0, 0, 3, 0xffffff] <> [IOp OpCall]
              <> pushOps [0x40, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items mempty)
        pure ()
      , after AllFinish "precompile-copies-only-its-output" $ test "failed-precompile-clears-returndata" $ do
        let callee = pushOps [0x40, 0] <> [IOp OpRevert]
            items = pushOps [0, 0, 0, 0, 0, into calleeAddr, 0xffffff] <> [IOp OpCall]
              -- ecPairing fails on input that is not a multiple of 192 bytes
              <> pushOps [0, 0, 0x80, 0, 0, 8, 0xffffff] <> [IOp OpCall]
              <> [IOp OpReturndatasize] <> pushOps [0] <> [IOp OpMstore]
              <> pushOps [0x20, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items mempty) { prog = Prog items callee }
        pure ()
      , after AllFinish "failed-precompile-clears-returndata" $ test "msize-after-symbolic-access" $ do
        -- the LOG0 expands memory at an offset from calldata
        let items = pushOps [1, 4] <> [IOp OpCalldataload, IOp (OpLog 0), IOp OpMsize]
              <> pushOps [0] <> [IOp OpMstore] <> pushOps [0x20, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items (BS.replicate 36 0))
        pure ()
      , after AllFinish "msize-after-symbolic-access" $ test "calldata-offset-copy" $ do
        let items = concat
              [ pushOps [0xff, 8] <> [IOp OpMstore8]
              , pushOps [0xff, 1] <> [IOp OpMstore8]
              , pushOps [10, 4, 0] <> [IOp OpCalldatacopy]
              , pushOps [10, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5, 6]))
        pure ()
    ]
