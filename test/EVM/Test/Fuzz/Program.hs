-- | Random programs, the accounts around them, and their assembly
module EVM.Test.Fuzz.Program
  ( Inputs(..), Item(..), Prog(..), TestCase(..), accountTargets, assembleItems
  , calleeAddr, codeOps, coinbaseAddr, contractAddr, contractBalance, createInitCode
  , extraAccounts, genOps, opPops, opTable, sizedInitCode
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word8)
import Witch (into, unsafeInto)
import EVM.Assembler (assemble)
import EVM.Concrete qualified as Concrete
import EVM.Op (intToOpName)
import EVM.Types hiding (Env)

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

coinbaseAddr :: Addr
coinbaseAddr = 0xff


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
