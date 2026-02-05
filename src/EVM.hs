{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TemplateHaskell #-}

module EVM where

import Prelude hiding (exponent, Foldable(..))

import Optics.Core
import Optics.State
import Optics.State.Operators
import Optics.Zoom

import EVM.ABI
import EVM.Expr (readStorage, concStoreContains, writeStorage, readByte, readWord, writeWord,
  writeByte, bufLength, indexWord, readBytes, copySlice, wordToAddr, maybeLitByteSimp, maybeLitWordSimp, maybeLitAddrSimp)
import EVM.Expr qualified as Expr
import EVM.FeeSchedule (FeeSchedule (..))
import EVM.FeeSchedule qualified as Fees (feeSchedule)
import EVM.Op
import EVM.Precompiled qualified
import EVM.Solidity
import EVM.Types
import EVM.Types qualified as Expr (Expr(Gas))
import EVM.Sign qualified
import EVM.RLP (RLP(..), rlpencode)
import EVM.Concrete qualified as Concrete
import EVM.CheatsTH
import EVM.Effects (Config (..))

import Control.Monad (unless, when)
import Control.Monad.ST (ST, RealWorld)
import Control.Monad.State.Strict (MonadState, State, get, gets, lift, modify', put)
import Data.Bits (FiniteBits, countLeadingZeros, finiteBitSize, shiftR)
import Data.ByteArray qualified as BA
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Base16 qualified as BS16
import Data.ByteString.Lazy (fromStrict)
import Data.ByteString.Lazy qualified as LS
import Data.ByteString.Char8 qualified as Char8
import Data.DoubleWord (Int256, Word256)
import Data.Either (partitionEithers)
import Data.Either.Extra (maybeToEither)
import Data.Foldable (toList, Foldable(..))
import Data.List (find, isPrefixOf)
import Data.List.Split (splitOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, fromJust, isJust, isNothing, mapMaybe)
import Data.Set (insert, member, fromList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (unpack, pack)
import Data.Text.Encoding (decodeUtf8)
import Data.Tree
import Data.Tree.Zipper qualified as Zipper
import Data.Typeable
import Data.Vector qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VS.Mutable
import Data.Vector.Storable.ByteString (vectorToByteString, byteStringToVector)
import Data.Word (Word8, Word64)
import Text.Read (readMaybe)
import Witch (into, tryFrom, unsafeInto, tryInto)

import Crypto.Hash (Digest, SHA256, RIPEMD160)
import Crypto.Hash qualified as Crypto
import Crypto.Number.ModArithmetic (expFast, inverse)
import Crypto.PubKey.ECC.Prim (pointAddTwoMuls, isPointValid)
import Crypto.PubKey.ECC.Types (getCurveByName, CurveName(..), Point(..), Curve(..), CurveCommon(..), CurvePrime(..))

defaultVMOpts :: VMOps t => VMOpts t
defaultVMOpts = VMOpts
  { contract       = emptyContract
  , otherContracts = []
  , calldata       = mempty
  , value          = Lit 0
  , address        = LitAddr 0xacab
  , caller         = LitAddr 0
  , origin         = LitAddr 0
  , gas            = toGas maxBound
  , gaslimit       = maxBound
  , baseFee        = 0
  , priorityFee    = 0
  , coinbase       = LitAddr 0
  , number         = Lit 0
  , timestamp      = Lit 0
  , blockGaslimit  = maxBound
  , gasprice       = 0
  , maxCodeSize    = 0xffffffff
  , prevRandao     = 0
  , schedule       = Fees.feeSchedule
  , chainId        = 1
  , create         = False
  , baseState      = EmptyBase
  , txAccessList   = mempty
  , allowFFI       = False
  , freshAddresses = 0
  , beaconRoot     = 0
  , parentHash     = 0
  , txdataFloorGas = 0
  , authorizationList = []
  }

blankState :: VMOps t => ST RealWorld (FrameState t)
blankState = do
  memory <- ConcreteMemory <$> VS.Mutable.new 0
  pure $ FrameState
    { contract     = LitAddr 0
    , codeContract = LitAddr 0
    , code         = RuntimeCode (ConcreteRuntimeCode "")
    , pc           = 0
    , stack        = mempty
    , memory
    , memorySize   = 0
    , calldata     = mempty
    , callvalue    = Lit 0
    , caller       = LitAddr 0
    , gas          = initialGas
    , returndata   = mempty
    , static       = False
    , overrideCaller = Nothing
    , resetCaller  = False
    }

-- | An "external" view of a contract's bytecode, appropriate for
-- e.g. @EXTCODEHASH@.
bytecode :: Getter Contract (Maybe (Expr Buf))
bytecode = #code % to f
  where f (InitCode _ _) = Just mempty
        f (RuntimeCode (ConcreteRuntimeCode bs)) = Just $ ConcreteBuf bs
        f (RuntimeCode (SymbolicRuntimeCode ops)) = Just $ Expr.fromList ops
        f (UnknownCode _) = Nothing

-- * Data accessors

currentContract :: VM t -> Maybe Contract
currentContract vm =
  Map.lookup vm.state.codeContract vm.env.contracts

-- * Data constructors
--
makeVm :: VMOps t => VMOpts t -> ST RealWorld (VM t)
makeVm o = do
  let txaccessList = o.txAccessList
      txorigin = o.origin
      txtoAddr = o.address
      -- EIP-7702: Authority addresses are warmed after chain_id validation
      authWarmAddrs = getAuthoritiesToWarm o.chainId o.authorizationList
      -- EIP-7702: Delegation targets are warmed for valid authorizations (included in authDelegationTargets)
      initialAccessedAddrs = fromList $
           [txorigin, txtoAddr, o.coinbase]
        ++ (fmap LitAddr [1..9])          -- Legacy precompiles (ECRECOVER, SHA256, etc.)
        ++ (fmap LitAddr [0x0A..0x11])    -- EIP-4844 Point Evaluation + BLS12-381 precompiles
        ++ [LitAddr 0x100]                -- EIP-7951 P256VERIFY
        ++ (Map.keys txaccessList)
        ++ authWarmAddrs                  -- EIP-7702: Warmed authority addresses
        ++ authDelegationTargets          -- EIP-7702: Warmed delegation targets (for valid authorizations)
      initialAccessedStorageKeys = fromList $ foldMap (uncurry (map . (,))) (Map.toList txaccessList)
      touched = if o.create then [txorigin] else [txorigin, txtoAddr]
  memory <- ConcreteMemory <$> VS.Mutable.new 0
  pure $ setEIP2935Storage o $ setEIP4788Storage o $ VM
    { result = Nothing
    , frames = mempty
    , tx = TxState
      { gasprice = o.gasprice
      , gaslimit = o.gaslimit
      , priorityFee = o.priorityFee
      , origin = txorigin
      , toAddr = txtoAddr
      , value = o.value
      , subState = SubState mempty touched initialAccessedAddrs initialAccessedStorageKeys authRefunds mempty
      , isCreate = o.create
      , txReversion = Map.fromList ((o.address,o.contract):o.otherContracts)
      , txdataFloorGas = o.txdataFloorGas
      , authorizationRefunds = authRefunds  -- EIP-7702: preserved on revert
      }
    , logs = []
    , traces = Zipper.fromForest []
    , block = block
    , state = FrameState
      { pc = 0
      , stack = mempty
      , memory
      , memorySize = 0
      , code = o.contract.code
      , contract = o.address
      , codeContract = o.address
      , calldata = fst o.calldata
      , callvalue = o.value
      , caller = o.caller
      , gas = o.gas
      , returndata = mempty
      , static = False
      , overrideCaller = Nothing
      , resetCaller = False
      }
    , env = env
    , burned = initialGas
    , constraints = snd o.calldata
    , iterations = mempty
    , config = RuntimeConfig
      { allowFFI = o.allowFFI
      , baseState = o.baseState
      }
    , forks = Seq.singleton (ForkState env block mempty "")
    , currentFork = 0
    , labels = mempty
    , osEnv = mempty
    , freshVar = 0
    , exploreDepth = 0
    , keccakPreImgs = fromList []
    , pathsVisited = mempty
    }
    where
    -- Process EIP-7702 authorization list to set delegation codes, collect refunds, and get addresses to warm
    baseContracts = Map.fromList ((o.address,o.contract):o.otherContracts)
    (contractsWithDelegations, authRefunds, authDelegationTargets) = processAuthorizations o.chainId o.origin o.authorizationList baseContracts
    env = Env
      { chainId = o.chainId
      , contracts = contractsWithDelegations
      , freshAddresses = o.freshAddresses
      , freshGasVals = 0
      }
    block = Block
      { coinbase = o.coinbase
      , timestamp = o.timestamp
      , number = o.number
      , prevRandao = o.prevRandao
      , maxCodeSize = o.maxCodeSize
      , gaslimit = o.blockGaslimit
      , baseFee = o.baseFee
      , schedule = o.schedule
      }

-- https://eips.ethereum.org/EIPS/eip-4788
setEIP4788Storage :: VMOpts t -> VM t -> VM t
setEIP4788Storage o vm = do
  let beaconRootsAddress = LitAddr 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
  case Map.lookup beaconRootsAddress vm.env.contracts of
    Just beaconRootsContract -> do
      -- https://eips.ethereum.org/EIPS/eip-4788#pseudocode
      -- https://eips.ethereum.org/EIPS/eip-4788#block-processing
      -- > Clients may decide to omit an explicit EVM call and directly set the
      -- > storage values. Note: While this is a valid optimization for Ethereum
      -- > mainnet, it could be problematic on non-mainnet situations in case
      -- > a different contract is used.
      let
        historyBufferLength = 8191
        timestampIdx = Expr.mod o.timestamp (Lit historyBufferLength)
        rootIdx = Expr.add timestampIdx (Lit historyBufferLength)
        storage =
          Expr.writeStorage timestampIdx o.timestamp .
          Expr.writeStorage rootIdx (Lit o.beaconRoot) $
          beaconRootsContract.storage
      vm {
        env = vm.env {
          contracts = Map.insert beaconRootsAddress
                                 (beaconRootsContract { storage } :: Contract)
                                 vm.env.contracts
        }
      }
    Nothing -> vm

-- https://eips.ethereum.org/EIPS/eip-2935
setEIP2935Storage :: VMOpts t -> VM t -> VM t
setEIP2935Storage o vm = do
  let historyStorageAddress = LitAddr 0x0000F90827F1C53a10cb7A02335B175320002935
  case Map.lookup historyStorageAddress vm.env.contracts of
    Just historyContract -> do
      let
        historyBufferLength = 8191
        slotIdx = Expr.mod (Expr.sub o.number (Lit 1)) (Lit historyBufferLength)
        storage = Expr.writeStorage slotIdx (Lit o.parentHash) historyContract.storage
      vm {
        env = vm.env {
          contracts = Map.insert historyStorageAddress
                                 (historyContract { storage } :: Contract)
                                 vm.env.contracts
        }
      }
    Nothing -> vm

-- | Initialize an abstract contract with unknown code
unknownContract :: Expr EAddr -> Contract
unknownContract addr = Contract
  { code        = UnknownCode addr
  , storage     = AbstractStore addr Nothing
  , tStorage    = AbstractStore addr Nothing
  , origStorage = AbstractStore addr Nothing
  , balance     = Balance addr
  , nonce       = Nothing
  , codehash    = hashcode (UnknownCode addr)
  , opIxMap     = mempty
  , codeOps     = mempty
  , external    = False
  }

-- | Initialize an abstract contract with known code
abstractContract :: ContractCode -> Expr EAddr -> Contract
abstractContract code addr = Contract
  { code        = code
  , storage     = AbstractStore addr Nothing
  , tStorage    = AbstractStore addr Nothing
  , origStorage = AbstractStore addr Nothing
  , balance     = Balance addr
  , nonce       = if isCreation code then Just 1 else Just 0
  , codehash    = hashcode code
  , opIxMap     = mkOpIxMap code
  , codeOps     = mkCodeOps code
  , external    = False
  }

-- | Initialize an empty contract without code
emptyContract :: Contract
emptyContract = initialContract (RuntimeCode (ConcreteRuntimeCode ""))

-- | Initialize empty contract with given code
initialContract :: ContractCode -> Contract
initialContract code = Contract
  { code        = code
  , storage     = ConcreteStore mempty
  , tStorage    = ConcreteStore mempty
  , origStorage = ConcreteStore mempty
  , balance     = Lit 0
  , nonce       = if isCreation code then Just 1 else Just 0
  , codehash    = hashcode code
  , opIxMap     = mkOpIxMap code
  , codeOps     = mkCodeOps code
  , external    = False
  }

isCreation :: ContractCode -> Bool
isCreation = \case
  InitCode _ _  -> True
  RuntimeCode _ -> False
  UnknownCode _ -> False

-- * Opcode dispatch (exec1)

-- | Update program counter
next :: (?op :: Word8) => EVM t ()
next = modifying' (#state % #pc) (+ (opSize ?op))

getOpW8 :: forall (t :: VMType) . FrameState t -> Word8
getOpW8 state = case state.code of
      UnknownCode _ -> internalError "Cannot execute unknown code"
      InitCode conc _ -> BS.index conc state.pc
      RuntimeCode (ConcreteRuntimeCode bs) -> BS.index bs state.pc
      RuntimeCode (SymbolicRuntimeCode ops) ->
        fromMaybe (internalError "could not analyze symbolic code") $
          maybeLitByteSimp $ ops V.! state.pc

getOpName :: forall (t :: VMType) . FrameState t -> [Char]
getOpName state = intToOpName $ fromEnum $ getOpW8 state

-- | Executes the EVM one step
exec1 :: forall (t :: VMType). (VMOps t, Typeable t) => Config ->  EVM t ()
exec1 conf = do
  vm <- get

  let
    -- Convenient aliases
    stk  = vm.state.stack
    self = vm.state.contract
    this = fromMaybe (internalError "state contract") (Map.lookup self vm.env.contracts)
    fees@FeeSchedule {..} = vm.block.schedule
    doStop = finishFrame (FrameReturned mempty)
    litSelf = maybeLitAddrSimp self

  if isJust litSelf && isPrecompileAddr' (fromJust litSelf) then do
    -- call to precompile
    let ?op = 0x00 -- dummy value
    let calldatasize = bufLength vm.state.calldata
    copyBytesToMemory vm.state.calldata calldatasize (Lit 0) (Lit 0)
    executePrecompile (fromJust litSelf) vm.state.gas (Lit 0) calldatasize (Lit 0) (Lit 0) []
    vmx <- get
    case vmx.state.stack of
      x:_ -> case x of
        Lit 0 ->
          fetchAccount self $ \_ -> do
            touchAccount self
            vmError PrecompileFailure
        Lit _ ->
          fetchAccount self $ \_ -> do
            touchAccount self
            out <- use (#state % #returndata)
            finishFrame (FrameReturned out)
        e -> unexpectedSymArg "precompile returned a symbolic value" [e]
      _ ->
        underrun

  else if vm.state.pc >= opslen vm.state.code
    then doStop

    else do
      let ?conf = conf
      let ?op = getOpW8 vm.state
      case getOp (?op) of

        OpPush0 -> {-# SCC "OpPush0" #-} do
          limitStack 1 $
            burn g_base $ do
              next
              pushSym (Lit 0)

        OpPush n' -> {-# SCC "OpPushN" #-} do
          let n = into n'
              !xs = case vm.state.code of
                UnknownCode _ -> internalError "Cannot execute unknown code"
                InitCode conc _ -> Lit $ word $ padRight n $ BS.take n (BS.drop (1 + vm.state.pc) conc)
                RuntimeCode (ConcreteRuntimeCode bs) -> Lit $ word $ BS.take n $ BS.drop (1 + vm.state.pc) bs
                RuntimeCode (SymbolicRuntimeCode ops) ->
                  let bytes = V.take n $ V.drop (1 + vm.state.pc) ops
                  in readWord (Lit 0) $ Expr.fromList $ padLeft' 32 bytes
          limitStack 1 $
            burn g_verylow $ do
              next
              pushSym xs

        OpDup i -> {-# SCC "OpDup" #-}
          case preview (ix (into i - 1)) stk of
            Nothing -> underrun
            Just y ->
              limitStack 1 $
                burn g_verylow $ do
                  next
                  pushSym y

        OpSwap i -> {-# SCC "OpSwap" #-}
          case (stk ^? ix_i, stk ^? ix_0) of
            (Just ei, Just e0) ->
              burn g_verylow $ do
                next
                zoom (#state % #stack) $ do
                  ix_i .= e0
                  ix_0 .= ei
            _ -> underrun
          where
            (ix_i, ix_0) = (ix (into i), ix 0)

        OpLog n -> {-# SCC "OpLog" #-}
          notStatic $
          case stk of
            (xOffset:xSize:xs) ->
              if length xs < (into n)
              then underrun
              else do
                bytes <- readMemory xOffset xSize
                let (topics, xs') = splitAt (into n) xs
                    logs'         = (LogEntry (WAddr self) bytes topics) : vm.logs
                burnLog xSize n $
                  accessMemoryRange xOffset xSize $ do
                    traceTopLog logs'
                    next
                    assign' (#state % #stack) xs'
                    assign #logs logs'
            _ ->
              underrun

        OpStop -> {-# SCC "OpStop" #-} doStop

        OpAdd -> {-# SCC "OpAdd" #-} stackOp2 g_verylow Expr.add
        OpMul -> {-# SCC "OpMul" #-} stackOp2 g_low Expr.mul
        OpSub -> {-# SCC "OpSub" #-} stackOp2 g_verylow Expr.sub

        OpDiv -> {-# SCC "OpDiv" #-} stackOp2 g_low Expr.div

        OpSdiv -> {-# SCC "OpSdiv" #-} stackOp2 g_low Expr.sdiv

        OpMod -> {-# SCC "OpMod" #-} stackOp2 g_low Expr.mod

        OpSmod -> {-# SCC "OpSmod" #-} stackOp2 g_low Expr.smod
        OpAddmod -> {-# SCC "OpAddmod" #-} stackOp3 g_mid Expr.addmod
        OpMulmod -> {-# SCC "OpMulmod" #-} stackOp3 g_mid Expr.mulmod

        OpLt -> {-# SCC "OpLt" #-} stackOp2 g_verylow Expr.lt
        OpGt -> {-# SCC "OpGt" #-} stackOp2 g_verylow Expr.gt
        OpSlt -> {-# SCC "OpSlt" #-} stackOp2 g_verylow Expr.slt
        OpSgt -> {-# SCC "OpSgt" #-} stackOp2 g_verylow Expr.sgt

        OpEq -> {-# SCC "OpEq" #-} stackOp2 g_verylow Expr.eq
        OpIszero -> {-# SCC "OpIszero" #-} stackOp1 g_verylow Expr.iszero

        OpAnd -> {-# SCC "OpAnd" #-} stackOp2 g_verylow Expr.and
        OpOr -> {-# SCC "OpOr" #-} stackOp2 g_verylow Expr.or
        OpXor -> {-# SCC "OpXor" #-} stackOp2 g_verylow Expr.xor
        OpNot -> {-# SCC "OpNot" #-} stackOp1 g_verylow Expr.not

        OpByte -> {-# SCC "OpByte" #-} stackOp2 g_verylow (\i w -> Expr.padByte $ Expr.indexWord i w)

        OpShl -> {-# SCC "OpShl" #-} stackOp2 g_verylow Expr.shl
        OpShr -> {-# SCC "OpShr" #-} stackOp2 g_verylow Expr.shr
        OpSar -> {-# SCC "OpSar" #-} stackOp2 g_verylow Expr.sar
        OpClz -> {-# SCC "OpClz" #-} stackOp1 g_low Expr.clz

        -- more accurately referred to as KECCAK
        OpSha3 -> {-# SCC "OpSha3" #-}
          case stk of
            xOffset:xSize:xs ->
              burnSha3 xSize $
                accessMemoryRange xOffset xSize $ do
                  hash <- readMemory xOffset xSize >>= \case
                    orig@(ConcreteBuf bs) ->
                      whenSymbolicElse
                        (pure $ Keccak orig)
                        (do
                          let kc = keccak' bs
                          modifying #keccakPreImgs (insert (bs, kc))
                          pure $ Lit kc
                        )
                    buf -> pure $ Keccak buf
                  next
                  assign' (#state % #stack) (hash : xs)
            _ -> underrun

        OpAddress -> {-# SCC "OpAddress" #-}
          limitStack 1 $
            burn g_base (next >> pushAddr self)

        OpBalance -> {-# SCC "OpBalance" #-}
          case stk of
            x:xs -> forceAddr x (freshVarFallback xs) $ \a ->
              accessAndBurn a $
                fetchAccountWithFallback a (freshVarFallback xs) $ \c -> do
                  next
                  assign' (#state % #stack) xs
                  pushSym c.balance
            [] -> underrun

        OpOrigin -> {-# SCC "OpOrigin" #-}
          limitStack 1 . burn g_base $
            next >> pushAddr vm.tx.origin

        OpCaller -> {-# SCC "OpCaller" #-}
          limitStack 1 . burn g_base $
            next >> pushAddr vm.state.caller

        OpCallvalue -> {-# SCC "OpCallvalue" #-}
          limitStack 1 . burn g_base $
            next >> pushSym vm.state.callvalue

        OpCalldataload -> {-# SCC "OpCalldataload" #-} stackOp1 g_verylow $
          \ind -> Expr.readWord ind vm.state.calldata

        OpCalldatasize -> {-# SCC "OpCalldatasize" #-}
          limitStack 1 . burn g_base $
            next >> pushSym (bufLength vm.state.calldata)

        OpCalldatacopy -> {-# SCC "OpCalldatacopy" #-}
          case stk of
            xTo:xFrom:xSize:xs ->
              burnCalldatacopy xSize $
                accessMemoryRange xTo xSize $ do
                  next
                  assign' (#state % #stack) xs
                  copyBytesToMemory vm.state.calldata xSize xFrom xTo
            _ -> underrun

        OpCodesize -> {-# SCC "OpCodesize" #-}
          limitStack 1 . burn g_base $
            next >> pushSym (codelen vm.state.code)

        OpCodecopy -> {-# SCC "OpCodecopy" #-}
          case stk of
            memOffset:codeOffset:n:xs ->
              burnCodecopy n $ do
                accessMemoryRange memOffset n $ do
                  next
                  assign' (#state % #stack) xs
                  case toBuf vm.state.code of
                    Just b -> copyBytesToMemory b n codeOffset memOffset
                    Nothing -> internalError "Cannot produce a buffer from UnknownCode"
            _ -> underrun

        OpGasprice -> {-# SCC "OpGasprice" #-}
          limitStack 1 . burn g_base $
            next >> push vm.tx.gasprice

        OpExtcodesize -> {-# SCC "OpExtcodesize" #-}
          case stk of
            x':xs -> forceAddr x' (freshVarFallback xs) $ \x -> do
              let impl = accessAndBurn x $
                           fetchAccountWithFallback x (freshVarFallback xs) $ \c -> do
                             next
                             assign' (#state % #stack) xs
                             case view bytecode c of
                               Just b -> pushSym (bufLength b)
                               Nothing -> pushSym $ CodeSize x
              case x of
                a@(LitAddr _) -> if a == cheatCode
                  then do
                    next
                    assign' (#state % #stack) xs
                    pushSym (Lit 1)
                  else impl
                _ -> impl
            [] ->
              underrun

        OpExtcodecopy -> {-# SCC "OpExtcodecopy" #-}
          case stk of
            extAccount':memOffset:codeOffset:codeSize:xs ->
              forceAddr extAccount' (unexpectedSymArgW "EXTCODECOPY") $ \extAccount -> do
                burnExtcodecopy extAccount codeSize $
                  accessMemoryRange memOffset codeSize $
                    fetchAccount extAccount $ \c -> do
                      next
                      assign' (#state % #stack) xs
                      case view bytecode c of
                        Just b -> copyBytesToMemory b codeSize codeOffset memOffset
                        Nothing -> unexpectedSymArg "Cannot copy from unknown code at" [extAccount]
            _ -> underrun

        OpReturndatasize -> {-# SCC "OpReturndatasize" #-}
          limitStack 1 . burn g_base $
            next >> pushSym (bufLength vm.state.returndata)

        OpReturndatacopy -> {-# SCC "OpReturndatacopy" #-}
          case stk of
            xTo:xFrom:xSize:xs ->
              burnReturndatacopy xSize $
                accessMemoryRange xTo xSize $ do
                  next
                  assign' (#state % #stack) xs

                  let jump True = vmError ReturnDataOutOfBounds
                      jump False = copyBytesToMemory vm.state.returndata xSize xFrom xTo

                  case (xFrom, bufLength vm.state.returndata, xSize) of
                    (Lit f, Lit l, Lit sz) ->
                      jump $ l < f + sz || f + sz < f
                    _ -> do
                      let oob = Expr.lt (bufLength vm.state.returndata) (Expr.add xFrom xSize)
                          overflow = Expr.lt (Expr.add xFrom xSize) (xFrom)
                      branch conf.maxDepth (Expr.or oob overflow) jump
            _ -> underrun

        OpExtcodehash -> {-# SCC "OpExtcodehash" #-}
          case stk of
            x':xs -> forceAddr x' (freshVarFallback xs) $ \x ->
              accessAndBurn x $ do
                fetchAccountWithFallback x (freshVarFallback xs) $ \c -> do
                   next
                   assign' (#state % #stack) xs
                   if accountEmpty c
                     then push (W256 0)
                     else case view bytecode c of
                            Just b -> pushSym $ keccak b
                            Nothing -> pushSym $ CodeHash x
            [] ->
              underrun

        OpBlockhash -> {-# SCC "OpBlockhash" #-} do
          stackOp1 g_blockhash $ \case
            Lit i -> case vm.block.number of
              Lit vmBlockNumber ->
                if i + 256 < vmBlockNumber || i >= vmBlockNumber
                -- blockhash is 0 if block is too old or too new as per EVM spec
                then Lit 0
                -- We adopt the fake block hash scheme of the VMTests,
                -- so that blockhash(i) is the hash of i as decimal ASCII.
                else fakeBlockHash i
              -- For symbolic block numbers, we don't know if it's too old or too new,
              -- so we return fake block hash
              _ -> fakeBlockHash i
            i -> BlockHash i
            where
              fakeBlockHash i = (into i :: Integer) & show & Char8.pack & keccak' & Lit

        OpCoinbase -> {-# SCC "OpCoinbase" #-}
          limitStack 1 . burn g_base $
            next >> pushAddr vm.block.coinbase

        OpTimestamp -> {-# SCC "OpTimestamp" #-}
          limitStack 1 . burn g_base $
            next >> pushSym vm.block.timestamp

        OpNumber -> {-# SCC "OpNumber" #-}
          limitStack 1 . burn g_base $
            next >> pushSym vm.block.number

        OpPrevRandao -> {-# SCC "OpPrevRandao" #-} do
          limitStack 1 . burn g_base $
            next >> push vm.block.prevRandao

        OpGaslimit -> {-# SCC "OpGaslimit" #-}
          limitStack 1 . burn g_base $
            next >> push (into vm.block.gaslimit)

        OpChainid -> {-# SCC "OpChainid" #-}
          limitStack 1 . burn g_base $
            next >> push vm.env.chainId

        OpSelfbalance -> {-# SCC "OpSelfbalance" #-}
          limitStack 1 . burn g_low $
            next >> pushSym this.balance

        OpBaseFee -> {-# SCC "OpBaseFee" #-}
          limitStack 1 . burn g_base $
            next >> push vm.block.baseFee

        OpBlobhash -> {-# SCC "OpBlobhash" #-}
          stackOp1 g_verylow $ \_ -> Lit 0

        OpBlobBaseFee -> {-# SCC "OpBlobBaseFee" #-}
          limitStack 1 . burn g_base $
            next >> push 0

        OpPop -> {-# SCC "OpPop" #-}
          case stk of
            _:xs -> burn g_base (next >> assign' (#state % #stack) xs)
            _    -> underrun

        OpMload -> {-# SCC "OpMload" #-}
          case stk of
            x:xs ->
              burn g_verylow $
                accessMemoryWord x $ do
                  next
                  buf <- readMemory x (Lit 32)
                  let w = Expr.readWordFromBytes (Lit 0) buf
                  assign' (#state % #stack) (w : xs)
            _ -> underrun


        OpMcopy -> {-# SCC "OpMcopy" #-}
          case stk of
            dstOff:srcOff:sz:xs ->
              case sz of
                Lit sz' -> do
                  let words_copied = (sz' + 31) `div` 32
                  let g_mcopy = 3*words_copied -- memory access cost is part of accessMemoryRange
                  burn (g_verylow + (unsafeInto g_mcopy)) $
                    accessMemoryRange srcOff sz $ accessMemoryRange dstOff sz $ do
                      next
                      assign' (#state % #stack) xs
                      mcopy sz srcOff dstOff
                _ -> do
                  -- symbolic, ignore gas
                  next
                  assign' (#state % #stack) xs
                  mcopy sz srcOff dstOff
            _ -> underrun
            where
            mcopy (Lit 0) _ _ = pure ()
            mcopy sz srcOff dstOff = do
                  m <- gets (.state.memory)
                  case m of
                    ConcreteMemory _ -> do
                      buf <- readMemory srcOff sz
                      copyBytesToMemory buf sz (Lit 0) dstOff
                    SymbolicMemory mem -> do
                      assign (#state % #memory) (SymbolicMemory $ copySlice srcOff dstOff sz mem mem)

        OpMstore -> {-# SCC "OpMstore" #-}
          case stk of
            x:y:xs ->
              burn g_verylow $
                accessMemoryWord x $ do
                  next
                  gets (.state.memory) >>= \case
                    ConcreteMemory mem -> do
                      case y of
                        Lit w ->
                          copyBytesToMemory (ConcreteBuf (word256Bytes w)) (Lit 32) (Lit 0) x
                        _ -> do
                          -- copy out and move to symbolic memory
                          buf <- freezeMemory mem
                          assign (#state % #memory) (SymbolicMemory $ writeWord x y buf)
                    SymbolicMemory mem ->
                      assign (#state % #memory) (SymbolicMemory $ writeWord x y mem)
                  assign' (#state % #stack) xs
            _ -> underrun

        OpMstore8 -> {-# SCC "OpMstore8" #-}
          case stk of
            x:y:xs ->
              burn g_verylow $
                accessMemoryRange x (Lit 1) $ do
                  let yByte = indexWord (Lit 31) y
                  next
                  gets (.state.memory) >>= \case
                    ConcreteMemory mem -> do
                      case yByte of
                        LitByte byte ->
                          copyBytesToMemory (ConcreteBuf (BS.pack [byte])) (Lit 1) (Lit 0) x
                        _ -> do
                          -- copy out and move to symbolic memory
                          buf <- freezeMemory mem
                          assign (#state % #memory) (SymbolicMemory $ writeByte x yByte buf)
                    SymbolicMemory mem ->
                      assign (#state % #memory) (SymbolicMemory $ writeByte x yByte mem)

                  assign' (#state % #stack) xs
            _ -> underrun

        OpSload -> {-# SCC "OpSload" #-}
          case stk of
            x:xs ->
              let
                finalizeLoad readValue = do next; assign' (#state % #stack) (readValue:xs)

                symbolicRead :: EVM t () = if this.external
                  then accessStorage self x finalizeLoad
                  else finalizeLoad $ Expr.readStorage' (Expr.concKeccakOnePass x) this.storage

                concreteRead :: EVM t () = do
                  acc <- accessStorageForGas self (forceLit x)
                  let cost = if acc then g_warm_storage_read else g_cold_sload
                  burn cost $ if this.external
                    then accessStorage self x finalizeLoad
                    else finalizeLoad $ Lit $ accessConcreteStorage this.storage (forceLit x)
              in whenSymbolicElse symbolicRead concreteRead
            _ -> underrun

        OpSstore -> {-# SCC "OpSstore" #-}
          notStatic $
          case stk of
            x:new:xs ->
              let
                updateVMState :: EVM t () = do
                  next
                  assign' (#state % #stack) xs
                  modifying (#env % #contracts % ix self % #storage) (writeStorage x new)

                concreteSstore :: EVM t () = do
                  let
                    slot = forceLit x
                    currentVal = accessConcreteStorage this.storage slot
                    newVal = forceLit new
                    originalVal = accessConcreteStorage this.origStorage slot
                  ensureGas g_callstipend $ do
                    let storage_cost
                          | (currentVal == newVal) = g_sload
                          | (currentVal == originalVal) && (originalVal == 0) = g_sset
                          | (currentVal == originalVal) = g_sreset
                          | otherwise = g_sload

                    acc <- accessStorageForGas self slot
                    let cold_storage_cost = if acc then 0 else g_cold_sload
                    burn (storage_cost + cold_storage_cost) $ do
                      updateVMState
                      case (originalVal, currentVal, newVal) of
                        (o, c, n)
                          | c == n -> pure ()
                          | o /= 0 && n == 0 -> refund (g_sreset + g_access_list_storage_key)
                          | o /= 0 && c == 0 -> do unRefund (g_sreset + g_access_list_storage_key); when (o == n) $ refund (g_sreset - g_sload)
                          | o /= 0 && o == n -> refund (g_sreset - g_sload)
                          | o == 0 && o == n -> refund (g_sset - g_sload)
                          | otherwise -> pure ()
              in
                whenSymbolicElse updateVMState concreteSstore
            _ -> underrun

        OpTload -> {-# SCC "OpTload" #-}
          case stk of
            x:xs -> do
              burn g_warm_storage_read $
                accessTStorage self x $ \y -> do
                  next
                  assign' (#state % #stack) (y:xs)
            _ -> underrun

        OpTstore -> {-# SCC "OpTstore" #-}
          notStatic $
          case stk of
            x:new:xs ->
              burn g_sload $ do
                next
                modifying (#env % #contracts % ix self % #tStorage) (writeStorage x new)
                assign' (#state % #stack) xs
            _ -> underrun

        OpJump -> {-# SCC "OpJump" #-}
          case stk of
            x:xs ->
              burn g_mid $ forceConcreteLimitSz x 2 "JUMP: symbolic jumpdest" $ \x' ->
                case tryInto x' of
                  Left _ -> vmError BadJumpDestination
                  Right i -> checkJump i xs
            _ -> underrun

        OpJumpi -> {-# SCC "OpJumpi" #-}
          case stk of
            x:y:xs -> forceConcreteLimitSz x 2 "JUMPI: symbolic jumpdest" $ \x' ->
              burn g_high $
                let jump :: Bool -> EVM t ()
                    jump False = assign' (#state % #stack) xs >> next
                    jump _    = case tryInto x' of
                      Left _ -> vmError BadJumpDestination
                      Right i -> checkJump i xs
                in branch conf.maxDepth y jump
            _ -> underrun

        OpPc -> {-# SCC "OpPc" #-}
          limitStack 1 . burn g_base $
            next >> push (unsafeInto vm.state.pc)

        OpMsize -> {-# SCC "OpMsize" #-}
          limitStack 1 . burn g_base $
            next >> push (into vm.state.memorySize)

        OpGas -> {-# SCC "OpGas" #-}
          limitStack 1 . burn g_base $
            next >> pushGas

        OpJumpdest -> {-# SCC "OpJumpdest" #-} burn g_jumpdest next

        OpExp -> {-# SCC "OpExp" #-}
          -- NOTE: this can be done symbolically using unrolling like this:
          --       https://hackage.haskell.org/package/sbv-9.0/docs/src/Data.SBV.Core.Model.html#.%5E
          --       However, it requires symbolic gas, since the gas depends on the exponent
          case stk of
            base:exponent:xs ->
              burnExp exponent $ do
                next
                assign' (#state % #stack) $ Expr.exp base exponent : xs
            _ -> underrun

        OpSignextend -> {-# SCC "OpSignextend" #-} stackOp2 g_low Expr.sex

        OpCreate -> {-# SCC "OpCreate" #-}
          notStatic $
          case stk of
            xValue:xOffset:xSize:xs ->
              accessMemoryRange xOffset xSize $ do
                availableGas <- use (#state % #gas)
                let (cost, gas') = costOfCreate fees availableGas xSize False

                -- handle `prank`
                let from' = fromMaybe self vm.state.overrideCaller
                resetCaller <- use (#state % #resetCaller)
                when resetCaller $ do
                  assign (#state % #overrideCaller) Nothing
                  assign (#state % #resetCaller) False

                touchAddress from'
                nonce <- zoom (#env % #contracts) $ do
                  contr <- use (at from')
                  pure $ (\c -> c.nonce) =<< contr

                newAddr <- createAddress from' nonce
                _ <- accessAccountForGas newAddr
                burn' cost $ do
                  initCode <- readMemory xOffset xSize
                  create from' this xSize gas' xValue xs newAddr initCode
            _ -> underrun

        OpCall -> {-# SCC "OpCall" #-}
          case stk of
            xGas:xTo':xValue:xInOffset:xInSize:xOutOffset:xOutSize:xs ->
              branch conf.maxDepth (Expr.gt xValue (Lit 0)) $ \gt0 -> do
                let addrFallback = if conf.promiseNoReent then const fallback
                                   else unexpectedSymArgW "unable to determine a call target"
                (if gt0 then notStatic else id) $
                  forceAddr xTo' addrFallback $ \xTo ->
                    case gasTryFrom xGas of
                      Left _ -> vmError IllegalOverflow
                      Right gas -> do
                        overrideC <- use $ #state % #overrideCaller
                        let delegateFallback = if conf.promiseNoReent then const fallback
                                               else unknownCode
                        delegateCall this gas xTo xTo xValue xInOffset xInSize xOutOffset xOutSize xs delegateFallback $
                          \callee -> do
                            let from' = fromMaybe self overrideC
                            zoom #state $ do
                              assign #callvalue xValue
                              assign #caller from'
                              assign #contract callee
                            touchAccount from'
                            touchAccount callee
                            transfer from' callee xValue
              where fallback = freshBufFallback xs
            _ -> underrun

        OpCallcode -> {-# SCC "OpCallcode" #-}
          case stk of
            xGas:xTo':xValue:xInOffset:xInSize:xOutOffset:xOutSize:xs ->
              forceAddr xTo' (unexpectedSymArgW "unable to determine a call target") $ \xTo ->
                case gasTryFrom xGas of
                  Left _ -> vmError IllegalOverflow
                  Right gas -> do
                    overrideC <- use $ #state % #overrideCaller
                    delegateCall this gas xTo self xValue xInOffset xInSize xOutOffset xOutSize xs unknownCode $ \_ -> do
                      zoom #state $ do
                        assign #callvalue xValue
                        assign #caller $ fromMaybe self overrideC
                      touchAccount self
            _ -> underrun

        OpReturn -> {-# SCC "OpReturn" #-}
          case stk of
            xOffset:xSize:_ ->
              accessMemoryRange xOffset xSize $ do
                output <- readMemory xOffset xSize
                let
                  codesize = fromMaybe (internalError "processing opcode RETURN. Cannot return dynamically sized abstract data")
                               . maybeLitWordSimp . bufLength $ output
                  maxsize = vm.block.maxCodeSize
                  creation = case vm.frames of
                    [] -> vm.tx.isCreate
                    frame:_ -> case frame.context of
                       CreationContext {} -> True
                       CallContext {} -> False
                if creation
                then
                  if codesize > maxsize
                  then
                    finishFrame (FrameErrored (MaxCodeSizeExceeded maxsize codesize))
                  else do
                    let frameReturned = burn (g_codedeposit * unsafeInto codesize) $
                                          finishFrame (FrameReturned output)
                        frameErrored = finishFrame $ FrameErrored InvalidFormat
                    case readByte (Lit 0) output of
                      LitByte 0xef -> frameErrored
                      LitByte _ -> frameReturned
                      y -> branch conf.maxDepth (Expr.eqByte y (LitByte 0xef)) $ \case
                          True -> frameErrored
                          False -> frameReturned
                else
                   finishFrame (FrameReturned output)
            _ -> underrun

        OpDelegatecall -> {-# SCC "OpDelegatecall" #-}
          case stk of
            xGas:xTo:xInOffset:xInSize:xOutOffset:xOutSize:xs ->
              forceAddr xTo (const $ unexpectedSymArg "unable to determine a call target" [xTo]) $ \xTo' ->
                  case gasTryFrom xGas of
                    Left _ -> vmError IllegalOverflow
                    Right gas ->
                      -- NOTE: we don't update overrideCaller in this case because
                      -- forge-std doesn't. see: https://github.com/foundry-rs/foundry/pull/8863
                      delegateCall this gas xTo' self (Lit 0) xInOffset xInSize xOutOffset xOutSize xs unknownCode $
                        \_ -> touchAccount self
            _ -> underrun

        OpCreate2 -> {-# SCC "OpCreate2" #-} notStatic $
          case stk of
            xValue:xOffset:xSize:xSalt':xs ->
              forceConcrete xSalt' "CREATE2" $ \(xSalt) ->
                accessMemoryRange xOffset xSize $ do
                  availableGas <- use (#state % #gas)
                  buf <- readMemory xOffset xSize
                  forceConcreteBuf buf "CREATE2" $
                    \initCode -> do
                      -- handle `prank`
                      let from' = fromMaybe self vm.state.overrideCaller
                      resetCaller <- use (#state % #resetCaller)
                      when resetCaller $ do
                        assign (#state % #overrideCaller) Nothing
                        assign (#state % #resetCaller) False

                      touchAddress from'

                      let (cost, gas') = costOfCreate fees availableGas xSize True
                      newAddr <- create2Address self xSalt initCode
                      _ <- accessAccountForGas newAddr
                      burn' cost $
                        create from' this xSize gas' xValue xs newAddr (ConcreteBuf initCode)
            _ -> underrun

        OpStaticcall -> {-# SCC "OpStaticcall" #-}
          case stk of
            xGas:xTo:xInOffset:xInSize:xOutOffset:xOutSize:xs ->
              forceAddr xTo (const fallback) $ \xTo' -> case gasTryFrom xGas of
                Left _ -> vmError IllegalOverflow
                Right gas -> do
                  overrideC <- use $ #state % #overrideCaller
                  delegateCall this gas xTo' xTo' (Lit 0) xInOffset xInSize xOutOffset xOutSize xs (const fallback) $
                    \callee -> do
                      zoom #state $ do
                        assign #callvalue (Lit 0)
                        assign #caller $ fromMaybe self overrideC
                        assign #contract callee
                        assign #static True
                      touchAccount self
                      touchAccount callee
                where
                  fallback = freshBufFallback xs
            _ -> underrun

        OpSelfdestruct -> {-# SCC "OpSelfdestruct" #-}
          notStatic $
          case stk of
            [] -> underrun
            (xTo':_) -> forceAddr xTo' (unexpectedSymArgW "SELFDESTRUCT") $ \case
              xTo@(LitAddr _) -> do
                cc <- gets (.tx.subState.createdContracts)
                let createdThisTr = self `member` cc
                acc <- accessAccountForGas xTo
                let cost = if acc then 0 else g_cold_account_access
                    funds = this.balance
                    recipientExists = accountExists xTo vm
                branch conf.maxDepth (Expr.iszero $ Expr.eq funds (Lit 0)) $ \hasFunds -> do
                  let c_new = if (not recipientExists) && hasFunds
                              then g_selfdestruct_newaccount
                              else 0
                  burn (g_selfdestruct + c_new + cost) $ do
                    when (createdThisTr || isCreation this.code) $ do
                      selfdestruct self
                    touchAccount xTo

                    if hasFunds
                    then fetchAccount xTo $ \_ -> do
                      when (createdThisTr || xTo /= self) $ do
                        #env % #contracts % ix xTo % #balance %= (Expr.add funds)
                        assign (#env % #contracts % ix self % #balance) (Lit 0)
                      doStop
                    else
                      doStop
              a -> unexpectedSymArg "trying to self destruct to a symbolic address" [a]

        OpRevert -> {-# SCC "OpRevert" #-}
          case stk of
            xOffset:xSize:_ ->
              accessMemoryRange xOffset xSize $ do
                output <- readMemory xOffset xSize
                finishFrame (FrameReverted output)
            _ -> underrun

        OpUnknown xxx -> {-# SCC "OpUnknown" #-} vmError $ UnrecognizedOpcode xxx

transfer :: (VMOps t, ?conf::Config) => Expr EAddr -> Expr EAddr -> Expr EWord -> EVM t ()
transfer _ _ (Lit 0) = pure ()
transfer src dst val = do
  sb <- preuse $ #env % #contracts % ix src % #balance
  db <- preuse $ #env % #contracts % ix dst % #balance
  case (sb, db) of
    -- both sender and recipient in state
    (Just srcBal, Just _) ->
      branch (?conf).maxDepth (Expr.gt val srcBal) $ \case
        True -> vmError $ BalanceTooLow val srcBal
        False -> do
          (#env % #contracts % ix src % #balance) %= (`Expr.sub` val)
          (#env % #contracts % ix dst % #balance) %= (`Expr.add` val)
    -- sender not in state
    (Nothing, Just _) -> do
      case src of
        LitAddr _ -> do
          touchAddress src
          transfer src dst val
        SymAddr _ -> unexpectedSymArg "Attempting to transfer eth from a symbolic address that is not present in the state" [src]
        GVar _ -> internalError "Unexpected GVar"
    -- recipient not in state
    (_ , Nothing) -> do
      case dst of
        LitAddr _ -> do
          touchAddress dst
          transfer src dst val
        SymAddr _ -> unexpectedSymArg "Attempting to transfer eth to a symbolic address that is not present in the state" [dst]
        GVar _ -> internalError "Unexpected GVar"

-- | Checks a *CALL for failure; OOG, too many callframes, memory access etc.
callChecks
  :: forall (t :: VMType). (?op :: Word8, ?conf :: Config, VMOps t)
  => Contract
  -> Gas t
  -> Expr EAddr
  -> Expr EAddr
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> [Expr EWord]
  -- continuation with gas available for call
  -> (Gas t -> EVM t ())
  -> EVM t ()
callChecks this xGas xContext xTo xValue xInOffset xInSize xOutOffset xOutSize xs continue = do
  vm <- get
  let fees = vm.block.schedule
  accessMemoryRange xInOffset xInSize $
    accessMemoryRange xOutOffset xOutSize $ do
      availableGas <- use (#state % #gas)
      let recipientExists = accountExists xContext vm
      let from = fromMaybe vm.state.contract vm.state.overrideCaller
      fromBal <- preuse $ #env % #contracts % ix from % #balance
      costOfCall fees recipientExists xValue availableGas xGas xTo $ \cost gas' -> do
        let checkCallDepth =
              if length vm.frames >= 1024
              then do
                assign' (#state % #stack) (Lit 0 : xs)
                assign (#state % #returndata) mempty
                pushTrace $ ErrorTrace CallDepthLimitReached
                next
              else continue (toGas gas')
        case (fromBal, xValue) of
          -- we're not transferring any value, and can skip the balance check
          (_, Lit 0) -> burn (cost - gas') checkCallDepth

          -- from is in the state, we check if they have enough balance
          (Just fb, _) -> do
            burn (cost - gas') $
              branch (?conf).maxDepth (Expr.gt xValue fb) $ \case
                True -> do
                  assign' (#state % #stack) (Lit 0 : xs)
                  assign (#state % #returndata) mempty
                  pushTrace $ ErrorTrace (BalanceTooLow xValue this.balance)
                  next
                False -> checkCallDepth

          -- from is not in the state, we insert it if safe to do so and run the checks again
          (Nothing, _) -> case from of
            LitAddr _ -> do
              -- insert an entry in the state
              let contract = case vm.config.baseState of
                    AbstractBase -> unknownContract from
                    EmptyBase -> emptyContract
              (#env % #contracts) %= (Map.insert from contract)
              -- run callChecks again
              callChecks this xGas xContext xTo xValue xInOffset xInSize xOutOffset xOutSize xs continue

            -- adding a symbolic address into the state here would be unsound (due to potential aliasing)
            SymAddr _ -> unexpectedSymArg "Attempting to transfer eth from a symbolic address that is not present in the state" [from]
            GVar _ -> internalError "Unexpected GVar"

precompiledContract
  :: (?conf :: Config, ?op :: Word8, VMOps t)
  => Contract
  -> Gas t
  -> Addr
  -> Addr
  -> Expr EWord
  -> Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
  -> [Expr EWord]
  -> EVM t ()
precompiledContract this xGas precompileAddr recipient xValue inOffset inSize outOffset outSize xs
  = callChecks this xGas (LitAddr recipient) (LitAddr precompileAddr) xValue inOffset inSize outOffset outSize xs $ \gas' ->
    do
      executePrecompile precompileAddr gas' inOffset inSize outOffset outSize xs
      self <- use (#state % #contract)
      stk <- use (#state % #stack)
      result' <- use #result
      case result' of
        Nothing -> case stk of
          x:_ -> case maybeLitWordSimp x of
            Just 0 ->
              pure ()
            Just 1 ->
              fetchAccount (LitAddr recipient) $ \_ -> do
                touchAccount self
                touchAccount (LitAddr recipient)
                transfer self (LitAddr recipient) xValue
            _ -> unexpectedSymArg "unexpected return value from precompile" [x]
          _ -> underrun
        _ -> pure ()

executePrecompile
  :: (?op :: Word8, VMOps t)
  => Addr
  -> Gas t -> Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord -> [Expr EWord]
  -> EVM t ()
executePrecompile preCompileAddr gasCap inOffset inSize outOffset outSize xs  = do
  vm <- get
  input <- readMemory inOffset inSize
  let fees = vm.block.schedule
      cost = costOfPrecompile fees preCompileAddr input
      notImplemented = whenSymbolicElse
        (partial $ PrecompileMissing {pc = vm.state.pc, addr = vm.state.contract, preAddr = preCompileAddr})
        (vmError $ NonexistentPrecompile preCompileAddr)
      precompileFail = burn' (subGas gasCap cost) $ do
                         assign' (#state % #stack) (Lit 0 : xs)
                         pushTrace $ ErrorTrace PrecompileFailure
                         next
  if not (enoughGas cost gasCap) then
    burn' gasCap $ do
      assign' (#state % #stack) (Lit 0 : xs)
      next
  else burn cost $
    case preCompileAddr of
      -- ECRECOVER
      0x1 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "ECRECOVER" $ \input' -> do
          case EVM.Precompiled.execute 0x1 (truncpadlit 128 input') 32 of
            Nothing -> do
              -- return no output for invalid signature
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) mempty
              next
            Just output -> do
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) (ConcreteBuf output)
              copyBytesToMemory (ConcreteBuf output) outSize (Lit 0) outOffset
              next

      -- SHA2-256
      0x2 ->
        forceConcreteBuf input "SHA2-256" $ \input' -> do
          let
            hash = sha256Buf input'
            sha256Buf x = ConcreteBuf $ BA.convert (Crypto.hash x :: Digest SHA256)
          assign' (#state % #stack) (Lit 1 : xs)
          assign (#state % #returndata) hash
          copyBytesToMemory hash outSize (Lit 0) outOffset
          next

      -- RIPEMD-160
      0x3 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "RIPEMD160" $ \input' -> do
          let
            padding = BS.pack $ replicate 12 0
            hash' = BA.convert (Crypto.hash input' :: Digest RIPEMD160)
            hash  = ConcreteBuf $ padding <> hash'
          assign' (#state % #stack) (Lit 1 : xs)
          assign (#state % #returndata) hash
          copyBytesToMemory hash outSize (Lit 0) outOffset
          next

      -- IDENTITY
      0x4 -> do
          assign' (#state % #stack) (Lit 1 : xs)
          assign (#state % #returndata) input
          copyCallBytesToMemory input outSize outOffset
          next

      -- MODEXP
      0x5 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "MODEXP" $ \input' -> do
          let
            (lenb, lene, lenm) = parseModexpLength input'
            -- EIP-7823: ModExp upper bounds - each input limited to 1024 bytes (8192 bits)
            modexpLimit = 1024 :: W256
          if lenb > modexpLimit || lene > modexpLimit || lenm > modexpLimit
          then precompileFail  -- EIP-7823: fail and consume all gas if limits exceeded
          else do
            let
              output = ConcreteBuf $
                if isZero (96 + lenb + lene) lenm input'
                then truncpadlit (unsafeInto lenm) (asBE (0 :: Int))
                else
                  let
                    b = asInteger $ lazySlice 96 lenb input'
                    e = asInteger $ lazySlice (96 + lenb) lene input'
                    m = asInteger $ lazySlice (96 + lenb + lene) lenm input'
                  in
                    padLeft (unsafeInto lenm) (asBE (expFast b e m))
            assign' (#state % #stack) (Lit 1 : xs)
            assign (#state % #returndata) output
            copyBytesToMemory output outSize (Lit 0) outOffset
            next

      -- ECADD
      0x6 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "ECADD" $ \input' ->
          case EVM.Precompiled.execute 0x6 (truncpadlit 128 input') 64 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 64 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- ECMUL
      0x7 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "ECMUL" $ \input' ->
          case EVM.Precompiled.execute 0x7 (truncpadlit 96 input') 64 of
          Nothing -> precompileFail
          Just output -> do
            let truncpaddedOutput = ConcreteBuf $ truncpadlit 64 output
            assign' (#state % #stack) (Lit 1 : xs)
            assign (#state % #returndata) truncpaddedOutput
            copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
            next

      -- ECPAIRING
      0x8 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "ECPAIR" $ \input' ->
          case EVM.Precompiled.execute 0x8 input' 32 of
          Nothing -> precompileFail
          Just output -> do
            let truncpaddedOutput = ConcreteBuf $ truncpadlit 32 output
            assign' (#state % #stack) (Lit 1 : xs)
            assign (#state % #returndata) truncpaddedOutput
            copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
            next

      -- BLAKE2
      0x9 ->
        -- TODO: support symbolic variant
        forceConcreteBuf input "BLAKE2" $ \input' -> do
          case (BS.length input', 1 >= BS.last input') of
            (213, True) -> case EVM.Precompiled.execute 0x9 input' 64 of
              Just output -> do
                let truncpaddedOutput = ConcreteBuf $ truncpadlit 64 output
                assign' (#state % #stack) (Lit 1 : xs)
                assign (#state % #returndata) truncpaddedOutput
                copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
                next
              Nothing -> precompileFail
            _ -> precompileFail

      -- Point Evaluation (EIP-4844)
      0x0A ->
        forceConcreteBuf input "POINT_EVALUATION" $ \input' -> do
          -- Input: versioned_hash (32) || z (32) || y (32) || commitment (48) || proof (48) = 192 bytes
          -- Per EIP-4844: Input must be exactly 192 bytes
          if BS.length input' /= 192
          then precompileFail
          else do
            let versionedHash = BS.take 32 input'
                z = BS.take 32 $ BS.drop 32 input'
                y = BS.take 32 $ BS.drop 64 input'
                -- commitment = BS.take 48 $ BS.drop 96 input'  -- Not used without KZG
                -- proof = BS.take 48 $ BS.drop 144 input'      -- Not used without KZG

                -- BLS_MODULUS: the field modulus for BLS12-381
                blsModulus :: Integer
                blsModulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513

                -- Check versioned_hash format: first byte must be 0x01 (VERSIONED_HASH_VERSION_KZG)
                hashVersion = if BS.null versionedHash then 0 else BS.head versionedHash

                -- Check z and y are valid field elements (< BLS_MODULUS)
                zInt = into @Integer $ word z
                yInt = into @Integer $ word y

            -- Validation checks per EIP-4844
            if hashVersion /= 0x01
            then precompileFail  -- Invalid versioned hash version
            else if zInt >= blsModulus || yInt >= blsModulus
            then precompileFail  -- z or y out of bounds
            else do
              -- TODO: Actual KZG verification requires c-kzg-4844 library
              -- For now, we perform the cryptographic verification using the library
              case pointEvaluationVerify input' of
                Just output -> do
                  assign' (#state % #stack) (Lit 1 : xs)
                  assign (#state % #returndata) (ConcreteBuf output)
                  copyBytesToMemory (ConcreteBuf output) outSize (Lit 0) outOffset
                  next
                Nothing -> precompileFail

      -- BLS12-381 G1ADD (EIP-2537) - 0x0B
      0x0B ->
        forceConcreteBuf input "BLS_G1ADD" $ \input' ->
          if BS.length input' /= 256
          then precompileFail
          else case EVM.Precompiled.execute 0x0B input' 128 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 128 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- BLS12-381 G1MSM (EIP-2537) - 0x0C
      0x0C ->
        forceConcreteBuf input "BLS_G1MSM" $ \input' -> do
          let len = BS.length input'
          if len == 0 || len `mod` 160 /= 0
          then precompileFail
          else case EVM.Precompiled.execute 0x0C input' 128 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 128 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- BLS12-381 G2ADD (EIP-2537) - 0x0D
      0x0D ->
        forceConcreteBuf input "BLS_G2ADD" $ \input' ->
          if BS.length input' /= 512
          then precompileFail
          else case EVM.Precompiled.execute 0x0D input' 256 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 256 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- BLS12-381 G2MSM (EIP-2537) - 0x0E
      0x0E ->
        forceConcreteBuf input "BLS_G2MSM" $ \input' -> do
          let len = BS.length input'
          if len == 0 || len `mod` 288 /= 0
          then precompileFail
          else case EVM.Precompiled.execute 0x0E input' 256 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 256 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- BLS12-381 PAIRING (EIP-2537) - 0x0F
      0x0F ->
        forceConcreteBuf input "BLS_PAIRING" $ \input' -> do
          let len = BS.length input'
          if len `mod` 384 /= 0
          then precompileFail
          else case EVM.Precompiled.execute 0x0F input' 32 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 32 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- BLS12-381 MAP_FP_TO_G1 (EIP-2537) - 0x10
      0x10 ->
        forceConcreteBuf input "BLS_MAP_FP_TO_G1" $ \input' ->
          if BS.length input' /= 64
          then precompileFail
          else case EVM.Precompiled.execute 0x10 input' 128 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 128 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- BLS12-381 MAP_FP2_TO_G2 (EIP-2537) - 0x11
      0x11 ->
        forceConcreteBuf input "BLS_MAP_FP2_TO_G2" $ \input' ->
          if BS.length input' /= 128
          then precompileFail
          else case EVM.Precompiled.execute 0x11 input' 256 of
            Nothing -> precompileFail
            Just output -> do
              let truncpaddedOutput = ConcreteBuf $ truncpadlit 256 output
              assign' (#state % #stack) (Lit 1 : xs)
              assign (#state % #returndata) truncpaddedOutput
              copyBytesToMemory truncpaddedOutput outSize (Lit 0) outOffset
              next

      -- P256VERIFY (EIP-7212)
      0x100 ->
        forceConcreteBuf input "P256VERIFY" $ \input' -> do
          -- Input: hash (32) || r (32) || s (32) || x (32) || y (32) = 160 bytes
          -- Per EIP-7212: "If the input is less than 160 bytes, the remaining bytes
          -- are considered to be zero"
          let paddedInput = truncpadlit 160 input'
              result = p256Verify paddedInput
          if result
          then do
            -- Success: return 1 (32 bytes, big-endian)
            let output = ConcreteBuf $ BS.replicate 31 0 <> BS.singleton 1
            assign' (#state % #stack) (Lit 1 : xs)
            assign (#state % #returndata) output
            copyBytesToMemory output outSize (Lit 0) outOffset
            next
          else do
            -- Verification failed or invalid input: return empty but CALL succeeds
            assign' (#state % #stack) (Lit 1 : xs)
            assign (#state % #returndata) mempty
            next

      _ -> notImplemented

truncpadlit :: Int -> ByteString -> ByteString
truncpadlit n xs = if m > n then BS.take n xs
                   else BS.append xs (BS.replicate (n - m) 0)
  where m = BS.length xs

-- | P-256 (secp256r1) signature verification for EIP-7212
-- Input format: hash (32) || r (32) || s (32) || x (32) || y (32)
-- Returns True if signature is valid, False otherwise
-- Note: EIP-7212 provides a PRE-HASHED message, so we implement ECDSA
-- verification manually to avoid double-hashing.
p256Verify :: ByteString -> Bool
p256Verify input =
  let -- Parse input
      hashBytes = BS.take 32 input
      e = into @Integer $ word hashBytes  -- message hash as integer
      r = into @Integer $ word $ BS.take 32 $ BS.drop 32 input
      s = into @Integer $ word $ BS.take 32 $ BS.drop 64 input
      x = into @Integer $ word $ BS.take 32 $ BS.drop 96 input
      y = into @Integer $ word $ BS.take 32 $ BS.drop 128 input

      -- P-256 curve order
      curve = getCurveByName SEC_p256r1
      n = case curve of
            CurveFP (CurvePrime _ cc) -> ecc_n cc
            _ -> 0  -- Should never happen for P-256

      -- Public key point
      pubPoint = Point x y

      -- ECDSA verification algorithm for pre-hashed message:
      -- 1. Verify r and s are in [1, n-1]
      -- 2. Verify public key is valid point on curve
      -- 3. Calculate w = s^(-1) mod n
      -- 4. Calculate u1 = (e * w) mod n
      -- 5. Calculate u2 = (r * w) mod n
      -- 6. Calculate R = u1*G + u2*Q
      -- 7. If R is at infinity, fail
      -- 8. Verify r == R.x mod n

  in if r < 1 || r >= n || s < 1 || s >= n
     then False
     else if not (isPointValid curve pubPoint)
     then False
     else case inverse s n of
       Nothing -> False  -- s has no inverse (shouldn't happen if s in [1, n-1])
       Just w ->
         let u1 = (e * w) `mod` n
             u2 = (r * w) `mod` n
             -- R = u1*G + u2*Q
             rPoint = pointAddTwoMuls curve u1 (ecc_g $ common_curve curve) u2 pubPoint
         in case rPoint of
              PointO -> False  -- Point at infinity
              Point rx _ -> (rx `mod` n) == r
  where
    common_curve (CurveFP (CurvePrime _ cc)) = cc
    common_curve _ = error "p256Verify: unexpected curve type"

-- | Point Evaluation precompile (EIP-4844) KZG proof verification
-- Input: versioned_hash (32) || z (32) || y (32) || commitment (48) || proof (48)
-- Output: FIELD_ELEMENTS_PER_BLOB (32) || BLS_MODULUS (32) on success
-- Returns Nothing on verification failure
--
-- Per EIP-4844, this precompile verifies:
-- 1. versioned_hash == kzg_to_versioned_hash(commitment)
-- 2. verify_kzg_proof(commitment, z, y, proof)
--
-- Note: Full KZG proof verification requires the c-kzg-4844 library.
-- This implementation can verify the versioned_hash matches the commitment,
-- but cannot perform the actual KZG proof verification without the library.
pointEvaluationVerify :: ByteString -> Maybe ByteString
pointEvaluationVerify input =
  let versionedHash = BS.take 32 input
      commitment = BS.take 48 $ BS.drop 96 input
      -- Per EIP-4844: kzg_to_versioned_hash(commitment) = 0x01 || SHA256(commitment)[1:32]
      commitmentHash = BA.convert (Crypto.hash commitment :: Digest SHA256)
      expectedVersionedHash = BS.singleton 0x01 <> BS.drop 1 commitmentHash
  in if versionedHash /= expectedVersionedHash
     then Nothing  -- Versioned hash doesn't match commitment
     else
       -- Try ethjet FFI first (in case KZG support is available)
       case EVM.Precompiled.execute 0x0A input 64 of
         Just output -> Just output
         Nothing ->
           -- Without c-kzg-4844, we cannot verify the KZG proof
           -- Return failure - this will cause valid proofs to fail,
           -- but at least invalid versioned hashes are caught above
           Nothing

lazySlice :: W256 -> W256 -> ByteString -> LS.ByteString
lazySlice offset size bs =
  let bs' = LS.take (unsafeInto size) (LS.drop (unsafeInto offset) (fromStrict bs))
  in bs' <> LS.replicate (unsafeInto size - LS.length bs') 0

parseModexpLength :: ByteString -> (W256, W256, W256)
parseModexpLength input =
  let lenb = word $ LS.toStrict $ lazySlice  0 32 input
      lene = word $ LS.toStrict $ lazySlice 32 32 input
      lenm = word $ LS.toStrict $ lazySlice 64 32 input
  in (lenb, lene, lenm)

--- checks if a range of ByteString bs starting at offset and length size is all zeros.
isZero :: W256 -> W256 -> ByteString -> Bool
isZero offset size bs =
  LS.all (== 0) $
    LS.take (unsafeInto size) $
      LS.drop (unsafeInto offset) $
        fromStrict bs

asInteger :: LS.ByteString -> Integer
asInteger xs = if xs == mempty then 0
  else 256 * asInteger (LS.init xs)
      + into (LS.last xs)

-- | BLS12-381 G1 MSM discount table from EIP-2537
-- Maps k (number of pairs) to discount in parts per 1000
-- max_discount = 519 for k > 128
blsG1MsmDiscount :: Word64 -> Word64
blsG1MsmDiscount k = case k of
  1 -> 1000; 2 -> 949; 3 -> 848; 4 -> 797; 5 -> 764; 6 -> 750; 7 -> 738; 8 -> 728; 9 -> 719; 10 -> 712
  11 -> 705; 12 -> 698; 13 -> 692; 14 -> 687; 15 -> 682; 16 -> 677; 17 -> 673; 18 -> 669; 19 -> 665; 20 -> 661
  21 -> 658; 22 -> 654; 23 -> 651; 24 -> 648; 25 -> 645; 26 -> 642; 27 -> 640; 28 -> 637; 29 -> 635; 30 -> 632
  31 -> 630; 32 -> 627; 33 -> 625; 34 -> 623; 35 -> 621; 36 -> 619; 37 -> 617; 38 -> 615; 39 -> 613; 40 -> 611
  41 -> 609; 42 -> 608; 43 -> 606; 44 -> 604; 45 -> 603; 46 -> 601; 47 -> 599; 48 -> 598; 49 -> 596; 50 -> 595
  51 -> 593; 52 -> 592; 53 -> 591; 54 -> 589; 55 -> 588; 56 -> 586; 57 -> 585; 58 -> 584; 59 -> 582; 60 -> 581
  61 -> 580; 62 -> 579; 63 -> 577; 64 -> 576; 65 -> 575; 66 -> 574; 67 -> 573; 68 -> 572; 69 -> 570; 70 -> 569
  71 -> 568; 72 -> 567; 73 -> 566; 74 -> 565; 75 -> 564; 76 -> 563; 77 -> 562; 78 -> 561; 79 -> 560; 80 -> 559
  81 -> 558; 82 -> 557; 83 -> 556; 84 -> 555; 85 -> 554; 86 -> 553; 87 -> 552; 88 -> 551; 89 -> 550; 90 -> 549
  91 -> 548; 92 -> 547; 93 -> 547; 94 -> 546; 95 -> 545; 96 -> 544; 97 -> 543; 98 -> 542; 99 -> 541; 100 -> 540
  101 -> 540; 102 -> 539; 103 -> 538; 104 -> 537; 105 -> 536; 106 -> 536; 107 -> 535; 108 -> 534; 109 -> 533; 110 -> 532
  111 -> 532; 112 -> 531; 113 -> 530; 114 -> 529; 115 -> 528; 116 -> 528; 117 -> 527; 118 -> 526; 119 -> 525; 120 -> 525
  121 -> 524; 122 -> 523; 123 -> 522; 124 -> 522; 125 -> 521; 126 -> 520; 127 -> 520; 128 -> 519
  -- For k > 128, use max_discount = 519
  _ -> 519

-- | BLS12-381 G2 MSM discount table from EIP-2537
-- Maps k (number of pairs) to discount in parts per 1000
-- max_discount = 524 for k > 128
blsG2MsmDiscount :: Word64 -> Word64
blsG2MsmDiscount k = case k of
  1 -> 1000; 2 -> 1000; 3 -> 923; 4 -> 884; 5 -> 855; 6 -> 832; 7 -> 812; 8 -> 796; 9 -> 782; 10 -> 770
  11 -> 759; 12 -> 749; 13 -> 740; 14 -> 732; 15 -> 724; 16 -> 717; 17 -> 711; 18 -> 704; 19 -> 699; 20 -> 693
  21 -> 688; 22 -> 683; 23 -> 679; 24 -> 674; 25 -> 670; 26 -> 666; 27 -> 663; 28 -> 659; 29 -> 655; 30 -> 652
  31 -> 649; 32 -> 646; 33 -> 643; 34 -> 640; 35 -> 637; 36 -> 634; 37 -> 632; 38 -> 629; 39 -> 627; 40 -> 624
  41 -> 622; 42 -> 620; 43 -> 618; 44 -> 615; 45 -> 613; 46 -> 611; 47 -> 609; 48 -> 607; 49 -> 606; 50 -> 604
  51 -> 602; 52 -> 600; 53 -> 598; 54 -> 597; 55 -> 595; 56 -> 593; 57 -> 592; 58 -> 590; 59 -> 589; 60 -> 587
  61 -> 586; 62 -> 584; 63 -> 583; 64 -> 582; 65 -> 580; 66 -> 579; 67 -> 578; 68 -> 576; 69 -> 575; 70 -> 574
  71 -> 573; 72 -> 571; 73 -> 570; 74 -> 569; 75 -> 568; 76 -> 567; 77 -> 566; 78 -> 565; 79 -> 563; 80 -> 562
  81 -> 561; 82 -> 560; 83 -> 559; 84 -> 558; 85 -> 557; 86 -> 556; 87 -> 555; 88 -> 554; 89 -> 553; 90 -> 552
  91 -> 552; 92 -> 551; 93 -> 550; 94 -> 549; 95 -> 548; 96 -> 547; 97 -> 546; 98 -> 545; 99 -> 545; 100 -> 544
  101 -> 543; 102 -> 542; 103 -> 541; 104 -> 541; 105 -> 540; 106 -> 539; 107 -> 538; 108 -> 537; 109 -> 537; 110 -> 536
  111 -> 535; 112 -> 535; 113 -> 534; 114 -> 533; 115 -> 532; 116 -> 532; 117 -> 531; 118 -> 530; 119 -> 530; 120 -> 529
  121 -> 528; 122 -> 528; 123 -> 527; 124 -> 526; 125 -> 526; 126 -> 525; 127 -> 524; 128 -> 524
  -- For k > 128, use max_discount = 524
  _ -> 524

-- * Opcode helper actions

noop :: Monad m => m ()
noop = pure ()

pushTo :: MonadState s m => Lens s s [a] [a] -> a -> m ()
pushTo f x = f %= (x :)

pushToSequence :: MonadState s m => Setter s s (Seq a) (Seq a) -> a -> m ()
pushToSequence f x = f %= (Seq.|> x)

getCodeLocation :: VM t -> CodeLocation
getCodeLocation vm = (vm.state.contract, vm.state.pc)

query :: Query t -> EVM t ()
query q = assign #result $ Just $ HandleEffect (Query q)

fork :: Maybe Int -> Int -> BranchContext -> EVM Symbolic ()
fork depthLimit exploreDepth forkContext = do
  if (isNothing depthLimit || (exploreDepth < fromJust depthLimit)) then do
    assign #result $ Just $ HandleEffect (Branch forkContext)
  else do
    vm <- get
    assign #result $ Just $ Unfinished (BranchTooDeep {pc = vm.state.pc, addr = vm.state.contract})

fetchAccount :: VMOps t => Expr EAddr -> (Contract -> EVM t ()) -> EVM t ()
fetchAccount addr continue =
  let fallback = unexpectedSymArgW "trying to access a symbolic address that isn't already present in storage"
  in fetchAccountWithFallback addr fallback continue

-- | Construct RPC Query and halt execution until resolved
fetchAccountWithFallback :: VMOps t => Expr EAddr -> (Expr EAddr -> EVM t ()) -> (Contract -> EVM t ()) -> EVM t ()
fetchAccountWithFallback addr fallback continue =
  use (#env % #contracts % at addr) >>= \case
    Just c -> continue c
    Nothing -> case addr of
      SymAddr _ -> fallback addr
      LitAddr a -> do
        base <- use (#config % #baseState)
        assign (#result) . Just . HandleEffect . Query $
          PleaseFetchContract a base $ \c -> do
            assign (#env % #contracts % at addr) (Just c)
            assign #result Nothing
            continue c
      GVar _ -> internalError "Unexpected GVar"

accessConcreteStorage :: Expr Storage -> W256 -> W256
accessConcreteStorage storage slot' =
  case storage of
    (ConcreteStore m) -> fromMaybe 0 $ Map.lookup slot' m
    _ -> internalError "Storage must be concrete"

accessStorage :: forall t . (?conf :: Config, VMOps t, Typeable t) => Expr EAddr
  -> Expr EWord
  -> (Expr EWord -> EVM t ())
  -> EVM t ()
accessStorage addr slot continue = do
  let slotConc = Expr.concKeccakSimpExpr slot
  use (#env % #contracts % at addr) >>= \case
    Just c ->
      -- Try first without concretization. Then if we get a Just, with concretization
      -- if both give a Just, should we `continue`.
      -- --> This is because readStorage can do smart rewrites, but only in case
      --     the expression is of a particular format, which can be destroyed by simplification.
      --     However, without concretization, it may not find things that are actually in the storage
      case readStorage slot c.storage of
        Just x -> case readStorage slotConc c.storage of
          Just (Lit _) -> continue x
          Just _ | not c.external -> continue x
          _ -> rpcCall c slotConc
        Nothing -> rpcCall c slotConc
    Nothing ->
      fetchAccount addr $ \_ -> accessStorage addr slot continue
  where
      rpcCall c slotConc = fetchAccount addr $ \_ ->
        if c.external
        then forceConcreteAddr addr "cannot read storage from symbolic addresses via rpc" $ \addr' ->
          forceConcrete slotConc "cannot read symbolic slots via RPC" $ \slot' -> do
            use (#env % #contracts % at (LitAddr addr')) >>= \case
              Nothing -> internalError $ "contract addr " <> show addr' <> " marked external not found in cache"
              -- At this point, we know the contract is external and the underlying storage
              -- is concrete. Check if the slot has already been fetched
              Just contr -> if concStoreContains (Lit slot') contr.storage
                then continue $ SLoad (Lit slot') contr.storage
                else mkQuery addr' slot'
        else do
          -- Symbolic address that cannot be cajoled/solved into a concrete one
          -- We cannot query the underlying storage, as we don't know which one to query
          -- So we store and return 0, as it is the only sound option
          modifying (#env % #contracts % ix addr % #storage) (writeStorage slot (Lit 0))
          continue $ Lit 0
      mkQuery :: Addr -> W256 -> EVM t ()
      mkQuery a s = query $ PleaseFetchSlot a s $ \x -> do
        modifying (#env % #contracts % ix (LitAddr a) % #storage) (writeStorage (Lit s) (Lit x))
        assign #result Nothing
        continue $ Lit x

accessTStorage
  :: VMOps t => Expr EAddr
  -> Expr EWord
  -> (Expr EWord -> EVM t ())
  -> EVM t ()
accessTStorage addr slot continue = do
  let slotConc = Expr.concKeccakSimpExpr slot
  use (#env % #contracts % at addr) >>= \case
    Just c ->
      -- Try first without concretization. Then if we get a Just, with concretization
      -- See `accessStorage` for more details
      case readStorage slot c.tStorage of
        Just x -> case readStorage slotConc c.tStorage of
          Just _ -> continue x
          Nothing -> continue $ Lit 0
        Nothing -> continue $ Lit 0
    Nothing ->
      fetchAccount addr $ \_ ->
        accessTStorage addr slot continue

clearTStorages :: EVM t ()
clearTStorages = (#env % #contracts) %= fmap (\c -> c { tStorage = ConcreteStore mempty } :: Contract)

accountExists :: Expr EAddr -> VM t -> Bool
accountExists addr vm =
  case Map.lookup addr vm.env.contracts of
    Just c -> not (accountEmpty c)
    Nothing -> False

-- EIP 161
accountEmpty :: Contract -> Bool
accountEmpty c =
  case c.code of
    RuntimeCode (ConcreteRuntimeCode "") -> True
    RuntimeCode (SymbolicRuntimeCode b) -> null b
    _ -> False
  && c.nonce == (Just 0)
  -- TODO: handle symbolic balance...
  && c.balance == Lit 0

-- Adds constraints such that two symbolic addresses cannot alias each other
-- and symbolic addresses cannot alias concrete addresses
addAliasConstraints :: EVM t ()
addAliasConstraints = do
  vm <- get
  let addrConstr = noClash $ Map.keys vm.env.contracts
  modifying #constraints ((++) addrConstr)
  where
    noClash addrs = [a ./= b | a <- addrs, b <- addrs, Expr.isSymAddr b, a < b]

-- * How to finalize a transaction
finalize :: VMOps t => EVM t ()
finalize = do
  let
    revertContracts  = use (#tx % #txReversion) >>= assign (#env % #contracts)
    -- EIP-7702: On revert, clear execution state but preserve authorization refunds
    -- Authorization refunds are computed before execution and should apply regardless of tx success
    revertSubstate   = do
      authRefunds <- use (#tx % #authorizationRefunds)
      assign (#tx % #subState) (SubState mempty mempty mempty mempty authRefunds mempty)

  addAliasConstraints
  use #result >>= \case
    Just (VMFailure (Revert _)) -> do
      revertContracts
      revertSubstate
    Just (VMFailure _) -> do
      -- burn remaining gas
      assign (#state % #gas) initialGas
      revertContracts
      revertSubstate
    Just (VMSuccess output) -> do
      clearTStorages
      -- deposit the code from a creation tx
      creation <- use (#tx % #isCreate)
      createe  <- use (#state % #contract)
      createeContract <- preuse (#env % #contracts % ix createe)
      -- Check if this is a collision case (target has RuntimeCode instead of InitCode)
      let isCollision = creation && case createeContract of
            Just c -> case c.code of
              InitCode _ _ -> False
              RuntimeCode _ -> True   -- collision: existing contract has RuntimeCode
              UnknownCode _ -> internalError "cannot determine collision with unknown code"
            Nothing -> internalError "create transaction but no code found"
      -- For collision: burn all gas (failed CREATE consumes all gas)
      when isCollision $ assign (#state % #gas) initialGas
      -- Only replace code if this is a creation tx, the contract exists,
      -- and it has InitCode (not RuntimeCode from a collision)
      let shouldReplaceCode = creation && not isCollision
      when shouldReplaceCode $
        case output of
          ConcreteBuf bs -> replaceCode createe (RuntimeCode (ConcreteRuntimeCode bs))
          _ ->
            case Expr.toList output of
              Nothing -> unexpectedSymArg "runtime code cannot have an abstract length" [output]
              Just ops -> replaceCode createe (RuntimeCode (SymbolicRuntimeCode ops))
    _ ->
      internalError "Finalising an unfinished tx."

  -- compute and pay the refund to the caller and the
  -- corresponding payment to the miner
  block <- use #block

  payRefunds

  touchAccount block.coinbase

  -- perform state trie clearing (EIP 161), of selfdestructs
  -- and touched accounts. addresses are cleared if they have
  --    a) selfdestructed, or
  --    b) been touched and
  --    c) are empty.
  -- (see Yellow Paper "Accrued Substate")
  --
  -- remove any destructed addresses
  destroyedAddresses <- use (#tx % #subState % #selfdestructs)
  modifying (#env % #contracts)
    (Map.filterWithKey (\k _ -> (k `notElem` destroyedAddresses)))
  -- then, clear any remaining empty and touched addresses
  touchedAddresses <- use (#tx % #subState % #touchedAccounts)
  modifying (#env % #contracts)
    (Map.filterWithKey
      (\k a -> not ((k `elem` touchedAddresses) && accountEmpty a)))

-- | Loads the selected contract as the current contract to execute
loadContract :: Expr EAddr -> State (VM t) ()
loadContract target =
  preuse (#env % #contracts % ix target % #code) >>=
    \case
      Nothing ->
        internalError "Call target doesn't exist"
      Just targetCode -> do
        assign (#state % #contract) target
        assign (#state % #code)     targetCode
        assign (#state % #codeContract) target

limitStack :: VMOps t => Int -> EVM (t :: VMType) () -> EVM t ()
limitStack n continue = do
  stk <- use (#state % #stack)
  if length stk + n > 1024
    then vmError StackLimitExceeded
    else continue

notStatic :: VMOps t => EVM t () -> EVM t ()
notStatic continue = do
  bad <- use (#state % #static)
  if bad
    then vmError StateChangeWhileStatic
    else continue

-- Ensures the account `addr` exists on the VM environment.
-- Useful when `addr` needs to e.g. keep a eth balance or
-- be the source of contract deployments via pranks
touchAddress :: VMOps t => Expr EAddr -> EVM t ()
touchAddress addr = do
  baseState <- use (#config % #baseState)
  let mkc = case baseState of
              AbstractBase -> unknownContract
              EmptyBase -> const emptyContract
  (#env % #contracts) %= (Map.insertWith (\_ e -> e) addr (mkc addr))

onlyDeployed :: forall t . (?conf :: Config, VMOps t, Typeable t) =>
  Expr EWord
  -> (Expr EWord -> EVM t ())
  -> (Expr EAddr -> EVM t ())
  -> EVM t ()
onlyDeployed addrExpr fallback continue = do
    vm <- get
    if not (?conf.onlyDeployed) then fallback addrExpr
    else case eqT @t @Symbolic of
      Just Refl -> do
        let deployedAddrs = map forceEAddrToEWord $ mapMaybe (codeMustExist vm) $ Map.keys vm.env.contracts
        fork (?conf.maxDepth) vm.exploreDepth $ PleaseRunAll deployedAddrs runAllPaths
      _ -> internalError "Unknown address in Concrete mode"
  where
    codeMustExist :: (VM t) -> Expr EAddr -> Maybe (Expr EAddr)
    codeMustExist vm addr = do
      contr <- Map.lookup addr vm.env.contracts
      case contr.code of
        RuntimeCode (ConcreteRuntimeCode _) -> Just addr
        _ -> Nothing
    runAllPaths val = do
        assign #result Nothing
        pushTo #constraints $ Expr.simplifyProp (addrExpr .== val)
        continue (forceEWordToEAddr val)

forceAddr :: forall t . (?conf :: Config, VMOps t, Typeable t) =>
  Expr EWord
  -> (Expr EWord -> EVM t ())
  -> (Expr EAddr -> EVM t ())
  -> EVM t ()
forceAddr addrExpr fallback continue = case wordToAddr addrExpr of
  Nothing -> manySolutions (?conf).maxDepth addrExpr 20 $ \case
    Just sol -> continue $ LitAddr (truncateToAddr sol)
    Nothing -> onlyDeployed addrExpr fallback continue
  Just c -> continue c


unexpectedSymArg :: (Typeable a, VMOps t) => String -> [Expr a] -> EVM t ()
unexpectedSymArg msg n = do
  pc <- use (#state % #pc)
  state <- use #state
  let opName = getOpName state
  partial $ UnexpectedSymbolicArg pc state.contract opName msg (wrap n)

unexpectedSymArgW :: (Typeable a, VMOps t) => String -> Expr a -> EVM t ()
unexpectedSymArgW msg n = unexpectedSymArg msg [n]

unknownCode :: VMOps t => Expr EAddr -> EVM t ()
unknownCode n = unexpectedSymArg "call target has unknown code" [n]

freshBufFallback :: (?conf :: Config, VMOps t, ?op :: Word8) => [Expr EWord] -> EVM t ()
freshBufFallback xs = do
  -- Reset caller if needed
  resetCaller <- use $ #state % #resetCaller
  when resetCaller $ assign (#state % #overrideCaller) Nothing
  -- overapproximate by returning a symbolic value
  freshVar <- use #freshVar
  assign #freshVar (freshVar + 1)
  let opName = pack $ show $ getOp ?op
  let freshVarExpr = Var (opName <> "-result-stack-fresh-" <> (pack . show) freshVar)
  modifying #constraints ((:) (PLEq freshVarExpr (Lit 1) ))
  let freshReturndataExpr = AbstractBuf (opName <> "-result-data-fresh-" <> (pack . show) freshVar)
  modifying #constraints ((:) (PLEq (bufLength freshReturndataExpr) (Lit (2 ^ ?conf.maxBufSize))))
  assign (#state % #returndata) freshReturndataExpr
  next >> assign' (#state % #stack) (freshVarExpr:xs)

freshVarFallback:: (VMOps t, ?op :: Word8) => [Expr EWord] -> Expr a -> EVM t ()
freshVarFallback xs _ = do
  -- Reset caller if needed
  resetCaller <- use $ #state % #resetCaller
  when resetCaller $ assign (#state % #overrideCaller) Nothing
  -- overapproximate by returning a symbolic value
  freshVar <- use #freshVar
  assign #freshVar (freshVar + 1)
  let opName = pack $ show $ getOp ?op
  let freshVarExpr = Var (opName <> "-result-stack-fresh-" <> (pack . show) freshVar)
  next >> assign' (#state % #stack) (freshVarExpr:xs)

forceConcrete :: (?conf :: Config, VMOps t) => Expr EWord -> String -> (W256 -> EVM t ()) -> EVM t ()
forceConcrete n = forceConcreteLimitSz n 32

forceConcreteLimitSz :: (?conf :: Config, VMOps t) => Expr EWord -> Int -> String -> (W256 -> EVM t ()) -> EVM t ()
forceConcreteLimitSz n bytes msg continue = case maybeLitWordSimp n of
  Nothing -> manySolutions (?conf).maxDepth n bytes $ maybe fallback continue
  Just c -> continue c
  where fallback = unexpectedSymArg msg [n]

forceConcreteAddr :: (?conf :: Config, VMOps t) => Expr EAddr -> String -> (Addr -> EVM t ()) -> EVM t ()
forceConcreteAddr n msg continue = case maybeLitAddrSimp n of
  Nothing -> manySolutions (?conf).maxDepth (WAddr n) 20 $ maybe fallback $ \c -> continue (truncateToAddr c)
  Just c -> continue c
  where fallback = unexpectedSymArg msg [n]

forceConcreteAddr2 :: VMOps t => (Expr EAddr, Expr EAddr) -> String -> ((Addr, Addr) -> EVM t ()) -> EVM t ()
forceConcreteAddr2 (n,m) msg continue = case (maybeLitAddrSimp n, maybeLitAddrSimp m) of
  (Just c, Just d) -> continue (c,d)
  _ -> unexpectedSymArg msg [n, m]

forceConcrete2 :: VMOps t => (Expr EWord, Expr EWord) -> String -> ((W256, W256) -> EVM t ()) -> EVM t ()
forceConcrete2 (n,m) msg continue = case (maybeLitWordSimp n, maybeLitWordSimp m) of
  (Just c, Just d) -> continue (c, d)
  _ -> unexpectedSymArg msg [n, m]

forceConcreteBuf :: VMOps t => Expr Buf -> String -> (ByteString -> EVM t ()) -> EVM t ()
forceConcreteBuf (ConcreteBuf b) _ continue = continue b
forceConcreteBuf b msg _ = unexpectedSymArg msg [b]

-- * Substate manipulation
refund :: Word64 -> EVM t ()
refund n = do
  self <- use (#state % #contract)
  pushTo (#tx % #subState % #refunds) (self, n)

unRefund :: Word64 -> EVM t ()
unRefund n = do
  self <- use (#state % #contract)
  refs <- use (#tx % #subState % #refunds)
  assign (#tx % #subState % #refunds)
    (filter (\(a,b) -> not (a == self && b == n)) refs)

touchAccount :: Expr EAddr -> EVM t ()
touchAccount = pushTo ((#tx % #subState) % #touchedAccounts)

selfdestruct :: Expr EAddr -> EVM t ()
selfdestruct = pushTo ((#tx % #subState) % #selfdestructs)

accessAndBurn :: VMOps t => Expr EAddr -> EVM t () -> EVM t ()
accessAndBurn x cont = do
  FeeSchedule {..} <- use (#block % #schedule)
  acc <- accessAccountForGas x
  let cost = if acc then g_warm_storage_read else g_cold_account_access
  burn cost cont

-- | returns a wrapped boolean- if true, this address has been touched before in the txn (warm gas cost as in EIP 2929)
-- otherwise cold
accessAccountForGas :: Expr EAddr -> EVM t Bool
accessAccountForGas addr = do
  accessedAddrs <- use (#tx % #subState % #accessedAddresses)
  let accessed = member addr accessedAddrs
  assign (#tx % #subState % #accessedAddresses) (insert addr accessedAddrs)
  pure accessed

-- | returns a wrapped boolean- if true, this slot has been touched before in the txn (warm gas cost as in EIP 2929)
-- otherwise cold
accessStorageForGas :: Expr EAddr -> W256 -> EVM t Bool
accessStorageForGas addr key = do
  accessedStrkeys <- use (#tx % #subState % #accessedStorageKeys)
  let accessed = member (addr, key) accessedStrkeys
  unless accessed $ assign (#tx % #subState % #accessedStorageKeys) (insert (addr, key) accessedStrkeys)
  pure accessed

-- * Cheat codes

-- The cheat code is 7109709ecfa91a80626ff3989d68f67f5b1dd12d.
-- Call this address using one of the cheatActions below to do
-- special things, e.g. changing the block timestamp. Beware that
-- these are necessarily hevm specific.
cheatCode :: Expr EAddr
cheatCode = LitAddr $ unsafeInto (keccak' "hevm cheat code")

cheat
  :: forall t . (?conf :: Config, ?op :: Word8, VMOps t, Typeable t)
  => Gas t -> (Expr EWord, Expr EWord) -> (Expr EWord, Expr EWord) -> [Expr EWord]
  -> EVM t ()
cheat gas (inOffset, inSize) (outOffset, outSize) xs = do
  vm <- get
  input <- readMemory (Expr.add inOffset (Lit 4)) (Expr.sub inSize (Lit 4))
  calldata <- readMemory inOffset inSize
  abi <- readBytes 4 (Lit 0) <$> readMemory inOffset (Lit 4)
  let newContext = CallContext cheatCode cheatCode outOffset outSize (Lit 0) (maybeLitWordSimp abi) calldata vm.env.contracts vm.tx.subState

  pushTrace $ FrameTrace newContext
  next
  vm1 <- get
  burn' gas $ pushTo #frames $ Frame
                    { state = vm1.state { stack = xs }
                    , context = newContext
                    }
  case maybeLitWordSimp abi of
    -- 4-byte function selector
    Nothing -> manySolutions (?conf).maxDepth abi 4 $ \case
      Just concAbi -> runCheat concAbi input
      Nothing -> unexpectedSymArg "symbolic cheatcode selector" [abi]
    Just concAbi -> runCheat concAbi input
  where
    runCheat :: W256 -> Expr 'Buf -> EVM t ()
    runCheat abi input =  do
      let abi' = unsafeInto abi
      case Map.lookup abi' cheatActions of
        Nothing -> do
          vm <- get
          whenSymbolicElse (partial $ CheatCodeMissing vm.state.pc vm.state.contract abi') (vmError $ BadCheatCode "Cannot understand cheatcode." abi')
        Just action -> action input

type CheatAction t = Expr Buf -> EVM t ()

cheatActions :: (?conf :: Config, VMOps t, Typeable t) => Map FunctionSelector (CheatAction t)
cheatActions = Map.fromList
  [ action "ffi(string[])" $
      \sig input -> do
        vm <- get
        if vm.config.allowFFI then
          case decodeBuf [AbiArrayDynamicType AbiStringType] input of
            (CAbi valsArr,"") -> case valsArr of
              [AbiArrayDynamic AbiStringType strsV] ->
                let
                  cmd = fmap
                          (\case
                            (AbiString a) -> toString a
                            _ -> "")
                          (V.toList strsV)
                  cont bs = continueOnce $ do
                    frameReturnBuf bs
                in query (PleaseDoFFI cmd vm.osEnv cont)
              _ -> vmError (BadCheatCode "ffi(string[]) decoding of string failed" sig)
            _ -> vmError (BadCheatCode "ffi(string[]) parameter decoding failed" sig)
        else vmError $ BadCheatCode "ffi disabled: run again with --ffi if you want to allow tests to call external scripts" sig

  , action "warp(uint256)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [x]  -> do
          assign (#block % #timestamp) x
          doStop
        _ -> vmError (BadCheatCode "warp(uint256) parameter decoding failed" sig)

  , action "deal(address,uint256)" $
      \sig input -> case decodeStaticArgs 0 2 input of
        [a, amt] ->
          forceAddr a (unexpectedSymArgW "vm.deal: cannot decode target into an address") $ \usr ->
            fetchAccount usr $ \_ -> do
              assign (#env % #contracts % ix usr % #balance) amt
              doStop
        _ -> vmError (BadCheatCode "deal(address,uint256) parameter decoding failed" sig)

  , action "assume(bool)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [c] -> do
          whenSymbolicElse (modifying #constraints ((:) (PEq (Lit 1) c)) >> doStop) $ do
            case c of
              Lit v -> if (v == 0) then (terminateVMWithError AssumeCheatFailed) else doStop
              _ -> internalError "Symbolic value encountered in concrete mode"
        _ -> vmError (BadCheatCode "assume(bool) parameter decoding failed." sig)

  , action "roll(uint256)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [x] -> do
          assign (#block % #number) x
          doStop
        _ -> vmError (BadCheatCode "roll(uint256) parameter decoding failed" sig)

  , action "store(address,bytes32,bytes32)" $
      \sig input -> case decodeStaticArgs 0 3 input of
        [a, slot, new] -> case wordToAddr a of
          Just a'@(LitAddr _) -> fetchAccount a' $ \_ -> do
            modifying (#env % #contracts % ix a' % #storage) (writeStorage slot new)
            doStop
          _ -> vmError (BadCheatCode "store(address,bytes32,bytes32) issue, address provided may not be an address?" sig)
        _ -> vmError (BadCheatCode "store(address,bytes32,bytes32) parameter decoding failed" sig)

  , action "load(address,bytes32)" $
      \sig input -> case decodeStaticArgs 0 2 input of
        [a, slot] -> case wordToAddr a of
          Just a'@(LitAddr _) -> fetchAccount a' $ \_ ->
            accessStorage a' slot $ \res -> do
              let buf = writeWord (Lit 0) res (ConcreteBuf "")
              frameReturnExpr buf -- TODO reivew
          _ -> vmError (BadCheatCode "load(address,bytes32) issue, maybe the address provided is not correct?" sig)
        _ -> vmError (BadCheatCode "load(address,bytes32) parameter decoding failed" sig)

  , action "sign(uint256,bytes32)" $
      \sig input -> case decodeStaticArgs 0 2 input of
        [sk, hash] ->
          forceConcrete2 (sk, hash) "cannot sign symbolic data" $ \(sk', hash') -> do
            let (v,r,s) = EVM.Sign.sign hash' (into sk')
                result = AbiTuple $
                  V.fromList
                    [ AbiUInt 8 $ into v
                    , AbiBytes 32 (word256Bytes r)
                    , AbiBytes 32 (word256Bytes s)
                    ]
            frameReturn result -- TODO ??
        _ -> vmError (BadCheatCode "sign(uint256,bytes32) parameter decoding failed" sig)

  , action "addr(uint256)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [sk] -> forceConcrete sk "cannot derive address for a symbolic key" $ \sk' -> do
          case EVM.Sign.deriveAddr $ into sk' of
            Nothing -> vmError (BadCheatCode "addr(uint256) could not derive address" sig)
            Just address -> do frameReturnBuf $ word256Bytes (into address) -- TODO ??
        _ -> vmError (BadCheatCode "addr(uint256) parameter decoding failed" sig)

  , action "prank(address)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [addr]  -> case wordToAddr addr of
          Just a -> do
            doStop
            assign (#state % #overrideCaller) (Just a)
            assign (#state % #resetCaller) True
          Nothing -> vmError (BadCheatCode "prank(address), could not decode address provided" sig)
        _ -> vmError (BadCheatCode "prank(address) parameter decoding failed" sig)

  , action "startPrank(address)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [addr]  -> case wordToAddr addr of
          Just a -> do
            doStop
            assign (#state % #overrideCaller) (Just a)
            assign (#state % #resetCaller) False
          Nothing -> vmError (BadCheatCode "startPrank(address), could not decode address provided" sig)
        _ -> vmError (BadCheatCode "startPrank(address) parameter decoding failed" sig)

  , action "stopPrank()" $
      \_ _ -> do
        doStop
        assign (#state % #overrideCaller) Nothing
        assign (#state % #resetCaller) False

  , action "createFork(string)" $
      \sig input -> case decodeBuf [AbiStringType] input of
        (CAbi valsArr,"") -> case valsArr of
          [AbiString bytes] -> do
            forkId <- length <$> gets (.forks)
            let urlOrAlias = Char8.unpack bytes
            modify' $ \vm -> vm { forks = vm.forks Seq.|> ForkState vm.env vm.block vm.pathsVisited urlOrAlias }
            frameReturn $ AbiUInt 256 (fromIntegral forkId)
          _ -> vmError (BadCheatCode "createFork(string) string provided may be incorrect?" sig)
        _ -> vmError (BadCheatCode "createFork(string) parameter decoding failed" sig)

  , action "selectFork(uint256)" $
      \sig input -> case decodeStaticArgs 0 1 input of
        [forkId] ->
          forceConcrete forkId "forkId of 'selectFork' must be concrete" $ \(fromIntegral -> forkId') -> do
            saved <- Seq.lookup forkId' <$> gets (.forks)
            case saved of
              Just forkState -> do
                vm <- get
                let contractAddr = vm.state.contract
                let callerAddr = vm.state.caller
                fetchAccount contractAddr $ \contractAcct -> fetchAccount callerAddr $ \callerAcct -> do
                  let
                    -- the current contract is persisted across forks
                    newContracts = Map.insert callerAddr callerAcct $
                                   Map.insert contractAddr contractAcct forkState.env.contracts
                    newEnv = (forkState.env :: Env) { contracts = newContracts }

                  when (vm.currentFork /= forkId') $ do
                    modify' $ \vm' -> vm'
                      { env = newEnv
                      , block = forkState.block
                      , forks = Seq.adjust' (\state -> (state :: ForkState)
                          { env = vm.env, block = vm.block, pathsVisited = vm.pathsVisited }
                        ) vm.currentFork  vm.forks
                      , currentFork = forkId'
                      }
                  doStop
              Nothing ->
                vmError (NonexistentFork forkId')
        _ -> vmError (BadCheatCode "selectFork(uint256) parameter decoding failed" sig)

  , action "activeFork()" $
      \_ _ -> do
        vm <- get
        frameReturn $ AbiUInt 256 (fromIntegral vm.currentFork)

  , action "label(address,string)" $
      \sig input -> case decodeBuf [AbiAddressType, AbiStringType] input of
        (CAbi valsArr,"") -> case valsArr of
          [AbiAddress addr, AbiString label] -> do
            #labels %= Map.insert addr (decodeUtf8 label)
            doStop
          _ -> vmError (BadCheatCode "label(address,string) address decoding failed" sig)
        _ -> vmError (BadCheatCode "label(address,string) parameter decoding failed" sig)

  , action "setEnv(string,string)" $
      \sig input -> case decodeBuf [AbiStringType, AbiStringType] input of
        (CAbi valsArr,"") -> case valsArr of
          [AbiString variable, AbiString value] -> do
            let (varStr, varVal) = (toString variable, toString value)
            #osEnv %= Map.insert varStr varVal
            doStop
          _ -> vmError (BadCheatCode "setEnv(string,string) address decoding failed" sig)
        _ -> vmError (BadCheatCode "setEnv(string,string) parameter decoding failed" sig)

  , action "etch(address,bytes)" $
      \sig input ->  case decodeBuf [AbiAddressType, AbiBytesDynamicType] input of
        (CAbi [AbiAddress addr, AbiBytesDynamic bytes],"") -> fetchAccount (LitAddr addr) $ \_ -> do
            replaceCodeEtch (LitAddr addr) (RuntimeCode (ConcreteRuntimeCode bytes))
            doStop
        _ -> vmError (BadCheatCode "etch(address,bytes) address decoding failed" sig)

  -- Single-value environment read cheat actions
  , $(envReadSingleCheat "envBool(string)") AbiBool stringToBool
  , $(envReadSingleCheat "envUint(string)") (AbiUInt 256) stringToWord256
  , $(envReadSingleCheat "envInt(string)") (AbiInt 256) stringToInt256
  , $(envReadSingleCheat "envAddress(string)") AbiAddress stringToAddress
  , $(envReadSingleCheat "envBytes32(string)") (AbiBytes 32) stringToBytes32
  , $(envReadSingleCheat "envString(string)") (\x -> AbiTuple $ V.fromList [AbiString x]) stringToByteString
  , $(envReadSingleCheat "envBytes(bytes)") (\x -> AbiTuple $ V.fromList [AbiBytesDynamic x]) stringHexToByteString

  -- Multi-value environment read cheat actions
  , $(envReadMultipleCheat "envBool(string,string)" AbiBoolType) stringToBool
  , $(envReadMultipleCheat "envUint(string,string)" $ AbiUIntType 256) stringToWord256
  , $(envReadMultipleCheat "envInt(string,string)" $ AbiIntType 256) stringToInt256
  , $(envReadMultipleCheat "envAddress(string,string)" AbiAddressType) stringToAddress
  , $(envReadMultipleCheat "envBytes32(string,string)" $ AbiBytesType 32) stringToBytes32
  , $(envReadMultipleCheat "envString(string,string)" AbiStringType) stringToByteString
  , $(envReadMultipleCheat "envBytes(bytes,bytes)" AbiBytesDynamicType) stringHexToByteString
  , action "assertTrue(bool)" $ \sig input ->
      case decodeBuf [AbiBoolType] input of
        (CAbi [AbiBool True],"") -> doStop
        (CAbi [AbiBool False],"") -> frameRevert "assertion failed"
        (SAbi [eword],"") -> case (Expr.simplify (Expr.iszero eword)) of
          Lit 1 -> frameRevert "assertion failed"
          Lit 0 -> doStop
          ew -> branch (?conf).maxDepth ew $ \case
            True -> frameRevert "assertion failed"
            False -> doStop
        k -> vmError $ BadCheatCode ("assertTrue(bool) parameter decoding failed: " <> show k) sig
  , action "assertFalse(bool)" $ \sig input ->
      case decodeBuf [AbiBoolType] input of
        (CAbi [AbiBool False],"") -> doStop
        (CAbi [AbiBool True],"") -> frameRevert "assertion failed"
        (SAbi [eword],"") -> case (Expr.simplify (Expr.iszero eword)) of
          Lit 0 -> frameRevert "assertion failed"
          Lit 1 -> doStop
          ew -> branch (?conf).maxDepth ew $ \case
            False -> frameRevert "assertion failed"
            True -> doStop
        k -> vmError $ BadCheatCode ("assertFalse(bool) parameter decoding failed: " <> show k) sig
  , action "assertEq(bool,bool)"       $ assertEq AbiBoolType
  , action "assertEq(uint256,uint256)" $ assertEq (AbiUIntType 256)
  , action "assertEq(int256,int256)"   $ assertEq (AbiIntType 256)
  , action "assertEq(address,address)" $ assertEq AbiAddressType
  , action "assertEq(bytes32,bytes32)" $ assertEq (AbiBytesType 32)
  , action "assertEq(string,string)"   $ assertEq (AbiStringType)
  --
  , action "assertNotEq(bool,bool)"       $ assertNotEq AbiBoolType
  , action "assertNotEq(uint256,uint256)" $ assertNotEq (AbiUIntType 256)
  , action "assertNotEq(int256,int256)"   $ assertNotEq (AbiIntType 256)
  , action "assertNotEq(address,address)" $ assertNotEq AbiAddressType
  , action "assertNotEq(bytes32,bytes32)" $ assertNotEq (AbiBytesType 32)
  , action "assertNotEq(string,string)"   $ assertNotEq (AbiStringType)
  --
  , action "assertLt(uint256,uint256)" $ assertLt (AbiUIntType 256)
  , action "assertLt(int256,int256)"   $ assertSLt (AbiIntType 256)
  , action "assertLe(uint256,uint256)" $ assertLe (AbiUIntType 256)
  , action "assertLe(int256,int256)"   $ assertSLe (AbiIntType 256)
  , action "assertGt(uint256,uint256)" $ assertGt (AbiUIntType 256)
  , action "assertGt(int256,int256)"   $ assertSGt (AbiIntType 256)
  , action "assertGe(uint256,uint256)" $ assertGe (AbiUIntType 256)
  , action "assertGe(int256,int256)"   $ assertSGe (AbiIntType 256)
  --
  , action "toString(address)" $ toStringCheat AbiAddressType
  , action "toString(bool)"    $ toStringCheat AbiBoolType
  , action "toString(uint256)" $ toStringCheat (AbiUIntType 256)
  , action "toString(int256)"  $ toStringCheat (AbiIntType 256)
  , action "toString(bytes32)" $ toStringCheat (AbiBytesType 32)
  , action "toString(bytes)"   $ toStringCheat AbiBytesDynamicType
  ]
  where
    action s f = (abiKeccak s, f (abiKeccak s))
    either' v l r = either l r v
    frameReturn :: VMOps t => AbiValue -> EVM t ()
    frameReturn v = frameReturnBuf $ encodeAbiValue v
    frameReturnBuf :: VMOps t => ByteString -> EVM t ()
    frameReturnBuf buf = frameReturnExpr $ ConcreteBuf buf
    frameReturnExpr :: VMOps t => Expr Buf -> EVM t ()
    frameReturnExpr e = finishFrame (FrameReturned e)
    frameRevert :: VMOps t => ByteString -> EVM t ()
    frameRevert err = finishFrame (FrameReverted $ errorMsg err)
    errorMsg :: ByteString -> Expr Buf
    errorMsg err = ConcreteBuf $ selector "Error(string)" <> encodeAbiValue (AbiTuple $ V.fromList [AbiString err])
    continueOnce cont = do
      assign #result Nothing
      cont
    doStop = finishFrame (FrameReturned mempty)
    toString = unpack . decodeUtf8
    strip0x s = if "0x" `isPrefixOf` s then drop 2 s else s
    stringToBool :: String -> Either ByteString Bool
    stringToBool s = case s of
      "true" -> Right True
      "True" -> Right True
      "false" -> Right False
      "False" -> Right False
      _ -> Left "invalid value"
    stringToWord256 :: String -> Either ByteString Word256
    stringToWord256 s = maybeToEither "invalid W256 value" $ readMaybe s
    stringToInt256 :: String -> Either ByteString Int256
    stringToInt256 s = maybeToEither "invalid Int256 value" $ readMaybe s
    stringToAddress :: String -> Either ByteString Addr
    stringToAddress s = fmap Addr $ maybeToEither "invalid address value" $ readMaybe s
    stringToBytes32 :: String -> Either ByteString ByteString
    stringToBytes32 s = fmap word256Bytes $ maybeToEither "invalid bytes32 value" $ readMaybe s
    stringToByteString :: String -> Either ByteString ByteString
    stringToByteString = Right . Char8.pack
    stringHexToByteString :: String -> Either ByteString ByteString
    stringHexToByteString s = either (const $ Left "invalid bytes value") Right $ BS16.decodeBase16Untyped . Char8.pack . strip0x $ s
    paramDecodeErr abitype name abivals = name <> "(" <> (show abitype) <> "," <> (show abitype) <>
      ")  parameter decoding failed. Error: " <> show abivals
    revertErr a b comp = frameRevert $ "assertion failed: " <>
      BS8.pack (show a) <> " " <> comp <> " " <> BS8.pack (show b)
    genAssert comp exprComp invComp name abitype sig input = do
      case decodeBuf [abitype, abitype] input of
        (CAbi [a, b],"") | a `comp` b -> doStop
        (CAbi [a, b],"")-> revertErr a b invComp
        (SAbi [ew1, ew2],"") -> case (Expr.simplify (Expr.iszero $ exprComp ew1 ew2)) of
          Lit 0 -> doStop
          Lit _ -> revertErr ew1 ew2 invComp
          ew -> branch (?conf).maxDepth ew $ \case
            False -> doStop
            True -> revertErr ew1 ew2 invComp
        abivals -> vmError (BadCheatCode (paramDecodeErr abitype name abivals) sig)
    assertEq =    genAssert (==) Expr.eq "!=" "assertEq"
    assertNotEq = genAssert (/=) (\a b -> Expr.iszero $ Expr.eq a b) "==" "assertNotEq"
    assertLt =    genAssert (<)  Expr.lt ">=" "assertLt"
    assertSLt =   genAssert (<)  Expr.slt ">=" "assertLt"
    assertGt =    genAssert (>)  Expr.gt "<=" "assertGt"
    assertSGt =   genAssert (>)  Expr.sgt "<=" "assertGt"
    assertLe =    genAssert (<=) Expr.leq ">" "assertLe"
    assertSLe =   genAssert (<=) (\a b -> Expr.iszero $ Expr.sgt a b) ">" "assertLe"
    assertGe =    genAssert (>=) Expr.geq "<" "assertGe"
    assertSGe =   genAssert (>=) (\a b -> Expr.iszero $ Expr.slt a b) "<" "assertGe"
    toStringCheat abitype sig input = do
      case decodeBuf [abitype] input of
        (CAbi [val],"") -> frameReturn $ AbiTuple $ V.fromList [AbiString $ Char8.pack $ show val]
        _ -> vmError (BadCheatCode ("toString parameter decoding failed for " <> show abitype) sig)

-- * General call implementation ("delegateCall")
-- note that the continuation is ignored in the precompile case
delegateCall
  :: forall t . (VMOps t, ?op :: Word8, ?conf :: Config, Typeable t)
  => Contract
  -> Gas t
  -> Expr EAddr
  -> Expr EAddr
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> [Expr EWord]
  -> (Expr EAddr -> EVM t ()) -- fallback
  -> (Expr EAddr -> EVM t ()) -- continue
  -> EVM t ()
delegateCall this gasGiven xTo xContext xValue xInOffset xInSize xOutOffset xOutSize xs fallback continue
  | isPrecompileAddr xTo
      = forceConcreteAddr2 (xTo, xContext) "Cannot call precompile with symbolic addresses" $
          \(xTo', xContext') ->
            precompiledContract this gasGiven xTo' xContext' xValue xInOffset xInSize xOutOffset xOutSize xs
  | xTo == cheatCode = do
      cheat gasGiven (xInOffset, xInSize) (xOutOffset, xOutSize) xs
  | otherwise =
      callChecks this gasGiven xContext xTo xValue xInOffset xInSize xOutOffset xOutSize xs $
        \xGas -> do
          resetCaller <- use $ #state % #resetCaller
          when resetCaller $ assign (#state % #overrideCaller) Nothing
          vm0 <- get
          fetchAccountWithFallback xTo (betterFallback xGas vm0) $ \target -> case target.code of
              UnknownCode _ -> betterFallback xGas vm0 xTo
              _ -> actualCall target xTo xGas vm0
  where
    betterFallback :: Gas t -> (VM t) -> Expr 'EAddr -> EVM t ()
    betterFallback xGas vm0 addr = onlyDeployed (forceEAddrToEWord addr) (fallback . forceEWordToEAddr) $ \a -> do
        let target = fromJust $ Map.lookup a vm0.env.contracts
        actualCall target a xGas vm0
    actualCall target addr xGas vm0 = do
        burn' xGas $ do
          calldata <- readMemory xInOffset xInSize
          abi <- maybeLitWordSimp . readBytes 4 (Lit 0) <$> readMemory xInOffset (Lit 4)
          -- EIP-7702: Resolve delegation if target has delegation code
          let (resolvedCode, codeAddr) = resolveDelegatedCode target addr vm0.env.contracts
              -- Check if target had delegation code (even if self-delegating)
              hasDelegation = isJust $ getDelegationTarget target.code
          -- EIP-7702: If delegation was resolved, charge access cost for the delegation target
          -- "If a code executing instruction accesses a cold account during the
          -- resolution of delegated code, add an additional COLD_ACCOUNT_READ_COST"
          -- Note: For self-delegation, codeAddr == addr but we still charge (warm access = 100)
          let finishCall = do
                let newContext = CallContext
                              { target    = addr
                              , context   = xContext
                              , offset    = xOutOffset
                              , size      = xOutSize
                              , codehash  = target.codehash
                              , callreversion = vm0.env.contracts
                              , subState  = vm0.tx.subState
                              , abi
                              , calldata
                              }
                pushTrace (FrameTrace newContext)
                next
                vm1 <- get
                pushTo #frames $ Frame
                  { state = vm1.state { stack = xs }
                  , context = newContext
                  }

                let clearInitCode = \case
                      (InitCode _ _) -> InitCode mempty mempty
                      a -> a

                newMemory <- ConcreteMemory <$> VS.Mutable.new 0
                zoom #state $ do
                  assign #gas xGas
                  assign #pc 0
                  -- EIP-7702: Use resolved code (possibly from delegated address)
                  assign #code (clearInitCode resolvedCode)
                  assign #codeContract codeAddr
                  assign #stack mempty
                  assign #memory newMemory
                  assign #memorySize 0
                  assign #returndata mempty
                  assign #calldata calldata
                  assign #overrideCaller Nothing
                  assign #resetCaller False
                continue addr
          -- Charge access cost for delegation target when delegation exists
          -- (even for self-delegation where codeAddr == addr)
          if hasDelegation
            then accessAndBurn codeAddr finishCall
            else finishCall

-- -- * Contract creation

-- EIP-684 and EIP-7610: collision if nonce != 0, code is non-empty, or storage is non-empty
collision :: Maybe Contract -> Bool
collision c' = case c' of
  Just c -> c.nonce /= Just 0 || not (isStorageEmpty c.storage) || case c.code of
    RuntimeCode (ConcreteRuntimeCode "") -> False
    RuntimeCode (SymbolicRuntimeCode b) -> not $ null b
    _ -> True
  Nothing -> False
  where
    isStorageEmpty :: Expr Storage -> Bool
    isStorageEmpty = \case
      ConcreteStore m -> Map.null m
      AbstractStore _ _ -> True -- empty symbolic store
      SStore _ _ _ -> False     -- has writes, so non-empty
      GVar _ -> internalError "unexpected global variable"

create :: forall t. (?op :: Word8, ?conf::Config, VMOps t)
  => Expr EAddr -> Contract
  -> Expr EWord -> Gas t -> Expr EWord -> [Expr EWord] -> Expr EAddr -> Expr Buf -> EVM t ()
create self this xSize xGas xValue xs newAddr initCode = do
  vm0 <- get
  -- are we exceeding the max init code size
  if xSize > Lit (vm0.block.maxCodeSize * 2)
  then do
    assign' (#state % #stack) (Lit 0 : xs)
    assign (#state % #returndata) mempty
    vmError $ MaxInitCodeSizeExceeded (vm0.block.maxCodeSize * 2) xSize
  -- are we overflowing the nonce
  else if this.nonce == Just maxBound
  then do
    assign' (#state % #stack) (Lit 0 : xs)
    assign (#state % #returndata) mempty
    pushTrace $ ErrorTrace NonceOverflow
    next
  -- are we overflowing the stack
  else if length vm0.frames >= 1024
  then do
    assign' (#state % #stack) (Lit 0 : xs)
    assign (#state % #returndata) mempty
    pushTrace $ ErrorTrace CallDepthLimitReached
    next
  -- are we deploying to an address that already has a contract?
  -- note: the symbolic interpreter generates constraints ensuring that
  -- symbolic storage keys cannot alias other storage keys, making this check
  -- safe to perform statically
  else if collision $ Map.lookup newAddr vm0.env.contracts
  then burn' xGas $ do
    assign' (#state % #stack) (Lit 0 : xs)
    assign (#state % #returndata) mempty
    modifying (#env % #contracts % ix self % #nonce) (fmap ((+) 1))
    next
  -- do we have enough balance
  else branch (?conf).maxDepth (Expr.gt xValue this.balance) $ \case
      True -> do
        assign' (#state % #stack) (Lit 0 : xs)
        assign (#state % #returndata) mempty
        pushTrace $ ErrorTrace $ BalanceTooLow xValue this.balance
        next
        touchAccount self
        touchAccount newAddr
      -- are we overflowing the nonce
      False -> burn' xGas $ do
        case parseInitCode initCode of
          Nothing -> unexpectedSymArg "initcode must have a concrete prefix" ([] :: [Expr EWord])
          Just c -> do
            let
              newContract = initialContract c
              newContext  =
                CreationContext { address   = newAddr
                                , codehash  = newContract.codehash
                                , createreversion = vm0.env.contracts
                                , subState  = vm0.tx.subState
                                }

            zoom (#env % #contracts) $ do
              oldAcc <- use (at newAddr)
              let oldBal = maybe (Lit 0) (.balance) oldAcc

              assign (at newAddr) (Just (newContract & #balance .~ oldBal))
              modifying (ix self % #nonce) (fmap ((+) 1))

            let
              resetStorage :: Expr Storage -> Expr Storage
              resetStorage = \case
                  ConcreteStore _ -> ConcreteStore mempty
                  AbstractStore a Nothing -> AbstractStore a Nothing
                  SStore _ _ p -> resetStorage p
                  AbstractStore _ (Just _) -> internalError "unexpected logical store in EVM.hs"
                  GVar _  -> internalError "unexpected global variable"

            modifying (#env % #contracts % ix newAddr % #storage) resetStorage
            modifying (#env % #contracts % ix newAddr % #origStorage) resetStorage
            modifying (#tx % #subState % #createdContracts) (insert newAddr)

            transfer self newAddr xValue

            pushTrace (FrameTrace newContext)
            next
            vm1 <- get
            pushTo #frames $ Frame
              { context = newContext
              , state   = vm1.state { stack = xs }
              }

            state :: FrameState t <- lift blankState
            assign #state $ state
              { contract     = newAddr
              , codeContract = newAddr
              , code         = c
              , callvalue    = xValue
              , caller       = self
              , gas          = xGas
              }

-- | Parses a raw Buf into an InitCode
--
-- solidity implements constructor args by appending them to the end of
-- the initcode. we support this internally by treating initCode as a
-- concrete region (initCode) followed by a potentially symbolic region
-- (arguments).
--
-- when constructing a contract that has symbolic constructor args, we
-- need to apply some heuristics to convert the (unstructured) initcode
-- in memory into this structured representation. The (unsound, bad,
-- hacky) way that we do this, is by: looking for the first potentially
-- symbolic byte in the input buffer and then splitting it there into code / data.
parseInitCode :: Expr Buf -> Maybe ContractCode
parseInitCode (ConcreteBuf b) = Just (InitCode b mempty)
parseInitCode buf = if V.null conc
                    then Nothing
                    else Just $ InitCode (BS.pack $ V.toList conc) sym
  where
    conc = Expr.concretePrefix buf
    -- unsafeInto: findIndex will always be positive
    sym = Expr.drop (unsafeInto (V.length conc)) buf

-- | Replace a contract's code, like when CREATE returns
-- from the constructor code.
replaceCode :: Expr EAddr -> ContractCode -> EVM t ()
replaceCode target newCode =
  zoom (#env % #contracts % at target) $
    get >>= \case
      Just now -> case now.code of
        InitCode _ _ ->
          put . Just $
            ((initialContract newCode) :: Contract)
              { balance = now.balance
              , nonce = now.nonce
              , storage = now.storage
              , tStorage = now.tStorage
              }
        RuntimeCode _ ->
          internalError $ "Can't replace code of deployed contract " <> show target
        UnknownCode _ ->
          internalError "Can't replace unknown code"
      Nothing ->
        internalError "Can't replace code of nonexistent contract"

replaceCodeEtch :: Expr EAddr -> ContractCode -> EVM t ()
replaceCodeEtch target newCode =
  zoom (#env % #contracts % at target) $
    get >>= \case
      Just now -> case now.code of
        InitCode _ _ -> internalError "Can't etch code of contract in init code phase"
        RuntimeCode _ -> do
          put . Just $
            ((now :: Contract)
              { code = newCode
              , codehash = hashcode newCode
              , opIxMap = mkOpIxMap newCode
              , codeOps = mkCodeOps newCode
              })
        UnknownCode _ -> internalError "Can't etch unknown code"
      Nothing -> put . Just $ initialContract newCode

replaceCodeOfSelf :: ContractCode -> EVM t ()
replaceCodeOfSelf newCode = do
  vm <- get
  replaceCode vm.state.contract newCode

resetState :: VMOps t => EVM t ()
resetState = do
  state <- lift blankState
  modify' $ \vm -> vm { result = Nothing, frames = [], state }

-- * VM error implementation

vmError :: VMOps t => EvmError -> EVM t ()
vmError e = finishFrame (FrameErrored e)

wrap :: Typeable a => [Expr a] -> [SomeExpr]
wrap = fmap SomeExpr

underrun :: VMOps t => EVM t ()
underrun = vmError StackUnderrun

-- | A stack frame can be popped in three ways.
data FrameResult
  = FrameReturned (Expr Buf) -- ^ STOP, RETURN, or no more code
  | FrameReverted (Expr Buf) -- ^ REVERT
  | FrameErrored EvmError -- ^ Any other error
  deriving Show

terminateVMWithError :: VMOps t => EvmError -> EVM t ()
terminateVMWithError err = do
  vm <- get
  case vm.frames of
    [] -> finishFrame (FrameErrored err)
    _ -> do
      finishFrame (FrameErrored err)
      terminateVMWithError err

finishAllFramesAndStop :: VMOps t => EVM t ()
finishAllFramesAndStop = do
  vm <- get
  case vm.frames of
    [] -> finishFrame (FrameReturned mempty)
    _ -> do
      finishFrame (FrameReturned mempty)
      finishAllFramesAndStop

-- | This function defines how to pop the current stack frame in either of
-- the ways specified by 'FrameResult'.
--
-- It also handles the case when the current stack frame is the only one;
-- in this case, we set the final '_result' of the VM execution.
finishFrame :: VMOps t => FrameResult -> EVM t ()
finishFrame how = do
  oldVm <- get

  case oldVm.frames of
    -- Is the current frame the only one?
    [] -> do
      case how of
          FrameReturned output -> assign #result . Just $ VMSuccess output
          FrameReverted buffer -> assign #result . Just $ VMFailure (Revert buffer)
          FrameErrored e       -> assign #result . Just $ VMFailure e
      finalize

    -- Are there some remaining frames?
    nextFrame : remainingFrames -> do

      -- Insert a debug trace.
      insertTrace $ case how of
        FrameReturned output -> ReturnTrace output nextFrame.context
        FrameReverted e -> ErrorTrace (Revert e)
        FrameErrored e -> ErrorTrace e
      -- Pop to the previous level of the debug trace stack.
      popTrace

      -- Pop the top frame.
      assign #frames remainingFrames
      -- Install the state of the frame to which we shall return.
      assign #state nextFrame.state

      -- Now dispatch on whether we were creating or calling,
      -- and whether we shall return, revert, or internalError(six cases).
      case nextFrame.context of

        -- Were we calling?
        CallContext _ _ outOffset outSize _ _ _ reversion subState' -> do

          -- Excerpt K.1. from the yellow paper:
          -- K.1. Deletion of an Account Despite Out-of-gas.
          -- At block 2675119, in the transaction 0xcf416c536ec1a19ed1fb89e4ec7ffb3cf73aa413b3aa9b77d60e4fd81a4296ba,
          -- an account at address 0x03 was called and an out-of-gas occurred during the call.
          -- Against the equation (197), this added 0x03 in the set of touched addresses, and this transaction turned σ[0x03] into ∅.

          -- In other words, we special case address 0x03 and keep it in the set of touched accounts during revert
          touched <- use (#tx % #subState % #touchedAccounts)

          let
            subState'' = over #touchedAccounts (maybe id cons (find (LitAddr 3 ==) touched)) subState'
            revertContracts = assign (#env % #contracts) reversion
            revertSubstate  = assign (#tx % #subState) subState''

          case how of
            -- Case 1: Returning from a call?
            FrameReturned output -> do
              assign (#state % #returndata) output
              copyCallBytesToMemory output outSize outOffset
              reclaimRemainingGasAllowance oldVm
              push 1

            -- Case 2: Reverting during a call?
            FrameReverted output -> do
              revertContracts
              revertSubstate
              assign (#state % #returndata) output
              copyCallBytesToMemory output outSize outOffset
              reclaimRemainingGasAllowance oldVm
              push 0

            -- Case 3: Error during a call?
            FrameErrored _ -> do
              revertContracts
              revertSubstate
              assign (#state % #returndata) mempty
              push 0
        -- Or were we creating?
        CreationContext _ _ reversion subState' -> do
          creator <- use (#state % #contract)
          let
            createe = oldVm.state.contract
            revertContracts = assign (#env % #contracts) reversion'
            revertSubstate  = assign (#tx % #subState) subState'

            -- persist the nonce through the reversion
            reversion' = (Map.adjust (over #nonce (fmap ((+) 1))) creator) reversion

          case how of
            -- Case 4: Returning during a creation?
            FrameReturned output -> do
              let onContractCode contractCode = do
                    replaceCode createe contractCode
                    assign (#state % #returndata) mempty
                    reclaimRemainingGasAllowance oldVm
                    pushAddr createe
              case output of
                ConcreteBuf bs ->
                  onContractCode $ RuntimeCode (ConcreteRuntimeCode bs)
                _ ->
                  case Expr.toList output of
                    Nothing -> partial $
                      UnexpectedSymbolicArg
                        oldVm.state.pc
                        oldVm.state.contract
                        (getOpName oldVm.state)
                        "runtime code cannot have an abstract length"
                        (wrap [output])
                    Just newCode -> do
                      onContractCode $ RuntimeCode (SymbolicRuntimeCode newCode)

            -- Case 5: Reverting during a creation?
            FrameReverted output -> do
              revertContracts
              revertSubstate
              assign (#state % #returndata) output
              reclaimRemainingGasAllowance oldVm
              push 0

            -- Case 6: Error during a creation?
            FrameErrored _ -> do
              revertContracts
              revertSubstate
              assign (#state % #returndata) mempty
              push 0


-- * Memory helpers

accessUnboundedMemoryRange
  :: VMOps t => Word64
  -> Word64
  -> EVM t ()
  -> EVM t ()
accessUnboundedMemoryRange _ 0 continue = continue
accessUnboundedMemoryRange f l continue = do
  m0 <- use (#state % #memorySize)
  fees <- gets (.block.schedule)
  let m1 = 32 * ceilDiv (max m0 (f + l)) 32
  burn (memoryCost fees m1 - memoryCost fees m0) $ do
    assign (#state % #memorySize) m1
    continue

accessMemoryRange
  :: VMOps t
  => Expr EWord
  -> Expr EWord
  -> EVM t ()
  -> EVM t ()
accessMemoryRange _ (Lit 0) continue = continue
accessMemoryRange (Lit offs) (Lit sz) continue =
  case (,) <$> toWord64 offs <*> toWord64 sz of
    Nothing -> vmError IllegalOverflow
    Just (offs64, sz64) ->
      if offs64 + sz64 < sz64
        then vmError IllegalOverflow
        -- we need to limit these to <256MB because otherwise we could run out of memory
        -- in e.g. OpCalldatacopy and subsequent memory allocation when running with abstract gas.
        -- In these cases, the system would try to allocate a large (but <2**64 bytes) memory
        -- that leads to out-of-heap. Real-world scenarios cannot allocate 256MB of memory due to gas
        else if offs64 >= 0x0fffffff || sz64 >= 0x0fffffff
             then vmError IllegalOverflow
             else accessUnboundedMemoryRange offs64 sz64 continue
-- we just ignore gas if we get symbolic inputs
accessMemoryRange _ _ continue = continue

accessMemoryWord
  :: VMOps t => Expr EWord -> EVM t () -> EVM t ()
accessMemoryWord x = accessMemoryRange x (Lit 32)

copyBytesToMemory
  :: Expr Buf -> Expr EWord -> Expr EWord -> Expr EWord -> EVM t ()
copyBytesToMemory bs size srcOffset memOffset =
  if size == Lit 0 then noop
  else do
    gets (.state.memory) >>= \case
      ConcreteMemory mem ->
        case (bs, size, srcOffset, memOffset) of
          (ConcreteBuf b, Lit size', Lit srcOffset', Lit memOffset') -> do
            let src =
                  if srcOffset' >= unsafeInto (BS.length b) then
                    BS.replicate (unsafeInto size') 0
                  else
                    BS.take (unsafeInto size') $
                    padRight (unsafeInto size') $
                    BS.drop (unsafeInto srcOffset') b

            writeMemory mem (unsafeInto memOffset') src
          _ -> do
            -- copy out and move to symbolic memory
            buf <- freezeMemory mem
            assign (#state % #memory) $
              SymbolicMemory $ copySlice srcOffset memOffset size bs buf
      SymbolicMemory mem ->
        assign (#state % #memory) $ SymbolicMemory $ copySlice srcOffset memOffset size bs mem

copyCallBytesToMemory
  :: Expr Buf -> Expr EWord -> Expr EWord -> EVM t ()
copyCallBytesToMemory bs size yOffset =
  copyBytesToMemory bs (Expr.min size (bufLength bs)) (Lit 0) yOffset

readMemory :: Expr EWord -> Expr EWord -> EVM t (Expr Buf)
readMemory offset' size' = do
  vm <- get
  case vm.state.memory of
    ConcreteMemory mem -> do
      case (offset', size') of
        (Lit offset, Lit size) -> do
          let memSize :: Word64 = unsafeInto (VS.Mutable.length mem)
          if size > Expr.maxBytes ||
             offset + size > Expr.maxBytes ||
             offset >= into memSize then
            -- reads past memory are all zeros
            pure $ ConcreteBuf $ BS.replicate (unsafeInto size) 0
          else do
            let pastEnd = (unsafeInto offset + unsafeInto size) - unsafeInto memSize
            let fromMemSize = if pastEnd > 0 then unsafeInto size - pastEnd else unsafeInto size

            buf <- VS.freeze $ VS.Mutable.slice (unsafeInto offset) fromMemSize mem
            let dataFromMem = vectorToByteString buf
            pure $ ConcreteBuf $ dataFromMem <> BS.replicate pastEnd 0
        _ -> do
          buf <- freezeMemory mem
          pure $ copySlice offset' (Lit 0) size' buf mempty
    SymbolicMemory mem ->
      pure $ copySlice offset' (Lit 0) size' mem mempty

-- * Tracing

withTraceLocation :: TraceData -> EVM t Trace
withTraceLocation x = do
  vm <- get
  let this = fromJust $ currentContract vm
  pure Trace
    { tracedata = x
    , contract = this
    , opIx = fromMaybe 0 $ this.opIxMap VS.!? vm.state.pc
    }

pushTrace :: TraceData -> EVM t ()
pushTrace x = do
  trace <- withTraceLocation x
  modifying #traces $
    \t -> Zipper.children $ Zipper.insert (Node trace []) t

insertTrace :: TraceData -> EVM t ()
insertTrace x = do
  trace <- withTraceLocation x
  modifying #traces $
    \t -> Zipper.nextSpace $ Zipper.insert (Node trace []) t

popTrace :: EVM t ()
popTrace =
  modifying #traces $
    \t -> case Zipper.parent t of
            Nothing -> internalError "internal internalError(trace root)"
            Just t' -> Zipper.nextSpace t'

zipperRootForest :: Zipper.TreePos Zipper.Empty a -> Forest a
zipperRootForest z =
  case Zipper.parent z of
    Nothing -> Zipper.toForest z
    Just z' -> zipperRootForest (Zipper.nextSpace z')

traceForest :: VM t -> Forest Trace
traceForest vm = zipperRootForest vm.traces

traceForest' :: Expr End -> Forest Trace
traceForest' (Success _ (TraceContext f _ _) _ _) = f
traceForest' (Partial _ (TraceContext f _ _) _) = f
traceForest' (Failure _ (TraceContext f _ _) _) = f
traceForest' (GVar {}) = internalError"Internal Error: Unexpected GVar"

traceContext :: Expr End -> TraceContext
traceContext (Success _ c _ _) = c
traceContext (Partial _ c _) = c
traceContext (Failure _ c _) = c
traceContext (GVar {}) = internalError"Internal Error: Unexpected GVar"

traceTopLog :: [Expr Log] -> EVM t ()
traceTopLog [] = noop
traceTopLog ((LogEntry addr bytes topics) : _) = do
  trace <- withTraceLocation (EventTrace addr bytes topics)
  modifying #traces $
    \t -> Zipper.nextSpace (Zipper.insert (Node trace []) t)
traceTopLog ((GVar _) : _) = internalError "unexpected global variable"

-- * Stack manipulation

push :: W256 -> EVM t ()
push = pushSym . Lit

pushSym :: Expr EWord -> EVM t ()
pushSym x = modifying' (#state % #stack) (x :)

pushAddr :: Expr EAddr -> EVM t ()
pushAddr (LitAddr x) = modifying' (#state % #stack) (Lit (into x) :)
pushAddr x@(SymAddr _) = modifying' (#state % #stack) (WAddr x :)
pushAddr (GVar _) = internalError "Unexpected GVar"

stackOp1
  :: (?op :: Word8, VMOps t)
  => Word64
  -> (Expr EWord -> Expr EWord)
  -> EVM t ()
stackOp1 cost f =
  use (#state % #stack) >>= \case
    x:xs ->
      burn cost $ do
        next
        let !y = f x
        assign' (#state % #stack) $ y : xs
    _ ->
      underrun

stackOp2
  :: (?op :: Word8, VMOps t)
  => Word64
  -> (Expr EWord -> Expr EWord -> Expr EWord)
  -> EVM t ()
stackOp2 cost f =
  use (#state % #stack) >>= \case
    x:y:xs ->
      burn cost $ do
        next
        assign' (#state % #stack) $ f x y : xs
    _ ->
      underrun

stackOp3
  :: (?op :: Word8, VMOps t)
  => Word64
  -> (Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord)
  -> EVM t ()
stackOp3 cost f =
  use (#state % #stack) >>= \case
    x:y:z:xs ->
      burn cost $ do
      next
      assign' (#state % #stack) $ f x y z : xs
    _ ->
      underrun

-- * Bytecode data functions

checkJump :: VMOps t => Int -> [Expr EWord] -> EVM t ()
checkJump x xs = noJumpIntoInitData x $ do
  vm <- get
  case isValidJumpDest vm x of
    True -> do
      assign' (#state % #stack) xs
      assign' (#state % #pc) x
    False -> vmError BadJumpDestination

-- fails with partial if we're trying to jump into the symbolic region of an `InitCode`
noJumpIntoInitData :: VMOps t => Int -> EVM t () -> EVM t ()
noJumpIntoInitData idx cont = do
  vm <- get
  case vm.state.code of
    -- init code is totally concrete, so we don't return partial if we're
    -- jumping beyond the range of `ops`
    InitCode _ (ConcreteBuf "") -> cont
    -- init code has a symbolic region, so check if we're trying to jump into
    -- the symbolic region and return partial if we are
    InitCode ops _ -> if idx > BS.length ops
                      then partial $ JumpIntoSymbolicCode vm.state.pc vm.state.contract idx
                      else cont
    -- we're not executing init code, so nothing to check here
    _ -> cont

isValidJumpDest :: VM t -> Int -> Bool
isValidJumpDest vm x = let
    code = vm.state.code
    self = vm.state.codeContract
    contract = fromMaybe
      (internalError "self not found in current contracts")
      (Map.lookup self vm.env.contracts)
    op = case code of
      UnknownCode _ -> internalError "Cannot analyze jumpdests for unknown code"
      InitCode ops _ -> BS.indexMaybe ops x
      RuntimeCode (ConcreteRuntimeCode ops) -> BS.indexMaybe ops x
      RuntimeCode (SymbolicRuntimeCode ops) -> ops V.!? x >>= maybeLitByteSimp
  in case op of
       Nothing -> False
       Just b -> 0x5b == b && (isJust $ contract.opIxMap VS.!? x)
         && (isJust $ contract.codeOps V.!? (contract.opIxMap VS.! x))
         && OpJumpdest == snd (contract.codeOps V.! (contract.opIxMap VS.! x))

opSize :: Word8 -> Int
opSize x | x >= 0x60 && x <= 0x7f = into x - 0x60 + 2
opSize _                          = 1

--  i of the resulting vector contains the operation index for
-- the program counter value i.  This is needed because source map
-- entries are per operation, not per byte.
mkOpIxMap :: ContractCode -> VS.Vector Int
mkOpIxMap (UnknownCode _) = internalError "Cannot build opIxMap for unknown code"
mkOpIxMap (InitCode conc _)
  = VS.create $ VS.Mutable.new (BS.length conc) >>= \v ->
      -- Loop over the byte string accumulating a vector-mutating action.
      -- This is somewhat obfuscated, but should be fast.
      let (_, _, _, m) = BS.foldl' (go v) (0 :: Word8, 0, 0, pure ()) conc
      in m >> pure v
      where
        -- concrete case
        go v (0, !i, !j, !m) x | x >= 0x60 && x <= 0x7f =
          {- Start of PUSH op. -} (x - 0x60 + 1, i + 1, j,     m >> VS.Mutable.write v i j)
        go v (1, !i, !j, !m) _ =
          {- End of PUSH op. -}   (0,            i + 1, j + 1, m >> VS.Mutable.write v i j)
        go v (0, !i, !j, !m) _ =
          {- Other op. -}         (0,            i + 1, j + 1, m >> VS.Mutable.write v i j)
        go v (n, !i, !j, !m) _ =
          {- PUSH data. -}        (n - 1,        i + 1, j,     m >> VS.Mutable.write v i j)

mkOpIxMap (RuntimeCode (ConcreteRuntimeCode ops)) =
  mkOpIxMap (InitCode ops mempty) -- a bit hacky

mkOpIxMap (RuntimeCode (SymbolicRuntimeCode ops))
  = VS.create $ VS.Mutable.new (length ops) >>= \v ->
      let (_, _, _, m) = foldl' (go v) (0, 0, 0, pure ()) (stripBytecodeMetadataSym $ V.toList ops)
      in m >> pure v
      where
        go v (0, !i, !j, !m) x = case maybeLitByteSimp x of
          Just x' -> if x' >= 0x60 && x' <= 0x7f
            -- start of PUSH op --
                     then (x' - 0x60 + 1, i + 1, j,     m >> VS.Mutable.write v i j)
            -- other data --
                     else (0,             i + 1, j + 1, m >> VS.Mutable.write v i j)
          _ -> internalError $ "cannot analyze symbolic code:\nx: " <> show x <> " i: " <> show i <> " j: " <> show j

        go v (1, !i, !j, !m) _ =
          {- End of PUSH op. -}   (0,            i + 1, j + 1, m >> VS.Mutable.write v i j)
        go v (n, !i, !j, !m) _ =
          {- PUSH data. -}        (n - 1,        i + 1, j,     m >> VS.Mutable.write v i j)


vmOp :: VM t -> Maybe Op
vmOp vm =
  let i  = vm ^. #state % #pc
      code' = vm ^. #state % #code
      (op, pushdata) = case code' of
        UnknownCode _ -> internalError "cannot get op from unknown code"
        InitCode xs' _ ->
          (BS.index xs' i, fmap LitByte $ BS.unpack $ BS.drop i xs')
        RuntimeCode (ConcreteRuntimeCode xs') ->
          (BS.index xs' i, fmap LitByte $ BS.unpack $ BS.drop i xs')
        RuntimeCode (SymbolicRuntimeCode xs') ->
          ( fromMaybe (internalError "unexpected symbolic code") . maybeLitByteSimp $ xs' V.! i , V.toList $ V.drop i xs')
  in if (opslen code' < i)
     then Nothing
     else Just (readOp op pushdata)

vmOpIx :: VM t -> Maybe Int
vmOpIx vm =
  do self <- currentContract vm
     self.opIxMap VS.!? vm.state.pc

-- Maps operation indices into a pair of (bytecode index, operation)
mkCodeOps :: ContractCode -> V.Vector (Int, Op)
mkCodeOps contractCode =
  let l = case contractCode of
            UnknownCode _ -> internalError "Cannot make codeOps for unknown code"
            InitCode bytes _ ->
              LitByte <$> (BS.unpack bytes)
            RuntimeCode (ConcreteRuntimeCode ops) ->
              LitByte <$> (BS.unpack $ stripBytecodeMetadata ops)
            RuntimeCode (SymbolicRuntimeCode ops) ->
              stripBytecodeMetadataSym $ V.toList ops
  in V.fromList . toList $ go 0 l
  where
    go !i !xs =
      case uncons xs of
        Nothing ->
          mempty
        Just (x, xs') ->
          let x' = fromMaybe (internalError "unexpected symbolic code argument") $ maybeLitByteSimp x
              j = opSize x'
          in (i, readOp x' xs') Seq.<| go (i + j) (drop j xs)

-- * Gas cost calculation helpers

concreteModexpGasFee :: ByteString -> Word64
concreteModexpGasFee input =
  let (lenb, lene, lenm) = parseModexpLength input
      -- EIP-7823: Cap input lengths at 1024 bytes (8192 bits)
      -- If any length exceeds this, the precompile will fail
      -- and consume all provided gas
      eip7823Limit :: W256
      eip7823Limit = 1024
  in if lenb > eip7823Limit || lene > eip7823Limit || lenm > eip7823Limit
     then 0  -- EIP-7823: limits exceeded, gas cost is 0 (precompileFail will consume all gas)
     else
       let ez = isZero (96 + lenb) lene input
           e' = word $ LS.toStrict $ lazySlice (96 + lenb) (min 32 lene) input
           maxLength :: Word64
           maxLength = unsafeInto $ max lenb lenm
           nwords :: Word64
           nwords = ceilDiv maxLength 8
           -- Check for overflow in nwords * nwords calculation
           multiplicationComplexity :: Word64
           multiplicationComplexity
             | maxLength <= 32 = 16
             | nwords > 0xFFFFFFFF = maxBound  -- nwords^2 would overflow
             | otherwise = let nw2 = nwords * nwords
                           in if nw2 > maxBound `div` 2
                              then maxBound
                              else 2 * nw2
           lene64 :: Word64
           lene64 = unsafeInto lene
           iterCount' :: Word64
           iterCount' | lene <= 32 && ez = 0
                      | lene <= 32 = unsafeInto (log2 e')
                      | e' == 0 = 16 * (lene64 - 32)
                      | otherwise = unsafeInto (log2 e') + 16 * (lene64 - 32)
           iterCount = max iterCount' 1
           -- Check for overflow in final multiplication
           result = if multiplicationComplexity == maxBound
                    then maxBound
                    else if iterCount > maxBound `div` multiplicationComplexity
                         then maxBound
                         else multiplicationComplexity * iterCount
       in max 500 result

-- Gas cost of precompiles
costOfPrecompile :: FeeSchedule Word64 -> Addr -> Expr Buf -> Word64
costOfPrecompile (FeeSchedule {..}) precompileAddr input =
  let errorDynamicSize = internalError "precompile input cannot have a dynamic size"
      inputLen = case input of
                   ConcreteBuf bs -> unsafeInto $ BS.length bs
                   AbstractBuf _ -> errorDynamicSize
                   buf -> case bufLength buf of
                            Lit l -> unsafeInto l -- TODO: overflow
                            _ -> errorDynamicSize
  in case precompileAddr of
    -- ECRECOVER
    0x1 -> 3000
    -- SHA2-256
    0x2 -> (((inputLen + 31) `div` 32) * 12) + 60
    -- RIPEMD-160
    0x3 -> (((inputLen + 31) `div` 32) * 120) + 600
    -- IDENTITY
    0x4 -> (((inputLen + 31) `div` 32) * 3) + 15
    -- MODEXP
    0x5 -> case input of
             ConcreteBuf i -> concreteModexpGasFee i
             _ -> internalError "Unsupported symbolic modexp gas calc "
    -- ECADD
    0x6 -> g_ecadd
    -- ECMUL
    0x7 -> g_ecmul
    -- ECPAIRING
    0x8 -> (inputLen `div` 192) * g_pairing_point + g_pairing_base
    -- BLAKE2
    0x9 -> case input of
             ConcreteBuf i -> g_fround * (unsafeInto $ asInteger $ lazySlice 0 4 i)
             _ -> internalError "Unsupported symbolic blake2 gas calc"
    -- Point Evaluation (EIP-4844)
    0x0A -> 50000
    -- BLS12-381 precompiles (EIP-2537)
    -- G1ADD (0x0B)
    0x0B -> 375
    -- G1MSM (0x0C)
    0x0C -> let k = inputLen `div` 160  -- 128 bytes point + 32 bytes scalar
            in if k == 0 then 0
               else 12000 * k * blsG1MsmDiscount k `div` 1000
    -- G2ADD (0x0D)
    0x0D -> 600
    -- G2MSM (0x0E)
    0x0E -> let k = inputLen `div` 288  -- 256 bytes point + 32 bytes scalar
            in if k == 0 then 0
               else 22500 * k * blsG2MsmDiscount k `div` 1000
    -- PAIRING (0x0F)
    0x0F -> let k = inputLen `div` 384  -- 128 bytes G1 + 256 bytes G2
            in 32600 * k + 37700
    -- MAP_FP_TO_G1 (0x10)
    0x10 -> 5500
    -- MAP_FP2_TO_G2 (0x11)
    0x11 -> 23800
    -- P256VERIFY (EIP-7951)
    0x100 -> 6900
    _ -> internalError $ "unimplemented precompiled contract " ++ show precompileAddr

-- Gas cost of memory expansion
memoryCost :: FeeSchedule Word64 -> Word64 -> Word64
memoryCost FeeSchedule{..} byteCount =
  let
    wordCount = ceilDiv byteCount 32
    linearCost = g_memory * wordCount
    quadraticCost = div (wordCount * wordCount) 512
  in
    linearCost + quadraticCost

hashcode :: ContractCode -> Expr EWord
hashcode (UnknownCode a) = CodeHash a
hashcode (InitCode ops args) = keccak $ (ConcreteBuf ops) <> args
hashcode (RuntimeCode (ConcreteRuntimeCode ops)) = keccak (ConcreteBuf ops)
hashcode (RuntimeCode (SymbolicRuntimeCode ops)) = keccak . Expr.fromList $ ops

-- | The length of the code ignoring any constructor args.
-- This represents the region that can contain executable opcodes
opslen :: ContractCode -> Int
opslen (UnknownCode _) = internalError "Cannot produce concrete opslen for unknown code"
opslen (InitCode ops _) = BS.length ops
opslen (RuntimeCode (ConcreteRuntimeCode ops)) = BS.length ops
opslen (RuntimeCode (SymbolicRuntimeCode ops)) = length ops

-- | The length of the code including any constructor args.
-- This can return an abstract value
codelen :: ContractCode -> Expr EWord
codelen (UnknownCode a) = CodeSize a
codelen c@(InitCode {}) = case toBuf c of
  Just b -> bufLength b
  Nothing -> internalError "impossible"
-- these are never going to be negative so unsafeInto is fine here
codelen (RuntimeCode (ConcreteRuntimeCode ops)) = Lit . unsafeInto $ BS.length ops
codelen (RuntimeCode (SymbolicRuntimeCode ops)) = Lit . unsafeInto $ length ops

toBuf :: ContractCode -> Maybe (Expr Buf)
toBuf (UnknownCode _) = Nothing
toBuf (InitCode ops args) = Just $ ConcreteBuf ops <> args
toBuf (RuntimeCode (ConcreteRuntimeCode ops)) = Just $ ConcreteBuf ops
toBuf (RuntimeCode (SymbolicRuntimeCode ops)) = Just $ Expr.fromList ops

codeloc :: EVM t CodeLocation
codeloc = do
  vm <- get
  pure (vm.state.contract, vm.state.pc)

createAddress :: Expr EAddr -> Maybe W64 -> EVM t (Expr EAddr)
createAddress (LitAddr a) (Just n) = pure $ Concrete.createAddress a n
createAddress (GVar _) _ = internalError "Unexpected GVar"
createAddress _ _ = freshSymAddr

create2Address :: Expr EAddr -> W256 -> ByteString -> EVM t (Expr EAddr)
create2Address (LitAddr a) s b = pure $ Concrete.create2Address a s b
create2Address (SymAddr _) _ _ = freshSymAddr
create2Address (GVar _) _ _ = internalError "Unexpected GVar"

freshSymAddr :: EVM t (Expr EAddr)
freshSymAddr = do
  modifying (#env % #freshAddresses) (+ 1)
  n <- use (#env % #freshAddresses)
  pure $ SymAddr ("freshSymAddr" <> (pack $ show n))

isPrecompileAddr' :: Addr -> Bool
isPrecompileAddr' 0x100 = True
isPrecompileAddr' x = 0x0 < x && x <= 0x11  -- Extended for BLS12-381 precompiles (EIP-2537)

isPrecompileAddr :: Expr EAddr -> Bool
isPrecompileAddr = \case
  LitAddr a -> isPrecompileAddr' a
  SymAddr _ -> False
  GVar _ -> internalError "Unexpected GVar"


-- EIP-7702 Delegation Handling --------------------------------------------------------------------


-- | EIP-7702 delegation code prefix: 0xef0100
-- A delegated account has code starting with this prefix followed by 20-byte target address
delegationPrefix :: ByteString
delegationPrefix = BS.pack [0xef, 0x01, 0x00]

-- | Check if a contract has delegation code and return the target address
-- Returns Just targetAddr if code is exactly 23 bytes starting with 0xef0100
getDelegationTarget :: ContractCode -> Maybe Addr
getDelegationTarget = \case
  RuntimeCode (ConcreteRuntimeCode code) ->
    if BS.length code == 23 && BS.take 3 code == delegationPrefix
    then Just $ unsafeInto $ word $ BS.drop 3 code
    else Nothing
  _ -> Nothing

-- | Resolve the code to execute for a contract, following EIP-7702 delegation
-- Returns (code to execute, codeContract address)
-- If the target has delegation code, returns the delegated-to contract's code
resolveDelegatedCode
  :: Contract           -- ^ The target contract being called
  -> Expr EAddr         -- ^ The address of the target
  -> Map (Expr EAddr) Contract  -- ^ All contracts
  -> (ContractCode, Expr EAddr)  -- ^ (resolved code, code source address)
resolveDelegatedCode target targetAddr contracts =
  case getDelegationTarget target.code of
    Nothing -> (target.code, targetAddr)
    Just delegatedTo ->
      let delegatedAddr = LitAddr delegatedTo
      -- EIP-7702: If delegation target is a precompile address (0x01-0x11 or 0x100),
      -- the retrieved code is considered empty and calls execute empty code
      in if isPrecompileAddr' delegatedTo
         then (RuntimeCode (ConcreteRuntimeCode ""), delegatedAddr)
         else case Map.lookup delegatedAddr contracts of
           Just delegatedContract -> (delegatedContract.code, delegatedAddr)
           -- If delegated-to doesn't exist, treat as empty code
           Nothing -> (RuntimeCode (ConcreteRuntimeCode ""), delegatedAddr)

-- | Create a delegation designator code for EIP-7702
-- The code is 0xef0100 || target_address (23 bytes total)
makeDelegationCode :: Addr -> ByteString
makeDelegationCode target = delegationPrefix <> word160Bytes target

-- | Recover the authorizing address from an EIP-7702 authorization entry
-- Returns the address that signed the authorization, or Nothing if invalid signature
-- Note: This does NOT check chain_id - per EIP-7702 spec, ecrecover happens first,
-- then the address is warmed, and only then is chain_id validated
recoverAuthorityAddress :: AuthorizationEntry -> Maybe Addr
recoverAuthorityAddress auth =
  -- EIP-2: Reject high-s signatures to prevent transaction malleability
  -- s must be in the lower half of the curve order
  let secp256k1nHalf = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 :: W256
  in if auth.authS > secp256k1nHalf
     then Nothing  -- Invalid signature: s value too high (EIP-2)
     else
       let -- EIP-7702 signing message: keccak(0x05 || rlp([chain_id, address, nonce]))
           rlpPayload = rlpList
             [ rlpWord256 auth.authChainId
             , BS $ word160Bytes auth.authAddress
             , rlpWord256 auth.authNonce
             ]
           signingMessage = BS.cons 0x05 rlpPayload
           msgHash = keccak' signingMessage
           -- v is yParity + 27 for ecrecover
           v = into auth.authYParity + 27
       in EVM.Sign.ecrec v auth.authR auth.authS msgHash
  where
    rlpList items = rlpencode $ List items
    rlpWord256 0 = BS mempty
    rlpWord256 n = BS $ octets n
    octets x = BS.pack $ dropWhile (== 0) [fromIntegral (shiftR x (8 * i)) | i <- reverse [0..31 :: Int]]

-- | Get all authority addresses that should be warmed from authorization list
-- Per EIP-7702 spec: addresses are warmed AFTER chain_id validation
-- Chain ID check happens first (must be 0 or match current chain), then ecrecover
getAuthoritiesToWarm :: W256 -> [AuthorizationEntry] -> [Expr EAddr]
getAuthoritiesToWarm chainId auths = map LitAddr $ mapMaybe (recoverIfValidChainId chainId) auths
  where
    recoverIfValidChainId :: W256 -> AuthorizationEntry -> Maybe Addr
    recoverIfValidChainId cid auth
      -- Chain ID must be 0 (any chain) or match current chain
      | auth.authChainId /= 0 && auth.authChainId /= cid = Nothing
      | otherwise = recoverAuthorityAddress auth

-- | Process all EIP-7702 authorization entries and return the updated contracts map, refunds, and addresses to warm
-- Per EIP-7702 spec, for each authorization:
-- 1. ecrecover to get authority address (addresses warmed separately via getAuthoritiesToWarm)
-- 2. Check chain_id: must be 0 or match current chain
-- 3. Check authority's code is empty or already delegated
-- 4. Check nonce matches (for self-sponsored: nonce == account_nonce + 1)
-- 5. Add refund if authority exists (PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST = 12500)
-- 6. Set delegation code and increment nonce
-- 7. Add delegation target address to accessed addresses (only for valid authorizations)
processAuthorizations
  :: W256                                -- ^ Chain ID
  -> Expr EAddr                          -- ^ Transaction origin address
  -> [AuthorizationEntry]                -- ^ Authorization list from transaction
  -> Map (Expr EAddr) Contract           -- ^ Current contracts state
  -> (Map (Expr EAddr) Contract, [(Expr EAddr, Word64)], [Expr EAddr])  -- ^ (Updated contracts, Refunds, Delegation targets to warm)
processAuthorizations chainId origin auths contracts = foldl processOne (contracts, [], []) auths
  where
    -- EIP-7702 refund: PER_EMPTY_ACCOUNT_COST (25000) - PER_AUTH_BASE_COST (12500) = 12500
    authRefundAmount :: Word64
    authRefundAmount = 12500

    processOne :: (Map (Expr EAddr) Contract, [(Expr EAddr, Word64)], [Expr EAddr]) -> AuthorizationEntry
               -> (Map (Expr EAddr) Contract, [(Expr EAddr, Word64)], [Expr EAddr])
    processOne (cs, refs, warmAddrs) auth = case recoverAuthorityAddress auth of
      Nothing -> (cs, refs, warmAddrs)  -- Invalid signature, skip
      Just authority ->
        -- Check chain_id: must be 0 (any chain) or match current chain
        if auth.authChainId /= 0 && auth.authChainId /= chainId
        then (cs, refs, warmAddrs)  -- Chain ID mismatch, skip (but address was already warmed)
        else
          let authorityAddr = LitAddr authority
              existingAccount = Map.lookup authorityAddr cs
              currentNonce = case existingAccount of
                Just c -> fromMaybe 0 c.nonce
                Nothing -> 0
              -- Check if code is empty or already delegated
              codeIsOk = case existingAccount of
                Nothing -> True  -- No account = empty code
                Just c -> case c.code of
                  RuntimeCode (ConcreteRuntimeCode code) ->
                    BS.null code || isDelegationCode code
                  _ -> True  -- Symbolic code, allow for now
              -- EIP-7702 step 5: nonce validation
              -- For self-sponsored (authority == origin), nonce must be account_nonce + 1
              -- Otherwise, nonce must equal account_nonce
              isSelfSponsored = authorityAddr == origin
              expectedNonce = if isSelfSponsored
                              then currentNonce + 1
                              else currentNonce
          in -- Check code constraint (EIP-7702 step 4)
             if not codeIsOk
             then (cs, refs, warmAddrs)  -- Account has non-delegation code, skip
             -- EIP-7702: If the account's nonce is 2^64-1, skip to prevent overflow
             else if currentNonce == maxBound
             then (cs, refs, warmAddrs)  -- Would overflow, skip
             -- Check nonce matches (step 5)
             else if into expectedNonce /= auth.authNonce
             then (cs, refs, warmAddrs)  -- Nonce mismatch, skip
             else
               -- EIP-7702: If target address is 0x0, set code to empty (clears delegation)
               -- Otherwise, set delegation code (0xef0100 || address)
               let newCode = if auth.authAddress == 0
                             then RuntimeCode (ConcreteRuntimeCode mempty)
                             else RuntimeCode (ConcreteRuntimeCode (makeDelegationCode auth.authAddress))
                   -- Create or update the authority's contract
                   newContract = case existingAccount of
                     Just c -> set #code newCode $
                               set #nonce (Just (currentNonce + 1)) c
                     Nothing -> set #nonce (Just 1) $ initialContract newCode
                   -- Add refund if authority exists in trie (EIP-7702 step 6)
                   -- An account "exists" if it has non-zero balance, nonce, or code
                   accountReallyExists = case existingAccount of
                     Nothing -> False
                     Just c ->
                       let hasBalance = case c.balance of
                             Lit b -> b /= 0
                             _ -> True  -- Symbolic, assume exists
                           hasNonce = case c.nonce of
                             Just n -> n /= 0
                             Nothing -> False
                           hasCode = case c.code of
                             RuntimeCode (ConcreteRuntimeCode code) -> not (BS.null code)
                             _ -> True  -- Symbolic or InitCode, assume exists
                       in hasBalance || hasNonce || hasCode
                   newRefs = if accountReallyExists
                             then (authorityAddr, authRefundAmount) : refs
                             else refs
                   -- Note: EIP-7702 step 7 says to add the AUTHORITY account to accessed_addresses,
                   -- which is handled separately in getAuthoritiesToWarm. The delegation TARGET
                   -- should only be warmed if it's the transaction's destination's delegation target,
                   -- not for every authorization. So we don't add delegation targets here.
               in (Map.insert authorityAddr newContract cs, newRefs, warmAddrs)

-- | Check if bytecode is a delegation code (0xef0100 prefix)
isDelegationCode :: ByteString -> Bool
isDelegationCode code = BS.length code == 23 && BS.isPrefixOf delegationPrefix code


-- * Arithmetic

ceilDiv :: (Num a, Integral a) => a -> a -> a
ceilDiv m n = div (m + n - 1) n

allButOne64th :: (Num a, Integral a) => a -> a
allButOne64th n = n - div n 64

log2 :: FiniteBits b => b -> Int
log2 x = finiteBitSize x - 1 - countLeadingZeros x

writeMemory :: MutableMemory -> Int -> ByteString -> EVM t ()
writeMemory memory offset buf = do
  memory' <- expandMemory (offset + BS.length buf)
  VS.iforM_ (byteStringToVector buf) $ \i v -> do
    VS.Mutable.unsafeWrite memory' (offset + i) v
  where
  expandMemory requiredSize = do
    let currentSize = VS.Mutable.length memory
    let toAlloc = requiredSize - currentSize
    if toAlloc > 0 then do
      -- As grow does a larger *copy* of the vector on a new place,
      -- we double the vector size to avoid the performance impact
      -- that would happen with repeated small expansion operations.
      let growthFactor = 2
      let targetSize = requiredSize * growthFactor
      -- Always grow at least 8k
      let toGrow = max 8192 $ targetSize - currentSize
      memory' <- VS.Mutable.grow memory toGrow
      assign (#state % #memory) (ConcreteMemory memory')
      pure memory'
    else
      pure memory

freezeMemory :: MutableMemory -> EVM t (Expr Buf)
freezeMemory memory =
  ConcreteBuf . vectorToByteString <$> VS.freeze memory


instance VMOps Symbolic where
  burn' _ continue = continue
  burnExp _ continue = continue
  burnSha3 _ continue = continue
  burnCalldatacopy _ continue = continue
  burnCodecopy _ continue = continue
  burnExtcodecopy _ _ continue = continue
  burnReturndatacopy _ continue = continue
  burnLog _ _ continue = continue

  initialGas = ()
  ensureGas _ continue = continue
  gasTryFrom _ = Right ()
  costOfCreate _ _ _ _ = ((), ())
  costOfCall _ _ _ _ _ _ continue = continue 0 0
  reclaimRemainingGasAllowance _ = pure ()
  payRefunds = pure ()
  pushGas = do
    modifying (#env % #freshGasVals) (+ 1)
    n <- use (#env % #freshGasVals)
    pushSym $ Expr.Gas "" n
  enoughGas _ _ = True
  subGas _ _ = ()
  toGas _ = ()
  whenSymbolicElse a _ = a

  partial e = assign #result $ Just (Unfinished e)
  branch depthLimit cond continue = do
    loc <- codeloc
    pathconds <- use #constraints
    vm <- get
    query $ PleaseAskSMT cond pathconds (runBothPaths loc vm.exploreDepth)
    where
      runBothPaths loc _ (Case v) = do
        assign #result Nothing
        let condSimp = Expr.simplify cond
        pushTo #constraints $ if v then Expr.simplifyProp (Lit 0 ./= condSimp)
                                   else Expr.simplifyProp (Lit 0 .== condSimp)
        (iteration, _) <- use (#iterations % at loc % non (0,[]))
        stack <- use (#state % #stack)
        assign (#pathsVisited % at (loc, iteration)) (Just v)
        assign (#iterations % at loc) (Just (iteration + 1, stack))
        continue v
      -- Both paths are possible; we ask for more input
      runBothPaths loc exploreDepth UnknownBranch =
        (fork depthLimit exploreDepth ) . PleaseRunBoth $ (runBothPaths loc exploreDepth) . Case

  -- numBytes allows us to specify how many bytes of the returned value is relevant
  -- if it's e.g.a JUMP, only 2 bytes can be relevant. This allows us to avoid
  -- getting solutions that are nonsensical
  manySolutions maxDepth ewordExpr numBytes continue = do
    pathconds <- use #constraints
    vm <- get
    query $ PleaseGetSols ewordExpr numBytes pathconds $ \case
      Just concVals -> do
        assign #result Nothing
        case concVals of
          -- zero solutions means that we are in a branch that's not possible
          -- so revert all frames and stop all execution on this branch
          [] -> finishAllFramesAndStop
          [val] -> do
            assign #result Nothing
            pushTo #constraints $ Expr.simplifyProp (ewordExpr .== (Lit val))
            continue $ Just val
          _ -> fork maxDepth vm.exploreDepth $ PleaseRunAll (map Lit concVals) runAllPaths
      Nothing -> do
        assign #result Nothing
        continue Nothing
    where
      runAllPaths val = do
        assign #result Nothing
        pushTo #constraints $ Expr.simplifyProp (ewordExpr .== val)
        case val of
          Lit v -> continue $ Just v
          _ -> internalError "runAllPaths can only get concrete values here"

instance VMOps Concrete where
  burn' n continue = do
    available <- use (#state % #gas)
    if n <= available
      then do
        #state % #gas %= (subtract n)
        #burned %= (+ n)
        continue
      else
        vmError (OutOfGas available n)

  burnExp (forceLit -> exponent) continue = do
    FeeSchedule {..} <- gets (.block.schedule)
    let cost = if exponent == 0
          then g_exp
          else g_exp + g_expbyte * unsafeInto (ceilDiv (1 + log2 exponent) 8)
    burn cost continue

  burnSha3 (forceLit -> xSize) continue = do
    FeeSchedule {..} <- gets (.block.schedule)
    burn (g_sha3 + g_sha3word * ceilDiv (unsafeInto xSize) 32) continue

  burnCalldatacopy (forceLit -> xSize) continue = do
    FeeSchedule {..} <- gets (.block.schedule)
    burn (g_verylow + g_copy * ceilDiv (unsafeInto xSize) 32) continue

  burnCodecopy (forceLit -> n) continue =
    case tryFrom n of
      Left _ -> vmError IllegalOverflow
      Right n' -> do
        FeeSchedule {..} <- gets (.block.schedule)
        if n' <= ( (maxBound :: Word64) - g_verylow ) `div` g_copy * 32 then
          burn (g_verylow + g_copy * ceilDiv (unsafeInto n) 32) continue
        else vmError IllegalOverflow

  burnExtcodecopy extAccount (forceLit -> codeSize) continue = do
    FeeSchedule {..} <- gets (.block.schedule)
    acc <- accessAccountForGas extAccount
    let cost = if acc then g_warm_storage_read else g_cold_account_access
    burn (cost + g_copy * ceilDiv (unsafeInto codeSize) 32) continue

  burnReturndatacopy (forceLit -> xSize) continue = do
    FeeSchedule {..} <- gets (.block.schedule)
    burn (g_verylow + g_copy * ceilDiv (unsafeInto xSize) 32) continue

  burnLog (forceLit -> xSize) n continue = do
    case tryFrom xSize of
      Right sz -> do
        FeeSchedule {..} <- gets (.block.schedule)
        burn (g_log + g_logdata * sz + (into n) * g_logtopic) continue
      _ -> vmError IllegalOverflow

  initialGas = 0

  ensureGas amount continue = do
    availableGas <- use (#state % #gas)

    if availableGas <= amount then
      vmError (OutOfGas availableGas amount)
    else continue

  gasTryFrom (forceLit -> w256) =
    -- EVM spec: gas values larger than Word64 max should be treated as "max gas"
    -- The 63/64 rule will cap it appropriately later
    -- Note: We can't use tryFrom here because TryFrom W256 Word64 always succeeds (truncates)
    if w256 > into (maxBound :: Word64)
    then Right maxBound  -- Cap at Word64 max for overflow
    else Right (unsafeInto w256)

  -- Gas cost of create, including hash cost if needed
  costOfCreate (FeeSchedule {..}) availableGas size hashNeeded = (createCost, initGas)
    where
      byteCost   = if hashNeeded then g_sha3word + g_initcodeword else g_initcodeword
      createCost = g_create + codeCost
      codeCost   = byteCost * (ceilDiv (unsafeInto (forceLit size)) 32)
      initGas    = allButOne64th (availableGas - createCost)

  -- Gas cost function for CALL, transliterated from the Yellow Paper.
  costOfCall (FeeSchedule {..}) recipientExists (forceLit -> xValue) availableGas xGas target continue = do
    acc <- accessAccountForGas target
    let call_base_gas = if acc then g_warm_storage_read else g_cold_account_access
        c_new = if not recipientExists && xValue /= 0
              then g_newaccount
              else 0
        c_xfer = if xValue /= 0  then g_callvalue else 0
        c_extra = call_base_gas + c_xfer + c_new
        c_gascap =  if availableGas >= c_extra
                    then min xGas (allButOne64th (availableGas - c_extra))
                    else xGas
        c_callgas = if xValue /= 0 then c_gascap + g_callstipend else c_gascap
    let (cost, gas') = (c_gascap + c_extra, c_callgas)
    continue cost gas'

  -- When entering a call, the gas allowance is counted as burned
  -- in advance; this unburns the remainder and adds it to the
  -- parent frame.
  reclaimRemainingGasAllowance oldVm = do
    let remainingGas = oldVm.state.gas
    modifying #burned (subtract remainingGas)
    modifying (#state % #gas) (+ remainingGas)

  payRefunds = do
    -- compute and pay the refund to the caller and the
    -- corresponding payment to the miner
    block        <- use #block
    tx           <- use #tx
    gasRemaining <- use (#state % #gas)

    let
      gasUsedBeforeRefund = tx.gaslimit - gasRemaining
      sumRefunds          = sum (snd <$> tx.subState.refunds)
      cappedRefund        = min (quot gasUsedBeforeRefund 5) sumRefunds
      gasUsedAfterRefund  = gasUsedBeforeRefund - cappedRefund
      -- EIP-7623: Apply floor cost based on calldata tokens
      -- gas_used = 21000 + max(4*tokens + execution + creation, 10*tokens)
      -- Since txdataFloorGas = 21000 + 10*tokens, we just compare totals
      gasUsed             = max gasUsedAfterRefund tx.txdataFloorGas
      -- Adjust refund if floor kicks in
      actualRefund        = if gasUsed > gasUsedAfterRefund
                            then cappedRefund - (gasUsed - gasUsedAfterRefund)
                            else cappedRefund
      originPay    = (into $ gasRemaining + actualRefund) * tx.gasprice
      minerPay     = tx.priorityFee * (into gasUsed)

    modifying (#env % #contracts)
       (Map.adjust (over #balance (Expr.add (Lit originPay))) tx.origin)
    modifying (#env % #contracts)
       (Map.adjust (over #balance (Expr.add (Lit minerPay))) block.coinbase)

  pushGas = do
    vm <- get
    push (into vm.state.gas)

  enoughGas cost gasCap = cost <= gasCap
  subGas gasCap cost = gasCap - cost
  toGas = id
  whenSymbolicElse _ a = a
  partial _ = internalError "won't happen during concrete exec"
  branch _ (forceLit -> cond) continue = continue (cond > 0)
  manySolutions _ _ _ = internalError "SMT solver should never be needed in concrete mode"

-- Create symbolic VM from concrete VM
symbolify :: VM Concrete -> VM Symbolic
symbolify vm =
  vm { result = symbolifyResult <$> vm.result
     , state  = symbolifyFrameState vm.state
     , frames = symbolifyFrame <$> vm.frames
     , burned = ()
     }

symbolifyFrameState :: FrameState Concrete -> FrameState Symbolic
symbolifyFrameState state = state { gas = () }

symbolifyFrame :: Frame Concrete -> Frame Symbolic
symbolifyFrame frame = frame { state = symbolifyFrameState frame.state }

symbolifyResult :: VMResult Concrete -> VMResult Symbolic
symbolifyResult result =
  case result of
    HandleEffect _ -> internalError "shouldn't happen"
    VMFailure e -> VMFailure e
    VMSuccess b -> VMSuccess b


burn :: VMOps t => Word64 -> EVM t () -> EVM t ()
burn = burn' . toGas
