module EVM.Transaction where

import EVM (initialContract, ceilDiv)
import EVM.Expr qualified as Expr
import EVM.FeeSchedule
import EVM.Format (hexText)
import EVM.RLP
import EVM.Sign
import EVM.Types

import Optics.Core hiding (cons)

import Data.Aeson (FromJSON (..))
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.ByteString (ByteString, cons)
import Data.ByteString qualified as BS
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isNothing, fromJust)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Numeric (showHex)
import Witch (into, unsafeInto)

data AccessListEntry = AccessListEntry
  { address :: Addr
  , storageKeys :: [W256]
  } deriving (Show, Generic)

instance JSON.ToJSON AccessListEntry

data TxType
  = LegacyTransaction
  | AccessListTransaction
  | EIP1559Transaction
  | EIP4844Transaction
  | EIP7702Transaction
  deriving (Show, Eq, Generic)

instance JSON.ToJSON TxType where
  toJSON t = case t of
               EIP7702Transaction    -> "0x4" -- EIP7702
               EIP4844Transaction    -> "0x3" -- EIP4844
               EIP1559Transaction    -> "0x2" -- EIP1559
               LegacyTransaction     -> "0x1" -- EIP2718
               AccessListTransaction -> "0x1" -- EIP2930


data Transaction = Transaction
  { txdata            :: ByteString
  , gasLimit          :: Word64
  , gasPrice          :: Maybe W256
  , nonce             :: W256
  , r                 :: W256
  , s                 :: W256
  , toAddr            :: Maybe Addr
  , v                 :: W256
  , value             :: W256
  , txtype            :: TxType
  , accessList        :: [AccessListEntry]
  , maxPriorityFeeGas :: Maybe W256
  , maxFeePerGas      :: Maybe W256
  , chainId           :: W256
  } deriving (Show, Generic)

instance JSON.ToJSON Transaction where
  toJSON t = JSON.object
    [ ("input",             (JSON.toJSON (ByteStringS t.txdata)))
    , ("gas",               (JSON.toJSON $ "0x" ++ showHex (into @Integer $ t.gasLimit) ""))
    , ("gasPrice",          (JSON.toJSON $ show $ fromJust t.gasPrice))
    , ("v",                 (JSON.toJSON $ show $ (t.v)-27))
    , ("r",                 (JSON.toJSON $ show t.r))
    , ("s",                 (JSON.toJSON $ show t.s))
    , ("to",                (JSON.toJSON t.toAddr))
    , ("nonce",             (JSON.toJSON $ show t.nonce))
    , ("value",             (JSON.toJSON $ show t.value))
    , ("type",              (JSON.toJSON t.txtype))
    , ("accessList",        (JSON.toJSON t.accessList))
    , ("maxPriorityFeePerGas", (JSON.toJSON $ show $ fromJust t.maxPriorityFeeGas))
    , ("maxFeePerGas",      (JSON.toJSON $ show $ fromJust t.maxFeePerGas))
    , ("chainId",           (JSON.toJSON $ show t.chainId))
    ]

emptyTransaction :: Transaction
emptyTransaction = Transaction { txdata = mempty
                               , gasLimit = 0
                               , gasPrice = Nothing
                               , nonce = 0
                               , r = 0
                               , s = 0
                               , toAddr = Nothing
                               , v = 0
                               , value = 0
                               , txtype = EIP1559Transaction
                               , accessList = []
                               , maxPriorityFeeGas = Nothing
                               , maxFeePerGas = Nothing
                               , chainId = 1
                               }

-- | utility function for getting a more useful representation of accesslistentries
-- duplicates only matter for gas computation
txAccessMap :: Transaction -> Map Addr [W256]
txAccessMap tx = ((Map.fromListWith (++)) . makeTups) tx.accessList
  where makeTups = map (\ale -> (ale.address , ale.storageKeys ))

-- Given Transaction, it recovers the address that sent it
sender :: Transaction -> Maybe Addr
sender tx = ecrec v' tx.r  tx.s hash
  where hash = keccak' (signingData tx)
        v    = tx.v
        v'   = if v == 27 || v == 28 then v
               else if v >= 35 then 28 - (v `mod` 2) -- EIP155
               else 27 + v

sign :: Integer -> Transaction -> Transaction
sign sk tx = tx { v = into v, r = r, s = s}
  where
    hash = keccak' $ signingData tx
    (v, r, s) = EVM.Sign.sign hash sk

signingData :: Transaction -> ByteString
signingData tx =
  case tx.txtype of
    LegacyTransaction -> if v == (tx.chainId * 2 + 35) || v == (tx.chainId * 2 + 36)
      then eip155Data
      else normalData
    AccessListTransaction -> eip2930Data
    EIP1559Transaction -> eip1559Data
    EIP4844Transaction -> eip4844Data
    EIP7702Transaction -> eip7702Data
  where v          = tx.v
        to'        = case tx.toAddr of
          Just a  -> BS $ word160Bytes a
          Nothing -> BS mempty
        maxFee = fromJust tx.maxFeePerGas
        maxPrio = fromJust tx.maxPriorityFeeGas
        gasPrice = fromJust tx.gasPrice
        accessList = tx.accessList
        rlpAccessList = EVM.RLP.List $ map (\accessEntry ->
          EVM.RLP.List [BS $ word160Bytes accessEntry.address,
                        EVM.RLP.List $ map rlpWordFull accessEntry.storageKeys]
          ) accessList
        normalData = rlpList
          [ rlpWord256 tx.nonce
          , rlpWord256 gasPrice
          , rlpWord256 (into tx.gasLimit)
          , to'
          , rlpWord256 tx.value
          , BS tx.txdata
          ]
        eip155Data = rlpList
          [ rlpWord256 tx.nonce
          , rlpWord256 gasPrice
          , rlpWord256 (into tx.gasLimit)
          , to'
          , rlpWord256 tx.value
          , BS tx.txdata
          , rlpWord256 tx.chainId
          , rlpWord256 0x0
          , rlpWord256 0x0
          ]
        eip1559Data = cons 0x02 $ rlpList
          [ rlpWord256 tx.chainId
          , rlpWord256 tx.nonce
          , rlpWord256 maxPrio
          , rlpWord256 maxFee
          , rlpWord256 (into tx.gasLimit)
          , to'
          , rlpWord256 tx.value
          , BS tx.txdata
          , rlpAccessList
          ]
        eip2930Data = cons 0x01 $ rlpList
          [ rlpWord256 tx.chainId
          , rlpWord256 tx.nonce
          , rlpWord256 gasPrice
          , rlpWord256 (into tx.gasLimit)
          , to'
          , rlpWord256 tx.value
          , BS tx.txdata
          , rlpAccessList
          ]
        eip4844Data = cons 0x03 $ rlpList
          [ rlpWord256 tx.chainId
          , rlpWord256 tx.nonce
          , rlpWord256 maxPrio
          , rlpWord256 maxFee
          , rlpWord256 (into tx.gasLimit)
          , to'
          , rlpWord256 tx.value
          , BS tx.txdata
          , rlpAccessList
          , rlpWord256 $ undefined -- TODO EIP4844 max_fee_per_blob_gas
          , undefined -- TODO EIP4844 blob_versioned_hashes
          ]
        eip7702Data = cons 0x04 $ rlpList
          [ rlpWord256 tx.chainId
          , rlpWord256 tx.nonce
          , rlpWord256 maxPrio
          , rlpWord256 maxFee
          , rlpWord256 (into tx.gasLimit)
          , to'
          , rlpWord256 tx.value
          , BS tx.txdata
          , rlpAccessList
          , undefined -- TODO EIP4844 authorization_list
          ]

accessListPrice :: FeeSchedule Word64 -> [AccessListEntry] -> Word64
accessListPrice fs al =
    sum (map
      (\ale ->
        fs.g_access_list_address  +
        (fs.g_access_list_storage_key  * (unsafeInto . length) ale.storageKeys))
        al)

txGasCost :: FeeSchedule Word64 -> Transaction -> Word64
txGasCost fs tx =
  let calldata     = tx.txdata
      zeroBytes    = BS.count 0 calldata
      nonZeroBytes = BS.length calldata - zeroBytes
      baseCost     = fs.g_transaction
        + (if isNothing tx.toAddr then fs.g_txcreate + initcodeCost else 0)
        + (accessListPrice fs tx.accessList )
      zeroCost     = fs.g_txdatazero
      nonZeroCost  = fs.g_txdatanonzero
      initcodeCost = fs.g_initcodeword * unsafeInto (ceilDiv (BS.length calldata) 32)
  in baseCost + zeroCost * (unsafeInto zeroBytes) + nonZeroCost * (unsafeInto nonZeroBytes)

instance FromJSON AccessListEntry where
  parseJSON (JSON.Object val) = do
    accessAddress_ <- addrField val "address"
    accessStorageKeys_ <- (val JSON..: "storageKeys") >>= parseJSONList
    pure $ AccessListEntry accessAddress_ accessStorageKeys_
  parseJSON invalid =
    JSON.typeMismatch "AccessListEntry" invalid

instance FromJSON Transaction where
  parseJSON (JSON.Object val) = do
    tdata    <- hexText <$> (val JSON..: "data")
    gasLimit <- word64Field val "gasLimit"
    gasPrice <- fmap read <$> val JSON..:? "gasPrice"
    maxPrio  <- fmap read <$> val JSON..:? "maxPriorityFeePerGas"
    maxFee   <- fmap read <$> val JSON..:? "maxFeePerGas"
    nonce    <- wordField val "nonce"
    r        <- wordField val "r"
    s        <- wordField val "s"
    toAddr   <- addrFieldMaybe val "to"
    v        <- wordField val "v"
    value    <- wordField val "value"
    txType   <- fmap (read :: String -> Int) <$> val JSON..:? "type"
    case txType of
      Just 0x00 -> pure $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value LegacyTransaction [] Nothing Nothing 1
      Just 0x01 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        pure $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value AccessListTransaction accessListEntries Nothing Nothing 1
      Just 0x02 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        pure $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value EIP1559Transaction accessListEntries maxPrio maxFee 1
      Just 0x03 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        -- TODO: capture max_fee_per_blob_gas and blob_versioned_hashes EIP4844
        pure $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value EIP4844Transaction accessListEntries maxPrio maxFee 1
      Just 0x04 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        -- TODO: capture authorization_list EIP7702
        pure $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value EIP7702Transaction accessListEntries maxPrio maxFee 1
      Just _ -> fail "unrecognized custom transaction type"
      Nothing -> pure $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value LegacyTransaction [] Nothing Nothing 1
  parseJSON invalid =
    JSON.typeMismatch "Transaction" invalid

accountAt :: Expr EAddr -> Getter (Map (Expr EAddr) Contract) Contract
accountAt a = (at a) % (to $ fromMaybe newAccount)

touchAccount :: Expr EAddr -> Map (Expr EAddr) Contract -> Map (Expr EAddr) Contract
touchAccount a = Map.insertWith (flip const) a newAccount

newAccount :: Contract
newAccount = initialContract (RuntimeCode (ConcreteRuntimeCode ""))

-- | Increments origin nonce and pays gas deposit
setupTx :: Expr EAddr -> Expr EAddr -> W256 -> Word64 -> Map (Expr EAddr) Contract -> Map (Expr EAddr) Contract
setupTx origin coinbase gasPrice gasLimit prestate =
  let gasCost = gasPrice * (into gasLimit)
  in (Map.adjust ((over #nonce   (fmap ((+) 1)))
               . (over #balance (`Expr.sub` (Lit gasCost)))) origin)
    . touchAccount origin
    . touchAccount coinbase $ prestate

-- | Given a valid tx loaded into the vm state,
-- subtract gas payment from the origin, increment the nonce
-- and pay receiving address
initTx :: VM t -> VM t
initTx vm =
  let
    toAddr   = vm.state.contract
    origin   = vm.tx.origin
    gasPrice = vm.tx.gasprice
    gasLimit = vm.tx.gaslimit
    coinbase = vm.block.coinbase
    value    = vm.state.callvalue
    toContract = initialContract vm.state.code
    preState = setupTx origin coinbase gasPrice gasLimit vm.env.contracts
    oldBalance = view (accountAt toAddr % #balance) preState
    creation = vm.tx.isCreate
    initState =
        ((Map.adjust (over #balance (`Expr.sub` value))) origin)
      . (Map.adjust (over #balance (Expr.add value))) toAddr
      . (if creation
         then Map.insert toAddr (toContract & (set #balance oldBalance))
         else touchAccount toAddr)
      $ preState
  in
    vm & #env % #contracts .~ initState
       & #tx % #txReversion .~ preState
