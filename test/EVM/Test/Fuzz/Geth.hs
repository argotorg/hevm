-- | Running a case in geth's evm
module EVM.Test.Fuzz.Geth
  ( EVMToolTrace(..), GethLog(..), GethRun(..), addrKey, blockHash, fromAddress
  , headMay, mkTx, nonZero, originBalance, preState, prevRandaoVal, runGeth
  ) where

import Control.Monad (when)
import Data.Aeson ((.:), (.:?))
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.Char (toLower)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import GHC.Generics (Generic)
import GHC.IO.Exception (ExitCode(ExitSuccess))
import Numeric (showHex)
import Optics.Core hiding (pre, elements)
import System.FilePath ((</>))
import System.Process (readCreateProcessWithExitCode, proc, CreateProcess(..))
import Test.Tasty.HUnit (assertFailure)
import Witch (into, unsafeInto)
import EVM.Fetch.MockNode (Account(..), World)
import EVM.Sign (deriveAddr)
import EVM.Transaction qualified
import EVM.Types hiding (Env)
import EVM.Test.Fuzz.Program

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
