{-# LANGUAGE QuasiQuotes #-}

module EVM.ConcreteExecution.ConcreteExecutionTests (tests) where

import Control.Monad.ST (stToIO)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe)
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V

import EVM.ABI
import EVM.Effects qualified as Effects
import EVM.FeeSchedule
import EVM.Fetch qualified as Fetch
import EVM.Solidity (solcRuntime)
import EVM.Solvers (defMemLimit)
import EVM.Stepper qualified
import EVM.Transaction (initTx)
import EVM.Types
import EVM (initialContract, makeVm)
import Test.Tasty
import Test.Tasty.HUnit

type SourceCode = Text
type ContractName = Text
type FunctionName = Text
type Args = [AbiValue]
type ExecResult = Either EvmError (Expr Buf)

compileOneContract :: SourceCode -> ContractName -> IO ByteString
compileOneContract sourceCode contractName =
  solcRuntime contractName sourceCode <&> fromMaybe (internalError $ "Contract " <> (show contractName) <> " not present in the given source code")


executeSingleCall :: SourceCode -> ContractName -> FunctionName -> Args -> IO ExecResult
executeSingleCall sourceCode contractName functionName abiArgs = do
  runtimeCode <- compileOneContract sourceCode contractName
  let functionSignature = functionName <> "(" <> T.intercalate "," (map (abiTypeSolidity . abiValueType) abiArgs) <> ")"
  let callData = abiMethod functionSignature (AbiTuple $ V.fromList abiArgs)
  let contractWithCode = initialContract (RuntimeCode $ ConcreteRuntimeCode runtimeCode)
  initialVM <- stToIO $ makeVm $ VMOpts
    { contract     = contractWithCode
    , otherContracts = []
    , calldata       = (ConcreteBuf callData, [])
    , value          = Lit 0
    , address        = (LitAddr 0xacab)
    , caller         = (LitAddr 0)
    , origin         = (LitAddr 0)
    , gas            = maxBound
    , baseFee        = 0
    , priorityFee    = 0
    , gaslimit       = maxBound
    , coinbase       = (LitAddr 0)
    , number         = Lit 0
    , timestamp      = Lit 0
    , blockGaslimit  = maxBound
    , gasprice       = 0
    , maxCodeSize    = maxBound
    , prevRandao     = 0
    , schedule       = feeSchedule
    , chainId        = 1
    , create         = False
    , baseState      = EmptyBase
    , txAccessList   = mempty
    , allowFFI       = False
    , freshAddresses = 0
    , beaconRoot     = 0
    }
  let withInitializedTransactionVM = EVM.Transaction.initTx initialVM
  let fetcher = Fetch.zero 0 Nothing defMemLimit
  Effects.runApp $ EVM.Stepper.interpret fetcher withInitializedTransactionVM EVM.Stepper.execFully

tests :: TestTree
tests = testGroup "Concrete execution tests"
  [ testCase "return-updated-input-argument" $ expectValue (AbiUInt 8 3) =<< executeSingleCall simpleUncheckedArithmeticExample "C" "a" [AbiUInt 8 1]
  , testCase "silent-overflow-in-unchecked-arithmetic" $ expectValue (AbiUInt 8 245) =<< executeSingleCall simpleUncheckedArithmeticExample "C" "a" [AbiUInt 8 250]
  , testCase "revert-on-arithmetic-overflow" $ expectRevert =<< executeSingleCall simpleCheckedArithmeticExample "C" "a" [AbiUInt 8 250]
  ]

expectValue :: AbiValue -> ExecResult -> IO ()
expectValue expectedVal res = do
  let abiType = abiValueType expectedVal
  bs <- expectSuccess res
  let obtainedVal = decodeAbiValue abiType (BS.fromStrict bs)
  assertEqual "Incorrect result of concrete execution" expectedVal obtainedVal

expectSuccess :: ExecResult -> IO ByteString
expectSuccess res = do
  buf <- assertRight res
  case buf of
    ConcreteBuf bs -> pure bs
    _ -> assertFailure $ "Unexpected symbolic buffer: " <> show buf

expectRevert :: ExecResult -> IO ()
expectRevert res = do
  err <- assertLeft res
  case err of
    Revert _ -> pure ()
    _ -> assertFailure "Revert was expected, but got a different EVM error"

assertLeft :: Either e a -> IO e
assertLeft = \case
  Left e -> pure e
  Right _ -> assertFailure "Left we expected, but got Right"

assertRight :: Show e => Either e a -> IO a
assertRight = \case
  Left e -> assertFailure $ "Unexpected error: " <> show e
  Right x -> pure x

simpleUncheckedArithmeticExample :: Text
simpleUncheckedArithmeticExample = [here|
  contract C {
    function a(uint8 x) public returns (uint8 b) {
      unchecked { b = x*2+1; }
    }
  }
|]

simpleCheckedArithmeticExample :: Text
simpleCheckedArithmeticExample = [here|
  contract C {
    function a(uint8 x) public returns (uint8 b) {
      b = x*2+1;
    }
  }
|]