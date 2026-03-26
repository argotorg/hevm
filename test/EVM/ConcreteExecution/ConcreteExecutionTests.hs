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
import Data.Tree (flatten)
import Data.Vector qualified as V

import EVM.ABI
import EVM.ConsoleLog (formatConsoleLog)
import EVM.Effects qualified as Effects
import EVM.Fetch qualified as Fetch
import EVM.Solidity (solcRuntime)
import EVM.Solvers (defMemLimit)
import EVM.Stepper qualified
import EVM.Transaction (initTx)
import EVM.Types
import EVM (initialContract, makeVm, defaultVMOpts, traceForest)
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
  initialVM <- stToIO $ makeVm $ defaultVMOpts
    { contract = contractWithCode
    , calldata = (ConcreteBuf callData, [])
    }
  let withInitializedTransactionVM = EVM.Transaction.initTx initialVM
  let fetcher = Fetch.zero 0 Nothing defMemLimit
  Effects.runApp $ EVM.Stepper.interpret fetcher withInitializedTransactionVM EVM.Stepper.execFully

tests :: TestTree
tests = testGroup "Concrete execution tests"
  [ testCase "return-updated-input-argument" $ expectValue (AbiUInt 8 3) =<< executeSingleCall simpleUncheckedArithmeticExample "C" "a" [AbiUInt 8 1]
  , testCase "silent-overflow-in-unchecked-arithmetic" $ expectValue (AbiUInt 8 245) =<< executeSingleCall simpleUncheckedArithmeticExample "C" "a" [AbiUInt 8 250]
  , testCase "revert-on-arithmetic-overflow" $ expectRevert =<< executeSingleCall simpleCheckedArithmeticExample "C" "a" [AbiUInt 8 250]
  , testCase "cheat-assume-satisfied" $ expectValue (AbiUInt 8 42) =<< executeSingleCall assumeCheatCodeExample "C" "a" [AbiUInt 8 42]
  , testCase "cheat-assume-failing" $ expectError AssumeCheatFailed =<< executeSingleCall assumeCheatCodeExample "C" "a" [AbiUInt 8 5]
  , testCase "console-log-does-not-revert" $ do
      res <- executeSingleCall consoleLogExample "C" "a" [AbiUInt 256 42]
      _ <- expectSuccess res
      pure ()
  , testCase "console-log-produces-trace" $ do
      vm <- executeSingleCallVM consoleLogExample "C" "a" [AbiUInt 256 42]
      let traces = concatMap flatten (traceForest vm)
          hasConsoleLog = any (\t -> case t.tracedata of ConsoleLog _ -> True; _ -> False) traces
      assertBool "Expected a ConsoleLog trace" hasConsoleLog
  , testCase "console-log-format-string" $ do
      let encoded = ConcreteBuf $ abiMethod "log(string)" (AbiTuple $ V.fromList [AbiString "hello world"])
      assertEqual "console.log(string) format" "console::log(\"hello world\")" (formatConsoleLog encoded)
  , testCase "console-log-format-uint" $ do
      let encoded = ConcreteBuf $ abiMethod "log(uint256)" (AbiTuple $ V.fromList [AbiUInt 256 42])
      assertEqual "console.log(uint256) format" "console::log(42)" (formatConsoleLog encoded)
  , testCase "console-log-format-string-uint" $ do
      let encoded = ConcreteBuf $ abiMethod "log(string,uint256)" (AbiTuple $ V.fromList [AbiString "count", AbiUInt 256 7])
      assertEqual "console.log(string,uint256) format" "console::log(\"count\", 7)" (formatConsoleLog encoded)
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

expectError :: EvmError -> ExecResult -> IO ()
expectError expectedErr res = do
  err <- assertLeft res
  assertEqual "Incorrect error obtained from concrete execution" expectedErr err

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

executeSingleCallVM :: SourceCode -> ContractName -> FunctionName -> Args -> IO (VM Concrete)
executeSingleCallVM sourceCode contractName functionName abiArgs = do
  runtimeCode <- compileOneContract sourceCode contractName
  let functionSignature = functionName <> "(" <> T.intercalate "," (map (abiTypeSolidity . abiValueType) abiArgs) <> ")"
  let callData = abiMethod functionSignature (AbiTuple $ V.fromList abiArgs)
  let contractWithCode = initialContract (RuntimeCode $ ConcreteRuntimeCode runtimeCode)
  initialVM <- stToIO $ makeVm $ defaultVMOpts
    { contract = contractWithCode
    , calldata = (ConcreteBuf callData, [])
    }
  let withInitializedTransactionVM = EVM.Transaction.initTx initialVM
  let fetcher = Fetch.zero 0 Nothing defMemLimit
  Effects.runApp $ EVM.Stepper.interpret fetcher withInitializedTransactionVM EVM.Stepper.runFully

assumeCheatCodeExample :: Text
assumeCheatCodeExample = [here|
  interface Hevm {function assume(bool) external;}
  contract C {
    function a(uint8 x) public returns (uint8 b) {
      Hevm hevm = Hevm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
      hevm.assume(x > 10);
      b = x;
    }
  }
|]

consoleLogExample :: Text
consoleLogExample = [here|
  contract C {
    function a(uint256 x) public view returns (uint256) {
      address console = 0x000000000000000000636F6e736F6c652e6c6f67;
      bytes memory payload = abi.encodeWithSignature("log(string,uint256)", "value is", x);
      (bool s,) = console.staticcall(payload);
      require(s);
      return x + 1;
    }
  }
|]