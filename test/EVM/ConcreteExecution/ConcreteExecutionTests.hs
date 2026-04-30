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


-- | Set up and run a single contract call, returning the final VM state.
setupAndRunCall :: SourceCode -> ContractName -> FunctionName -> Args -> EVM.Stepper.Stepper Concrete a -> IO a
setupAndRunCall sourceCode contractName functionName abiArgs stepper = do
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
  Effects.runApp $ EVM.Stepper.interpret fetcher withInitializedTransactionVM stepper

executeSingleCall :: SourceCode -> ContractName -> FunctionName -> Args -> IO ExecResult
executeSingleCall src name func args = setupAndRunCall src name func args EVM.Stepper.execFully

executeSingleCallVM :: SourceCode -> ContractName -> FunctionName -> Args -> IO (VM Concrete)
executeSingleCallVM src name func args = setupAndRunCall src name func args EVM.Stepper.runFully

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
  , testCase "console-log-extcodesize-nonzero" $ do
      res <- executeSingleCall consoleLogExtcodesizeExample "C" "a" []
      val <- expectSuccess res
      let obtained = decodeAbiValue (AbiUIntType 256) (BS.fromStrict val)
      assertEqual "extcodesize of console addr should be nonzero" (AbiUInt 256 1) obtained
  , testCase "console-log-returns-correct-value" $ do
      res <- executeSingleCall consoleLogExample "C" "a" [AbiUInt 256 99]
      val <- expectSuccess res
      let obtained = decodeAbiValue (AbiUIntType 256) (BS.fromStrict val)
      assertEqual "return value should be x+1" (AbiUInt 256 100) obtained
  , testCase "console-log-multiple-calls" $ do
      vm <- executeSingleCallVM consoleLogMultipleExample "C" "a" [AbiUInt 256 5]
      let traces = concatMap flatten (traceForest vm)
          consoleLogs = filter (\t -> case t.tracedata of ConsoleLog _ -> True; _ -> False) traces
      assertEqual "Should have 2 console.log traces" 2 (length consoleLogs)
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

consoleLogExtcodesizeExample :: Text
consoleLogExtcodesizeExample = [here|
  contract C {
    function a() public view returns (uint256) {
      address console = 0x000000000000000000636F6e736F6c652e6c6f67;
      uint256 sz;
      assembly { sz := extcodesize(console) }
      return sz;
    }
  }
|]

consoleLogMultipleExample :: Text
consoleLogMultipleExample = [here|
  contract C {
    function a(uint256 x) public view returns (uint256) {
      address console = 0x000000000000000000636F6e736F6c652e6c6f67;
      bytes memory p1 = abi.encodeWithSignature("log(string)", "before");
      (bool s1,) = console.staticcall(p1);
      require(s1);
      bytes memory p2 = abi.encodeWithSignature("log(uint256)", x);
      (bool s2,) = console.staticcall(p2);
      require(s2);
      return x;
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
