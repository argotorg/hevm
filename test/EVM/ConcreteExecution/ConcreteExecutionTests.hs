{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ImplicitParams #-}

module EVM.ConcreteExecution.ConcreteExecutionTests (tests) where

import Control.Monad (forM_)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (execStateT, liftIO)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, isNothing, mapMaybe)
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Tree (flatten)
import Data.Vector qualified as V
import Witch (into)

import EVM.ABI
import EVM.Assembler (assemble)
import EVM.ConsoleLog (formatConsoleLog)
import EVM.Effects qualified as Effects
import EVM.Exec (vmForEthrunCreation)
import EVM.Expr (maybeLitByteSimp)
import EVM.Fetch qualified as Fetch
import EVM.Precompiled (execute)
import EVM.Solidity (solcRuntime)
import EVM.Solvers (defMemLimit)
import EVM.Stepper qualified
import EVM.SymExec
import EVM.Transaction (initTx)
import EVM.Types
import EVM qualified
import EVM (initialContract, makeVm, defaultVMOpts, traceForest)
import EVM.Test.Helpers
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
  , testGroup "Console log formatting"
    [ testCase "format-string" $ do
        let encoded = ConcreteBuf $ abiMethod "log(string)" (AbiTuple $ V.fromList [AbiString "hello world"])
        assertEqual "console.log(string) format" "console::log(\"hello world\")" (formatConsoleLog encoded)
    , testCase "format-uint" $ do
        let encoded = ConcreteBuf $ abiMethod "log(uint256)" (AbiTuple $ V.fromList [AbiUInt 256 42])
        assertEqual "console.log(uint256) format" "console::log(42)" (formatConsoleLog encoded)
    , testCase "format-string-uint" $ do
        let encoded = ConcreteBuf $ abiMethod "log(string,uint256)" (AbiTuple $ V.fromList [AbiString "count", AbiUInt 256 7])
        assertEqual "console.log(string,uint256) format" "console::log(\"count\", 7)" (formatConsoleLog encoded)
    , testCase "format-bool" $ do
        let encoded = ConcreteBuf $ abiMethod "log(bool)" (AbiTuple $ V.fromList [AbiBool True])
        assertEqual "console.log(bool) format" "console::log(true)" (formatConsoleLog encoded)
    , testCase "format-address" $ do
        let encoded = ConcreteBuf $ abiMethod "log(address)" (AbiTuple $ V.fromList [AbiAddress 0xdeadbeef])
        assertEqual "console.log(address) format" "console::log(0x00000000000000000000000000000000DeaDBeef)" (formatConsoleLog encoded)
    , testCase "format-no-args" $ do
        let encoded = ConcreteBuf $ abiMethod "log()" (AbiTuple $ V.fromList [])
        assertEqual "console.log() format" "console::log()" (formatConsoleLog encoded)
    , testCase "format-unknown-selector" $ do
        let encoded = ConcreteBuf $ BS.pack [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02]
        let result = formatConsoleLog encoded
        assertBool "unknown selector should produce hex fallback" (T.isPrefixOf "console::log(0x" result)
    , testCase "format-short-input" $ do
        let encoded = ConcreteBuf $ BS.pack [0x01, 0x02]
        assertEqual "short input format" "console::log()" (formatConsoleLog encoded)
    ]
  , testGroup "Storage fetch cache"
    [ test "accessStorage-uses-fetched-storage" $ do
        let dummyContract =
              (initialContract (RuntimeCode (ConcreteRuntimeCode mempty)))
                { external = True }
        vm :: VM Concrete <- liftIO $ stToIO $ vmForEthrunCreation ""
        -- perform the initial access
        let ?conf = testEnv.config
        vm1 <- liftIO $ stToIO $ execStateT (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm
        -- it should fetch the contract first
        vm2 <- case vm1.result of
                Just (HandleEffect (Query (PleaseFetchContract _addr _ continue))) ->
                  liftIO $ stToIO $ execStateT (continue dummyContract) vm1
                _ -> internalError "unexpected result"
        -- then it should fetch the slot
        vm3 <- case vm2.result of
                Just (HandleEffect (Query (PleaseFetchSlot _addr _slot continue))) ->
                  liftIO $ stToIO $ execStateT (continue 1337) vm2
                _ -> internalError "unexpected result"
        -- perform the same access as for vm1
        vm4 <- liftIO $ stToIO $ execStateT (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm3

        -- there won't be query now as accessStorage uses fetch cache
        assertBoolM (show vm4.result) (isNothing vm4.result)
    ]
  , testGroup "Precompiled contracts"
      [ testGroup "Example (reverse)"
          [ test "reverses-input" $
              assertEqualM "example contract reverses"
                (execute 0xdeadbeef "foobar" 6) (Just "raboof")
          , test "rejects-length-mismatch" $
              assertEqualM "example contract fails on length mismatch"
                (execute 0xdeadbeef "foobar" 5) Nothing
          ]

      , testGroup "ECRECOVER"
          [ test "recovers-signer" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4732"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
                a = hex "0000000000000000000000002d5e56d45c63150d937f2182538a0f18510cb11f"
              assertEqualM "successful recovery"
                (Just a)
                (execute 1 (h <> v <> r <> s) 32)
          , test "rejects-v-other-than-27-or-28" $ forM_ [0x1d, 0x1e] $ \v -> do
              let
                h = BS.replicate 31 0 <> BS.singleton 1
                vw = BS.replicate 31 0 <> BS.singleton v
                r = BS.replicate 31 0 <> BS.singleton 2
                s = BS.replicate 31 0 <> BS.singleton 1
              assertEqualM "v must be rejected" Nothing (execute 1 (h <> vw <> r <> s) 32)
          , test "rejects-made-up-values" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4731"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
              assertEqualM "fail because bit flip"
                Nothing
                (execute 1 (h <> v <> r <> s) 32)
          ]
      , testGroup "Unimplemented"
          [ test "concrete-call-gives-nonexistent-precompile" $ forM_ [0x0a, 0x10, 0x11, 0x100 :: Addr] $ \a -> do
              let code = BS.pack . mapMaybe maybeLitByteSimp $ V.toList $ assemble
                    [ OpPush (Lit 0)
                    , OpPush (Lit 0)
                    , OpPush (Lit 0)
                    , OpPush (Lit 0)
                    , OpPush (Lit (into a))
                    , OpGas
                    , OpStaticcall
                    , OpStop
                    ]
              vm <- liftIO $ stToIO $ vmForEthrunCreation code
              vm' <- EVM.Stepper.interpret (Fetch.zero 0 Nothing 1024) vm EVM.Stepper.runFully
              case vm'.result of
                Just (VMFailure (NonexistentPrecompile a')) -> assertEqualM "wrong address" a a'
                r -> liftIO $ assertFailure $ "unexpected result for " <> show a <> ": " <> show r
          , test "symbolic-call-gives-partial" $ do
              Just c <- solcRuntime "C" [i|
                  contract C {
                    function fun() public {
                      (bool success, ) = address(0x10).staticcall("");
                      assert(success);
                    }
                  } |]
              (e, _) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just $ Sig "fun()" []) [] defaultVeriOpts
              assertBoolM "expected a PrecompileMissing partial" $ any isPartial e
          ]
      ]
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
