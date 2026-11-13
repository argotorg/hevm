{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module EVM.Equivalence.EquivalenceTests (tests) where

import Control.Monad (when, unless, forM_)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (evalStateT)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Either.Extra (fromRight)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe, fromJust)
import Data.List qualified as List (isInfixOf, nub)
import Data.Map.Strict qualified as Map
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (diffUTCTime, getCurrentTime)
import Data.Vector qualified as V
import System.Environment (lookupEnv)
import System.FilePath (makeRelative, normalise)
import System.FilePath.Find (find, always, filePath, fileType, (&&?), FileType(RegularFile))
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.HUnit
import Text.RE.TDFA.String hiding (matches)
import Text.RE.Replace (replaceAll, captureText, CaptureOrdinal(..), CaptureID(..))


import EVM (makeVm, initialContract, defaultVMOpts)
import EVM.Assembler (assemble, assembleBytes)
import EVM.Effects qualified as Effects
import EVM.Exec (exec)
import EVM.Expr qualified as Expr
import EVM.Format (hexByteString)
import EVM.Types
import EVM.Solidity (solcRuntime, solidity, yul)
import EVM.Solidity qualified as Solidity (CodeType(..))
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.SymExec
import EVM.CexReplay
import EVM.Equivalence

tests :: TestTree
tests = testGroup "Bytecode equivalence tests"
  [ runtimeSolidityEquivalenceTests
  , deploymentSolidityEquivalenceTests
  , bytecodeEquivalenceTests
  , yulEquivalenceTests
  ]


type SourceCode = Text

infix 2 `with`
infix 1 `on`

type Substitution = (Text, Text)
with :: Text -> Text -> Substitution
with = (,)

type SubstitutionJob = (Substitution, Text)
on :: Substitution -> Text -> SubstitutionJob
on = (,)

replace :: SubstitutionJob -> Text
replace ((old, new), txt) =
  case break matches (T.lines txt) of
    (xs, _:ys) -> T.unlines (xs ++ new : ys)
    _          -> internalError "replace: line not found"
  where
    matches line = T.strip line == T.strip old

compile :: SourceCode -> Solidity.CodeType -> IO ByteString
compile sourceCode Solidity.Runtime = solcRuntime "C" sourceCode <&> fromMaybe (internalError "Contract C not present in the given source code")
compile sourceCode Solidity.Creation = solidity "C" sourceCode <&> fromMaybe (internalError "Contract C not present in the given source code")

run :: SourceCode -> SourceCode -> Solidity.CodeType -> IO EqIssues
run s s' codeType = do
  a <- compile s codeType
  b <- compile s' codeType
  Effects.runApp $ withSolvers Bitwuzla 3 Nothing defMemLimit $ \sg -> do
    (calldata, _) <- mkCalldata Nothing []
    equivalenceCheck sg Nothing a b defaultVeriOpts calldata (codeType == Solidity.Creation)

runtimeSolidityEquivalenceTests :: TestTree
runtimeSolidityEquivalenceTests = testGroup "Solidity runtime equivalence"
  [
    testCase "eq-simple-diff" $ do
      let a = [here|
                contract C {
                  function stuff() public returns (uint256) {
                    return 4;
                  }
                }
             |]
      let b = replace $ "return 4;" `with` "return 5;" `on` a
      expectDifference 1 a b
  -- diverging gas overapproximations are caught
  -- previously, they had the same name (gas_...), so they compared equal
  , testCase "eq-partials-not-duplicated" $ do
    let a = [here|
              contract C {
                function stuff(uint n) public returns (uint256) {
                  uint count = 0;
                  for (uint i = 0; i < n; i++) count++;
                  return count;
                }
              }
           |]
        b = replace $ "return count;" `with` "return count + 1;" `on` a
    codeA <- compile a Solidity.Runtime
    codeB <- compile b Solidity.Runtime
    let opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 3 } }
    eq <- Effects.runApp $ withSolvers Bitwuzla 3 Nothing defMemLimit $ \sg -> do
      (calldata, _) <- mkCalldata Nothing []
      equivalenceCheck sg Nothing codeA codeB opts calldata False
    assertBool "Must have partial end states" (not (null eq.partials))
    -- each partial end state used to be reported once per end state of the other program
    assertEqual "Partial end states must not be duplicated" (List.nub eq.partials) eq.partials
  , testCase "eq-divergent-overapprox-gas" $ do
    let a = [here|
              contract C {
                uint x;
                function stuff(uint a) public returns (uint256) {
                  unchecked { x = a * 2; }
                  return gasleft();
                }
              }
            |]
    let b = replace $ "unchecked { x = a * 2; }" `with` "unchecked { x = a + a; }" `on` a
    expectDifference 1 a b
  -- diverging gas overapproximations are caught
  -- previously, CALL fresh variables were the same so they compared equal
  , testCase "eq-divergent-overapprox-call" $ do
    let a = [i|
              contract C {
                function checkval(address inputAddr, uint256 x, uint256 y) public returns (bool) {
                    bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                    (bool success, bytes memory returnData) = inputAddr.staticcall(data);
                    return success;
                }
              }
            |]
    let b = replace $ [here|bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);|]
              `with`  [here|bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, x);|]
              `on` a
    expectDifference 1 a b
  , testCase "eq-unknown-addr" $ do
      let a = [i|
                contract C {
                  address addr;
                  function a(address a, address b) public {
                    addr = a;
                  }
                }
              |]
      let b = replace $ "addr = a;" `with` "addr = b;" `on` a
      expectDifference 1 a b
  , testCase "eq-sol-exp-cex" $ do
      let a = [i|
                contract C {
                  function a(uint8 x) public returns (uint8 b) {
                    unchecked {
                      b = x*2+1;
                    }
                  }
                }
              |]
      let b = replace $ "b = x*2+1;" `with` "b = x<<1;" `on` a
      expectDifference 1 a b
  , testCase "eq-sol-exp-qed" $ do
      let a = [i|
                contract C {
                  function a(uint8 x) public returns (uint8 b) {
                    unchecked {
                      b = x*2;
                    }
                  }
                }
              |]
      let b = replace $ "b = x*2;" `with` "b = x<<1;" `on` a
      expectEquivalent a b
  , testCase "eq-balance-differs" $ do
      let a = [i|
                contract Send {
                  constructor(address payable dst) payable {
                    selfdestruct(dst);
                  }
                }
                contract C {
                  function f() public {
                    new Send{value:2}(payable(address(0x0)));
                  }
                }
              |]
      let b = replace $ "new Send{value:2}(payable(address(0x0)));" `with` "new Send{value:1}(payable(address(0x0)));" `on` a
      expectDifferent a b
  , testCase "eq-storage-write-to-static-array-uint128" $ do
      let a =
            [i|
              contract C {
                uint128[5] arr;
                function set(uint i, uint128 v) external returns (uint) {
                  arr[i] = v;
                  arr[i] = v;
                  return 0;
                }
              }
            |]
      let b = replace $ "arr[i] = v;" `with` "" `on` a -- NOTE: This effectively removes the first occurrence
      expectEquivalent a b
  , testCase "eq-storage-write-to-static-array-uint8" $ do
      let a =
            [i|
              contract C {
                uint8[10] arr;
                function set(uint i, uint8 v) external returns (uint) {
                  arr[i] = v;
                  arr[i] = v;
                  return 0;
                }
              }
            |]
      let b = replace $ "arr[i] = v;" `with` "" `on` a -- NOTE: This effectively removes the first occurrence
      expectEquivalent a b
  , testCase "eq-storage-write-to-static-array-uint32" $ do
      let a =
            [i|
              contract C {
                uint32[5] arr;
                function set(uint i, uint32 v) external returns (uint) {
                  arr[i] = 1;
                  arr[i] = v;
                  return 0;
                }
              }
            |]
      let b = replace $ "arr[i] = 1;" `with` "" `on` a
      expectEquivalent a b
  , ignoreTest $ testCase "eq-handles-contract-deployment" $ do -- TODO: this fails because we don't check equivalence of deployed contracts
      let a = [i|
                contract Send {
                  constructor(address payable dst) payable {
                    selfdestruct(dst);
                  }
                }

                contract A {
                  address parent;
                  constructor(address p) {
                    parent = p;
                  }
                  function evil() public {
                    parent.call(abi.encode(C.drain.selector));
                  }
                }

                contract C {
                  address child;
                  function a() public {
                    child = address(new A(address(this)));
                  }
                  function drain() public {
                    require(msg.sender == child);
                    new Send{value: address(this).balance}(payable(address(0x0)));
                  }
                }
              |]
      let b = [i|
                contract Send {
                  constructor(address payable dst) payable {
                    selfdestruct(dst);
                  }
                }

                contract A {
                  address parent;
                  constructor(address p) {
                      parent = p;
                  }
                }

                contract C {
                  address child;
                  function a() public {
                    child = address(new A(address(this)));
                  }
                  function drain() public {
                    require(msg.sender == child);
                    new Send{value: address(this).balance}(payable(address(0x0)));
                  }
                }
              |]
      expectDifferent a b
  ]
  where
    expectDifference :: Int -> SourceCode -> SourceCode -> IO ()
    expectDifference diffCount s s' = do
      eq <- run s s' Solidity.Runtime
      assertBool "Must have a difference" (any (isCex . fst) eq.res)
      let cexs = mapMaybe (getCex . fst) eq.res
      assertEqual "Must have exactly one cex" diffCount (length cexs)

    expectDifferent :: SourceCode -> SourceCode -> IO ()
    expectDifferent s s' = do
      eq <- run s s' Solidity.Runtime
      assertBool "Must have a difference" (any (isCex . fst) eq.res)

    expectEquivalent :: SourceCode -> SourceCode -> IO ()
    expectEquivalent s s' = do
      eq <- run s s' Solidity.Runtime
      assertEqual "Must have no difference" [] (map fst eq.res)

deploymentSolidityEquivalenceTests :: TestTree
deploymentSolidityEquivalenceTests = testGroup "Solidity deployment equivalence"
  [ testCase "constructor-same-deployed-diff" $ do
      let a = [i|
                contract C {
                  uint public immutable NUMBER;
                  constructor(uint a) {
                    NUMBER = 4;
                  }
                  function stuff(uint b) public returns (uint256) {
                    unchecked{return 2*b+NUMBER;}
                  }
                }
              |]
      let b = replace $ "unchecked{return 2*b+NUMBER;}" `with` "unchecked {return 4*b+NUMBER;}" `on` a
      expectDifferent a b
  , testCase "constructor-same-deployed-diff2" $ do
      let aBody = [i|
                    uint public immutable NUMBER;
                    constructor(uint a) {
                      NUMBER = 4;
                    }
                    function stuff(uint b) public returns (uint256) {
                      unchecked{return 4*b+NUMBER;}
                    }
                  |]
      let bBody = aBody
            <> [i|
                function stuff_other(uint b) public returns (uint256) {
                  unchecked {return 2*b+NUMBER;}
                }
              |]
      let a = wrap aBody
      let b = wrap bBody
      expectDifferent a b
  , testCase "constructor-same-deployed-diff3" $ do
      let aBody = [i|
                    uint public immutable NUMBER;
                    constructor(uint a) {
                      NUMBER = 4;
                    }
                  |]
      let bBody = aBody
            <> [i|
                function stuff(uint b) public returns (uint256) {
                    unchecked{return 4*b+NUMBER;}
                }
                |]
      let a = wrap aBody
      let b = wrap bBody
      expectDifferent a b

  -- We set x to be 0 on deployment. Default value is also 0. So they are equivalent
  -- We cannot deal with symbolic code. However, the below will generate symbolic code,
  -- because of the parameter in the constructor that is set to NUMBER in the deployed code.
  -- Hence, this test is ignored.
  , ignoreTest $ testCase "constructor-diff-deploy" $ do
    let a = [i|
              contract C {
                uint public immutable NUMBER;
                constructor(uint a) {
                  NUMBER = a+4;
                }
                function stuff(uint b) public returns (uint256) {
                  return NUMBER;
                }
              }
            |]
    let b = replace $ "NUMBER = a+4;" `with` "NUMBER = a*2;" `on` a
    expectDifferent a b
  -- We set x to be 0 on deployment. Default value is also 0. So they are equivalent
  , testCase "constructor-implicit" $ do
    let aBody = [i|
                  uint immutable x;
                  function stuff(uint a) public returns (uint256) {
                    unchecked {return 8+a;}
                  }
                |]
    let bBody = aBody <> "constructor() {x = 0;}"
    let a = wrap aBody
    let b = wrap bBody
    expectEquivalent a b
  -- We set x to be 3 vs 0 (default) on deployment.
  , testCase "constructor-differing" $ do
    let aBody = [i|
                  uint x;
                  function stuff(uint a) public returns (uint256) {
                    unchecked {return a+x;}
                  }
                |]
    let bBody = aBody <> "constructor() {x = 3;}"
    let a = wrap aBody
    let b = wrap bBody
    expectDifferent a b
  -- A writes 0 to slot 1, B leaves it unset; both read as 0
  , testCase "storage-zero-same-as-unset" $ do
    let a = [i|
              contract C {
                uint a = 1;
                uint b = 0;
                function get() public view returns (uint, uint) { return (a, b); }
              }
            |]
    let b = replace $ "uint b = 0;" `with` "uint b;" `on` a
    expectEquivalent a b
  , testCase "storage-nonzero-differs-from-unset" $ do
    let a = [i|
              contract C {
                uint a = 1;
                uint b = 2;
                function get() public view returns (uint) { return a; }
              }
            |]
    let b = replace $ "uint b = 2;" `with` "uint b;" `on` a
    expectDifferent a b
  ]
  where
    expectDifferent :: SourceCode -> SourceCode -> IO ()
    expectDifferent s s' = do
      eq <- run s s' Solidity.Creation
      assertBool "Must have a difference" (any (isCex . fst) eq.res)

    expectEquivalent :: SourceCode -> SourceCode -> IO ()
    expectEquivalent s s' = do
      eq <- run s s' Solidity.Creation
      assertEqual "Must have no difference" [] (map fst eq.res)

    wrap body = "contract C {\n" <> body <> "}"

bytecodeEquivalenceTests :: TestTree
bytecodeEquivalenceTests = testGroup "Bytecode equivalence"
  [ testCase "eq-issue-with-length-cex-bug679" $ do -- check bug https://github.com/argotorg/hevm/issues/679
    let a = fromJust (hexByteString "5f610100526020610100f3")
        b = fromJust (hexByteString "5f356101f40115610100526020610100f3")
    eq <- Effects.runApp $ withSolvers Z3 1 Nothing defMemLimit $ \s -> do
      (calldata, _) <- mkCalldata Nothing []
      equivalenceCheck s Nothing a b defaultVeriOpts calldata False
    assertBool "Must have a difference" (any (isCex . fst) eq.res)
    let cexs :: [SMTCex] = mapMaybe (getCex . fst) eq.res
    cex <- case cexs of
      [cex] -> pure cex
      _     -> assertFailure "Must have exactly one cex"
    let def = fromRight (internalError "cannot be") $ defaultSymbolicValues $ subModel cex (AbstractBuf "txdata")
    let buf = prettyBuf $ Expr.concKeccakSimpExpr def
    assertBool "Must start with specific string" (T.isPrefixOf "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0c" buf)
  -- calls to unknown code with the same inputs must give the same results (#1116)
  , testCase "eq-call-same-inputs-same-result" $ do
    eq <- eqBytecode False (sCall "1234" "5f" <> pop <> revertRet) ("5b" <> sCall "1234" "5f" <> pop <> revertRet)
    assertEqual "must be equivalent" [] (map fst eq.res)
  , testCase "eq-call-different-calldata" $ do
    eq <- eqBytecode False (sCall "1234" "5f" <> pop <> revertRet) (sCall "1234" "6001" <> pop <> revertRet)
    assertBool "different calldata may give different results" (any (isCex . fst) eq.res)
  , testCase "eq-call-after-extra-view-call" $ do
    eq <- eqBytecode False (sCall "1234" "5f" <> pop <> revertRet)
                           (sCall "5678" "5f" <> pop <> sCall "1234" "5f" <> pop <> revertRet)
    assertEqual "a view call does not change later results" [] (map fst eq.res)
  , testCase "eq-call-twice-in-one-program" $ do
    -- returns whether two identical calls succeeded differently, vs making the call once and
    -- returning 0 (so that both touch the same accounts)
    eq <- eqBytecode False (sCall "1234" "5f" <> sCall "1234" "5f" <> "1415" <> "5f52" <> "60205ff3")
                           (sCall "1234" "5f" <> pop <> "5f5f5260205ff3")
    assertBool "the callee can read GAS, so identical calls may disagree (#1201)" (any (isCex . fst) eq.res)
  , testCase "eq-call-twice-in-both-programs" $ do
    let twice = sCall "1234" "5f" <> sCall "1234" "5f" <> "1415" <> "5f52" <> "60205ff3"
    eq <- eqBytecode False twice ("5b" <> twice)
    assertEqual "the n-th identical call of A and B must agree" [] (map fst eq.res)
  , testCase "eq-staticcall-in-one-program" $ do
    eq <- eqBytecode False (sCall "1234" "5f" <> pop) ""
    assertBool "a view call whose result is unused changes nothing" (null eq.res)
  , testCase "eq-transient-storage-starts-empty" $ do
    -- tload(0) is zero, so this stops in both
    eq <- eqBytecode False "5f5c15600757fe5b00" "00"
    assertBool "transient storage must start empty" (null eq.res)
  , testCase "eq-block-number-is-symbolic" $ do
    -- sstore(1, 0) vs sstore(1, number())
    eq <- eqBytecode False "5f600155" "43600155"
    assertBool "the block number may be nonzero" (any (isCex . fst) eq.res)
  , testCase "eq-timestamp-is-symbolic" $ do
    -- sstore(1, 0) vs sstore(1, timestamp())
    eq <- eqBytecode False "5f600155" "42600155"
    assertBool "the timestamp may be nonzero" (any (isCex . fst) eq.res)
  , testCase "eq-revert-data-length-differs" $ do
    eq <- uncurry eqOps (zerosOfLen32vs31 OpRevert)
    assertBool "32 vs 31 bytes of revert data" (any (isCex . fst) eq.res)
  , testCase "eq-return-data-length-differs" $ do
    eq <- uncurry eqOps (zerosOfLen32vs31 OpReturn)
    assertBool "32 vs 31 bytes of return data" (any (isCex . fst) eq.res)
  , testCase "eq-calldataload-near-max-offset-is-zero" $ do
    -- sstore(0, calldataload(2^256-1)) vs sstore(0, 0)
    eq <- eqBytecode False "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff355f55" "5f5f55"
    assertBool "reading past the end of calldata gives zero" (null eq.res)
  , testCase "eq-calldataload-near-max-offset-does-not-wrap" $ do
    -- sstore(0, calldataload(2^256-1)) vs sstore(0, shr(8, calldataload(0)))
    eq <- eqBytecode False "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff355f55" "5f3560081c5f55"
    assertBool "the read must not wrap around to the start of calldata" (any (isCex . fst) eq.res)
  , testCase "eq-call-moves-its-value" $ do
    eq <- eqBytecode True (call "1234" <> pop) (callWithWei "1234" <> pop)
    assertBool "the callee gets the value" (any (isCex . fst) eq.res)
  , testCase "eq-replay-compares-balances" $ do
    -- selfdestruct(0x1234) vs stop
    replays <- replayAll "611234ff" "00"
    assertBool "Must have a counterexample" (not (null replays))
    forM_ replays $ \case
      Validated {} -> pure ()
      r -> assertFailure $ "Counterexample must replay as validated, got: " <> show r
  , testCase "eq-call-may-send-ether-back" $ do
    -- sstore(0, selfbalance()) after the call vs with the balance from before it
    eq <- eqBytecode True (call "1234" <> pop <> "475f55") ("47" <> call "1234" <> pop <> "5f55")
    assertBool "the callee may send the caller ether" (any (isCex . fst) eq.res)
  , testCase "eq-call-after-same-state-changing-call" $ do
    eq <- eqBytecode True (call "1234" <> pop <> sCall "5678" "5f" <> pop <> revertRet)
                          ("5b" <> call "1234" <> pop <> sCall "5678" "5f" <> pop <> revertRet)
    assertEqual "must be equivalent" [] (map fst eq.res)
  , testCase "eq-call-after-state-changing-call-in-one-program" $ do
    eq <- eqBytecode True (call "1234" <> pop <> sCall "5678" "5f" <> pop <> revertRet)
                          (sCall "5678" "5f" <> pop <> revertRet)
    assertBool "a state-changing call may change later results" (any (isCex . fst) eq.res)
  , testCase "eq-replay-validates-storage-difference" $ do
    -- sstore(0, 1) vs sstore(0, 2)
    replays <- replayAll "6001600055" "6002600055"
    assertBool "Must have a counterexample" (not (null replays))
    forM_ replays $ \case
      Validated ra rb -> assertBool "Replay must show the different stores" (ra /= rb)
      r -> assertFailure $ "Counterexample must replay as validated, got: " <> show r
  , testCase "eq-created-contracts-differ" $ forM_
    -- the salt (#1193)
    [ (returnTop (create2 1 []), returnTop (create2 2 []))
    , (returnTop (create []), returnTop (create2 1 []))
    -- the child's runtime code (#1192)
    , (returnTop (create (deploy OpStop)), returnTop (create (deploy OpInvalid)))
    -- what the child's constructor stores (#1178)
    , (create (storeAt0 1) <> [OpPop], create (storeAt0 2) <> [OpPop])
    -- a CREATE bumps the nonce even when it deploys nothing
    , (create [] <> [OpPop], [OpStop])
    ] $ \(a, b) -> do
      replays <- replayCode (assembleBytes a) (assembleBytes b)
      assertBool ("Must have a counterexample: " <> show (a, b)) (not (null replays))
      forM_ replays $ \case
        Validated {} -> pure ()
        r -> assertFailure $ "Counterexample must replay as validated, got: " <> show r
  , testCase "eq-same-create2-equivalent" $ do
    -- the entrypoints differ, but the created contract and the returned address don't
    let a = returnTop (create2 1 [])
    eq <- eqCode False (assembleBytes a) (assembleBytes (a <> [OpStop]))
    assertBool ("Must be equivalent, got: " <> show eq.res) (null eq.res)
  , testCase "eq-replay-zero-write-over-nonzero-slot" $ do
    -- stop vs sstore(1, 0): they differ only if slot 1 starts nonzero, so the model must give its value
    replays <- replayAll "00" "5f600155"
    assertBool "Must have a counterexample" (not (null replays))
    forM_ replays $ \case
      Validated {} -> pure ()
      r -> assertFailure $ "Counterexample must replay as validated, got: " <> show r
  , testCase "eq-replay-answers-calls-to-unknown-code" $ do
    -- STATICCALL(gas, 0x1234, 0, 0, 0, 32), then sstore(0, mload(0) == 5) vs sstore(0, 0)
    let callOut = "60205f5f5f6112345afa50"
    replays <- replayAll (callOut <> "5f516005145f55") (callOut <> "5f5f55")
    assertBool "Must have a counterexample" (not (null replays))
    forM_ replays $ \case
      Validated {} -> pure ()
      r -> assertFailure $ "The callee must answer as in the counterexample, got: " <> show r
  , testCase "eq-replay-keeps-long-returndata-compact" $ do
    -- the model makes the return data 16 MB long, with one nonzero byte
    let out = AbstractBuf "out"
        inputs = CallInputs (Lit 0) (Lit 0xfa) (Lit 0x1234) (Lit 0) (ConcreteBuf "") (Lit 0) (LitAddr 0xacab)
          (AbstractStore (LitAddr 0xacab) Nothing) (ConcreteStore mempty) (Lit 0) (Lit 0)
        cex = (mempty :: SMTCex) { buffers = Map.singleton out (EVM.Types.Comp (Write 7 3 (Base 0 (2 ^ (24 :: Int))))) }
    case modelUnknownCalls cex [PCall inputs (Lit 1) out Nothing] of
      [Right m] -> do
        assertEqual "only the bytes up to the last nonzero one are kept" (BS.pack [0, 0, 0, 7]) m.returndata
        assertEqual "the length is kept" (2 ^ (24 :: Int)) m.returndataLength
      r -> assertFailure $ "Must model the call, got: " <> show r
  , testCase "eq-replay-stub-pads-returndata-with-zeros" $ do
    -- the calldata is longer than the given part of the returndata
    let input = BS.replicate 40 0xaa
        code = stubCode [(input, (True, BS.pack [7], 64))]
    res <- stToIO $ do
      vm <- makeVm @Concrete $ (defaultVMOpts @Concrete)
        { contract = initialContract (RuntimeCode (ConcreteRuntimeCode code))
        , calldata = (ConcreteBuf input, [])
        , gas = 0xffffffffffffffff
        , gaslimit = 0xffffffffffffffff
        }
      evalStateT (exec Effects.defaultConfig) vm
    case res of
      VMSuccess (ConcreteBuf out) -> assertEqual "the rest of the returndata is zero" (BS.pack [7] <> BS.replicate 63 0) out
      r -> assertFailure $ "The stub must return, got: " <> show r
  , testCase "eq-replay-equal-programs-not-reproducible" $ do
    -- sstore(0, 1), and the same after a JUMPDEST
    let a = fromJust (hexByteString "6001600055")
        b = fromJust (hexByteString "5b6001600055")
    r <- Effects.runApp $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \s ->
      replayEqCex s False a b (AbstractBuf "txdata") mempty
    case r of
      NotReproducible {} -> pure ()
      _ -> assertFailure $ "Replay of equal programs must not reproduce, got: " <> show r
  ]
  where
    -- STATICCALL(gas, addr, 0, size, 0, 0), size pushed by the given op
    sCall addr size = "5f5f" <> size <> "5f61" <> addr <> "5afa"
    -- CALL(gas, addr, 0, 0, 0, 0, 0)
    call addr = "5f5f5f5f5f61" <> addr <> "5af1"
    -- CALL(gas, addr, 1, 0, 0, 0, 0)
    callWithWei addr = "5f5f5f5f600161" <> addr <> "5af1"
    pop = "50"
    -- revert with the last call's return data
    revertRet = "3d5f5f3e3d5ffd"
    -- both halt with all-zero data: the byte stored in B is byte(0, iszero(..)), i.e. always 0
    zerosOfLen32vs31 :: Op -> ([Op], [Op])
    zerosOfLen32vs31 halt =
      ( [OpPush (Lit 32), OpPush (Lit 4), halt]
      , [ OpPush0, OpCalldataload, OpIszero, OpPush0, OpByte, OpPush (Lit 31), OpMstore
        , OpPush (Lit 31), OpPush (Lit 32), halt ] )
    push = OpPush . Lit
    -- the init code, at most 32 bytes, is a word in memory; they leave the new address
    create code = storeCode code <> [push (codeSize code), push 0, push 0, OpCreate]
    create2 salt code = storeCode code <> [push salt, push (codeSize code), push 0, push 0, OpCreate2]
    storeCode code = let bs = assembleBytes code in [push (word (bs <> BS.replicate (32 - BS.length bs) 0)), push 0, OpMstore]
    codeSize = fromIntegral . BS.length . assembleBytes
    deploy o = [push (fromIntegral (BS.head (assembleBytes [o]))), push 0, OpMstore8, push 1, push 0, OpReturn]
    storeAt0 v = [push v, push 0, OpSstore, push 0, push 0, OpReturn]
    returnTop ops = ops <> [push 0, OpMstore, push 0x20, push 0, OpReturn]
    eqOps :: [Op] -> [Op] -> IO EqIssues
    eqOps a b = eqCode False (asm a) (asm b)
      where asm = BS.pack . mapMaybe Expr.maybeLitByteSimp . V.toList . assemble
    eqBytecode :: Bool -> ByteString -> ByteString -> IO EqIssues
    eqBytecode noReent ha hb = eqCode noReent (fromJust (hexByteString ha)) (fromJust (hexByteString hb))
    eqCode :: Bool -> ByteString -> ByteString -> IO EqIssues
    eqCode noReent a b = do
      let env = Effects.Env { config = Effects.defaultConfig { Effects.promiseNoReent = noReent } }
      Effects.runEnv env $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \s -> do
        (calldata, _) <- mkCalldata Nothing []
        equivalenceCheck s Nothing a b defaultVeriOpts calldata False
    replayAll :: ByteString -> ByteString -> IO [CexReplay]
    replayAll ha hb = replayCode (fromJust (hexByteString ha)) (fromJust (hexByteString hb))
    replayCode :: ByteString -> ByteString -> IO [CexReplay]
    replayCode a b =
      Effects.runApp $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \s -> do
        (calldata, _) <- mkCalldata Nothing []
        eq <- equivalenceCheck s Nothing a b defaultVeriOpts calldata False
        mapM (replayEqCex s False a b (AbstractBuf "txdata")) (mapMaybe (getCex . fst) eq.res)

yulEquivalenceTests :: TestTree
yulEquivalenceTests = testGroup "Yul equivalence"
  [ testCase "eq-yul-simple-cex" $ do
    let a = [i|
              {
                calldatacopy(0, 0, 32)
                switch mload(0)
                case 0 { }
                case 1 { }
                default { invalid() }
              }
            |]
    let b = replace $ "case 1 { }" `with` "case 2 { }" `on` a
    Right aPrgm <- yul "" a
    Right bPrgm <- yul "" b
    eq <- Effects.runApp $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \s -> do
      (calldata, _) <- mkCalldata Nothing []
      equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
    assertBool "Must have a difference" (any (isCex . fst) eq.res)
  , yulOptimizationsSolcTests
  ]

yulOptimizationsSolcTests :: TestTree
yulOptimizationsSolcTests = testCase "eq-all-yul-optimization-tests" $ do
        let opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 5, askSmtIters = 20, loopHeuristic = Naive }}
            ignoredTests = fmap normalise
                    -- unbounded loop --
                    [ "commonSubexpressionEliminator/branches_for.yul"
                    , "conditionalSimplifier/no_opt_if_break_is_not_last.yul"
                    , "conditionalUnsimplifier/no_opt_if_break_is_not_last.yul"
                    , "expressionSimplifier/inside_for.yul"
                    , "forLoopConditionIntoBody/cond_types.yul"
                    , "forLoopConditionIntoBody/simple.yul"
                    , "fullSimplify/inside_for.yul"
                    , "fullSuite/no_move_loop_orig.yul"
                    , "loopInvariantCodeMotion/multi.yul"
                    , "redundantAssignEliminator/for_deep_simple.yul"
                    , "unusedAssignEliminator/for_deep_noremove.yul"
                    , "unusedAssignEliminator/for_deep_simple.yul"
                    , "ssaTransform/for_def_in_init.yul"
                    , "loopInvariantCodeMotion/simple_state.yul"
                    , "loopInvariantCodeMotion/simple.yul"
                    , "loopInvariantCodeMotion/recursive.yul"
                    , "loopInvariantCodeMotion/no_move_staticall_returndatasize.yul"
                    , "loopInvariantCodeMotion/no_move_state_loop.yul"
                    , "loopInvariantCodeMotion/no_move_state.yul" -- not infinite, but rollaround on a large int
                    , "loopInvariantCodeMotion/no_move_loop.yul"

                    -- infinite recursion
                    , "unusedStoreEliminator/function_side_effects_2.yul"
                    , "unusedStoreEliminator/write_before_recursion.yul"
                    , "fullInliner/multi_fun_callback.yul"
                    , "conditionalUnsimplifier/side_effects_of_functions.yul"
                    , "expressionInliner/double_recursive_calls.yul"
                    , "conditionalSimplifier/side_effects_of_functions.yul"

                    -- Takes too long, would timeout on most test setups.
                    -- We could probably fix these by "bunching together" queries
                    , "loadResolver/multi_sload_loop.yul"
                    , "fullSuite/abi_example1.yul"
                    , "loadResolver/merge_known_write_with_distance.yul"
                    , "loadResolver/second_mstore_with_delta.yul"
                    , "stackLimitEvader" -- all that are in this subdirectory

                    -- stack too deep --
                    , "fullSuite/aztec.yul"
                    , "stackCompressor/unusedPrunerWithMSize.yul"

                    -- New: symbolic index on MSTORE/MLOAD/CopySlice/CallDataCopy/ExtCodeCopy/Revert,
                    --      or exponent is symbolic (requires symbolic gas)
                    --      or SHA3 offset symbolic
                    , "expressionSimplifier/exp_simplifications.yul"
                    , "loadResolver/merge_mload_with_known_distance.yul"
                    , "loopInvariantCodeMotion/complex_move.yul"
                    , "loopInvariantCodeMotion/no_move_memory.yul"
                    , "loopInvariantCodeMotion/no_move_storage.yul"
                    -- EOF
                    , "loadResolver/extstaticcall.yul"
                    , "loadResolver/memory_with_extcall_invalidation.yul"
                    , "loadResolver/zero_length_reads_eof.yul"
                    -- Yul subobjects
                    , "fullSuite/sub_objects.yul"
                    ]

        solcRepo <- fromMaybe (internalError "cannot find solidity repo") <$> (lookupEnv "HEVM_SOLIDITY_REPO")
        let testDir = normalise $ solcRepo <> "/test/libyul/yulOptimizerTests"
            shouldIgnore fp = any (`List.isInfixOf` (makeRelative testDir fp)) ignoredTests
            isRegularFile = (== RegularFile) <$> fileType
        filesFiltered <- find always (isRegularFile &&? (not . shouldIgnore <$> filePath)) testDir

        -- Takes one file which follows the Solidity Yul optimizer unit tests format,
        -- extracts both the nonoptimized and the optimized versions, and checks equivalence.
        forM_ filesFiltered (\f-> do
          origcont <- readFile f
          let
            onlyAfter pattern (a:ax) = if a =~ pattern then ax else onlyAfter pattern ax
            onlyAfter _ [] = []
            replaceOnce pat repl inp = go inp [] where
              go (a:ax) b = if a =~ pat then let a2 = replaceAll repl $ a *=~ pat in b ++ a2:ax
                                        else go ax (b ++ [a])
              go [] b = b

            -- takes a yul program and ensures memory is symbolic by prepending
            -- `calldatacopy(0,0,1024)`. (calldata is symbolic, but memory starts empty).
            -- This forces the exploration of more branches, and makes the test vectors a
            -- little more thorough.
            symbolicMem program@(a:_) = if a =~ [re|^ *object|] then
                                      let replacementTemplate = "$0\n    calldatacopy(0,0,1024)"
                                          replaced = replaceAll replacementTemplate $ (unlines program) *=~ [re|code {|]
                                      in lines replaced
                                    else replaceOnce [re|^ *{|] "{\ncalldatacopy(0,0,1024)" program
            symbolicMem _ = internalError "Program too short"

            unfiltered = lines origcont
            filteredASym = symbolicMem [ x | x <- unfiltered, (not $ x =~ [re|^//|]) && (not $ x =~ [re|^$|]) ]
            filteredBSym = symbolicMem [ cleaned | x <- onlyAfter [re|^// step:|] unfiltered
                                        , let cleaned = replaceAll "" $ x *=~[re|^//|]
                                        , not $ null cleaned
                                       ]
            contractName = let
               match = head filteredASym ?=~ [re|^ *object +"([^"]+)"|]
               success = captureText (IsCaptureOrdinal $ CaptureOrdinal 1) match
             in T.pack $ case matched match of
                  False -> ""
                  True-> success
          start <- getCurrentTime
          let verbosity :: Int = 0
          when (verbosity > 0) $ putStrLn $ "Checking file: " <> f
          when (verbosity > 1) $ do
            putStrLn "-------------Original Below-----------------"
            mapM_ putStrLn unfiltered
            putStrLn "------------- Filtered A + Symb below-----------------"
            mapM_ putStrLn filteredASym
            putStrLn "------------- Filtered B + Symb below-----------------"
            mapM_ putStrLn filteredBSym
            putStrLn "------------- END -----------------"
          Right aPrgm <- yul contractName $ T.pack $ unlines filteredASym
          Right bPrgm <- yul contractName $ T.pack $ unlines filteredBSym
          eq <- Effects.runApp $ withSolvers Bitwuzla 1 (Just 100) defMemLimit $ \s -> do
            (calldata, _) <- mkCalldata Nothing []
            equivalenceCheck s Nothing aPrgm bPrgm opts calldata False
          let res = map fst eq.res
          end <- getCurrentTime
          case any isCex res of
            False -> do
              when (verbosity > 0) $ print $ "OK. Took " <> (show $ diffUTCTime end start) <> " seconds"
              let timeouts = filter isUnknown res
              let errors = filter isError res
              unless (null timeouts && null errors) $ do
                putStrLn $ "But " <> (show $ length timeouts) <> " timeout(s) and " <>  (show $ length errors) <> " error(s) occurred"
                assertFailure "Encountered timeout(s) and/or error(s)"
            True -> do
              putStrLn $ "Not OK: " <> show f <> " Got: " <> show res
              assertFailure "Was NOT equivalent"
           )