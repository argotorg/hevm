{-# LANGUAGE QuasiQuotes #-}

module EVM.Equivalence.EquivalenceTests (tests) where

import Control.Monad (when, unless, forM_)
import Data.ByteString (ByteString)
import Data.Either.Extra (fromRight)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe, fromJust)
import Data.List qualified as List (isInfixOf)
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (diffUTCTime, getCurrentTime)
import System.Environment (lookupEnv)
import System.FilePath (makeRelative, normalise)
import System.FilePath.Find (find, always, filePath, fileType, (&&?), FileType(RegularFile))
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.HUnit
import Text.RE.TDFA.String hiding (matches)
import Text.RE.Replace (replaceAll)


import EVM.Effects qualified as Effects
import EVM.Expr qualified as Expr
import EVM.Format (hexByteString)
import EVM.Types
import EVM.Solidity (solcRuntime, solidity, yul)
import EVM.Solidity qualified as Solidity (CodeType(..))
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.SymExec

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
    calldata <- mkCalldata Nothing []
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
      calldata <- mkCalldata Nothing []
      equivalenceCheck s Nothing a b defaultVeriOpts calldata False
    assertBool "Must have a difference" (any (isCex . fst) eq.res)
    let cexs :: [SMTCex] = mapMaybe (getCex . fst) eq.res
    cex <- case cexs of
      [cex] -> pure cex
      _     -> assertFailure "Must have exactly one cex"
    let def = fromRight (internalError "cannot be") $ defaultSymbolicValues $ subModel cex (AbstractBuf "txdata")
    let buf = prettyBuf $ Expr.concKeccakSimpExpr def
    assertBool "Must start with specific string" (T.isPrefixOf "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0c" buf)
  ]

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
      calldata <- mkCalldata Nothing []
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
                    , "reasoningBasedSimplifier/mulmod.yul"
                    , "loadResolver/multi_sload_loop.yul"
                    , "reasoningBasedSimplifier/mulcheck.yul"
                    , "reasoningBasedSimplifier/smod.yul"
                    , "fullSuite/abi_example1.yul"
                    , "fullInliner/large_function_multi_use.yul"
                    , "loadResolver/merge_known_write_with_distance.yul"
                    , "loadResolver/second_mstore_with_delta.yul"
                    , "rematerialiser/for_continue_2.yul"
                    , "rematerialiser/for_continue_with_assignment_in_post.yul"

                    -- invalid test --
                    -- https://github.com/ethereum/solidity/issues/9500
                    , "commonSubexpressionEliminator/object_access.yul"
                    , "expressionSplitter/object_access.yul"

                    -- stack too deep --
                    , "fullSuite/abi2.yul"
                    , "fullSuite/aztec.yul"
                    , "stackCompressor/inlineInBlock.yul"
                    , "stackCompressor/inlineInFunction.yul"
                    , "stackCompressor/unusedPrunerWithMSize.yul"
                    , "wordSizeTransform/function_call.yul"
                    , "fullInliner/no_inline_into_big_function.yul"
                    , "controlFlowSimplifier/switch_only_default.yul"
                    , "stackLimitEvader" -- all that are in this subdirectory

                    -- typed yul --
                    , "conditionalSimplifier/add_correct_type_wasm.yul"
                    , "conditionalSimplifier/add_correct_type.yul"
                    , "disambiguator/for_statement.yul"
                    , "disambiguator/funtion_call.yul"
                    , "disambiguator/if_statement.yul"
                    , "disambiguator/long_names.yul"
                    , "disambiguator/switch_statement.yul"
                    , "disambiguator/variables_clash.yul"
                    , "disambiguator/variables_inside_functions.yul"
                    , "disambiguator/variables.yul"
                    , "expressionInliner/simple.yul"
                    , "expressionInliner/with_args.yul"
                    , "expressionSplitter/typed.yul"
                    , "fullInliner/multi_return_typed.yul"
                    , "functionGrouper/empty_block.yul"
                    , "functionGrouper/multi_fun_mixed.yul"
                    , "functionGrouper/nested_fun.yul"
                    , "functionGrouper/single_fun.yul"
                    , "functionHoister/empty_block.yul"
                    , "functionHoister/multi_mixed.yul"
                    , "functionHoister/nested.yul"
                    , "functionHoister/single.yul"
                    , "mainFunction/empty_block.yul"
                    , "mainFunction/multi_fun_mixed.yul"
                    , "mainFunction/nested_fun.yul"
                    , "mainFunction/single_fun.yul"
                    , "ssaTransform/typed_for.yul"
                    , "ssaTransform/typed_switch.yul"
                    , "ssaTransform/typed.yul"
                    , "varDeclInitializer/typed.yul"

                    -- New: symbolic index on MSTORE/MLOAD/CopySlice/CallDataCopy/ExtCodeCopy/Revert,
                    --      or exponent is symbolic (requires symbolic gas)
                    --      or SHA3 offset symbolic
                    , "blockFlattener/basic.yul"
                    , "commonSubexpressionEliminator/case2.yul"
                    , "equalStoreEliminator/indirect_inferrence.yul"
                    , "expressionJoiner/reassignment.yul"
                    , "expressionSimplifier/exp_simplifications.yul"
                    , "expressionSimplifier/zero_length_read.yul"
                    , "expressionSimplifier/side_effects_in_for_condition.yul"
                    , "fullSuite/create_and_mask.yul"
                    , "fullSuite/unusedFunctionParameterPruner_return.yul"
                    , "fullSuite/unusedFunctionParameterPruner_simple.yul"
                    , "fullSuite/unusedFunctionParameterPruner.yul"
                    , "loadResolver/double_mload_with_other_reassignment.yul"
                    , "loadResolver/double_mload_with_reassignment.yul"
                    , "loadResolver/double_mload.yul"
                    , "loadResolver/keccak_reuse_basic.yul"
                    , "loadResolver/keccak_reuse_expr_mstore.yul"
                    , "loadResolver/keccak_reuse_msize.yul"
                    , "loadResolver/keccak_reuse_mstore.yul"
                    , "loadResolver/keccak_reuse_reassigned_branch.yul"
                    , "loadResolver/keccak_reuse_reassigned_value.yul"
                    , "loadResolver/keccak_symbolic_memory.yul"
                    , "loadResolver/merge_mload_with_known_distance.yul"
                    , "loadResolver/mload_self.yul"
                    , "loadResolver/keccak_reuse_in_expression.yul"
                    , "loopInvariantCodeMotion/complex_move.yul"
                    , "loopInvariantCodeMotion/move_memory_function.yul"
                    , "loopInvariantCodeMotion/move_state_function.yul"
                    , "loopInvariantCodeMotion/no_move_memory.yul"
                    , "loopInvariantCodeMotion/no_move_storage.yul"
                    , "loopInvariantCodeMotion/not_first.yul"
                    , "ssaAndBack/single_assign_if.yul"
                    , "ssaAndBack/single_assign_switch.yul"
                    , "structuralSimplifier/switch_inline_no_match.yul"
                    , "unusedFunctionParameterPruner/simple.yul"
                    , "unusedStoreEliminator/covering_calldatacopy.yul"
                    , "unusedStoreEliminator/remove_before_revert.yul"
                    , "unusedStoreEliminator/unknown_length2.yul"
                    , "unusedStoreEliminator/unrelated_relative.yul"
                    , "fullSuite/extcodelength.yul"
                    , "unusedStoreEliminator/create_inside_function.yul"-- "trying to reset symbolic storage with writes in create"

                    -- Due to tstorage warnings treated as errors when running solc with --standard-json
                    --   these cannot be currently run. See: https://github.com/ethereum/solidity/issues/15397
                    --   When that fix comes to upstream, we can re-enabled again
                    , "equalStoreEliminator/transient_storage.yul"
                    , "unusedStoreEliminator/tload.yul"
                    , "unusedStoreEliminator/tstore.yul"
                    , "fullSuite/transient_storage.yul"
                    , "unusedPruner/transient_storage.yul"

                    -- Bug in solidity, fixed in newer versions:
                    -- https://github.com/ethereum/solidity/issues/15397#event-14116827816
                    , "no_move_transient_storage.yul"

                    -- to investigate, currently crash
                    , "commonSubexpressionEliminator/long_literals_as_builtin_args.yul"
                    , "disambiguator/string_as_hex_and_hex_as_string.yul"
                    , "fullSuite/sub_objects.yul"
                    , "loadResolver/extstaticcall.yul"
                    , "loadResolver/memory_with_extcall_invalidation.yul"
                    , "loadResolver/zero_length_reads_eof.yul"
                    , "equivalentFunctionCombiner/constant_representation_datasize.yul"
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
            onlyAfter pattern (a:ax) = if a =~ pattern then (a:ax) else onlyAfter pattern ax
            onlyAfter _ [] = []
            replaceOnce pat repl inp = go inp [] where
              go (a:ax) b = if a =~ pat then let a2 = replaceAll repl $ a *=~ pat in b ++ a2:ax
                                        else go ax (b ++ [a])
              go [] b = b

            -- takes a yul program and ensures memory is symbolic by prepending
            -- `calldatacopy(0,0,1024)`. (calldata is symbolic, but memory starts empty).
            -- This forces the exploration of more branches, and makes the test vectors a
            -- little more thorough.
            symbolicMem (a:ax) = if a =~ [re|"^ *object"|] then
                                      let a2 = replaceAll "a calldatacopy(0,0,1024)" $ a *=~ [re|code {|]
                                      in (a2:ax)
                                    else replaceOnce [re|^ *{|] "{\ncalldatacopy(0,0,1024)" $ onlyAfter [re|^ *{|] (a:ax)
            symbolicMem _ = internalError "Program too short"

            unfiltered = lines origcont
            filteredASym = symbolicMem [ x | x <- unfiltered, (not $ x =~ [re|^//|]) && (not $ x =~ [re|^$|]) ]
            filteredBSym = symbolicMem [ replaceAll "" $ x *=~[re|^//|] | x <- onlyAfter [re|^// step:|] unfiltered, not $ x =~ [re|^$|] ]
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
          Right aPrgm <- yul "" $ T.pack $ unlines filteredASym
          Right bPrgm <- yul "" $ T.pack $ unlines filteredBSym
          eq <- Effects.runApp $ withSolvers Bitwuzla 1 (Just 100) defMemLimit $ \s -> do
            calldata <- mkCalldata Nothing []
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