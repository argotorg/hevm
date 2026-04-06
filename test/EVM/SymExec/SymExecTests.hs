{-# LANGUAGE QuasiQuotes #-}

module EVM.SymExec.SymExecTests (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure

import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (ReaderT)
import Data.ByteString (ByteString)
import Data.List qualified as List (isInfixOf)
import Data.Maybe (isJust, mapMaybe)
import Data.Monoid (Any(..))
import Data.String.Here

import EVM.ABI
import EVM.Effects qualified as Effects
import EVM.Expr qualified as Expr
import EVM.Types
import EVM.SMT qualified as SMT (getVar)
import EVM.Solidity (solcRuntime)
import EVM.Solvers (withSolvers, defMemLimit, Solver(..), SolverGroup)
import EVM.SymExec
import EVM.Traversals


tests :: TestTree
tests = testGroup "Symbolic execution"
  [solidityExplorationTests]

solidityExplorationTests :: TestTree
solidityExplorationTests = testGroup "Exploration of Solidity"
    [ basicTests
    , maxDepthTests
    , copySliceTests
    , storageTests
    , panicCodeTests
    , cheatCodeTests
    , arithmeticTests
    ]

basicTests :: TestTree
basicTests = testGroup "simple-checks"
  [ testCase "simple-stores" $ do
    Just c <- solcRuntime "MyContract"
      [i|
      contract MyContract {
        mapping(uint => uint) items;
        function func() public {
          assert(items[5] == 0);
        }
      }
      |]
    let sig = (Sig "func()" [])
    (_, [Cex (_, _ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
    assertBool "" True
  , testCase "simple-fixed-value" $ do
    Just c <- solcRuntime "MyContract"
      [i|
      contract MyContract {
        mapping(uint => uint) items;
        function func(uint a) public {
          assert(a != 1337);
        }
      }
      |]
    let sig = (Sig "func(uint256)" [AbiUIntType 256])
    (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
    assertEqual "Expected input not found" (1337 :: W256) (SMT.getVar ctr "arg1")
  , testCase "simple-fixed-value2" $ do
    Just c <- solcRuntime "MyContract"
      [i|
      contract MyContract {
        function func(uint a, uint b) public {
          assert(!((a == 1337) && (b == 99)));
        }
      }
      |]
    let sig = (Sig "func(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
    (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
    let a = SMT.getVar ctr "arg1"
    let b = SMT.getVar ctr "arg2"
    assertBool "Expected input not found" (a == 1337 && b == 99)
  , testCase "simple-fixed-value3" $ do
    Just c <- solcRuntime "MyContract"
      [i|
      contract MyContract {
        function func(uint a, uint b) public {
          assert(((a != 1337) && (b != 99)));
        }
      }
      |]
    let sig = (Sig "func(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
    (_, cexs) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
    assertBool ("Expected at least 1 counterexample, got " ++ show (length cexs)) (not $ null cexs)
  , testCase "simple-fixed-value-store1" $ do
    Just c <- solcRuntime "MyContract"
      [i|
      contract MyContract {
        mapping(uint => uint) items;
        function func(uint a) public {
          uint f = items[2];
          assert(a != f);
        }
      }
      |]
    let sig = (Sig "func(uint256)" [AbiUIntType 256, AbiUIntType 256])
    (_, [Cex _]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
    assertBool "" True
  , testCase "simple-fixed-value-store2" $ do
    Just c <- solcRuntime "MyContract"
      [i|
      contract MyContract {
        mapping(uint => uint) items;
        function func(uint a) public {
          items[0] = 1337;
          assert(a != items[0]);
        }
      }
      |]
    let sig = (Sig "func(uint256)" [AbiUIntType 256, AbiUIntType 256])
    (_, [Cex (_, _ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
    assertBool "" True
  , testCase "symbolic-exp-0-to-n" $ do
    Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function fun(uint256 a, uint256 b, uint256 k) external pure {
            uint x = 0 ** b;
            assert (x == 1);
          }
          }
        |]
    let sig = Just (Sig "fun(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])
    (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
    let b = SMT.getVar ctr "arg2"
    assertBool "b must be non-0" (b /= 0)
  , testCase "symbolic-exp-0-to-n2" $ do
    Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function fun(uint256 a, uint256 b, uint256 k) external pure {
            uint x = 0 ** b;
            assert (x == 0);
          }
          }
        |]
    let sig = Just (Sig "fun(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])
    (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
    let b = SMT.getVar ctr "arg2"
    assertBool "b must be 0" (b == 0)
  ]

copySliceTests :: TestTree
copySliceTests = testGroup "Copyslice tests"
  [ testCase "symbolic-mcopy" $ do
      Just c <- solcRuntime "MyContract"
          [i|
          contract MyContract {
            function fun(uint256 a, uint256 s) external returns (uint) {
              require(a < 5);
              assembly {
                  mcopy(0x2, 0, s)
                  a:=mload(s)
              }
              assert(a < 5);
              return a;
            }
            }
          |]
      let sig = Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, k) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numErrs = sum $ map (fromEnum . isError) k
      assertEqual "number of errors (i.e. copySlice issues) is 1" 1 numErrs
      let errStrings = mapMaybe getResError k
      assertEqual "All errors are from copyslice" True $ all ("CopySlice" `List.isInfixOf`) errStrings
  , testCase "symbolic-copyslice" $ do
      Just c <- solcRuntime "MyContract"
          [i|
          contract MyContract {
            function fun(uint256 a, uint256 s) external returns (uint) {
              require(a < 10);
              if (a >= 8) {
                assembly {
                    calldatacopy(0x5, s, s)
                    a:=mload(s)
                }
              } else {
                assembly {
                    calldatacopy(0x2, 0x2, 5)
                    a:=mload(s)
                }
              }
              assert(a < 9);
              return a;
            }
            }
          |]
      let sig = Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, k) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numErrs = sum $ map (fromEnum . isError) k
      assertEqual "number of errors (i.e. copySlice issues) is 1" 1 numErrs
      let errStrings = mapMaybe getResError k
      assertEqual "All errors are from copyslice" True $ all ("CopySlice" `List.isInfixOf`) errStrings

  ]

storageTests :: TestTree
storageTests = testGroup "Storage handling" [storageDecompositionTests, storageSimplificationTests]

storageDecompositionTests :: TestTree
storageDecompositionTests = testGroup "Storage decomposition"
    [ testCase "decompose-1" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (address => uint) balances;
          function prove_mapping_access(address x, address y) public {
              require(x != y);
              balances[x] = 1;
              balances[y] = 2;
              assert(balances[x] != balances[y]);
          }
        }
        |]
      paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "prove_mapping_access(address,address)" [AbiAddressType, AbiAddressType])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      assertBool "Decompose did not succeed." (all isJust simpExpr)
    , testCase "decompose-2" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (address => uint) balances;
          function prove_mixed_symoblic_concrete_writes(address x, uint v) public {
              balances[x] = v;
              balances[address(0)] = balances[x];
              assert(balances[address(0)] == v);
          }
        }
        |]
      paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "prove_mixed_symoblic_concrete_writes(address,uint256)" [AbiAddressType, AbiUIntType 256])) [] defaultVeriOpts
      let pathsSimp = map (mapExprM (Expr.decomposeStorage . Expr.concKeccakSimpExpr . Expr.simplify)) paths
      assertBool "Decompose did not succeed." (all isJust pathsSimp)
    , testCase "decompose-3" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          function prove_array(uint x, uint v1, uint y, uint v2) public {
              require(v1 != v2);
              a[x] = v1;
              a[y] = v2;
              assert(a[x] == a[y]);
          }
        }
        |]
      paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "prove_array(uint256,uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      assertBool "Decompose did not succeed." (all isJust simpExpr)
    , testCase "decompose-4-mixed" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          mapping( uint => uint) balances;
          function prove_array(uint x, uint v1, uint y, uint v2) public {
              require(v1 != v2);
              balances[x] = v1+1;
              balances[y] = v1+2;
              a[x] = v1;
              assert(balances[x] != balances[y]);
          }
        }
        |]
      paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "prove_array(uint256,uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertBool "Decompose did not succeed." (all isJust simpExpr)
    , testCase "decompose-5-mixed" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (address => uint) balances;
          mapping (uint => bool) auth;
          uint[] arr;
          uint a;
          uint b;
          function prove_mixed(address x, address y, uint val) public {
            b = val+1;
            require(x != y);
            balances[x] = val;
            a = val;
            arr[val] = 5;
            auth[val+1] = true;
            balances[y] = val+2;
            if (balances[y] == balances[y]) {
                assert(balances[y] == val);
            }
          }
        }
        |]
      paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "prove_mixed(address,address,uint256)" [AbiAddressType, AbiAddressType, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      assertBool "Decompose did not succeed." (all isJust simpExpr)
    , testCase "decompose-6" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] arr;
          function prove_mixed(uint val) public {
            arr[val] = 5;
            arr[val+1] = val+5;
            assert(arr[val] == arr[val+1]);
          }
        }
        |]
      paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "prove_mixed(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      assertBool "Decompose did not succeed." (all isJust simpExpr)
    -- This test uses array.length, which is is concrete 0 only in case we start with an empty storage
    -- otherwise (i.e. with getExpr) it's symbolic, and the exploration loops forever
    , testCase "decompose-7-empty-storage" $ do
       Just c <- solcRuntime "MyContract" [i|
        contract MyContract {
          uint[] arr;
          function nested_append(uint v, uint w) public {
            arr.push(w);
            arr.push();
            arr.push();
            arr.push(arr[0]-1);

            arr[2] = v;
            arr[1] = arr[0]-arr[2];

            assert(arr.length == 4);
            assert(arr[0] == w);
            assert(arr[1] == w-v);
            assert(arr[2] == v);
            assert(arr[3] == w-1);
          }
       } |]
       let sig = Just $ Sig "nested_append(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256]
       paths <- executeWithBitwuzla $ \s -> getExprEmptyStore s c sig [] defaultVeriOpts
       assertEqual "Expression must be clean." (badStoresInExpr paths) False
    ]

storageSimplificationTests :: TestTree
storageSimplificationTests = testGroup "Storage simplification"
    [ testCase "simplify-storage-array-only-static" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              a[0] = val1 + 1;
              a[1] = val2 + 2;
              assert(a[0]+a[1] == val1 + val2 + 3);
            }
          }
        }
        |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , testCase "simplify-storage-map-only-static" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items1;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              items1[0] = val1+1;
              items1[1] = val2+2;
              assert(items1[0]+items1[1] == val1 + val2 + 3);
            }
          }
        }
        |]
       let sig = (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256]))
       paths <- executeWithBitwuzla $ \s -> getExpr s c sig [] defaultVeriOpts
       let pathsSimp = map (mapExpr (Expr.concKeccakSimpExpr . Expr.simplify)) paths
       assertEqual "Expression is not clean." (badStoresInExpr pathsSimp) False
    , testCase "simplify-storage-map-only-2" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items1;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              items1[acct] = val1+1;
              items1[acct+1] = val2+2;
              assert(items1[acct]+items1[acct+1] == val1 + val2 + 3);
            }
          }
        }
        |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , testCase "simplify-storage-map-with-struct" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          struct MyStruct {
            uint a;
            uint b;
          }
          mapping(uint => MyStruct) items1;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              items1[acct].a = val1+1;
              items1[acct].b = val2+2;
              assert(items1[acct].a+items1[acct].b == val1 + val2 + 3);
            }
          }
        }
        |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , testCase "simplify-storage-map-and-array" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          mapping(uint => uint) items1;
          mapping(uint => uint) items2;
          function transfer(uint acct, uint val1, uint val2) public {
            uint beforeVal1 = items1[acct];
            uint beforeVal2 = items2[acct];
            unchecked {
              items1[acct] = val1+1;
              items2[acct] = val2+2;
              a[0] = val1 + val2 + 1;
              a[1] = val1 + val2 + 2;
              assert(items1[acct]+items2[acct]+a[0]+a[1] > beforeVal1 + beforeVal2);
            }
          }
        }
       |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , testCase "simplify-storage-array-loop-struct" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          struct MyStruct {
            uint a;
            uint b;
          }
          MyStruct[] arr;
          function transfer(uint v1, uint v2) public {
            for (uint i = 0; i < arr.length; i++) {
              arr[i].a = v1+1;
              arr[i].b = v2+2;
              assert(arr[i].a + arr[i].b == v1 + v2 + 3);
            }
          }
        }
        |]
       let veriOpts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 5 }}
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] veriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    -- This case is somewhat artificial. We can't simplify this using only
    -- static rewrite rules, because `acct` is totally abstract and a[acct]
    -- could overflow the store and rewrite slot 1, where the array size is stored.
    -- The load/store simplifications would have to take other constraints into account.
    , ignoreTestBecause "We cannot simplify this with only static rewrite rules" $ testCase "simplify-storage-array-symbolic-index" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint b;
          uint[] a;
          function transfer(uint acct, uint val1) public {
            unchecked {
              a[acct] = val1;
              assert(a[acct] == val1);
            }
          }
        }
        |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- T.writeFile "symbolic-index.expr" $ formatExpr paths
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , ignoreTestBecause "We cannot simplify this with only static rewrite rules" $ testCase "simplify-storage-array-of-struct-symbolic-index" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          struct MyStruct {
            uint a;
            uint b;
          }
          MyStruct[] arr;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              arr[acct].a = val1+1;
              arr[acct].b = val1+2;
              assert(arr[acct].a + arr[acct].b == val1+val2+3);
            }
          }
        }
        |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , testCase "simplify-storage-array-loop-nonstruct" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          function transfer(uint v) public {
            for (uint i = 0; i < a.length; i++) {
              a[i] = v;
              assert(a[i] == v);
            }
          }
        }
        |]
       let veriOpts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 5 }}
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "transfer(uint256)" [AbiUIntType 256])) [] veriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
    , testCase "simplify-storage-map-newtest1" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (uint => uint) a;
          mapping (uint => uint) b;
          function fun(uint v, uint i) public {
            require(i < 1000);
            require(v < 1000);
            b[i+v] = v+1;
            a[i] = v;
            b[i+1] = v+1;
            assert(a[i] == v);
            assert(b[i+1] == v+1);
          }
        }
        |]
       paths <- executeWithBitwuzla $ \s -> getExpr s c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Expression is not clean." (badStoresInExpr paths) False
       (_, []) <- executeWithBitwuzla $ \s -> checkAssert s [0x11] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertBool "" True
    , testCase "simplify-storage-map-todo" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (uint => uint) a;
          mapping (uint => uint) b;
          function fun(uint v, uint i) public {
            require(i < 1000);
            require(v < 1000);
            a[i] = v;
            b[i+1] = v+1;
            b[i+v] = 55; // note: this can overwrite b[i+1], hence assert below can fail
            assert(a[i] == v);
            assert(b[i+1] == v+1);
          }
        }
        |]
       -- TODO: expression below contains (load idx1 (store idx1 (store idx1 (store idx0)))), and the idx0
       --       is not stripped. This is due to us not doing all we can in this case, see
       --       note above readStorage. Decompose remedies this (when it can be decomposed)
       -- paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- putStrLnM $ T.unpack $ formatExpr paths
       (_, [Cex _]) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertBool "" True
    ,
    -- TODO: we can't deal with symbolic jump conditions
    expectFail $ testCase "call-zero-inited-var-thats-a-function" $ do
      Just c <- solcRuntime "MyContract"
          [i|
          contract MyContract {
            function (uint256) internal returns (uint) funvar;
            function fun2(uint256 a) internal returns (uint){
              return a;
            }
            function fun(uint256 a) external returns (uint) {
              if (a != 44) {
                funvar = fun2;
              }
              return funvar(a);
            }
            }
          |]
      (_, [Cex (_, cex)]) <- executeWithBitwuzla $ \s -> checkAssert s [0x51] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
      let a = SMT.getVar cex "arg1"
      assertEqual "unexpected cex value" 44 a
    ]


panicCodeTests :: TestTree
panicCodeTests = testGroup "Panic code tests via symbolic execution"
  [ testCase "assert-fail" $ do
      Just c <- solcRuntime "MyContract"
          [i|
          contract MyContract {
            function fun(uint256 a) external pure {
              assert(a != 0);
            }
          }
          |]
      (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
      assertEqual "Must be 0" 0 $ SMT.getVar ctr "arg1"
  , testCase "safeAdd-fail" $ do
      Just c <- solcRuntime "MyContract"
          [i|
          contract MyContract {
            function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
              c = a+b;
            }
            }
          |]
      (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s [0x11] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let x = SMT.getVar ctr "arg1"
      let y = SMT.getVar ctr "arg2"

      let maxUint = 2 ^ (256 :: Integer) :: Integer
      assertBool "Overflow must occur" (toInteger x + toInteger y >= maxUint)
  , testCase "div-by-zero-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
               c = a/b;
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s [0x12] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        assertEqual "Division by 0 needs b=0" (SMT.getVar ctr "arg2") 0
        -- putStrLnM "expected counterexample found"
  , testCase "unused-args-fail" $ do
         Just c <- solcRuntime "C"
             [i|
             contract C {
               function fun(uint256 a) public pure {
                 assert(false);
               }
             }
             |]
         (_, results) <- executeWithBitwuzla $ \s -> checkAssert s [0x1] c Nothing [] defaultVeriOpts
         expectOneCex results
  , testCase "gas-decrease-monotone" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint8 a) external {
                uint a = gasleft();
                uint b = gasleft();
                assert(a > b);
              }
             }
            |]
        let sig = (Just (Sig "fun(uint8)" [AbiUIntType 8]))
        (_, results) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        expectNoCex results
  , testCase "enum-conversion-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              enum MyEnum { ONE, TWO }
              function fun(uint256 a) external pure returns (MyEnum b) {
                b = MyEnum(a);
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s [0x21] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        assertBool "Enum is only defined for 0 and 1" $ (SMT.getVar ctr "arg1") > 1
  ,
    -- TODO 0x22 is missing: "0x22: If you access a storage byte array that is incorrectly encoded."
     -- TODO below should NOT fail
     -- TODO this has a loop that depends on a symbolic value and currently causes interpret to loop 
    ignoreTest $ testCase "pop-empty-array" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              uint[] private arr;
              function fun(uint8 a) external {
                arr.push(1);
                arr.push(2);
                for (uint i = 0; i < a; i++) {
                  arr.pop();
                }
              }
             }
            |]
        a <- executeWithBitwuzla $ \s -> checkAssert s [0x31] c (Just (Sig "fun(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
        print $ length a
        print $ show a
        putStrLn "expected counterexample found"
  , testCase "access-out-of-bounds-array" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              uint[] private arr;
              function fun(uint8 a) external returns (uint x){
                arr.push(1);
                arr.push(2);
                x = arr[a];
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- executeWithBitwuzla $ \s -> checkAssert s [0x32] c (Just (Sig "fun(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
        assertBool "Access must be beyond index 1" $ (SMT.getVar ctr "arg1") > 1
  , testCase "alloc-too-much" $ do -- Note: we catch the assertion here, even though we are only able to explore partially
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a) external {
                uint[] memory arr = new uint[](a);
              }
             }
            |]
        (_, results) <- executeWithBitwuzla $ \s -> checkAssert s [0x41] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        expectOneCex results
  ]

cheatCodeTests :: TestTree
cheatCodeTests = testGroup "Cheatcode tests via symbolic execution"
  [ testCase "vm.deal unknown address" $ do
      Just c <- solcRuntime "C"
        [i|
          interface Vm {
            function deal(address,uint256) external;
          }
          contract C {
            // this is not supported yet due to restrictions around symbolic address aliasing...
            function f(address e, uint val) external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.deal(e, val);
                assert(e.balance == val);
            }
          }
        |]
      result <- verifyUserAsserts c (Just $ Sig "f(address,uint256)" [AbiAddressType, AbiUIntType 256])
      expectPartial result -- FIXME: Ideally, we would be able to explore fully and prove the assertion
  , testCase "vm.prank-create" $ do
      Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function prank(address) external;
            }
            contract Owned {
              address public owner;
              constructor() {
                owner = msg.sender;
              }
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

                Owned target = new Owned();
                assert(target.owner() == address(this));

                address usr = address(1312);
                vm.prank(usr);
                target = new Owned();
                assert(target.owner() == usr);
                target = new Owned();
                assert(target.owner() == address(this));
              }
            }
          |]
      result <- verifyUserAsserts c (Just $ Sig "f()" [])
      expectNoCexNoPartial result
  , testCase "vm.prank underflow" $ do
      Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function prank(address) external;
            }
            contract Payable {
                function hi() public payable {}
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

                uint amt = 10;
                address from = address(0xacab);
                require(from.balance < amt);

                Payable target = new Payable();
                vm.prank(from);
                target.hi{value : amt}();
              }
            }
          |]
      expectAllBranchesFail c Nothing
  , testCase "cheatcode-nonexistent" $ do
      Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function nonexistent_cheatcode(uint) external;
            }
          contract C {
            function fun(uint a) public {
                // Cheatcode address
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.nonexistent_cheatcode(a);
                assert(1 == 1);
            }
          }
          |]
      let sig = Just (Sig "fun(uint256)" [AbiUIntType 256])
      result <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      expectPartial result
  , testCase "cheatcode-with-selector" $ do
      Just c <- solcRuntime "C"
          [i|
          contract C {
          function prove_warp_symbolic(uint128 jump) public {
                  uint pre = block.timestamp;
                  address hevm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  (bool success, ) = hevm.call(abi.encodeWithSelector(bytes4(keccak256("warp(uint256)")), block.timestamp+jump));
                  require(success, "Call to hevm.warp failed");
                  assert(block.timestamp == pre + jump);
              }
          }
          |]
      result <- verifyUserAsserts c Nothing
      expectNoCexNoPartial result
  , testCase "call ffi when disabled" $ do
      Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function ffi(string[] calldata) external;
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

                string[] memory inputs = new string[](2);
                inputs[0] = "echo";
                inputs[1] = "acab";

                // should fail to explore this branch
                vm.ffi(inputs);
              }
            }
          |]
      expectAllBranchesFail c Nothing
  ]

maxDepthTests :: TestTree
maxDepthTests = testGroup "Tests for branching depth"
  [
      -- below we hit the limit of the depth of the symbolic execution tree
      testCase "limit-num-explore-hit-limit" $ do
        let conf = symExecTestsConfig {Effects.maxDepth = Just 3}
        Just c <- solcRuntime "C"
          [i|
          contract C {
              function checkval(uint256 a, uint256 b, uint256 c) public {
                if (a == b) {
                  if (b == c) {
                    assert(false);
                  }
                }
              }
          }
          |]
        let sig = Just (Sig "checkval(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])
        res@(_, ret) <- Effects.runEnv (Effects.Env conf) $ withBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        expectPartial res
        expectNoCex ret
        expectNoError ret
      -- below we don't hit the limit of the depth of the symbolic execution tree
      , testCase "limit-num-explore-no-hit-limit" $ do
        let conf = symExecTestsConfig {Effects.maxDepth = Just 7}
        Just c <- solcRuntime "C"
          [i|
          contract C {
              function checkval(uint256 a, uint256 b, uint256 c) public {
                if (a == b) {
                  if (b == c) {
                    assert(false);
                  }
                }
              }
          }
          |]
        let sig = Just (Sig "checkval(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])
        (paths, ret) <- Effects.runEnv (Effects.Env conf) $ withBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        expectNoError ret
        expectOneCex ret
        assertBool "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
  ]

arithmeticTests :: TestTree
arithmeticTests = testGroup "Arithmetic tests"
  [ testCase "math-avg" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_Avg(uint a, uint b) external pure {
            require(a + b >= a);
            unchecked {
              uint r1 = (a & b) + (a ^ b) / 2;
              uint r2 = (a + b) / 2;
              assert(r1 == r2);
            }
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "unsigned-div-by-zero" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_unsigned_div_by_zero(uint256 a) external pure {
            uint256 result;
            assembly { result := div(a, 0) }
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "arith-div-pass" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_Div_pass(uint x, uint y) external pure {
            require(x > y);
            require(y > 0);
            uint q;
            assembly { q := div(x, y) }
            assert(q != 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "arith-div-fail" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_Div_fail(uint x, uint y) external pure {
            require(x > y);
            uint q;
            assembly { q := div(x, y) }
            assert(q != 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectOneCex res
  , testCase "arith-mod-fail" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_Div_fail(uint x, uint y) external pure {
              require(x > y);
              uint q;
              assembly { q := mod(x, y) }
              assert(q != 0);
            }
          } |]
        (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        expectOneCex res
  ,testCase "arith-mod" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function unchecked_smod(int x, int y) internal pure returns (int ret) {
            assembly { ret := smod(x, y) }
          }
          function prove_Mod(int x, int y) external pure {
            unchecked {
              assert(unchecked_smod(x, 0) == 0);
              assert(x % 1 == 0);
              assert(x % 2 < 2 && x % 2 > -2);
              assert(x % 4 < 4 && x % 4 > -4);
              int x_smod_y = unchecked_smod(x, y);
              assert(x_smod_y <= y || y < 0);}
          }
        } |]
      (_, res) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , ignoreTestBecause "Currently takes too long" $ testCase "math-mint-fail" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function prove_mint(uint s, uint A1, uint S1) external pure {
              uint a = (s * A1) / S1;
              uint A2 = A1 + a;
              uint S2 = S1 + s;
              assert(A1 * S2 <= A2 * S1);
            }
          } |]
        (_, res) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        expectOneCex res
  , signedDivModTests
  , abdkMathTests
  ]

signedDivModTests :: TestTree
signedDivModTests = testGroup "Tests for signed division and modulo"
  [ testCase "sdiv-by-one" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_by_one(int256 a) external pure {
            int256 result;
            assembly { result := sdiv(a, 1) }
            assert(result == a);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-by-neg-one" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_by_neg_one(int256 a) external pure {
            int256 result;
            assembly { result := sdiv(a, sub(0, 1)) }
            if (a == -170141183460469231731687303715884105728 * 2**128) { // type(int256).min
                assert(result == a);
            } else {
                assert(result == -a);
            }
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-intmin-by-two" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_intmin_by_two() external pure {
            int256 result;
            assembly {
              let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
              result := sdiv(intmin, 2)
            }
            // -2**254 is 0xc000...0000
            assert(result == -0x4000000000000000000000000000000000000000000000000000000000000000);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-by-zero" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_by_zero(int256 a) external pure {
            int256 result;
            assembly { result := smod(a, 0) }
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-intmin-by-three" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_intmin_by_three() external pure {
            int256 result;
            assembly { result := smod(0x8000000000000000000000000000000000000000000000000000000000000000, 3) }
            assert(result == -2);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-by-zero" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_by_zero(int256 a) external pure {
            int256 result;
            assembly { result := sdiv(a, 0) }
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-zero-dividend" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_zero_dividend(int256 b) external pure {
            int256 result;
            assembly { result := sdiv(0, b) }
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-truncation" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_truncation() external pure {
            int256 result;
            assembly { result := sdiv(sub(0, 7), 2) }
            assert(result == -3);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , ignoreTestBecause "Currently takes too long" $ testCase "sdiv-sign-symmetry" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_sign_symmetry(int256 a, int256 b) external pure {
            if (a == -57896044618658097711785492504343953926634992332820282019728792003956564819968) return;
            if (b == -57896044618658097711785492504343953926634992332820282019728792003956564819968) return;
            if (b == 0) return;
            int256 r1;
            int256 r2;
            assembly {
              r1 := sdiv(a, b)
              r2 := sdiv(sub(0, a), sub(0, b))
            }
            assert(r1 == r2);
          }
        } |]
      (_, res) <- executeWithBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , ignoreTestBecause "Currently takes too long" $ testCase "sdiv-sign-antisymmetry" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_sign_antisymmetry(int256 a, int256 b) external pure {
            if (a == -57896044618658097711785492504343953926634992332820282019728792003956564819968) return;
            if (b == 0) return;
            int256 r1;
            int256 r2;
            assembly {
              r1 := sdiv(a, b)
              r2 := sdiv(sub(0, a), b)
            }
            assert(r1 == -r2);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-by-one" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_by_one(int256 a) external pure {
            int256 r1;
            int256 r2;
            assembly {
              r1 := smod(a, 1)
              r2 := smod(a, sub(0, 1))
            }
            assert(r1 == 0);
            assert(r2 == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-zero-dividend" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_zero_dividend(int256 b) external pure {
            int256 result;
            assembly { result := smod(0, b) }
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-sign-matches-dividend" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_sign_matches_dividend(int256 a, int256 b) external pure {
            if (b == 0 || a == 0) return;
            int256 result;
            assembly { result := smod(a, b) }
            if (result != 0) {
              assert((a > 0 && result > 0) || (a < 0 && result < 0));
            }
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-intmin" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_intmin() external pure {
            int256 result;
            assembly { result := smod(0x8000000000000000000000000000000000000000000000000000000000000000, 2) }
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-intmin-by-neg-one" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_intmin_by_neg_one() external pure {
            int256 result;
            assembly {
              let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
              result := sdiv(intmin, sub(0, 1))
            }
            // EVM defines sdiv(MIN_INT, -1) = MIN_INT (overflow)
            assert(result == -57896044618658097711785492504343953926634992332820282019728792003956564819968);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "smod-intmin-by-neg-one" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_smod_intmin_by_neg_one() external pure {
            int256 result;
            assembly {
              let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
              result := smod(intmin, sub(0, 1))
            }
            // smod(MIN_INT, -1) = 0 since MIN_INT is divisible by -1
            assert(result == 0);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  , testCase "sdiv-intmin-by-intmin" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
          function prove_sdiv_intmin_by_intmin() external pure {
            int256 result;
            assembly {
              let intmin := 0x8000000000000000000000000000000000000000000000000000000000000000
              result := sdiv(intmin, intmin)
            }
            assert(result == 1);
          }
        } |]
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      expectProved res
  ]

abdkMathTests :: TestTree
abdkMathTests = testGroup "ABDK math tests"
  [ -- "make verify-hevm T=prove_div_negative_divisor" in https://github.com/gustavo-grieco/abdk-math-64.64-verification
    ignoreTestBecause "Currently takes too long" $ testCase "prove_div_values-abdk" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
            bool public IS_TEST = true;

            int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;
            int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

            // ABDKMath64x64.fromInt(0) == 0
            int128 private constant ZERO_FP = 0;
            // ABDKMath64x64.fromInt(1) == 1 << 64
            int128 private constant ONE_FP = 0x10000000000000000;

            // ABDKMath64x64.div
            function div(int128 x, int128 y) internal pure returns (int128) {
                unchecked {
                    require(y != 0);
                    int256 result = (int256(x) << 64) / y;
                    require(result >= MIN_64x64 && result <= MAX_64x64);
                    return int128(result);
                }
            }

            // ABDKMath64x64.abs
            function abs(int128 x) internal pure returns (int128) {
                unchecked {
                    require(x != MIN_64x64);
                    return x < 0 ? -x : x;
                }
            }

            // Property: |x / y| <= |x| when |y| >= 1, and |x / y| >= |x| when |y| < 1
            function prove_div_values(int128 x, int128 y) public pure {
                require(y != ZERO_FP);

                int128 x_y = abs(div(x, y));

                if (abs(y) >= ONE_FP) {
                    assert(x_y <= abs(x));
                } else {
                    assert(x_y >= abs(x));
                }
            }
        } |]
      let sig = (Just $ Sig "prove_div_values(int128,int128)" [AbiIntType 128, AbiIntType 128])
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      expectProved res
  -- "make verify-hevm T=prove_div_negative_divisor" in https://github.com/gustavo-grieco/abdk-math-64.64-verification
  , ignoreTestBecause "Currently takes too long" $ testCase "prove_div_negative_divisor" $ do
      Just c <- solcRuntime "C" [i|
        contract C {
            bool public IS_TEST = true;

            int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;
            int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

            // ABDKMath64x64.fromInt(0) == 0
            int128 private constant ZERO_FP = 0;
            
            // ABDKMath64x64.div
            function div(int128 x, int128 y) internal pure returns (int128) {
                unchecked {
                    require(y != 0);
                    int256 result = (int256(x) << 64) / y;
                    require(result >= MIN_64x64 && result <= MAX_64x64);
                    return int128(result);
                }
            }
            
            // ABDKMath64x64.neg
            function neg(int128 x) internal pure returns (int128) {
                unchecked {
                    require(x != MIN_64x64);
                    return -x;
                }
            }

            // Property: x / (-y) == -(x / y)
            function prove_div_negative_divisor(int128 x, int128 y) public pure {
                require(y < ZERO_FP);

                int128 x_y = div(x, y);
                int128 x_minus_y = div(x, neg(y));

                assert(x_y == neg(x_minus_y));
            }
        } |]
      let sig = (Just $ Sig "prove_div_negative_divisor(int128,int128)" [AbiIntType 128, AbiIntType 128])
      (_, res) <- executeWithShortBitwuzla $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      expectProved res
  ]

expectProved :: [VerifyResult] -> Assertion
expectProved results = assertBool "Must be proved" (null results)

expectNoCex :: [VerifyResult] -> Assertion
expectNoCex results = assertBool "There should be no cex" (not $ any isCex results)

expectNoError :: [VerifyResult] -> Assertion
expectNoError results = assertBool "There should be no error" (not $ any isError results)

expectOneCex :: [VerifyResult] -> Assertion
expectOneCex [Cex _] = assertBool "" True
expectOneCex _ = assertFailure "There should exactly one cex"

expectPartial :: ([Expr End], [VerifyResult]) -> Assertion
expectPartial (paths, _) = assertBool "There should be a partial path" (any isPartial paths)

expectNoCexNoPartial :: ([Expr End], [VerifyResult]) -> Assertion
expectNoCexNoPartial (paths, results) = do
  assertBool "There should be no partial paths" (not $ any isPartial paths)
  expectNoCex results

-- Finds SLoad -> SStore. This should not occur in most scenarios
-- as we can simplify them away
badStoresInExpr :: [Expr a] -> Bool
badStoresInExpr exprs = any (getAny . foldExpr match mempty) exprs
  where
      match (SLoad _ (SStore _ _ _)) = Any True
      match _ = Any False

symExecTestsConfig :: Effects.Config
symExecTestsConfig = Effects.defaultConfig

symExecTestsEnvironment :: Effects.Env
symExecTestsEnvironment = Effects.Env symExecTestsConfig

executeWithBitwuzla :: MonadUnliftIO m => (SolverGroup -> ReaderT Effects.Env m a) -> m a
executeWithBitwuzla action = Effects.runEnv symExecTestsEnvironment $ withBitwuzla action

executeWithShortBitwuzla :: MonadUnliftIO m => (SolverGroup -> ReaderT Effects.Env m a) -> m a
executeWithShortBitwuzla action = Effects.runEnv symExecTestsEnvironment $ withSolvers Bitwuzla 1 (Just 5) defMemLimit action


withBitwuzla :: Effects.App m => (SolverGroup -> m a) -> m a
withBitwuzla = withSolvers Bitwuzla 1 Nothing defMemLimit

verifyUserAsserts :: ByteString -> Maybe Sig -> IO ([Expr End], [VerifyResult])
verifyUserAsserts c sig = executeWithBitwuzla $ \s -> checkAssert s [0x01] c sig [] defaultVeriOpts

expectAllBranchesFail :: ByteString -> Maybe Sig -> Assertion
expectAllBranchesFail c sig = do
  result <- executeWithBitwuzla $ \s -> verifyContract s c sig [] defaultVeriOpts Nothing post
  expectNoCexNoPartial result
  where
    post _ = \case
      Success _ _ _ _ -> PBool False
      _ -> PBool True
