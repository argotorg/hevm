{-# LANGUAGE QuasiQuotes #-}

module EVM.SymExec.SymExecTests (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure

import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (ReaderT)
import Data.Maybe (isJust)
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
    , storageTests
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
    ]

-- Finds SLoad -> SStore. This should not occur in most scenarios
-- as we can simplify them away
badStoresInExpr :: [Expr a] -> Bool
badStoresInExpr exprs = any (getAny . foldExpr match mempty) exprs
  where
      match (SLoad _ (SStore _ _ _)) = Any True
      match _ = Any False

symExecTestsEnvironment :: Effects.Env
symExecTestsEnvironment = Effects.defaultEnv

executeWithBitwuzla :: MonadUnliftIO m => (SolverGroup -> ReaderT Effects.Env m a) -> m a
executeWithBitwuzla action = Effects.runEnv symExecTestsEnvironment $ withBitwuzla action

withBitwuzla :: Effects.App m => (SolverGroup -> m a) -> m a
withBitwuzla = withSolvers Bitwuzla 1 Nothing defMemLimit