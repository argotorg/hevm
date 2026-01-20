{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeAbstractions #-}

module Main where

import Prelude hiding (LT, GT)

import GHC.TypeLits
import Data.Proxy
import Control.Monad
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Control.Monad.Reader (ReaderT)
import Data.Bits hiding (And, Xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.Binary.Put (runPut)
import Data.Binary.Get (runGetOrFail)
import Data.DoubleWord
import Data.Either
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Monoid (Any(..))
import Data.Set qualified as Set
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (diffUTCTime, getCurrentTime)
import Data.Tuple.Extra
import Data.Tree (flatten)
import Data.Typeable
import Data.Vector qualified as V
import Data.Word (Word8, Word64)
import Data.Char (digitToInt)
import GHC.Conc (getNumProcessors)
import System.Directory
import System.Environment
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Test.QuickCheck.Instances.Text()
import Test.QuickCheck.Instances.Natural()
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty.HUnit
import Test.Tasty.Runners hiding (Failure, Success)
import Test.Tasty.ExpectedFailure
import Text.RE.TDFA.String
import Text.RE.Replace
import Witch (unsafeInto, into)
import Data.Containers.ListUtils (nubOrd)

import Optics.Core hiding (pre, re, elements)
import Optics.State

import EVM
import EVM.ABI
import EVM.Assembler
import EVM.Exec
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (hexByteString, hexText, formatExpr)
import EVM.Precompiled
import EVM.RLP
import EVM.SMT hiding (one)
import EVM.Solidity
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Test.FuzzSymExec qualified as FuzzSymExec
import EVM.Test.Utils (runForgeTest, runForgeTestCustom)
import EVM.Traversals
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.UnitTest (writeTrace, printWarnings)
import EVM.Expr (maybeLitByteSimp)
import EVM.Keccak (concreteKeccaks)

import EVM.Expr.ExprTests qualified as ExprTests

testEnv :: Env
testEnv = Env { config = defaultConfig {
  dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , dumpTrace = False
  , decomposeStorage = True
  , verb = 1
  } }

putStrLnM :: (MonadUnliftIO m) => String -> m ()
putStrLnM a = liftIO $ putStrLn a

assertEqualM :: (App m, Eq a, Show a, HasCallStack) => String -> a -> a -> m ()
assertEqualM a b c = liftIO $ assertEqual a b c

assertBoolM
  :: (MonadUnliftIO m, HasCallStack)
  => String -> Bool -> m ()
assertBoolM a b = liftIO $ assertBool a b

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv testEnv b

testNoSimplify :: TestName -> ReaderT Env IO () -> TestTree
testNoSimplify a b = let testEnvNoSimp = Env { config = testEnv.config { simp = False } }
  in testCase a $ runEnv testEnvNoSimp b

prop :: Testable prop => ReaderT Env IO prop -> Property
prop a = ioProperty $ runEnv testEnv a

propNoSimp :: Testable prop => ReaderT Env IO prop -> Property
propNoSimp a = let testEnvNoSimp = Env { config = testEnv.config { simp = False } }
  in ioProperty $ runEnv testEnvNoSimp a

withDefaultSolver :: App m => (SolverGroup -> m a) -> m a
withDefaultSolver = withSolvers Z3 3 1 Nothing

withCVC5Solver :: App m => (SolverGroup -> m a) -> m a
withCVC5Solver = withSolvers CVC5 3 1 Nothing

withBitwuzlaSolver :: App m => (SolverGroup -> m a) -> m a
withBitwuzlaSolver = withSolvers Bitwuzla 3 1 Nothing

main :: IO ()
main = defaultMain tests

-- | run a subset of tests in the repl. p is a tasty pattern:
-- https://github.com/UnkindPartition/tasty/tree/ee6fe7136fbcc6312da51d7f1b396e1a2d16b98a#patterns
runSubSet :: String -> IO ()
runSubSet p = defaultMain . applyPattern p $ tests

tests :: TestTree
tests = testGroup "hevm"
  [ FuzzSymExec.tests
  , ExprTests.tests
  , testGroup "simplify-storage"
    [ test "simplify-storage-array-only-static" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    -- This case is somewhat artificial. We can't simplify this using only
    -- static rewrite rules, because acct is totally abstract and acct + 1
    -- could overflow back to zero. we may be able to do better if we have some
    -- smt assisted simplification that can take branch conditions into account.
    , expectFail $ test "simplify-storage-array-symbolic-index" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- T.writeFile "symbolic-index.expr" $ formatExpr paths
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , expectFail $ test "simplify-storage-array-of-struct-symbolic-index" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , test "simplify-storage-array-loop-nonstruct" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256)" [AbiUIntType 256])) [] veriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , test "simplify-storage-map-newtest1" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
       (_, []) <- withDefaultSolver $ \s -> checkAssert s [0x11] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       liftIO $ putStrLn "OK"
    , ignoreTest $ test "simplify-storage-map-todo" $ do
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
       (_, [Cex _]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       liftIO $ putStrLn "OK"
    , test "simplify-storage-array-loop-struct" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] veriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , test "decompose-1" $ do
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
      paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "prove_mapping_access(address,address)" [AbiAddressType, AbiAddressType])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      assertEqualM "Decompose did not succeed." (all isJust simpExpr) True
    , test "decompose-2" $ do
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
      paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "prove_mixed_symoblic_concrete_writes(address,uint256)" [AbiAddressType, AbiUIntType 256])) [] defaultVeriOpts
      let pathsSimp = map (mapExprM (Expr.decomposeStorage . Expr.concKeccakSimpExpr . Expr.simplify)) paths
      -- putStrLnM $ T.unpack $ formatExpr (fromJust pathsSimp)
      assertEqualM "Decompose did not succeed." (all isJust pathsSimp) True
    , test "decompose-3" $ do
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
      paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "prove_array(uint256,uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      assertEqualM "Decompose did not succeed." (all isJust simpExpr) True
    , test "decompose-4-mixed" $ do
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
      paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "prove_array(uint256,uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (all isJust simpExpr) True
    , test "decompose-5-mixed" $ do
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
      paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "prove_mixed(address,address,uint256)" [AbiAddressType, AbiAddressType, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (all isJust simpExpr) True
    , test "decompose-6" $ do
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
      paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "prove_mixed(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = map (mapExprM Expr.decomposeStorage) paths
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (all isJust simpExpr) True
    -- This test uses array.length, which is is concrete 0 only in case we start with an empty storage
    -- otherwise (i.e. with getExpr) it's symbolic, and the exploration loops forever
    , test "decompose-7-emtpy-storage" $ do
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
       paths <- withDefaultSolver $ \s -> getExprEmptyStore s c sig [] defaultVeriOpts
       assertEqualM "Expression must be clean." (badStoresInExpr paths) False
    , test "simplify-storage-map-only-static" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c sig [] defaultVeriOpts
       let pathsSimp = map (mapExpr (Expr.concKeccakSimpExpr . Expr.simplify)) paths
       assertEqualM "Expression is not clean." (badStoresInExpr pathsSimp) False
    , test "simplify-storage-map-only-2" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- putStrLnM $ T.unpack $ formatExpr paths
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , test "simplify-storage-map-with-struct" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , test "simplify-storage-map-and-array" $ do
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
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- putStrLnM $ T.unpack $ formatExpr paths
       assertEqualM "Expression is not clean." (badStoresInExpr paths) False
    , test "simplify-storage-wordToAddr" $ do
       let a = "000000000000000000000000d95322745865822719164b1fc167930754c248de000000000000000000000000000000000000000000000000000000000000004a"
           store = ConcreteStore (Map.fromList[(W256 0xebd33f63ba5dda53a45af725baed5628cdad261db5319da5f5d921521fe1161d,W256 0x5842cf)])
           expr = SLoad (Keccak (ConcreteBuf (hexStringToByteString a))) store
           simpExpr = Expr.wordToAddr expr
           simpExpr2 = Expr.concKeccakSimpExpr expr
       assertEqualM "Expression should simplify to value." simpExpr (Just $ LitAddr 0x5842cf)
       assertEqualM "Expression should simplify to value." simpExpr2 (Lit 0x5842cf)
    , test "simplify-storage-wordToAddr-complex" $ do
       let a = "000000000000000000000000d95322745865822719164b1fc167930754c248de000000000000000000000000000000000000000000000000000000000000004a"
           store = ConcreteStore (Map.fromList[(W256 0xebd33f63ba5dda53a45af725baed5628cdad261db5319da5f5d921521fe1161d,W256 0x5842cf)])
           expr = SLoad (Keccak (ConcreteBuf (hexStringToByteString a))) store
           writeWChain = WriteWord (Lit 0x32) (Lit 0x72) (WriteWord (Lit 0x0) expr (ConcreteBuf ""))
           kecc = Keccak (CopySlice (Lit 0x0) (Lit 0x0) (Lit 0x20) (WriteWord (Lit 0x0) expr (writeWChain)) (ConcreteBuf ""))
           keccAnd =  (And (Lit 1461501637330902918203684832716283019655932542975) kecc)
           outer = And (Lit 1461501637330902918203684832716283019655932542975) (SLoad (keccAnd) (ConcreteStore (Map.fromList[(W256 1184450375068808042203882151692185743185288360635, W256 0xacab)])))
           simp = Expr.concKeccakSimpExpr outer
       assertEqualM "Expression should simplify to value." simp (Lit 0xacab)
    ]
  , testGroup "StorageTests"
    [ test "read-from-sstore" $ assertEqualM ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x0) (Lit 0xab) (AbstractStore (LitAddr 0x0) Nothing)))
    , test "read-from-concrete" $ assertEqualM ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, 0xab)]))
    , test "read-past-write" $ assertEqualM ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x1) (Var "b") (ConcreteStore $ Map.fromList [(0x0, 0xab)])))
    , test "accessStorage uses fetchedStorage" $ do
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
            -- then it should fetch the slow
        vm3 <- case vm2.result of
                    Just (HandleEffect (Query (PleaseFetchSlot _addr _slot continue))) ->
                      liftIO $ stToIO $ execStateT (continue 1337) vm2
                    _ -> internalError "unexpected result"
            -- perform the same access as for vm1
        vm4 <- liftIO $ stToIO $ execStateT (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm3

        -- there won't be query now as accessStorage uses fetch cache
        assertBoolM (show vm4.result) (isNothing vm4.result)
    ]
  , testGroup "SimplifierUnitTests"
    -- common overflow cases that the simplifier was getting wrong
    [ test "writeWord-overflow" $ do
        let e = ReadByte (Lit 0x0) (WriteWord (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd) (Lit 0x0) (ConcreteBuf "\255\255\255\255"))
        b <- checkEquiv e (Expr.simplify e)
        assertBoolM "Simplifier failed" b
    , test "copyslice-simps" $ do
        let e a b =  CopySlice (Lit 0) (Lit 0) (BufLength (AbstractBuf "buff")) (CopySlice (Lit 0) (Lit 0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf a)) (ConcreteBuf b)
            expr1 = e "" ""
            expr2 = e "" "aasdfasdf"
            expr3 = e "9832478932" ""
            expr4 = e "9832478932" "aasdfasdf"
        assertEqualM "Not full simp" (Expr.simplify expr1) (AbstractBuf "buff")
        assertEqualM "Not full simp" (Expr.simplify expr2) $ CopySlice (Lit 0x0) (Lit 0x0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf "aasdfasdf")
        assertEqualM "Not full simp" (Expr.simplify expr3) (AbstractBuf "buff")
        assertEqualM "Not full simp" (Expr.simplify expr4) $ CopySlice (Lit 0x0) (Lit 0x0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf "aasdfasdf")
    , test "buffer-length-copy-slice-beyond-source1" $ do
        let e = BufLength (CopySlice (Lit 0x2) (Lit 0x2) (Lit 0x1) (ConcreteBuf "a") (ConcreteBuf ""))
        b <- checkEquiv e (Expr.simplify e)
        assertBoolM "Simplifier failed" b
    , test "buffer-length-copy-slice-beyond-source2" $ do
        let e = BufLength (CopySlice (Lit 0x2) (Lit 0x2) (Lit 0x1) (ConcreteBuf "") (ConcreteBuf ""))
        b <- checkEquiv e (Expr.simplify e)
        assertBoolM "Simplifier failed" b
    , test "simp-readByte1" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (ReadWord (Lit 0x1) (AbstractBuf "stuff2"))
          src = (AbstractBuf "stuff2")
          e = ReadByte (Lit 0x0) (CopySlice srcOffset (Lit 0x10) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqualM "readByte simplification" simp (ReadByte (Lit 0x0) (AbstractBuf "dst"))
    , test "simp-readByte2" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (Lit 0x1)
          src = (AbstractBuf "stuff2")
          e = ReadByte (Lit 0x0) (CopySlice srcOffset (Lit 0x10) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      res <- checkEquiv e simp
      assertEqualM "readByte simplification"  res True
    , test "simp-readWord1" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (ReadWord (Lit 0x1) (AbstractBuf "stuff2"))
          src = (AbstractBuf "stuff2")
          e = ReadWord (Lit 0x1) (CopySlice srcOffset (Lit 0x40) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqualM "readWord simplification" simp (ReadWord (Lit 0x1) (AbstractBuf "dst"))
    , test "simp-readWord2" $ do
      let srcOffset = (ReadWord (Lit 0x12) (AbstractBuf "stuff1"))
          size = (Lit 0x1)
          src = (AbstractBuf "stuff2")
          e = ReadWord (Lit 0x12) (CopySlice srcOffset (Lit 0x50) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      res <- checkEquiv e simp
      assertEqualM "readWord simplification"  res True
    , test "simp-max-buflength" $ do
      let simp = Expr.simplify $ Max (Lit 0) (BufLength (AbstractBuf "txdata"))
      assertEqualM "max-buflength rules" simp $ BufLength (AbstractBuf "txdata")
    , test "simp-PLT-max" $ do
      let simp = Expr.simplifyProp $ PLT (Max (Lit 5) (BufLength (AbstractBuf "txdata"))) (Lit 99)
      assertEqualM "max-buflength rules" simp $ PLT (BufLength (AbstractBuf "txdata")) (Lit 99)
    , test "simp-assoc-add1" $ do
      let simp = Expr.simplify $        Add (Add (Var "c") (Var "a")) (Var "b")
      assertEqualM "assoc rules" simp $ Add (Var "a") (Add (Var "b") (Var "c"))
    , test "simp-assoc-add2" $ do
      let simp = Expr.simplify $        Add (Add (Lit 1) (Var "c")) (Var "b")
      assertEqualM "assoc rules" simp $ Add (Lit 1) (Add (Var "b") (Var "c"))
    , test "simp-assoc-add3" $ do
      let simp = Expr.simplify $        Add (Lit 1) (Add (Lit 2) (Var "c"))
      assertEqualM "assoc rules" simp $ Add (Lit 3) (Var "c")
    , test "simp-assoc-add4" $ do
      let simp = Expr.simplify $        Add (Lit 1) (Add (Var "b") (Lit 2))
      assertEqualM "assoc rules" simp $ Add (Lit 3) (Var "b")
    , test "simp-assoc-add5" $ do
      let simp = Expr.simplify $        Add (Var "a") (Add (Lit 1) (Lit 2))
      assertEqualM "assoc rules" simp $ Add (Lit 3) (Var "a")
    , test "simp-assoc-add6" $ do
      let simp = Expr.simplify $        Add (Lit 7) (Add (Lit 1) (Lit 2))
      assertEqualM "assoc rules" simp $ Lit 10
    , test "simp-assoc-add-7" $ do
      let simp = Expr.simplify $        Add (Var "a") (Add (Var "b") (Lit 2))
      assertEqualM "assoc rules" simp $ Add (Lit 2) (Add (Var "a") (Var "b"))
    , test "simp-assoc-add8" $ do
      let simp = Expr.simplify $        Add (Add (Var "a") (Add (Lit 0x2) (Var "b"))) (Add (Var "c") (Add (Lit 0x2) (Var "d")))
      assertEqualM "assoc rules" simp $ Add (Lit 4) (Add (Var "a") (Add (Var "b") (Add (Var "c") (Var "d"))))
    , test "simp-assoc-mul1" $ do
      let simp = Expr.simplify $        Mul (Mul (Var "b") (Var "a")) (Var "c")
      assertEqualM "assoc rules" simp $ Mul (Var "a") (Mul (Var "b") (Var "c"))
    , test "simp-assoc-mul2" $ do
      let simp = Expr.simplify       $  Mul (Lit 2) (Mul (Var "a") (Lit 3))
      assertEqualM "assoc rules" simp $ Mul (Lit 6) (Var "a")
    , test "simp-assoc-xor1" $ do
      let simp = Expr.simplify       $  Xor (Lit 2) (Xor (Var "a") (Lit 3))
      assertEqualM "assoc rules" simp $ Xor (Lit 1) (Var "a")
    , test "simp-assoc-xor2" $ do
      let simp = Expr.simplify       $  Xor (Lit 2) (Xor (Var "b") (Xor (Var "a") (Lit 3)))
      assertEqualM "assoc rules" simp $ Xor (Lit 1) (Xor (Var "a") (Var "b"))
    , test "simp-zero-write-extend-buffer-len" $ do
        let
          expr = BufLength $ CopySlice (Lit 0) (Lit 0x10) (Lit 0) (AbstractBuf "buffer") (ConcreteBuf "bimm")
          simp = Expr.simplify expr
        ret <-  checkEquiv expr simp
        assertEqualM "Must be equivalent" True ret
    , test "bufLength-simp" $ do
      let
        a = BufLength (ConcreteBuf "ab")
        simp = Expr.simplify a
      assertEqualM "Must be simplified down to a Lit" simp (Lit 2)
    , test "stripWrites-overflow" $ do
        -- below eventually boils down to
        -- unsafeInto (0xf0000000000000000000000000000000000000000000000000000000000000+1) :: Int
        -- which failed before
        let
          a = ReadByte (Lit 0xf0000000000000000000000000000000000000000000000000000000000000) (WriteByte (And (SHA256 (ConcreteBuf "")) (Lit 0x1)) (LitByte 0) (ConcreteBuf ""))
          b = Expr.simplify a
        ret <- checkEquiv a b
        assertBoolM "must be equivalent" ret
    , test "read-beyond-bound (negative-test)" $ do
      let
        e1 = CopySlice (Lit 1) (Lit 0) (Lit 2) (ConcreteBuf "a") (ConcreteBuf "")
        e2 = ConcreteBuf "Definitely not the same!"
      equal <- checkEquiv e1 e2
      assertBoolM "Should not be equivalent!" $ not equal
    , testNoSimplify "simplify-comparison-GEq" $ do
      let
        expr = PEq (Lit 0x1) (GEq (Var "v") (Lit 0x2))
        simp = Expr.simplifyProp expr
      ret <- checkEquivPropAndLHS expr simp
      assertEqualM "Must be equivalent" True ret
    , test "buffer-length-zero" $ do
        let
          p = PEq (BufLength (AbstractBuf "b")) (Lit 0x0)
          simp = Expr.simplifyProp p
        liftIO $ print simp
        ret <-  checkEquivProp p simp
        assertEqualM "Must be equivalent" True ret
    ]
  -- These tests fuzz the simplifier by generating a random expression,
  -- applying some simplification rules, and then using the smt encoding to
  -- check that the simplified version is semantically equivalent to the
  -- unsimplified one
  , adjustOption (\(Test.Tasty.QuickCheck.QuickCheckTests n) -> Test.Tasty.QuickCheck.QuickCheckTests (div n 2)) $ testGroup "SimplifierTests"
    [ testProperty  "buffer-simplification" $ \(expr :: Expr Buf) -> propNoSimp $ do
        let simplified = Expr.simplify expr
        checkEquivAndLHS expr simplified
    , testProperty  "buffer-simplification-len" $ \(expr :: Expr Buf) -> propNoSimp $ do
        let simplified = Expr.simplify (BufLength expr)
        checkEquivAndLHS (BufLength expr) simplified
    , testProperty "store-simplification" $ \(expr :: Expr Storage) -> propNoSimp $ do
        let simplified = Expr.simplify expr
        checkEquivAndLHS expr simplified
    , testProperty "load-simplification" $ \(GenWriteStorageLoad expr) -> propNoSimp $ do
        let simplified = Expr.simplify expr
        checkEquivAndLHS expr simplified
    , ignoreTest $ testProperty "load-decompose" $ \(GenWriteStorageLoad expr) -> propNoSimp $ do
        putStrLnM $ T.unpack $ formatExpr expr
        let simp = Expr.simplify expr
        let decomposed = fromMaybe simp $ mapExprM Expr.decomposeStorage simp
        -- putStrLnM $ "-----------------------------------------"
        -- putStrLnM $ T.unpack $ formatExpr decomposed
        -- putStrLnM $ "\n\n\n\n"
        checkEquiv expr decomposed
    , testProperty "byte-simplification" $ \(expr :: Expr Byte) -> propNoSimp $ do
        let simplified = Expr.simplify expr
        checkEquivAndLHS expr simplified
    , askOption $ \(QuickCheckTests n) -> testProperty "word-simplification" $ withMaxSuccess (min n 20) $ \(ZeroDepthWord expr) -> propNoSimp $ do
        let simplified = Expr.simplify expr
        checkEquivAndLHS expr simplified
    , testProperty "readStorage-equivalance" $ \(store, slot) -> propNoSimp $ do
        let simplified = Expr.readStorage' slot store
            full = SLoad slot store
        checkEquiv full simplified
    , testProperty "writeStorage-equivalance" $ \(val, GenWriteStorageExpr (slot, store)) -> propNoSimp $ do
        let simplified = Expr.writeStorage slot val store
            full = SStore slot val store
        checkEquiv full simplified
    , testProperty "readWord-equivalance" $ \(buf, idx) -> propNoSimp $ do
        let simplified = Expr.readWord idx buf
            full = ReadWord idx buf
        checkEquiv full simplified
    , testProperty "writeWord-equivalance" $ \(idx, val, WriteWordBuf buf) -> propNoSimp $ do
        let simplified = Expr.writeWord idx val buf
            full = WriteWord idx val buf
        checkEquiv full simplified
    , testProperty "arith-simplification" $ \(_ :: Int) -> propNoSimp $ do
        expr <- liftIO $ generate . sized $ genWordArith 15
        let simplified = Expr.simplify expr
        checkEquivAndLHS expr simplified
    , testProperty "readByte-equivalance" $ \(buf, idx) -> propNoSimp $ do
        let simplified = Expr.readByte idx buf
            full = ReadByte idx buf
        checkEquiv full simplified
    -- we currently only simplify concrete writes over concrete buffers so that's what we test here
    , testProperty "writeByte-equivalance" $ \(LitOnly val, LitOnly buf, GenWriteByteIdx idx) -> propNoSimp $ do
        let simplified = Expr.writeByte idx val buf
            full = WriteByte idx val buf
        checkEquiv full simplified
    , testProperty "copySlice-equivalance" $ \(srcOff, GenCopySliceBuf src, GenCopySliceBuf dst, LitWord @300 size) -> propNoSimp $ do
        -- we bias buffers to be concrete more often than not
        dstOff <- liftIO $ generate (maybeBoundedLit 100_000)
        let simplified = Expr.copySlice srcOff dstOff size src dst
            full = CopySlice srcOff dstOff size src dst
        checkEquiv full simplified
    , testProperty "indexWord-equivalence" $ \(src, LitWord @50 idx) -> propNoSimp $ do
        let simplified = Expr.indexWord idx src
            full = IndexWord idx src
        checkEquiv full simplified
    , testProperty "pow-base2-simp" $ \(_ :: Int) -> propNoSimp $ do
        expo <- liftIO $ generate . sized $ genWordArith 15
        let full = Exp (Lit 2) expo
            simplified = Expr.simplify full
        checkEquiv full simplified
    , testProperty "pow-low-exponent-simp" $ \(LitWord @100 expo) -> propNoSimp $ do
        base <- liftIO $ generate . sized $ genWordArith 15
        let full = Exp base expo
            simplified = Expr.simplify full
        checkEquiv full simplified
    , testProperty "indexWord-mask-equivalence" $ \(src :: Expr EWord, LitWord @35 idx) -> propNoSimp $ do
        mask <- liftIO $ generate $ do
          pow <- arbitrary :: Gen Int
          frequency
           [ (1, pure $ Lit $ (shiftL 1 (pow `mod` 256)) - 1)        -- potentially non byte aligned
           , (1, pure $ Lit $ (shiftL 1 ((pow * 8) `mod` 256)) - 1)  -- byte aligned
           ]
        let
          input = And mask src
          simplified = Expr.indexWord idx input
          full = IndexWord idx input
        checkEquiv full simplified
    , testProperty "toList-equivalance" $ \buf -> propNoSimp $ do
        let
          -- transforms the input buffer to give it a known length
          fixLength :: Expr Buf -> Gen (Expr Buf)
          fixLength = mapExprM go
            where
              go :: Expr a -> Gen (Expr a)
              go = \case
                WriteWord _ val b -> liftM3 WriteWord idx (pure val) (pure b)
                WriteByte _ val b -> liftM3 WriteByte idx (pure val) (pure b)
                CopySlice so _ sz src dst -> liftM5 CopySlice (pure so) idx (pure sz) (pure src) (pure dst)
                AbstractBuf _ -> cbuf
                e -> pure e
              cbuf = do
                bs <- arbitrary
                pure $ ConcreteBuf bs
              idx = do
                w <- arbitrary
                -- we use 100_000 as an upper bound for indices to keep tests reasonably fast here
                pure $ Lit (w `mod` 100_000)

        input <- liftIO $ generate $ fixLength buf
        case Expr.toList input of
          Nothing -> do
            putStrLnM "skip"
            pure True -- ignore cases where the buf cannot be represented as a list
          Just asList -> do
            let asBuf = Expr.fromList asList
            checkEquiv asBuf input
    , testProperty "simplifyProp-equivalence-lit" $ \(LitProp p) -> propNoSimp $ do
        let simplified = Expr.simplifyProps [p]
        case simplified of
          [] -> checkEquivProp (PBool True) p
          [val@(PBool _)] -> checkEquivProp val p
          _ -> liftIO $ assertFailure "must evaluate down to a literal bool"
    , testProperty "simplifyProp-equivalence-sym" $ \(p) -> propNoSimp $ do
        let simplified = Expr.simplifyProp p
        checkEquivPropAndLHS p simplified
    , testProperty "simplify-joinbytes" $ \(SymbolicJoinBytes exprList) -> propNoSimp $ do
        let x = joinBytesFromList exprList
        let simplified = Expr.simplify x
        y <- checkEquiv x simplified
        assertBoolM "Must be equal" y
    , testProperty "simpProp-equivalence-sym-Prop" $ \(ps :: [Prop]) -> propNoSimp $ do
        let simplified = pand (Expr.simplifyProps ps)
        checkEquivPropAndLHS (pand ps) simplified
    , testProperty "simpProp-equivalence-sym-LitProp" $ \(LitProp p) -> propNoSimp $ do
        let simplified = pand (Expr.simplifyProps [p])
        checkEquivPropAndLHS p simplified
    , testProperty "storage-slot-simp-property" $ \(StorageExp s) -> propNoSimp $ do
        -- we have to run `Expr.litToKeccak` on the unsimplified system, or
        -- we'd need some form of minimal simplifier for things to work out. As long as
        -- we trust the litToKeccak, this is fine, as that function is stand-alone,
        -- and quite minimal
        let s2 = Expr.litToKeccak s
        let simplified = Expr.simplify s2
        checkEquivAndLHS s2 simplified
    , test "storage-slot-single" $ do
        -- this tests that "" and "0"x32 is not equivalent in Keccak
        let x = SLoad (Add (Keccak (ConcreteBuf "")) (Lit 1)) (SStore (Keccak (ConcreteBuf "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")) (Lit 0) (AbstractStore (SymAddr "stuff") Nothing))
        let simplified = Expr.simplify x
        y <- checkEquivAndLHS x simplified
        assertBoolM "Must be equal" y
    , test "word-eq-bug" $ do
        -- This test is actually OK because the simplified takes into account that it's impossible to find a
        -- near-collision in the keccak hash
        let x =  (SLoad (Keccak (AbstractBuf "es")) (SStore (Add (Keccak (ConcreteBuf "")) (Lit 0x1)) (Lit 0xacab) (ConcreteStore (Map.empty))))
        let simplified = Expr.simplify x
        y <- checkEquiv x simplified
        assertBoolM "Must be equal, given keccak distance axiom" y
    ]
  {- NOTE: These tests were designed to test behaviour on reading from a buffer such that the indices overflow 2^256.
           However, such scenarios are impossible in the real world (the operation would run out of gas). The problem
           is that the behaviour of bytecode interpreters does not match the semantics of SMT. Intrepreters just
           return all zeroes for any read beyond buffer size, while in SMT reading multiple bytes may lead to overflow
           on indices and subsequently to reading from the beginning of the buffer (wrap-around semantics).
  , testGroup "concrete-buffer-simplification-large-index" [
      test "copy-slice-large-index-nooverflow" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x1) (ConcreteBuf "a") (ConcreteBuf "")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "copy-slice-overflow-back-into-source" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x2) (ConcreteBuf "a") (ConcreteBuf "")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "copy-slice-overflow-beyond-source" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x3) (ConcreteBuf "a") (ConcreteBuf "")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "copy-slice-overflow-beyond-source-into-nonempty" $ do
        let
          e = CopySlice (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Lit 0x0) (Lit 0x3) (ConcreteBuf "a") (ConcreteBuf "b")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
    , test "read-word-overflow-back-into-source" $ do
        let
          e = ReadWord (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (ConcreteBuf "kkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkk")
          s = Expr.simplify e
        equal <- checkEquiv e s
        assertEqualM "Must be equal" True equal
  ]
  -}
  , testGroup "simpProp-concrete-tests" [
      test "simpProp-concrete-trues" $ do
        let
          t = [PBool True, PBool True]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [] simplified
    , test "simpProp-concrete-false1" $ do
        let
          t = [PBool True, PBool False]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-concrete-false2" $ do
        let
          t = [PBool False, PBool False]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-concrete-or-1" $ do
        let
          -- a = 5 && (a=4 || a=3)  -> False
          t = [PEq (Lit 5) (Var "a"), POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 3))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , ignoreTest $ test "simpProp-concrete-or-2" $ do
        let
          -- Currently does not work, because we don't do simplification inside
          --   POr/PAnd using canBeSat
          -- a = 5 && (a=4 || a=5)  -> a=5
          t = [PEq (Lit 5) (Var "a"), POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 5))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [] simplified
    , test "simpProp-concrete-and-1" $ do
        let
          -- a = 5 && (a=4 && a=3)  -> False
          t = [PEq (Lit 5) (Var "a"), PAnd (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 3))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-concrete-or-of-or" $ do
        let
          -- a = 5 && ((a=4 || a=6) || a=3)  -> False
          t = [PEq (Lit 5) (Var "a"), POr (POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 6))) (PEq (Var "a") (Lit 3))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-inner-expr-simp" $ do
        let
          -- 5+1 = 6
          t = [PEq (Add (Lit 5) (Lit 1)) (Var "a")]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PEq (Lit 6) (Var "a")] simplified
    , test "simpProp-inner-expr-simp-with-canBeSat" $ do
        let
          -- 5+1 = 6, 6 != 7
          t = [PAnd (PEq (Add (Lit 5) (Lit 1)) (Var "a")) (PEq (Var "a") (Lit 7))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-inner-expr-bitwise-and" $ do
        let
          -- 1 & 2 != 2
          t = [PEq (And (Lit 1) (Lit 2)) (Lit 2)]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-inner-expr-bitwise-or" $ do
        let
          -- 2 | 4 == 6
          t = [PEq (Or (Lit 2) (Lit 4)) (Lit 6)]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [] simplified
    , test "simpProp-constpropagate-1" $ do
        let
          -- 5+1 = 6
          t = [PEq (Add (Lit 5) (Lit 1)) (Var "a"), PEq (Var "b") (Var "a")]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PEq (Lit 6) (Var "a"), PEq (Lit 6) (Var "b")] simplified
    , test "simpProp-constpropagate-2" $ do
        let
          -- 5+1 = 6
          t = [PEq (Add (Lit 5) (Lit 1)) (Var "a"), PEq (Var "b") (Var "a"), PEq (Var "c") (Sub (Var "b") (Lit 1))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PEq (Lit 6) (Var "a"), PEq (Lit 6) (Var "b"), PEq (Lit 5) (Var "c")] simplified
    , test "simpProp-constpropagate-3" $ do
        let
          t = [ PEq (Add (Lit 5) (Lit 1)) (Var "a") -- a = 6
              , PEq (Var "b") (Var "a")             -- b = 6
              , PEq (Var "c") (Sub (Var "b") (Lit 1)) -- c = 5
              , PEq (Var "d") (Sub (Var "b") (Var "c"))] -- d = 1
          simplified = Expr.simplifyProps t
        assertEqualM "Must  know d == 1" ((PEq (Lit 1) (Var "d")) `elem` simplified) True
  ]
  , testGroup "MemoryTests"
    [ test "read-write-same-byte"  $ assertEqualM ""
        (LitByte 0x12)
        (Expr.readByte (Lit 0x20) (WriteByte (Lit 0x20) (LitByte 0x12) mempty))
    , test "read-write-same-word"  $ assertEqualM ""
        (Lit 0x12)
        (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    , test "read-byte-write-word"  $ assertEqualM ""
        -- reading at byte 31 a word that's been written should return LSB
        (LitByte 0x12)
        (Expr.readByte (Lit 0x1f) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
    , test "read-byte-write-word2"  $ assertEqualM ""
        -- Same as above, but offset not 0
        (LitByte 0x12)
        (Expr.readByte (Lit 0x20) (WriteWord (Lit 0x1) (Lit 0x12) mempty))
    ,test "read-write-with-offset"  $ assertEqualM ""
        -- 0x3F = 63 decimal, 0x20 = 32. 0x12 = 18
        --    We write 128bits (32 Bytes), representing 18 at offset 32.
        --    Hence, when reading out the 63rd byte, we should read out the LSB 8 bits
        --           which is 0x12
        (LitByte 0x12)
        (Expr.readByte (Lit 0x3F) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    ,test "read-write-with-offset2"  $ assertEqualM ""
        --  0x20 = 32, 0x3D = 61
        --  we write 128 bits (32 Bytes) representing 0x10012, at offset 32.
        --  we then read out a byte at offset 61.
        --  So, at 63 we'd read 0x12, at 62 we'd read 0x00, at 61 we should read 0x1
        (LitByte 0x1)
        (Expr.readByte (Lit 0x3D) (WriteWord (Lit 0x20) (Lit 0x10012) mempty))
    , test "read-write-with-extension-to-zero" $ assertEqualM ""
        -- write word and read it at the same place (i.e. 0 offset)
        (Lit 0x12)
        (Expr.readWord (Lit 0x0) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
    , test "read-write-with-extension-to-zero-with-offset" $ assertEqualM ""
        -- write word and read it at the same offset of 4
        (Lit 0x12)
        (Expr.readWord (Lit 0x4) (WriteWord (Lit 0x4) (Lit 0x12) mempty))
    , test "read-write-with-extension-to-zero-with-offset2" $ assertEqualM ""
        -- write word and read it at the same offset of 16
        (Lit 0x12)
        (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    , test "read-word-over-write-byte" $ assertEqualM ""
        (ReadWord (Lit 0x4) (AbstractBuf "abs"))
        (Expr.readWord (Lit 0x4) (WriteByte (Lit 0x1) (LitByte 0x12) (AbstractBuf "abs")))
    , test "read-word-copySlice-overlap" $ assertEqualM ""
        -- we should not recurse into a copySlice if the read index + 32 overlaps the sliced region
        (ReadWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
        (Expr.readWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
    , test "read-word-copySlice-after-slice" $ assertEqualM "Read word simplification missing!"
        (ReadWord (Lit 100) (AbstractBuf "dst"))
        (Expr.readWord (Lit 100) (CopySlice (Var "srcOff") (Lit 12) (Lit 60) (AbstractBuf "src") (AbstractBuf "dst")))
    , test "indexword-MSB" $ assertEqualM ""
        -- 31st is the LSB byte (of 32)
        (LitByte 0x78)
        (Expr.indexWord (Lit 31) (Lit 0x12345678))
    , test "indexword-LSB" $ assertEqualM ""
        -- 0th is the MSB byte (of 32), Lit 0xff22bb... is exactly 32 Bytes.
        (LitByte 0xff)
        (Expr.indexWord (Lit 0) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
    , test "indexword-LSB2" $ assertEqualM ""
        -- same as above, but with offset 2
        (LitByte 0xbb)
        (Expr.indexWord (Lit 2) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
    , test "encodeConcreteStore-overwrite" $
      assertEqualM ""
        (pure "(store (store ((as const Storage) #x0000000000000000000000000000000000000000000000000000000000000000) (_ bv1 256) (_ bv2 256)) (_ bv3 256) (_ bv4 256))")
        (EVM.SMT.encodeConcreteStore $ Map.fromList [(W256 1, W256 2), (W256 3, W256 4)])
    , test "indexword-oob-sym" $ assertEqualM ""
        -- indexWord should return 0 for oob access
        (LitByte 0x0)
        (Expr.indexWord (Lit 100) (JoinBytes
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)))
    , test "stripbytes-concrete-bug" $ assertEqualM ""
        (Expr.simplifyReads (ReadByte (Lit 0) (ConcreteBuf "5")))
        (LitByte 53)
    ]
  , testGroup "ABI"
    [ testProperty "Put/get inverse" $ \x ->
        case runGetOrFail (getAbi (abiValueType x)) (runPut (putAbi x)) of
          Right ("", _, x') -> x' == x
          _ -> False
    , test "ABI-negative-small-int" $ do
        let bs = hex "ffffd6" -- -42 as int24
        let padded = BS.replicate (32 - BS.length bs) 0 <> bs -- padded to 32 bytes
        let withSelector = BS.replicate 4 0 <> padded -- added extra 4 bytes, simulating selector
        case decodeAbiValues [AbiIntType 24] withSelector of
          [AbiInt 24 val] -> assertEqualM "Incorrectly decoded int24 value" (-42) val
          _ -> internalError "Error in decoding function"
    ]
  , testGroup "Solidity-Expressions"
    [ test "Trivial" $
        SolidityCall "x = 3;" []
          ===> AbiUInt 256 3
    , test "Arithmetic" $ do
        SolidityCall "x = a + 1;"
          [AbiUInt 256 1] ===> AbiUInt 256 2
        SolidityCall "unchecked { x = a - 1; }"
          [AbiUInt 8 0] ===> AbiUInt 8 255
    , test "negative-numbers-nonzero-comp-1" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(int256 x) public {
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertGe(int256,int256)", x, -1);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(int256)" [AbiIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "negative-numbers-nonzero-comp-2" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(int256 x) public {
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertGe(int256,int256)", x, 1);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(int256)" [AbiIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "negative-numbers-min" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(int256 x) public {
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertLt(int256,int256)", x, type(int256).min);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(int256)" [AbiIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "negative-numbers-int128-1" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(int128 y) public {
                  int256 x = int256(y);
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertLt(int256,int256)", x, -1);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(int128)" [AbiIntType 128]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "negative-numbers-zero-comp-simpleassert" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(int256 x) public {
                assert(x >= 0);
              }
            } |]
        let sig = Just $ Sig "fun(int256)" [AbiIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "signed-int8-range" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function fun(int8 x) public {
              int256 y = x;
              assert (y != 1000);
            }
          } |]
        let sig = Just $ Sig "fun(int8)" [AbiIntType 8]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 0 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "base-2-exp-uint8" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function fun(uint8 x) public {
              unchecked {
                require(x < 10);
                uint256 y = 2**x;
                assert (y <= 512);
              }
            }
          } |]
        let sig = Just $ Sig "fun(uint8)" [AbiUIntType 8]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 0 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "base-2-exp-no-rollaround" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function fun(uint256 x) public {
              unchecked {
                require(x > 10);
                require(x < 256);
                uint256 y = 2**x;
                assert (y > 512);
              }
            }
          } |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 0 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "base-2-exp-rollaround" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function fun(uint256 x) public {
              unchecked {
                require(x == 256);
                uint256 y = 2**x;
                assert (y > 512);
              }
            }
          } |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "unsigned-int8-range" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function fun(uint8 x) public {
              uint256 y = x;
              assert (y != 1000);
            }
          } |]
        let sig = Just $ Sig "fun(uint8)" [AbiUIntType 8]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 0 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "negative-numbers-zero-comp" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(int256 x) public {
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertGe(int256,int256)", x, 0);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(int256)" [AbiIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "positive-numbers-cex" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(uint256 x) public {
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertGe(uint256,uint256)", x, 1);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 1 numCexes
        assertEqualM "number of errors" 0 numErrs
    , test "positive-numbers-qed" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(uint256 x) public {
                  // Cheatcode address
                  address vm = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
                  bytes memory data = abi.encodeWithSignature("assertGe(uint256,uint256)", x, 0);
                  (bool success, ) = vm.staticcall(data);
                  assert(success == true);
              }
            } |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must not be partial" $ not (any isPartial e)
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertEqualM "number of counterexamples" 0 numCexes
        assertEqualM "number of errors" 0 numErrs

    , test "keccak256()" $
        SolidityCall "x = uint(keccak256(abi.encodePacked(a)));"
          [AbiString ""] ===> AbiUInt 256 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    , testProperty "symbolic-abi-enc-vs-solidity" $ \(SymbolicAbiVal y) -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a);|] [y] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let
              frag = [symAbiArg "y" (AbiTupleType $ V.fromList [abiValueType y])]
              (hevmEncoded, _) = first (Expr.drop 4) $ combineFragments frag (ConcreteBuf "")
              expectedVals = expectedConcVals "y" (AbiTuple . V.fromList $ [y])
              hevmConcretePre = fromRight (error "cannot happen") $ subModel expectedVals hevmEncoded
              hevmConcrete = case Expr.simplify hevmConcretePre of
                               ConcreteBuf b -> b
                               buf -> internalError ("valMap: " <> show expectedVals <> "\ny:" <> show y <> "\n" <> "buf: " <> show buf)
          -- putStrLnM $ "frag: " <> show frag
          -- putStrLnM $ "expectedVals: " <> show expectedVals
          -- putStrLnM $ "frag: " <> show frag
          -- putStrLnM $ "hevmEncoded: " <> show hevmEncoded
          -- putStrLnM $ "solidity encoded: " <> show solidityEncoded
          -- putStrLnM $ "our encoded     : " <> show (AbiBytesDynamic hevmConcrete)
          -- putStrLnM $ "y     : " <> show y
          -- putStrLnM $ "y type: " <> showAlter y
          -- putStrLnM $ "hevmConcretePre: " <> show hevmConcretePre
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmConcrete)
    , testProperty "symbolic-abi encoding-vs-solidity-2-args" $ \(SymbolicAbiVal x', SymbolicAbiVal y') -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a, b);|] [x', y'] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [x',y'])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)
    , testProperty "abi-encoding-vs-solidity" $ forAll (arbitrary >>= genAbiValue) $
      \y -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a);|]
            [y] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [y])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    , testProperty "abi-encoding-vs-solidity-2-args" $ forAll (arbitrary >>= bothM genAbiValue) $
      \(x', y') -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a, b);|]
            [x', y'] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [x',y'])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    -- we need a separate test for this because the type of a function is "function() external" in solidity but just "function" in the abi:
    , askOption $ \(QuickCheckTests n) -> testProperty "abi-encoding-vs-solidity-function-pointer" $ withMaxSuccess (min n 20) $ forAll (genAbiValue AbiFunctionType) $
      \y -> prop $ do
          Just encoded <- runFunction [i|
              function foo(function() external a) public pure returns (bytes memory x) {
                x = abi.encode(a);
              }
            |] (abiMethod "foo(function)" (AbiTuple (V.singleton y)))
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [y])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)
    ]

  , testGroup "Precompiled contracts"
      [ testGroup "Example (reverse)"
          [ test "success" $
              assertEqualM "example contract reverses"
                (execute 0xdeadbeef "foobar" 6) (Just "raboof")
          , test "failure" $
              assertEqualM "example contract fails on length mismatch"
                (execute 0xdeadbeef "foobar" 5) Nothing
          ]

      , testGroup "ECRECOVER"
          [ test "success" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4732"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
                a = hex "0000000000000000000000002d5e56d45c63150d937f2182538a0f18510cb11f"
              assertEqualM "successful recovery"
                (Just a)
                (execute 1 (h <> v <> r <> s) 32)
          , test "fail on made up values" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4731"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
              assertEqualM "fail because bit flip"
                Nothing
                (execute 1 (h <> v <> r <> s) 32)
          ]
      ]
  , testGroup "Byte/word manipulations"
    [ testProperty "padLeft length" $ \n (Bytes bs) ->
        BS.length (padLeft n bs) == max n (BS.length bs)
    , testProperty "padLeft identity" $ \(Bytes bs) ->
        padLeft (BS.length bs) bs == bs
    , testProperty "padRight length" $ \n (Bytes bs) ->
        BS.length (padLeft n bs) == max n (BS.length bs)
    , testProperty "padRight identity" $ \(Bytes bs) ->
        padLeft (BS.length bs) bs == bs
    , testProperty "padLeft zeroing" $ \(NonNegative n) (Bytes bs) ->
        let x = BS.take n (padLeft (BS.length bs + n) bs)
            y = BS.replicate n 0
        in x == y
    ]

  , testGroup "Word/Addr encoding"
    [ testProperty "word256Bytes" $ \w ->
        word256Bytes w == slow_word256Bytes w
    , testProperty "word160Bytes" $ \a ->
        word160Bytes a == slow_word160Bytes a
    ]

  , testGroup "Unresolved link detection"
    [ test "holes detected" $ do
        let code' = "608060405234801561001057600080fd5b5060405161040f38038061040f83398181016040528101906100329190610172565b73__$f3cbc3eb14e5bd0705af404abcf6f741ec$__63ab5c1ffe826040518263ffffffff1660e01b81526004016100699190610217565b60206040518083038186803b15801561008157600080fd5b505af4158015610095573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906100b99190610145565b50506103c2565b60006100d36100ce84610271565b61024c565b9050828152602081018484840111156100ef576100ee610362565b5b6100fa8482856102ca565b509392505050565b600081519050610111816103ab565b92915050565b600082601f83011261012c5761012b61035d565b5b815161013c8482602086016100c0565b91505092915050565b60006020828403121561015b5761015a61036c565b5b600061016984828501610102565b91505092915050565b6000602082840312156101885761018761036c565b5b600082015167ffffffffffffffff8111156101a6576101a5610367565b5b6101b284828501610117565b91505092915050565b60006101c6826102a2565b6101d081856102ad565b93506101e08185602086016102ca565b6101e981610371565b840191505092915050565b60006102016003836102ad565b915061020c82610382565b602082019050919050565b6000604082019050818103600083015261023181846101bb565b90508181036020830152610244816101f4565b905092915050565b6000610256610267565b905061026282826102fd565b919050565b6000604051905090565b600067ffffffffffffffff82111561028c5761028b61032e565b5b61029582610371565b9050602081019050919050565b600081519050919050565b600082825260208201905092915050565b60008115159050919050565b60005b838110156102e85780820151818401526020810190506102cd565b838111156102f7576000848401525b50505050565b61030682610371565b810181811067ffffffffffffffff821117156103255761032461032e565b5b80604052505050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b600080fd5b600080fd5b600080fd5b600080fd5b6000601f19601f8301169050919050565b7f6261720000000000000000000000000000000000000000000000000000000000600082015250565b6103b4816102be565b81146103bf57600080fd5b50565b603f806103d06000396000f3fe6080604052600080fdfea26469706673582212207d03b26e43dc3d116b0021ddc9817bde3762a3b14315351f11fc4be384fd14a664736f6c63430008060033"
        assertBoolM "linker hole not detected" (containsLinkerHole code'),
      test "no false positives" $ do
        let code' = "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fea265627a7a723158205d775f914dcb471365a430b5f5b2cfe819e615cbbb5b2f1ccc7da1fd802e43c364736f6c634300050b0032"
        assertBoolM "false positive" (not . containsLinkerHole $ code')
    ]

  , testGroup "metadata stripper"
    [ test "it strips the metadata for solc => 0.6" $ do
        let code' = hexText "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fea265627a7a723158205d775f914dcb471365a430b5f5b2cfe819e615cbbb5b2f1ccc7da1fd802e43c364736f6c634300050b0032"
            stripped = stripBytecodeMetadata code'
        assertEqualM "failed to strip metadata" (show (ByteStringS stripped)) "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fe"
    ,
      testCase "it strips the metadata and constructor args" $ do
        let srccode =
              [i|
                contract A {
                  uint y;
                  constructor(uint x) public {
                    y = x;
                  }
                }
                |]

        Just initCode <- solidity "A" srccode
        assertEqual "constructor args screwed up metadata stripping" (stripBytecodeMetadata (initCode <> encodeAbiValue (AbiUInt 256 1))) (stripBytecodeMetadata initCode)
    ]

  , testGroup "RLP encodings"
    [ testProperty "rlp decode is a retraction (bytes)" $ \(Bytes bs) ->
      rlpdecode (rlpencode (BS bs)) == Just (BS bs)
    , testProperty "rlp encode is a partial inverse (bytes)" $ \(Bytes bs) ->
        case rlpdecode bs of
          Just r -> rlpencode r == bs
          Nothing -> True
    ,  testProperty "rlp decode is a retraction (RLP)" $ \(RLPData r) ->
       rlpdecode (rlpencode r) == Just r
    ]
 , testGroup "Panic code tests via symbolic execution"
  [
     test "assert-fail" $ do
       Just c <- solcRuntime "MyContract"
           [i|
           contract MyContract {
             function fun(uint256 a) external pure {
               assert(a != 0);
             }
            }
           |]
       (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Must be 0" 0 $ getVar ctr "arg1"
       putStrLnM  $ "expected counterexample found, and it's correct: " <> (show $ getVar ctr "arg1")
     ,
     test "safeAdd-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
               c = a+b;
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s [0x11] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        let x = getVar ctr "arg1"
        let y = getVar ctr "arg2"

        let maxUint = 2 ^ (256 :: Integer) :: Integer
        assertBoolM "Overflow must occur" (toInteger x + toInteger y >= maxUint)
        putStrLnM "expected counterexample found"
     ,
     test "div-by-zero-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
               c = a/b;
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Bitwuzla 1 1 Nothing $ \s -> checkAssert s [0x12] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        assertEqualM "Division by 0 needs b=0" (getVar ctr "arg2") 0
        putStrLnM "expected counterexample found"
     ,
      test "unused-args-fail" $ do
         Just c <- solcRuntime "C"
             [i|
             contract C {
               function fun(uint256 a) public pure {
                 assert(false);
               }
             }
             |]
         (_, [Cex _]) <- withSolvers Bitwuzla 1 1 Nothing $ \s -> checkAssert s [0x1] c Nothing [] defaultVeriOpts
         putStrLnM "expected counterexample found"
     , test "gas-decrease-monotone" $ do
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
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        putStrLnM "expected Qed found"
     , test "enum-conversion-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              enum MyEnum { ONE, TWO }
              function fun(uint256 a) external pure returns (MyEnum b) {
                b = MyEnum(a);
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Bitwuzla 1 1 Nothing $ \s -> checkAssert s [0x21] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        assertBoolM "Enum is only defined for 0 and 1" $ (getVar ctr "arg1") > 1
        putStrLnM "expected counterexample found"
     ,
     -- TODO 0x22 is missing: "0x22: If you access a storage byte array that is incorrectly encoded."
     -- TODO below should NOT fail
     -- TODO this has a loop that depends on a symbolic value and currently causes interpret to loop
     ignoreTest $ test "pop-empty-array" $ do
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
        a <- withDefaultSolver $ \s -> checkAssert s [0x31] c (Just (Sig "fun(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
        liftIO $ do
          print $ length a
          print $ show a
          putStrLnM "expected counterexample found"
     ,
     test "access-out-of-bounds-array" $ do
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
        (_, [Cex (_, _)]) <- withDefaultSolver $ \s -> checkAssert s [0x32] c (Just (Sig "fun(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
        -- assertBoolM "Access must be beyond element 2" $ (getVar ctr "arg1") > 1
        putStrLnM "expected counterexample found"
      ,
      -- Note: we catch the assertion here, even though we are only able to explore partially
      test "alloc-too-much" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a) external {
                uint[] memory arr = new uint[](a);
              }
             }
            |]
        (_, [Cex _]) <- withDefaultSolver $ \s ->
          checkAssert s [0x41] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "expected counterexample found"
      ,
      test "vm.deal unknown address" $ do
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
        Right e <- reachableUserAsserts c (Just $ Sig "f(address,uint256)" [AbiAddressType, AbiUIntType 256])
        assertBoolM "The expression is not partial" $ any isPartial e
      ,
      test "vm.prank-create" $ do
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
        Right _ <- reachableUserAsserts c (Just $ Sig "f()" [])
        liftIO $ putStrLn "no reachable assertion violations"
      ,
      test "vm.prank underflow" $ do
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
        r <- allBranchesFail c Nothing
        assertBoolM "all branches must fail" (isRight r)
      , test "cheatcode-nonexistent" $ do
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
        (e, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression must contain Partial." $ any isPartial e
      , test "cheatcode-with-selector" $ do
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
        Right e <- reachableUserAsserts c Nothing
        assertBoolM "The expression should not contain Partial." $ Prelude.not $ any isPartial e
      ,
      test "call ffi when disabled" $ do
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
        r <- allBranchesFail c Nothing
        assertBoolM "all branches must fail" (isRight r)
      ,
      -- TODO: we can't deal with symbolic jump conditions
      expectFail $ test "call-zero-inited-var-thats-a-function" $ do
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
        (_, [Cex (_, cex)]) <- withDefaultSolver $
          \s -> checkAssert s [0x51] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        let a = fromJust $ Map.lookup (Var "arg1") cex.vars
        assertEqualM "unexpected cex value" a 44
        putStrLnM "expected counterexample found"
      , test "symbolic-exp-0-to-n" $ do
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
        a <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        case a of
          (_, [Cex (_, ctr)]) -> do
            let b = getVar ctr "arg2"
            putStrLnM $ "b:" <> show b
            assertBoolM "b must be non-0" (b /= 0)
          _ -> assertBoolM "Wrong" False
      , test "symbolic-exp-0-to-n2" $ do
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
        a <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        case a of
          (_, [Cex (_, ctr)]) -> do
            let b = getVar ctr "arg2"
            putStrLnM $ "b:" <> show b
            assertBoolM "b must be 0" (b == 0)
          _ -> assertBoolM "Wrong" False
      ,
      test "symbolic-mcopy" $ do
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
        (_, k) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        let numErrs = sum $ map (fromEnum . isError) k
        assertEqualM "number of errors (i.e. copySlice issues) is 1" 1 numErrs
        let errStrings = mapMaybe getResError k
        assertEqualM "All errors are from copyslice" True $ all ("CopySlice" `List.isInfixOf`) errStrings
      -- below we hit the limit of the depth of the symbolic execution tree
      , testCase "limit-num-explore-hit-limit" $ do
        let conf = testEnv.config {maxDepth = Just 3}
        let myTestEnv :: Env = (testEnv :: Env) {config = conf :: Config}
        runEnv myTestEnv $ do
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
          (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
          let numCexes = sum $ map (fromEnum . isCex) ret
          let numErrs = sum $ map (fromEnum . isError) ret
          assertBoolM "The expression MUST be partial" (any isPartial paths)
          assertEqualM "number of errors" 0 numErrs
          assertEqualM "number of counterexamples" 0 numCexes
      -- below we don't hit the limit of the depth of the symbolic execution tree
      , testCase "limit-num-explore-no-hit-limit" $ do
        let conf = testEnv.config {maxDepth = Just 7}
        let myTestEnv :: Env = (testEnv :: Env) {config = conf :: Config}
        runEnv myTestEnv $ do
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
          (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
          let numCexes = sum $ map (fromEnum . isCex) ret
          let numErrs = sum $ map (fromEnum . isError) ret
          assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
          assertEqualM "number of errors" 0 numErrs
          assertEqualM "number of counterexamples" 1 numCexes
      , test "symbolic-copyslice" $ do
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
        (_, k) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        let numErrs = sum $ map (fromEnum . isError) k
        assertEqualM "number of errors (i.e. copySlice issues) is 1" 1 numErrs
        let errStrings = mapMaybe getResError k
        assertEqualM "All errors are from copyslice" True $ all ("CopySlice" `List.isInfixOf`) errStrings
  ]
  , testGroup "Symbolic-Constructor-Args"
    -- this produced some hard to debug failures. keeping it around since it seemed to exercise the contract creation code in interesting ways...
    [ test "multiple-symbolic-constructor-calls" $ do
        Just initCode <- solidity "C"
          [i|
            contract A {
                uint public x;
                constructor (uint z)  {}
            }

            contract B {
                constructor (uint i)  {}

            }

            contract C {
                constructor(uint u) {
                  new A(u);
                  new B(u);
                }
            }
          |]
        withSolvers Bitwuzla 1 1 Nothing $ \s -> do
          let calldata = (WriteWord (Lit 0x0) (Var "u") (ConcreteBuf ""), [])
          initVM <- liftIO $ stToIO $ abstractVM calldata initCode Nothing True
          let iterConf = IterConfig {maxIter=Nothing, askSmtIters=1, loopHeuristic=StackBased }
          paths <- interpret (Fetch.noRpcFetcher s) iterConf initVM runExpr noopPathHandler
          let exprSimp = map Expr.simplify paths
          assertBoolM "unexptected partial execution" (not $ any isPartial exprSimp)
    , test "mixed-concrete-symbolic-args" $ do
        Just c <- solcRuntime "C"
          [i|
            contract B {
                uint public x;
                uint public y;
                constructor (uint i, uint j)  {
                  x = i;
                  y = j;
                }

            }

            contract C {
                function foo(uint i) public {
                  B b = new B(10, i);
                  assert(b.x() == 10);
                  assert(b.y() == i);
                }
            }
          |]
        Right paths <- reachableUserAsserts c (Just $ Sig "foo(uint256)" [AbiUIntType 256])
        assertBoolM "unexptected partial execution" $ Prelude.not (any isPartial paths)
    , test "extcodesize-symbolic" $ do
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function foo(address a, uint x) public {
               require(x > 10);
                uint size;
                assembly {
                  size := extcodesize(a)
                }
                assert(x >= 5);
              }
            }
          |]
        let sig = (Just $ Sig "foo(address,uint256)" [AbiAddressType, AbiUIntType 256])
        (e, res) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        liftIO $ printWarnings Nothing e res "the contracts under test"
        assertEqualM "Must be QED" res []
    , test "extcodesize-symbolic2" $ do
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function foo(address a, uint x) public {
                uint size;
                assembly {
                  size := extcodesize(a)
                }
                assert(size > 5);
              }
            }
          |]
        let sig = (Just $ Sig "foo(address,uint256)" [AbiAddressType, AbiUIntType 256])
        (e, res@[Cex _]) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        liftIO $ printWarnings Nothing e res "the contracts under test"
    , test "jump-into-symbolic-region" $ do
        let
          -- our initCode just jumps directly to the end
          code = BS.pack . mapMaybe maybeLitByteSimp $ V.toList $ assemble
              [ OpPush (Lit 0x85)
              , OpJump
              , OpPush (Lit 1)
              , OpPush (Lit 1)
              , OpPush (Lit 1)
              , OpJumpdest
              ]
          -- we write a symbolic word to the middle, so the jump above should
          -- fail since the target is not in the concrete region
          initCode = (WriteWord (Lit 0x43) (Var "HI") (ConcreteBuf code), [])

          -- we pass in the above initCode buffer as calldata, and then copy
          -- it into memory before calling Create
          runtimecode = RuntimeCode (SymbolicRuntimeCode $ assemble
              [ OpPush (Lit 0x85)
              , OpPush (Lit 0x0)
              , OpPush (Lit 0x0)
              , OpCalldatacopy
              , OpPush (Lit 0x85)
              , OpPush (Lit 0x0)
              , OpPush (Lit 0x0)
              , OpCreate
              ])
        withDefaultSolver $ \s -> do
          vm <- liftIO $ stToIO $ loadSymVM runtimecode (Lit 0) initCode False
          let iterConf = IterConfig {maxIter=Nothing, askSmtIters=1, loopHeuristic=StackBased }
          paths <- interpret (Fetch.noRpcFetcher s) iterConf vm runExpr noopPathHandler
          let exprSimp = map Expr.simplify paths
          assertBoolM "expected partial execution" (any isPartial exprSimp)
    ]
  , testGroup "Dapp-Tests"
    [ test "Trivial-Pass" $ do
        let testFile = "test/contracts/pass/trivial.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "Foundry" $ do
        -- quick smokecheck to make sure that we can parse ForgeStdLib style build outputs
        -- return is a pair of (No Cex, No Warnings)
        let cases =
              [ ("test/contracts/pass/trivial.sol",       ".*", (True, True))
              , ("test/contracts/pass/dsProvePass.sol",   ".*", (True, True))
              , ("test/contracts/pass/revertEmpty.sol",   ".*", (True, True))
              , ("test/contracts/pass/revertString.sol",  ".*", (True, True))
              , ("test/contracts/pass/requireEmpty.sol",  ".*", (True, True))
              , ("test/contracts/pass/requireString.sol", ".*", (True, True))
              -- overapproximation
              , ("test/contracts/pass/no-overapprox-staticcall.sol", ".*", (True, True))
              , ("test/contracts/pass/no-overapprox-delegatecall.sol", ".*", (True, True))
              -- failure cases
              , ("test/contracts/fail/trivial.sol",       ".*", (False, False))
              , ("test/contracts/fail/dsProveFail.sol",   "prove_add", (False, True))
              , ("test/contracts/fail/dsProveFail.sol",   "prove_multi", (False, True))
              -- all branches revert, which is a warning
              , ("test/contracts/fail/dsProveFail.sol",   "prove_trivial.*", (False, False))
              , ("test/contracts/fail/dsProveFail.sol",   "prove_distributivity", (False, True))
              , ("test/contracts/fail/assertEq.sol",      ".*", (False, True))
              -- bad cheatcode detected, hence the warning
              , ("test/contracts/fail/bad-cheatcode.sol", ".*", (False, False))
              -- symbolic failures -- either the text or the selector is symbolic
              , ("test/contracts/fail/symbolicFail.sol",      "prove_conc_fail_allrev.*", (False, False))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_conc_fail_somerev.*", (False, True))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_allrev_text.*", (False, False))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_somerev_text.*", (False, True))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_allrev_selector.*", (False, False))
              , ("test/contracts/fail/symbolicFail.sol",      "prove_symb_fail_somerev_selector.*", (False, True))]
        forM_ cases $ \(testFile, match, expected) -> do
          actual <- runForgeTestCustom testFile match Nothing Nothing False Fetch.noRpc
          putStrLnM $ "Test result for " <> testFile <> " match: " <> T.unpack match <> ": " <> show actual
          assertEqualM "Must match" expected actual
    , test "Trivial-Fail" $ do
        let testFile = "test/contracts/fail/trivial.sol"
        runForgeTest testFile "prove_false" >>= assertEqualM "test result" (False, False)
    , test "Abstract" $ do
        let testFile = "test/contracts/pass/abstract.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "Constantinople" $ do
        let testFile = "test/contracts/pass/constantinople.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "ConstantinopleMin" $ do
        let testFile = "test/contracts/pass/constantinople_min.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "Prove-Tests-Pass" $ do
        let testFile = "test/contracts/pass/dsProvePass.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "prefix-check-for-dapp" $ do
        let testFile = "test/contracts/fail/check-prefix.sol"
        runForgeTest testFile "prove_trivial" >>= assertEqualM "test result" (False, False)
    , test "transfer-dapp" $ do
        let testFile = "test/contracts/pass/transfer.sol"
        runForgeTest testFile "prove_transfer" >>= assertEqualM "should prove transfer" (True, True)
    , test "nonce-issues" $ do
        let testFile = "test/contracts/pass/nonce-issues.sol"
        runForgeTest testFile "prove_prank_addr_exists" >>= assertEqualM "should not bail" (True, True)
        runForgeTest testFile "prove_nonce_addr_nonexistent" >>= assertEqualM "should not bail" (True, True)
    , test "Prove-Tests-Fail" $ do
        let testFile = "test/contracts/fail/dsProveFail.sol"
        runForgeTest testFile "prove_trivial" >>= assertEqualM "prove_trivial" (False, False)
        runForgeTest testFile "prove_trivial_dstest" >>= assertEqualM "prove_trivial_dstest" (False, False)
        runForgeTest testFile "prove_add" >>= assertEqualM "prove_add" (False, True)
        runForgeTestCustom testFile "prove_smtTimeout" (Just 1) Nothing False Fetch.noRpc
          >>= assertEqualM "prove_smtTimeout" (True, False)
        runForgeTest testFile "prove_multi" >>= assertEqualM "prove_multi" (False, True)
        runForgeTest testFile "prove_distributivity" >>= assertEqualM "prove_distributivity" (False, True)
    , test "Loop-Tests" $ do
        let testFile = "test/contracts/pass/loops.sol"
        runForgeTestCustom testFile "prove_loop" Nothing (Just 10) False Fetch.noRpc  >>= assertEqualM "test result" (True, False)
        runForgeTestCustom testFile "prove_loop" Nothing (Just 100) False Fetch.noRpc >>= assertEqualM "test result" (False, False)
    , test "Cheat-Codes-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodes.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, False)
    , test "Cheat-Codes-Fork-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodesFork.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "Unwind" $ do
        let testFile = "test/contracts/pass/unwind.sol"
        runForgeTest testFile ".*" >>= assertEqualM "test result" (True, True)
    , test "Keccak" $ do
        let testFile = "test/contracts/pass/keccak.sol"
        runForgeTest testFile "prove_access" >>= assertEqualM "test result" (True, True)
    ]
  , testGroup "max-iterations"
    [ test "concrete-loops-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 5; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun()" []
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 3 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is not partial" $ any isPartial e
    , test "concrete-loops-not-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 5; i++) count++;
                return count;
              }
            }
            |]

        let sig = Just $ Sig "fun()" []
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 6 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is partial" $ not $ any isPartial e
    , test "symbolic-loops-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let veriOpts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 5 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] veriOpts
        assertBoolM "The expression MUST be partial" $ any (Expr.containsNode isPartial) e
    , test "inconsistent-paths" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 3);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- we don't ask the solver about the loop condition until we're
            -- already in an inconsistent path (i == 5, j <= 3, i < j), so we
            -- will continue looping here until we hit max iterations
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf { maxIter = Just 10, askSmtIters = 5 }}
        (e, []) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression MUST be partial" $ any (Expr.containsNode isPartial) e
    , test "mem-tuple" $ do
        Just c <- solcRuntime "C"
          [i|
            contract C {
              struct Pair {
                uint x;
                uint y;
              }
              function prove_tuple_pass(Pair memory p) public pure {
                uint256 f = p.x;
                uint256 g = p.y;
                unchecked {
                  p.x+=p.y;
                  assert(p.x == (f + g));
                }
              }
            }
          |]
        let opts = defaultVeriOpts
        let sig = Just $ Sig "prove_tuple_pass((uint256,uint256))" [AbiTupleType (V.fromList [AbiUIntType 256, AbiUIntType 256])]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] opts
        putStrLnM "Qed, memory tuple is good"
    , test "symbolic-loops-not-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 3);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- askSmtIters is low enough here to avoid the inconsistent path
            -- conditions, so we never hit maxIters
            opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 5, askSmtIters = 1 }}
        (e, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression MUST NOT be partial" $ not (any (Expr.containsNode isPartial) e)
    ]
  , testGroup "Symbolic Addresses"
    -- TODO ignore only because Martin has a fix for this-- it should not be using `verify`
    [ test "symbolic-address-create" $ do
        let src = [i|
                  contract A {
                    constructor() payable {}
                  }
                  contract C {
                    function fun(uint256 a) external{
                      require(address(this).balance > a);
                      new A{value:a}();
                    }
                  }
                  |]
        Just a <- solcRuntime "A" src
        Just c <- solcRuntime "C" src
        let sig = Sig "fun(uint256)" [AbiUIntType 256]
        paths <- withDefaultSolver $ \s -> exploreContract s c (Just sig) [] defaultVeriOpts Nothing
        let isSuc (Success {}) = True
            isSuc _ = False
        case filter isSuc paths of
          [Success _ _ _ store] -> do
            let ca = fromJust (Map.lookup (SymAddr "freshSymAddr1") store)
            let code = case ca.code of
                  RuntimeCode (ConcreteRuntimeCode c') -> c'
                  _ -> internalError "expected concrete code"
            assertEqualM "balance mismatch" (Var "arg1") (Expr.simplify ca.balance)
            assertEqualM "code mismatch" (stripBytecodeMetadata a) (stripBytecodeMetadata code)
            assertEqualM "nonce mismatch" (Just 1) ca.nonce
          _ -> assertBoolM "too many/too few success nodes!" False
    , test "symbolic-balance-call" $ do
        let src = [i|
                  contract A {
                    function f() public payable returns (uint) {
                      return msg.value;
                    }
                  }
                  contract C {
                    function fun(uint256 x) external {
                      require(address(this).balance > x);
                      A a = new A();
                      uint res = a.f{value:x}();
                      assert(res == x);
                    }
                  }
                  |]
        Just c <- solcRuntime "C" src
        res <- reachableUserAsserts c Nothing
        assertBoolM "unexpected cex" (isRight res)
    , test "deployed-contract-addresses-cannot-alias1" $ do
        Just c <- solcRuntime "C"
          [i|
            contract A {}
            contract C {
              function f() external {
                A a = new A();
                uint256 addr = uint256(uint160(address(a)));
                uint256 addr2 = uint256(uint160(address(this)));
                assert(addr != addr2);
              }
            }
          |]
        res <- reachableUserAsserts c Nothing
        assertBoolM "should not be able to alias" (isRight res)
    , test "deployed-contract-addresses-cannot-alias2" $ do
        Just c <- solcRuntime "C"
          [i|
            contract A {}
            contract C {
              function f() external {
                A a = new A();
                assert(address(a) != address(this));
              }
            }
          |]
        res <- reachableUserAsserts c Nothing
        assertBoolM "should not be able to alias" (isRight res)
    , test "addresses-in-args-can-alias-anything" $ do
        let addrs :: [Text]
            addrs = ["address(this)", "tx.origin", "block.coinbase", "msg.sender"]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract C {
                             function f(address a) external {
                               if (${vs} == a) assert(false);
                             }
                           }
                         |]

        [self, origin, coinbase, caller] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a = (Map.lookup (SymAddr "arg1") as) @?= (Map.lookup a as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check coinbase (SymAddr "coinbase")
          check caller (SymAddr "caller")
    , test "addresses-in-args-can-alias-themselves" $ do
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function f(address a, address b) external {
                if (a == b) assert(false);
              }
            }
          |]
        let sig = Just $ Sig "f(address,address)" [AbiAddressType,AbiAddressType]
        Left [cex] <- reachableUserAsserts c sig
        let arg1 = fromJust $ Map.lookup (SymAddr "arg1") cex.addrs
            arg2 = fromJust $ Map.lookup (SymAddr "arg1") cex.addrs
        assertEqualM "should match" arg1 arg2
    -- TODO: fails due to missing aliasing rules
    , expectFail $ test "tx.origin cannot alias deployed contracts" $ do
        Just c <- solcRuntime "C"
          [i|
            contract A {}
            contract C {
              function f() external {
                address a = address(new A());
                if (tx.origin == a) assert(false);
              }
            }
          |]
        cexs <- reachableUserAsserts c Nothing
        assertBoolM "unexpected cex" (isRight cexs)
    , test "tx.origin can alias everything else" $ do
        let addrs = ["address(this)", "block.coinbase", "msg.sender", "arg"] :: [Text]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract C {
                             function f(address arg) external {
                               if (${vs} == tx.origin) assert(false);
                             }
                           }
                         |]

        [self, coinbase, caller, arg] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a = (Map.lookup (SymAddr "origin") as) @?= (Map.lookup a as)
          check self (SymAddr "entrypoint")
          check coinbase (SymAddr "coinbase")
          check caller (SymAddr "caller")
          check arg (SymAddr "arg1")
    , test "coinbase can alias anything" $ do
        let addrs = ["address(this)", "tx.origin", "msg.sender", "a", "arg"] :: [Text]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract A {}
                           contract C {
                             function f(address arg) external {
                               address a = address(new A());
                               if (${vs} == block.coinbase) assert(false);
                             }
                           }
                         |]

        [self, origin, caller, a, arg] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a' = (Map.lookup (SymAddr "coinbase") as) @?= (Map.lookup a' as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check caller (SymAddr "caller")
          check a (SymAddr "freshSymAddr1")
          check arg (SymAddr "arg1")
    , test "caller can alias anything" $ do
        let addrs = ["address(this)", "tx.origin", "block.coinbase", "a", "arg"] :: [Text]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract A {}
                           contract C {
                             function f(address arg) external {
                               address a = address(new A());
                               if (${vs} == msg.sender) assert(false);
                             }
                           }
                         |]

        [self, origin, coinbase, a, arg] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a' = (Map.lookup (SymAddr "caller") as) @?= (Map.lookup a' as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check coinbase (SymAddr "coinbase")
          check a (SymAddr "freshSymAddr1")
          check arg (SymAddr "arg1")
    , test "vm.load fails for a potentially aliased address" $ do
        Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function load(address,bytes32) external returns (bytes32);
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.load(msg.sender, 0x0);
              }
            }
          |]
        -- NOTE: we have a postcondition here, not just a regular verification
        (_, [Cex _]) <- withDefaultSolver $ \s ->
          verifyContract s c Nothing [] defaultVeriOpts Nothing (checkBadCheatCode "load(address,bytes32)")
        pure ()
    , test "vm.store fails for a potentially aliased address" $ do
        Just c <- solcRuntime "C"
          [i|
            interface Vm {
                function store(address,bytes32,bytes32) external;
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.store(msg.sender, 0x0, 0x0);
              }
            }
          |]
        -- NOTE: we have a postcondition here, not just a regular verification
        (_, [Cex _]) <- withDefaultSolver $ \s ->
          verifyContract s c Nothing [] defaultVeriOpts Nothing (checkBadCheatCode "store(address,bytes32,bytes32)")
        pure ()
    -- TODO: make this work properly
    , test "transfering-eth-does-not-dealias" $ do
        Just c <- solcRuntime "C"
          [i|
            // we can't do calls to unknown code yet so we use selfdestruct
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }
            contract C {
              function f() external {
                uint preSender = msg.sender.balance;
                uint preOrigin = tx.origin.balance;

                new Send{value:10}(payable(msg.sender));
                new Send{value:5}(payable(tx.origin));

                if (msg.sender == tx.origin) {
                  assert(preSender == preOrigin
                      && msg.sender.balance == preOrigin + 15
                      && tx.origin.balance == preSender + 15);
                } else {
                  assert(msg.sender.balance == preSender + 10
                      && tx.origin.balance == preOrigin + 5);
                }
              }
            }
          |]
        Right e <- reachableUserAsserts c Nothing
        -- TODO: this should work one day
        assertBoolM "should be partial" (any isPartial e)
    , test "symbolic-addresses-cannot-be-zero-or-precompiles" $ do
        let addrs = [T.pack . show . Addr $ a | a <- [0x0..0x09]]
            mkC a = fromJust <$> solcRuntime "A"
              [i|
                contract A {
                  function f() external {
                    assert(msg.sender != address(${a}));
                  }
                }
              |]
        codes <- mapM mkC addrs
        results <- mapM (flip reachableUserAsserts (Just (Sig "f()" []))) codes
        let ok = and $ fmap (isRight) results
        assertBoolM "unexpected cex" ok
    , test "addresses-in-context-are-symbolic" $ do
        Just a <- solcRuntime "A"
          [i|
            contract A {
              function f() external {
                assert(msg.sender != address(0x10));
              }
            }
          |]
        Just b <- solcRuntime "B"
          [i|
            contract B {
              function f() external {
                assert(block.coinbase != address(0x11));
              }
            }
          |]
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function f() external {
                assert(tx.origin != address(0x12));
              }
            }
          |]
        Just d <- solcRuntime "D"
          [i|
            contract D {
              function f() external {
                assert(address(this) != address(0x13));
              }
            }
          |]
        [acex,bcex,ccex,dcex] <- forM [a,b,c,d] $ \con -> do
          Left [cex] <- reachableUserAsserts con Nothing
          assertEqualM "wrong number of addresses" 1 (length (Map.keys cex.addrs))
          pure cex

        -- Lowest allowed address is 0x10 due to reserved addresses up to 0x9
        assertEqualM "wrong model for a" (Addr 0x10) (fromJust $ Map.lookup (SymAddr "caller") acex.addrs)
        assertEqualM "wrong model for b" (Addr 0x11) (fromJust $ Map.lookup (SymAddr "coinbase") bcex.addrs)
        assertEqualM "wrong model for c" (Addr 0x12) (fromJust $ Map.lookup (SymAddr "origin") ccex.addrs)
        assertEqualM "wrong model for d" (Addr 0x13) (fromJust $ Map.lookup (SymAddr "entrypoint") dcex.addrs)
    ]
  , testGroup "Symbolic execution"
      [
     test "require-test" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 a) external pure {
              require(a <= 0);
              assert (a <= 0);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256)" [AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "Require works as expected"
     , test "symbolic-block-number" $ do
       Just c <- solcRuntime "C" [i|
           interface Vm {
               function roll(uint) external;
           }
           contract C {
             function myfun(uint x, uint y) public {
               Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
               vm.roll(x);
               assert(block.number == y);
             }
           } |]
       (e, [Cex _]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
       assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial e)
     , test "symbolic-to-concrete-multi" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            interface Vm {
              function deal(address,uint256) external;
            }
            contract MyContract {
              function fun(uint160 a) external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                uint160 c = 10 + (a % 2);
                address b = address(c);
                vm.deal(b, 10);
              }
             }
            |]
        let sig = Just (Sig "fun(uint160)" [AbiUIntType 160])
        (e, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertBoolM "The expression is not partial" $ Prelude.not (any isPartial e)
     ,
     -- here test
     test "ITE-with-bitwise-AND" $ do
       Just c <- solcRuntime "C"
         [i|
         contract C {
           function f(uint256 x) public pure {
             require(x > 0);
             uint256 a = (x & 8);
             bool w;
             // assembly is needed here, because solidity doesn't allow uint->bool conversion
             assembly {
                 w:=a
             }
             if (!w) assert(false); //we should get a CEX: when x has a 0 at bit 3
           }
         }
         |]
       -- should find a counterexample
       (_, [Cex _]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       putStrLnM "expected counterexample found"
     ,
     test "ITE-with-bitwise-OR" $ do
       Just c <- solcRuntime "C"
         [i|
         contract C {
           function f(uint256 x) public pure {
             uint256 a = (x | 8);
             bool w;
             // assembly is needed here, because solidity doesn't allow uint->bool conversion
             assembly {
                 w:=a
             }
             assert(w); // due to bitwise OR with positive value, this must always be true
           }
         }
         |]
       (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       putStrLnM "this should always be true, due to bitwise OR with positive value"
     ,
     test "abstract-returndata-size" $ do
       Just c <- solcRuntime "C"
         [i|
         contract C {
           function f(uint256 x) public pure {
             assembly {
                 return(0, x)
             }
           }
         }
         |]
       paths <- withDefaultSolver $ \s -> getExpr s c (Just (Sig "f(uint256)" [])) [] defaultVeriOpts
       assertBoolM "The expression is partial" $ Prelude.not (any isPartial paths)
    ,
    -- CopySlice check
    -- uses identity precompiled contract (0x4) to copy memory
    -- checks 9af114613075a2cd350633940475f8b6699064de (readByte + CopySlice had src/dest mixed up)
    -- without 9af114613 it dies with: `Exception: UnexpectedSymbolicArg 296 "MSTORE index"`
    --       TODO: check  9e734b9da90e3e0765128b1f20ce1371f3a66085 (bufLength + copySlice was off by 1)
    test "copyslice-check" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
          function checkval(uint8 a) public {
            bytes memory data = new bytes(5);
            for(uint i = 0; i < 5; i++) data[i] = bytes1(a);
            bytes memory ret = new bytes(data.length);
            assembly {
                let len := mload(data)
                if iszero(call(0xff, 0x04, 0, add(data, 0x20), len, add(ret,0x20), len)) {
                    invalid()
                }
            }
            for(uint i = 0; i < 5; i++) assert(ret[i] == data[i]);
          }
        }
        |]
      let sig = Just (Sig "checkval(uint8)" [AbiUIntType 8])
      (res, []) <- withDefaultSolver $ \s ->
        checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored " <> show (length res) <> " paths"
    , test "staticcall-check-orig" $ do
      Just c <- solcRuntime "C"
        [i|
        contract Target {
            function add(uint256 x, uint256 y) external pure returns (uint256) {
              unchecked {
                return x + y;
              }
            }
        }

        contract C {
            function checkval(uint256 x, uint256 y) public {
                Target t = new Target();
                address realAddr = address(t);
                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = realAddr.staticcall(data);
                assert(success);

                uint result = abi.decode(returnData, (uint256));
                uint expected;
                unchecked {
                  expected = x + y;
                }
                assert(result == expected);
            }
        }
        |]
      let sig = Just (Sig "checkval(uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of counterexamples" 0 numCexes
      assertEqualM "number of errors" 0 numErrs
    , test "staticcall-check-orig2" $ do
      Just c <- solcRuntime "C"
        [i|
        contract Target {
            function add(uint256 x, uint256 y) external pure returns (uint256) {
              assert(1 == 0);
            }
        }
        contract C {
            function checkval(uint256 x, uint256 y) public {
                Target t = new Target();
                address realAddr = address(t);
                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = realAddr.staticcall(data);
                assert(success);
            }
        }
        |]
      let sig = Just (Sig "checkval(uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      assertBoolM "The expression is NOT partial" $ Prelude.not (any isPartial res)
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of counterexamples" 1 numCexes
      assertEqualM "number of errors" 0 numErrs
    , test "copyslice-symbolic-ok" $ do
      Just c <- solcRuntime "C"
        [i|
         contract Target {
           function get(address addr) external view returns (uint256) {
               return 55;
           }
         }
         contract C {
           function retFor(address addr) public returns (uint256) {
               Target mm = new Target();
               uint256 ret = mm.get(addr);
               assert(ret == 4);
               return ret;
           }
         }
        |]
      let sig2 = Just (Sig "retFor(address)" [AbiAddressType])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig2 [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length paths) <> " paths"
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      assertBoolM "The expression is NOT partial" $ not (any isPartial paths)
    , test "no-overapprox-when-present" $ do
      Just c <- solcRuntime "C" [i|
        contract ERC20 {
          function f() public {
          }
        }

        contract C {
          address token;

          function no_overapp() public {
            token = address(new ERC20());
            token.delegatecall(abi.encodeWithSignature("f()"));
          }
        } |]
      let sig2 = Just (Sig "no_overapp()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig2 [] defaultVeriOpts
      -- putStrLnM $ "paths: " <> show paths
      putStrLnM $ "successfully explored: " <> show (length paths) <> " paths"
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      assertBoolM "The expression is NOT partial" $ not (any isPartial paths)
      let numCexes = sum $ map (fromEnum . isCex) ret
      assertEqualM "number of counterexamples" 0 numCexes
    -- NOTE: below used to be symbolic copyslice copy error before new copyslice
    --       simplifications in Expr.simplify
    , test "overapproximates-undeployed-contract-symbolic" $ do
      Just c <- solcRuntime "C"
        [i|
         contract Target {
           function get(address addr) external view returns (uint256) {
               return 55;
           }
         }
         contract C {
           Target mm;
           function retFor(address addr) public returns (uint256) {
               // NOTE: this is symbolic execution, and no setUp has been ran
               //       hence, this below calls unknown code! It's trying to load:
               //       (SLoad (Lit 0x0) (AbstractStore (SymAddr "entrypoint") Nothing))
               //       So it overapproximates.
               uint256 ret = mm.get(addr);
               assert(ret == 4);
               return ret;
           }
         }
        |]
      let sig2 = Just (Sig "retFor(address)" [AbiAddressType])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig2 [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length paths) <> " paths"
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      assertBoolM "The expression is NOT partial" $ not (any isPartial paths)
      let numCexes = sum $ map (fromEnum . isCex) ret
      -- There are 2 CEX-es
      -- This is because with one CEX, the return DATA
      -- is empty, and in the other, the return data is non-empty (but symbolic)
      assertEqualM "number of counterexamples" 2 numCexes
    , test "overapproximates-unknown-addr" $ do
      Just c <- solcRuntime "C"
        [i|
         contract Target {
           function get() external view returns (uint256) {
               return 55;
           }
         }
         contract C {
           Target mm;
           function retFor(address addr) public returns (uint256) {
               Target target = Target(addr);
               uint256 ret = target.get();
               assert(ret == 4);
               return ret;
           }
         }
        |]
      let sig2 = Just (Sig "retFor(address)" [AbiAddressType])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig2 [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length paths) <> " paths"
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      let numCexes = sum $ map (fromEnum . isCex) ret
      assertBoolM "The expression is NOT partial" $ not (any isPartial paths)
      -- There are 2 CEX-es
      -- This is because with one CEX, the return DATA
      -- is empty, and in the other, the return data is non-empty (but symbolic)
      assertEqualM "number of counterexamples" 2 numCexes
    , test "overapproximates-fixed-zero-addr" $ do
      Just c <- solcRuntime "C"
        [i|
         contract Target {
           function get() external view returns (uint256) {
               return 55;
           }
         }
         contract C {
           Target mm;
           function retFor() public returns (uint256) {
               Target target = Target(address(0));
               uint256 ret = target.get();
               assert(ret == 4);
               return ret;
           }
         }
        |]
      let sig2 = Just (Sig "retFor()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig2 [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length paths) <> " paths"
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      let numCexes = sum $ map (fromEnum . isCex) ret
      assertBoolM "The expression is NOT partial" $ not (any isPartial paths)
      -- There are 2 CEX-es
      -- This is because with one CEX, the return DATA
      -- is empty, and in the other, the return data is non-empty (but symbolic)
      assertEqualM "number of counterexamples" 2 numCexes
    , test "overapproximates-fixed-wrong-addr" $ do
      Just c <- solcRuntime "C"
        [i|
         contract Target {
           function get() external view returns (uint256) {
               return 55;
           }
         }
         contract C {
           Target mm;
           function retFor() public returns (uint256) {
               Target target = Target(address(0xacab));
               uint256 ret = target.get();
               assert(ret == 4);
               return ret;
           }
         }
        |]
      let sig2 = Just (Sig "retFor()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig2 [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length paths) <> " paths"
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      assertBoolM "The expression is NOT partial" $ not (any isPartial paths)
      let numCexes = sum $ map (fromEnum . isCex) ret
      -- There are 2 CEX-es
      -- This is because with one CEX, the return DATA
      -- is empty, and in the other, the return data is non-empty (but symbolic)
      assertEqualM "number of counterexamples" 2 numCexes
    , test "staticcall-no-overapprox-2" $ do
      Just c <- solcRuntime "C"
        [i|
        contract Target {
            function add(uint256 x, uint256 y) external pure returns (uint256) {
              unchecked {
                return x + y;
              }
            }
        }
        contract C {
            function checkval(uint256 x, uint256 y) public {
                Target t = new Target();
                address realAddr = address(t);
                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = realAddr.staticcall(data);
                assert(success);
                assert(returnData.length == 32);

                // Decode the return value
                uint256 result = abi.decode(returnData, (uint256));

                // Assert that the result is equal to x + y
                unchecked {
                  assert(result == x + y);
                }
            }
        }
        |]
      let sig = Just (Sig "checkval(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      assertBoolM "The expression is NOT partial" $ not (any isPartial res)
      assertBoolM "The expression is NOT unknown" $ not $ any isUnknown ret
      assertBoolM "The expression is NOT error" $ not $ any isError ret
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of counterexamples" 0 numCexes
      assertEqualM "number of errors" 0 numErrs
    , test "staticcall-check-symbolic1" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval(address inputAddr, uint256 x, uint256 y) public {
                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = inputAddr.staticcall(data);
                assert(success);
            }
        }
        |]
      let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      -- There are 2 CEX-es, in contrast to the above (staticcall-check-orig2).
      -- This is because with one CEX, the return DATA
      -- is empty, and in the other, the return data is non-empty (but symbolic)
      assertEqualM "number of counterexamples" 2 numCexes
      assertEqualM "number of errors" 0 numErrs
    -- This checks that calling a symbolic address with staticcall will ALWAYS return 0/1
    -- which is the semantic of the EVM. We insert a  constraint over the return value
    -- even when overapproximation is used, as below.
    , test "staticcall-check-symbolic-yul" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval(address inputAddr, uint256 x, uint256 y) public {
            uint success;
            assembly {
              // Allocate memory for the call data
              let callData := mload(0x40)

              // Function signature for "add(uint256,uint256)" is "0x771602f7"
              mstore(callData, 0x771602f700000000000000000000000000000000000000000000000000000000)

              // Store the parameters x and y
              mstore(add(callData, 4), x)
              mstore(add(callData, 36), y)

              // Perform the static call
              success := staticcall(
                  gas(),          // Forward all available gas
                  inputAddr,      // Address to call
                  callData,       // Input data location
                  68,             // Input data size (4 bytes for function signature + 32 bytes each for x and y)
                  0,              // Output data location (0 means we don't care about the output)
                  0               // Output data size
              )
              }
              assert(success <= 1);
          }
        }
        |]
      let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of counterexamples" 0 numCexes -- no counterexamples, because it is always  0/1
      assertEqualM "number of errors" 0 numErrs
    , test "staticcall-check-symbolic2" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval(address inputAddr, uint256 x, uint256 y) public {
                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = inputAddr.staticcall(data);
                assert(success);

                uint result = abi.decode(returnData, (uint256));
                uint expected;
                unchecked {
                  expected = x + y;
                }
                assert(result == expected);
            }
        }
        |]
      let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of counterexamples" 2 numCexes
      assertEqualM "number of errors" 1 numErrs
    , testCase "call-symbolic-noreent" $ do
      let conf = testEnv.config {promiseNoReent = True}
      let myTestEnv :: Env = (testEnv :: Env) {config = conf :: Config}
      runEnv myTestEnv $ do
        Just c <- solcRuntime "C"
          [i|
          contract C {
              function checkval(address inputAddr, uint256 x, uint256 y) public {
                  bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                  (bool success, bytes memory returnData) = inputAddr.call(data);
                  assert(success);
              }
          }
          |]
        let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
        (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      -- There are 2 CEX-es
      -- This is because with one CEX, the return DATA
      -- is empty, and in the other, the return data is non-empty and success is false
        assertEqualM "number of errors" 0 numErrs
        assertEqualM "number of counterexamples" 2 numCexes
    , test "call-symbolic-reent" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval(address inputAddr, uint256 x, uint256 y) public {
                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = inputAddr.call(data);
                assert(success);
            }
        }
        |]
      let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      assertBoolM "The expression MUST be partial due to CALL to unknown code and no promise" (any isPartial paths)
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 0 numCexes
    , testCase "call-symbolic-noreent-maxbufsize16" $ do
      let conf = testEnv.config {promiseNoReent = True, maxBufSize = 4}
      let myTestEnv :: Env = (testEnv :: Env) {config = conf :: Config}
      runEnv myTestEnv $ do
        Just c <- solcRuntime "C"
          [i|
          contract C {
              function checkval(address inputAddr, uint256 x, uint256 y) public {
                  bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                  (bool success, bytes memory returnData) = inputAddr.call(data);
                  assert(returnData.length < 16);
              }
          }
          |]
        let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
        (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
        assertEqualM "number of errors" 0 numErrs
        assertEqualM "number of counterexamples" 0 numCexes
    , testCase "call-symbolic-noreent-maxbufsize16-fail" $ do
      let conf = testEnv.config {promiseNoReent = True, maxBufSize = 20}
      let myTestEnv :: Env = (testEnv :: Env) {config = conf :: Config}
      runEnv myTestEnv $ do
        Just c <- solcRuntime "C"
          [i|
          contract C {
              function checkval(address inputAddr, uint256 x, uint256 y) public {
                  bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                  (bool success, bytes memory returnData) = inputAddr.call(data);
                  assert(returnData.length < 16);
              }
          }
          |]
        let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
        (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        let numCexes = sum $ map (fromEnum . isCex) ret
        let numErrs = sum $ map (fromEnum . isError) ret
        assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
        assertEqualM "number of errors" 0 numErrs
        assertEqualM "number of counterexamples" 1 numCexes
    , test "call-balance-symb" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval(address inputAddr) public {
                uint256 balance = inputAddr.balance;
                assert(balance < 10);
            }
        }
        |]
      let sig = Just (Sig "checkval(address)" [AbiAddressType])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 1 numCexes
    , test "call-balance-symb2" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval() public {
                uint256 balance = address(0xacab).balance;
                assert(balance < 10);
            }
        }
        |]
      let sig = Just (Sig "checkval()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 1 numCexes
    , test "call-balance-concrete-pass" $ do
      Just c <- solcRuntime "C"
        [i|
        interface Vm {
          function deal(address,uint256) external;
        }
        contract Target {
        }
        contract C {
            function checkval() public {
                Target t = new Target();
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.deal(address(t), 5);
                uint256 balance = address(t).balance;
                assert(balance < 10);
            }
        }
        |]
      let sig = Just (Sig "checkval()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numErrs = sum $ map (fromEnum . isError) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
    , test "call-balance-concrete-fail" $ do
      Just c <- solcRuntime "C"
        [i|
        interface Vm {
          function deal(address,uint256) external;
        }
        contract Target {
        }
        contract C {
            function checkval() public {
                Target t = new Target();
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.deal(address(t), 5);
                uint256 balance = address(t).balance;
                assert(balance < 5);
            }
        }
        |]
      let sig = Just (Sig "checkval()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numErrs = sum $ map (fromEnum . isError) ret
      let numCexes = sum $ map (fromEnum . isCex) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 1 numCexes
    , test "call-extcodehash-symb1" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval(address inputAddr) public {
                bytes32 hash = inputAddr.codehash;
                assert(uint(hash) < 10);
            }
        }
        |]
      let sig = Just (Sig "checkval(address)" [AbiAddressType])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 1 numCexes
    , test "call-extcodehash-symb2" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function checkval() public {
                bytes32 hash = address(0xacab).codehash;
                assert(uint(hash) < 10);
            }
        }
        |]
      let sig = Just (Sig "checkval()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 1 numCexes
    , test "call-extcodehash-concrete-fail" $ do
      Just c <- solcRuntime "C"
        [i|
        contract Target {
        }
        contract C {
            function checkval() public {
                Target t = new Target();
                bytes32 hash = address(t).codehash;
                assert(uint(hash) == 8);
            }
        }
        |]
      let sig = Just (Sig "checkval()" [])
      (paths, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      let numErrs = sum $ map (fromEnum . isError) ret
      let numCexes = sum $ map (fromEnum . isCex) ret
      assertBoolM "The expression MUST NOT be partial" $ Prelude.not (any isPartial paths)
      assertEqualM "number of errors" 0 numErrs
      assertEqualM "number of counterexamples" 1 numCexes
    , test "jump-symbolic" $ do
      Just c <- solcRuntime "C"
        [i|
        // Target contract with a view function
        contract Target {
        }

        // Caller contract using staticcall
        contract C {
            function checkval(address inputAddr, uint256 x, uint256 y) public {
                Target t = new Target();
                address realAddr = address(t);

                bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                (bool success, bytes memory returnData) = inputAddr.staticcall(data);
                assert(success == true);
            }
        }
        |]
      let sig = Just (Sig "checkval(address,uint256,uint256)" [AbiAddressType, AbiUIntType 256, AbiUIntType 256])
      (res, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      let numCexes = sum $ map (fromEnum . isCex) ret
      let numErrs = sum $ map (fromEnum . isError) ret
      assertEqualM "number of counterexamples" numCexes 2
      assertEqualM "number of symbolic copy errors" numErrs 0
     ,
     test "opcode-mul-assoc" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 a, int256 b, int256 c) external pure {
              int256 tmp1;
              int256 out1;
              int256 tmp2;
              int256 out2;
              assembly {
                tmp1 := mul(a, b)
                out1 := mul(tmp1,c)
                tmp2 := mul(b, c)
                out2 := mul(a, tmp2)
              }
              assert (out1 == out2);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256,int256)" [AbiIntType 256, AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "MUL is associative"
     ,
     -- TODO look at tests here for SAR: https://github.com/dapphub/dapptools/blob/01ef8ea418c3fe49089a44d56013d8fcc34a1ec2/src/dapp-tests/pass/constantinople.sol#L250
     test "opcode-sar-neg" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
              require(shift_by >= 0);
              require(val <= 0);
              assembly {
                out := sar(shift_by,val)
              }
              assert (out <= 0);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-sar-pos" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
              require(shift_by >= 0);
              require(val >= 0);
              assembly {
                out := sar(shift_by,val)
              }
              assert (out >= 0);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-sar-fixedval-pos" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
              require(shift_by == 1);
              require(val == 64);
              assembly {
                out := sar(shift_by,val)
              }
              assert (out == 32);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-sar-fixedval-neg" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
                require(shift_by == 1);
                require(val == -64);
                assembly {
                  out := sar(shift_by,val)
                }
                assert (out == -32);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-div-zero-1" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := div(val, 0)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [])  <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "sdiv works as expected"
      ,
     test "opcode-sdiv-zero-1" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := sdiv(val, 0)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [])  <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "sdiv works as expected"
      ,
     test "opcode-sdiv-zero-2" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := sdiv(0, val)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [])  <- withCVC5Solver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "sdiv works as expected"
      ,
     test "signed-overflow-checks" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(int256 a) external returns (int256) {
                  return a + a;
              }
            }
            |]
        (_, [Cex (_, _)]) <- withDefaultSolver $ \s -> checkAssert s [0x11] c (Just (Sig "fun(int256)" [AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "expected cex discovered"
      ,
     test "opcode-signextend-neg" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(b <= 31);
                require(b >= 0);
                require(val < (1 <<(b*8)));
                require(val & (1 <<(b*8-1)) != 0); // MSbit set, i.e. negative
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                if (b == 31) assert(out == val);
                else assert(out > val);
                assert(out & (1<<254) != 0); // MSbit set, i.e. negative
              }
            }
            |]
        (_, [])  <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
      ,
     test "opcode-signextend-pos-nochop" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(val < (1 <<(b*8)));
                require(val & (1 <<(b*8-1)) == 0); // MSbit not set, i.e. positive
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                assert (out == val);
              }
            }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
      ,
      test "opcode-signextend-pos-chopped" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(b == 0); // 1-byte
                require(val == 514); // but we set higher bits
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                assert (out == 2); // chopped
              }
            }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
      ,
      -- when b is too large, value is unchanged
      test "opcode-signextend-pos-b-toolarge" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(b >= 31);
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                assert (out == val);
              }
            }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
     ,
     test "opcode-shl" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 shift_by, uint256 val) external pure {
              require(val < (1<<16));
              require(shift_by < 16);
              uint256 out;
              assembly {
                out := shl(shift_by,val)
              }
              assert (out >= val);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-xor-cancel" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure {
              require(a == b);
              uint256 c;
              assembly {
                c := xor(a,b)
              }
              assert (c == 0);
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "XOR works as expected"
      ,
      test "opcode-xor-reimplement" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure {
              uint256 c;
              assembly {
                c := xor(a,b)
              }
              assert (c == (~(a & b)) & (a | b));
              }
             }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "XOR works as expected"
      ,
      test "opcode-add-commutative" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure {
                uint256 res1;
                uint256 res2;
                assembly {
                  res1 := add(a,b)
                  res2 := add(b,a)
                }
                assert (res1 == res2);
              }
            }
            |]
        a <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        case a of
          (_, [Cex (_, ctr)]) -> do
            let x = getVar ctr "arg1"
            let y = getVar ctr "arg2"
            putStrLnM $ "y:" <> show y
            putStrLnM $ "x:" <> show x
            assertEqualM "Addition is not commutative... that's wrong" False True
          (_, []) -> do
            putStrLnM "adding is commutative"
          _ -> internalError "Unexpected"
      ,
      test "opcode-div-res-zero-on-div-by-zero" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint16 a) external pure {
                uint16 b = 0;
                uint16 res;
                assembly {
                  res := div(a,b)
                }
                assert (res == 0);
              }
            }
            |]
        (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint16)" [AbiUIntType 16])) [] defaultVeriOpts
        putStrLnM "DIV by zero is zero"
      ,
      -- Somewhat tautological since we are asserting the precondition
      -- on the same form as the actual "requires" clause.
      test "SafeAdd success case" $ do
        Just safeAdd <- solcRuntime "SafeAdd"
          [i|
          contract SafeAdd {
            function add(uint x, uint y) public pure returns (uint z) {
                 require((z = x + y) >= x);
            }
          }
          |]
        let pre preVM = let (x, y) = case getStaticAbiArgs 2 preVM of
                                       [x', y'] -> (x', y')
                                       _ -> internalError "expected 2 args"
                        in (x .<= Expr.add x y)
                        -- TODO check if it's needed
                           .&& preVM.state.callvalue .== Lit 0
            post prestate leaf =
              let (x, y) = case getStaticAbiArgs 2 prestate of
                             [x', y'] -> (x', y')
                             _ -> internalError "expected 2 args"
              in case leaf of
                   Success _ _ b _ -> (ReadWord (Lit 0) b) .== (Add x y)
                   _ -> PBool True
            sig = Just (Sig "add(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
        (res, []) <- withDefaultSolver $ \s ->
          verifyContract s safeAdd sig [] defaultVeriOpts (Just pre) post
        putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
     ,

      test "x == y => x + y == 2 * y" $ do
        Just safeAdd <- solcRuntime "SafeAdd"
          [i|
          contract SafeAdd {
            function add(uint x, uint y) public pure returns (uint z) {
                 require((z = x + y) >= x);
            }
          }
          |]
        let pre preVM = let (x, y) = case getStaticAbiArgs 2 preVM of
                                       [x', y'] -> (x', y')
                                       _ -> internalError "expected 2 args"
                        in (x .<= Expr.add x y)
                           .&& (x .== y)
                           .&& preVM.state.callvalue .== Lit 0
            post prestate leaf =
              let (_, y) = case getStaticAbiArgs 2 prestate of
                             [x', y'] -> (x', y')
                             _ -> internalError "expected 2 args"
              in case leaf of
                   Success _ _ b _ -> (ReadWord (Lit 0) b) .== (Mul (Lit 2) y)
                   _ -> PBool True
        (res, []) <- withDefaultSolver $ \s ->
          verifyContract s safeAdd (Just (Sig "add(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts (Just pre) post
        putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
      ,
      test "summary storage writes" $ do
        Just c <- solcRuntime "A"
          [i|
          contract A {
            uint x;
            function f(uint256 y) public {
               unchecked {
                 x += y;
                 x += y;
               }
            }
          }
          |]
        let pre vm = Lit 0 .== vm.state.callvalue
            post prestate leaf =
              let y = case getStaticAbiArgs 1 prestate of
                        [y'] -> y'
                        _ -> internalError "expected 1 arg"
                  this = prestate.state.codeContract
                  prestore = (fromJust (Map.lookup this prestate.env.contracts)).storage
                  prex = Expr.readStorage' (Lit 0) prestore
              in case leaf of
                Success _ _ _ postState -> let
                    poststore = (fromJust (Map.lookup this postState)).storage
                  in Expr.add prex (Expr.mul (Lit 2) y) .== (Expr.readStorage' (Lit 0) poststore)
                _ -> PBool True
            sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (res, []) <- withDefaultSolver $ \s ->
          verifyContract s c sig [] defaultVeriOpts (Just pre) post
        putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        -- tests how whiffValue handles Neg via application of the triple IsZero simplification rule
        -- regression test for: https://github.com/dapphub/dapptools/pull/698
        test "Neg" $ do
            let src =
                  [i|
                    object "Neg" {
                      code {
                        // Deploy the contract
                        datacopy(0, dataoffset("runtime"), datasize("runtime"))
                        return(0, datasize("runtime"))
                      }
                      object "runtime" {
                        code {
                          let v := calldataload(4)
                          if iszero(iszero(and(v, not(0xffffffffffffffffffffffffffffffffffffffff)))) {
                            invalid()
                          }
                        }
                      }
                    }
                    |]
            Right c <- liftIO $ yulRuntime "Neg" src
            (res, []) <- withSolvers Z3 4 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "hello(address)" [AbiAddressType])) [] defaultVeriOpts
            putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "catch-storage-collisions-noproblem" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public {
                 if (x != y) {
                   assembly {
                     let newx := sub(sload(x), 1)
                     let newy := add(sload(y), 1)
                     sstore(x,newx)
                     sstore(y,newy)
                   }
                 }
              }
            }
            |]
          let pre vm = (Lit 0) .== vm.state.callvalue
              post prestate poststate =
                let (x,y) = case getStaticAbiArgs 2 prestate of
                        [x',y'] -> (x',y')
                        _ -> error "expected 2 args"
                    this = prestate.state.codeContract
                    prestore = (fromJust (Map.lookup this prestate.env.contracts)).storage
                    prex = Expr.readStorage' x prestore
                    prey = Expr.readStorage' y prestore
                in case poststate of
                     Success _ _ _ postcs -> let
                           poststore = (fromJust (Map.lookup this postcs)).storage
                           postx = Expr.readStorage' x poststore
                           posty = Expr.readStorage' y poststore
                       in Expr.add prex prey .== Expr.add postx posty
                     _ -> PBool True
              sig = Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
          (_, []) <- withDefaultSolver $ \s ->
            verifyContract s c sig [] defaultVeriOpts (Just pre) post
          putStrLnM "Correct, this can never fail"
        ,
        -- Inspired by these `msg.sender == to` token bugs
        -- which break linearity of totalSupply.
        test "catch-storage-collisions-good" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public {
                 assembly {
                   let newx := sub(sload(x), 1)
                   let newy := add(sload(y), 1)
                   sstore(x,newx)
                   sstore(y,newy)
                 }
              }
            }
            |]
          let pre vm = (Lit 0) .== vm.state.callvalue
              post prestate leaf =
                let (x,y) = case getStaticAbiArgs 2 prestate of
                        [x',y'] -> (x',y')
                        _ -> error "expected 2 args"
                    this = prestate.state.codeContract
                    prestore = (fromJust (Map.lookup this prestate.env.contracts)).storage
                    prex = Expr.readStorage' x prestore
                    prey = Expr.readStorage' y prestore
                in case leaf of
                     Success _ _ _ poststate -> let
                           poststore = (fromJust (Map.lookup this poststate)).storage
                           postx = Expr.readStorage' x poststore
                           posty = Expr.readStorage' y poststore
                       in Expr.add prex prey .== Expr.add postx posty
                     _ -> PBool True
              sig = Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
          (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s ->
            verifyContract s c sig [] defaultVeriOpts (Just pre) post
          let x = getVar ctr "arg1"
          let y = getVar ctr "arg2"
          putStrLnM $ "y:" <> show y
          putStrLnM $ "x:" <> show x
          assertEqualM "Catch storage collisions" x y
          putStrLnM "expected counterexample found"
        ,
        test "simple-assert" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo() external pure {
                assert(false);
              }
             }
            |]
          (_, [Cex (Failure _ _ (Revert msg), _)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo()" [])) [] defaultVeriOpts
          assertEqualM "incorrect revert msg" msg (ConcreteBuf $ panicMsg 0x01)
        ,
        test "simple-assert-2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                assert(x != 10);
              }
             }
            |]
          (_, [(Cex (_, ctr))]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertEqualM "Must be 10" 10 $ getVar ctr "arg1"
          putStrLnM "Got 10 Cex, as expected"
        ,
        test "assert-fail-equal" $ do
          Just c <- solcRuntime "AssertFailEqual"
            [i|
            contract AssertFailEqual {
              function fun(uint256 deposit_count) external pure {
                assert(deposit_count == 0);
                assert(deposit_count == 11);
              }
             }
            |]
          (_, [Cex (_, a), Cex (_, b)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let ints = map (flip getVar "arg1") [a,b]
          assertBoolM "0 must be one of the Cex-es" $ isJust $ List.elemIndex 0 ints
          putStrLnM "expected 2 counterexamples found, one Cex is the 0 value"
        ,
        test "assert-fail-notequal" $ do
          Just c <- solcRuntime "AssertFailNotEqual"
            [i|
            contract AssertFailNotEqual {
              function fun(uint256 deposit_count) external pure {
                assert(deposit_count != 0);
                assert(deposit_count != 11);
              }
             }
            |]
          (_, [Cex (_, a), Cex (_, b)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let x = getVar a "arg1"
          let y = getVar b "arg1"
          assertBoolM "At least one has to be 0, to go through the first assert" (x == 0 || y == 0)
          putStrLnM "expected 2 counterexamples found."
        ,
        test "assert-fail-twoargs" $ do
          Just c <- solcRuntime "AssertFailTwoParams"
            [i|
            contract AssertFailTwoParams {
              function fun(uint256 deposit_count1, uint256 deposit_count2) external pure {
                assert(deposit_count1 != 0);
                assert(deposit_count2 != 11);
              }
             }
            |]
          (_, [Cex _, Cex _]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "expected 2 counterexamples found"
        ,
        test "assert-2nd-arg" $ do
          Just c <- solcRuntime "AssertFailTwoParams"
            [i|
            contract AssertFailTwoParams {
              function fun(uint256 deposit_count1, uint256 deposit_count2) external pure {
                assert(deposit_count2 != 666);
              }
             }
            |]
          (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          assertEqualM "Must be 666" 666 $ getVar ctr "arg2"
          putStrLnM "Found arg2 Ctx to be 666"
        ,
        -- LSB is zeroed out, byte(31,x) takes LSB, so y==0 always holds
        test "check-lsb-msb1" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00;
                uint8 y;
                assembly { y := byte(31,x) }
                assert(y == 0);
              }
            }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        -- We zero out everything but the LSB byte. However, byte(31,x) takes the LSB byte
        -- so there is a counterexamle, where LSB of x is not zero
        test "check-lsb-msb2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0x00000000000000000000000000000000000000000000000000000000000000ff;
                uint8 y;
                assembly { y := byte(31,x) }
                assert(y == 0);
              }
            }
            |]
          (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertBoolM "last byte must be non-zero" $ ((Data.Bits..&.) (getVar ctr "arg1") 0xff) > 0
          putStrLnM "Expected counterexample found"
        ,
        -- We zero out everything but the 2nd LSB byte. However, byte(31,x) takes the 2nd LSB byte
        -- so there is a counterexamle, where 2nd LSB of x is not zero
        test "check-lsb-msb3 -- 2nd byte" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0x000000000000000000000000000000000000000000000000000000000000ff00;
                uint8 y;
                assembly { y := byte(30,x) }
                assert(y == 0);
              }
            }
            |]
          (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertBoolM "second to last byte must be non-zero" $ ((Data.Bits..&.) (getVar ctr "arg1") 0xff00) > 0
          putStrLnM "Expected counterexample found"
        ,
        -- Reverse of test above
        test "check-lsb-msb4 2nd byte rev" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff;
                uint8 y;
                assembly {
                    y := byte(30,x)
                }
                assert(y == 0);
              }
            }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        -- Bitwise OR operation test
        test "opcode-bitwise-or-full-1s" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                uint256 y;
                uint256 z = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
                assembly { y := or(x, z) }
                assert(y == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
              }
            }
            |]
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "When OR-ing with full 1's we should get back full 1's"
        ,
        -- Bitwise OR operation test
        test "opcode-bitwise-or-byte-of-1s" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                uint256 y;
                uint256 z = 0x000000000000000000000000000000000000000000000000000000000000ff00;
                assembly { y := or(x, z) }
                assert((y & 0x000000000000000000000000000000000000000000000000000000000000ff00) ==
                  0x000000000000000000000000000000000000000000000000000000000000ff00);
              }
            }
            |]
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "When OR-ing with a byte of 1's, we should get 1's back there"
        ,
        test "Deposit contract loop (z3)" $ do
          Just c <- solcRuntime "Deposit"
            [i|
            contract Deposit {
              function deposit(uint256 deposit_count) external pure {
                require(deposit_count < 2**32 - 1);
                ++deposit_count;
                bool found = false;
                for (uint height = 0; height < 32; height++) {
                  if ((deposit_count & 1) == 1) {
                    found = true;
                    break;
                  }
                 deposit_count = deposit_count >> 1;
                 }
                assert(found);
              }
             }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "deposit(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "Deposit-contract-loop-error-version" $ do
          Just c <- solcRuntime "Deposit"
            [i|
            contract Deposit {
              function deposit(uint8 deposit_count) external pure {
                require(deposit_count < 2**32 - 1);
                ++deposit_count;
                bool found = false;
                for (uint height = 0; height < 32; height++) {
                  if ((deposit_count & 1) == 1) {
                    found = true;
                    break;
                  }
                 deposit_count = deposit_count >> 1;
                 }
                assert(found);
              }
             }
            |]
          (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s allPanicCodes c (Just (Sig "deposit(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
          assertEqualM "Must be 255" 255 $ getVar ctr "arg1"
          putStrLnM  $ "expected counterexample found, and it's correct: " <> (show $ getVar ctr "arg1")
        ,
        test "explore function dispatch" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x) public pure returns (uint) {
                return x;
              }
            }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "check-asm-byte-in-bounds" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 idx, uint256 val) external pure {
                uint256 actual;
                uint256 expected;
                require(idx < 32);
                assembly {
                  actual := byte(idx,val)
                  expected := shr(248, shl(mul(idx, 8), val))
                }
                assert(actual == expected);
              }
            }
            |]
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM "in bounds byte reads return the expected value"
        ,
        test "check-div-mod-sdiv-smod-by-zero-constant-prop" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 e) external pure {
                uint x = 0;
                uint y = 55;
                uint z;
                assembly { z := div(y,x) }
                assert(z == 0);
                assembly { z := div(x,y) }
                assert(z == 0);
                assembly { z := sdiv(y,x) }
                assert(z == 0);
                assembly { z := sdiv(x,y) }
                assert(z == 0);
                assembly { z := mod(y,x) }
                assert(z == 0);
                assembly { z := mod(x,y) }
                assert(z == 0);
                assembly { z := smod(y,x) }
                assert(z == 0);
                assembly { z := smod(x,y) }
                assert(z == 0);
              }
            }
            |]
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "div/mod/sdiv/smod by zero works as expected during constant propagation"
        ,
        test "check-asm-byte-oob" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x, uint256 y) external pure {
                uint256 z;
                require(x >= 32);
                assembly { z := byte(x,y) }
                assert(z == 0);
              }
            }
            |]
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM "oob byte reads always return 0"
        ,
        test "injectivity of keccak (diff sizes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint128 x, uint256 y) external pure {
                assert(
                    keccak256(abi.encodePacked(x)) !=
                    keccak256(abi.encodePacked(y))
                );
              }
            }
            |]
          Right _ <- reachableUserAsserts c (Just $ Sig "f(uint128,uint256)" [AbiUIntType 128, AbiUIntType 256])
          pure ()
        ,
        test "injectivity of keccak (32 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public pure {
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))) assert(x == y);
              }
            }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "injectivity of keccak contrapositive (32 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public pure {
                require (x != y);
                assert (keccak256(abi.encodePacked(x)) != keccak256(abi.encodePacked(y)));
              }
            }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "injectivity of keccak (64 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y, uint w, uint z) public pure {
                assert (keccak256(abi.encodePacked(x,y)) != keccak256(abi.encodePacked(w,z)));
              }
            }
            |]
          (_, [Cex (_, ctr)]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256,uint256,uint256)" (replicate 4 (AbiUIntType 256)))) [] defaultVeriOpts
          let x = getVar ctr "arg1"
          let y = getVar ctr "arg2"
          let w = getVar ctr "arg3"
          let z = getVar ctr "arg4"
          assertEqualM "x==y for hash collision" x y
          assertEqualM "w==z for hash collision" w z
          putStrLnM "expected counterexample found"
        ,
        test "calldata beyond calldatasize is 0 (symbolic calldata)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f() public pure {
                uint y;
                assembly {
                  let x := calldatasize()
                  y := calldataload(x)
                }
                assert(y == 0);
              }
            }
            |]
          (res, []) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "calldata beyond calldatasize is 0 (concrete dalldata prefix)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint256 z) public pure {
                uint y;
                assembly {
                  let x := calldatasize()
                  y := calldataload(x)
                }
                assert(y == 0);
              }
            }
            |]
          (res, []) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "calldata symbolic access" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint256 z) public pure {
                uint x; uint y;
                assembly {
                  y := calldatasize()
                }
                require(z >= y);
                require(z < 2**64); // Accesses to larger indices are not supported
                assembly {
                  x := calldataload(z)
                }
                assert(x == 0);
              }
            }
            |]
          (res, []) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "multiple-contracts" $ do
          let code =
                [i|
                  contract C {
                    uint x;
                    A constant a = A(0x35D1b3F3D7966A1DFe207aa4514C12a259A0492B);

                    function call_A() public view {
                      // should fail since x can be anything
                      assert(a.x() == x);
                    }
                  }
                  contract A {
                    uint public x;
                  }
                |]
              aAddr = LitAddr (Addr 0x35D1b3F3D7966A1DFe207aa4514C12a259A0492B)
              cAddr = SymAddr "entrypoint"
          Just c <- solcRuntime "C" code
          Just a <- solcRuntime "A" code
          (_, [Cex (_, cex)]) <- withDefaultSolver $ \s -> do
            calldata <- mkCalldata (Just (Sig "call_A()" [])) []
            vm <- liftIO $ stToIO $ abstractVM calldata c Nothing False
                    <&> set (#state % #callvalue) (Lit 0)
                    <&> over (#env % #contracts)
                       (Map.insert aAddr (initialContract (RuntimeCode (ConcreteRuntimeCode a))))
            verify s (Fetch.noRpcFetcher s) defaultVeriOpts vm (checkAssertions defaultPanicCodes) Nothing

          let storeCex = cex.store
              testCex = case (Map.lookup cAddr storeCex, Map.lookup aAddr storeCex) of
                          (Just sC, Just sA) -> case (Map.lookup 0 sC, Map.lookup 0 sA) of
                              (Just x, Just y) -> x /= y
                              (Just x, Nothing) -> x /= 0
                              _ -> False
                          _ -> False
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "expected counterexample found"
        , test "calling-unique-contracts--read-from-storage" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                uint x;
                A a;

                function call_A() public {
                  a = new A();
                  // should fail since x can be anything
                  assert(a.x() == x);
                }
              }
              contract A {
                uint public x;
              }
            |]
          (_, [Cex _]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "call_A()" [])) [] defaultVeriOpts
          putStrLnM "expected counterexample found"
        ,
        test "keccak-concrete-and-sym-agree" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function kecc(uint x) public pure {
                  if (x == 0) {
                    assert(keccak256(abi.encode(x)) == keccak256(abi.encode(0)));
                  }
                }
              }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "kecc(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "keccak-concrete-and-sym-agree-nonzero" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function kecc(uint x) public pure {
                  if (x == 55) {
                    // Note: 3014... is the encode & keccak & uint256 conversion of 55
                    assert(uint256(keccak256(abi.encode(x))) == 30148980456718914367279254941528755963179627010946392082519497346671089299886);
                  }
                }
              }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "kecc(uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "keccak concrete and sym injectivity" $ do
          Just c <- solcRuntime "A"
            [i|
              contract A {
                function f(uint x) public pure {
                  if (x !=3) assert(keccak256(abi.encode(x)) != keccak256(abi.encode(3)));
                }
              }
            |]
          (res, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (length res) <> " paths"
        ,
        test "safemath-distributivity-yul" $ do
          let yulsafeDistributivity = hex "6355a79a6260003560e01c14156016576015601f565b5b60006000fd60a1565b603d602d604435600435607c565b6039602435600435607c565b605d565b6052604b604435602435605d565b600435607c565b141515605a57fe5b5b565b6000828201821115151560705760006000fd5b82820190505b92915050565b6000818384048302146000841417151560955760006000fd5b82820290505b92915050565b"
          calldata <- mkCalldata (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) []
          vm <- liftIO $ stToIO $ abstractVM calldata yulsafeDistributivity Nothing False
          (_, []) <-  withDefaultSolver $ \s -> verify s (Fetch.noRpcFetcher s) defaultVeriOpts vm (checkAssertions defaultPanicCodes) Nothing
          putStrLnM "Proven"
        ,
        test "safemath-distributivity-sol" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function distributivity(uint x, uint y, uint z) public {
                  assert(mul(x, add(y, z)) == add(mul(x, y), mul(x, z)));
                }

                function add(uint x, uint y) internal pure returns (uint z) {
                  unchecked {
                    require((z = x + y) >= x, "ds-math-add-overflow");
                    }
                }

                function mul(uint x, uint y) internal pure returns (uint z) {
                  unchecked {
                    require(y == 0 || (z = x * y) / y == x, "ds-math-mul-overflow");
                  }
                }
              }
            |]

          (_, []) <- withSolvers Bitwuzla 1 1 (Just 99999999) $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "Proven"
        ,
        test "storage-cex-1" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint x;
              uint y;
              function fun(uint256 a) external{
                require(x != 0);
                require(y != 0);
                assert (x == y);
              }
            }
            |]
          (_, [(Cex (_, cex))]) <- withDefaultSolver $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let addr = SymAddr "entrypoint"
              testCex = Map.size cex.store == 1 &&
                        case Map.lookup addr cex.store of
                          Just s -> Map.size s == 2 &&
                                    case (Map.lookup 0 s, Map.lookup 1 s) of
                                      (Just x, Just y) -> x /= y
                                      _ -> False
                          _ -> False
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "Expected counterexample found"
        ,
        test "storage-cex-2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint[10] arr1;
              uint[10] arr2;
              function fun(uint256 a) external{
                assert (arr1[0] < arr2[a]);
              }
            }
            |]
          (_, [(Cex (_, cex))]) <- withDefaultSolver $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let addr = SymAddr "entrypoint"
              a = getVar cex "arg1"
              testCex = Map.size cex.store == 1 &&
                        case Map.lookup addr cex.store of
                          Just s -> case (Map.lookup 0 s, Map.lookup (10 + a) s) of
                                      (Just x, Just y) -> x >= y
                                      _ -> False
                          Nothing -> False -- arr2 must contain an element, or it'll be 0
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "Expected counterexample found"
        ,
        test "storage-cex-concrete" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint x;
              uint y;
              function fun(uint256 a) external{
                require (x != 0);
                require (y != 0);
                assert (x != y);
              }
            }
            |]
          let sig = Just (Sig "fun(uint256)" [AbiUIntType 256])
          (_, [Cex (_, cex)]) <- withDefaultSolver $
            \s -> verifyContract s c sig [] defaultVeriOpts Nothing (checkAssertions [0x01])
          let addr = SymAddr "entrypoint"
              testCex = Map.size cex.store == 1 &&
                        case Map.lookup addr cex.store of
                          Just s -> Map.size s == 2 &&
                                    case (Map.lookup 0 s, Map.lookup 1 s) of
                                      (Just x, Just y) -> x == y
                                      _ -> False
                          _ -> False
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "Expected counterexample found"
        , test "temp-store-check" $ do
          Just c <- solcRuntime "C"
            [i|
            pragma solidity ^0.8.25;
            contract C {
                mapping(address => bool) sentGifts;
                function stuff(address k) public {
                    require(sentGifts[k] == false);
                    assembly {
                        if tload(0) { revert(0, 0) }
                        tstore(0, 1)
                    }
                    sentGifts[k] = true;
                    assembly {
                        tstore(0, 0)
                    }
                    assert(sentGifts[k]);
                }
            }
            |]
          let sig = (Just (Sig "stuff(address)" [AbiAddressType]))
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
          putStrLnM $ "Basic tstore check passed"
  ]
  , testGroup "simple-checks"
    [ test "simple-stores" $ do
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
      (_, [Cex (_, ctr)]) <- withCVC5Solver $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexample found.  ctr: " <> (show ctr)
    , test "simple-fixed-value" $ do
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
      (_, [Cex (_, ctr)]) <- withCVC5Solver $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexample found.  ctr: " <> (show ctr)
    , test "simple-fixed-value2" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function func(uint a, uint b) public {
            assert(!((a == 1337) && (b == 99)));
          }
        }
        |]
      let sig = (Sig "func(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, [Cex (_, ctr)]) <- withCVC5Solver $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexample found.  ctr: " <> (show ctr)
    , test "simple-fixed-value3" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function func(uint a, uint b) public {
            assert(((a != 1337) && (b != 99)));
          }
        }
        |]
      let sig = (Sig "func(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, [Cex (_, ctr1), Cex (_, ctr2)]) <- withSolvers Bitwuzla 1 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexamples found.  ctr1: " <> (show ctr1) <> " ctr2: " <> (show ctr2)
    , test "simple-fixed-value-store1" $ do
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
      (_, [Cex _]) <- withCVC5Solver $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  "expected counterexamples found"
    , test "simple-fixed-value-store2" $ do
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
      (_, [Cex (_, ctr1)]) <- withCVC5Solver $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexamples found: " <> show ctr1
  ]
  , testGroup "prop-and-expr-properties"
  [
    test "nubOrd-Prop-PLT" $ do
        let a = [ PLT (Lit 0x0) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))
                , PLT (Lit 0x1) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))
                , PLT (Lit 0x2) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))
                , PLT (Lit 0x0) (ReadWord (ReadWord (Lit 0x0) (AbstractBuf "txdata")) (AbstractBuf "txdata"))]
        let simp = nubOrd a
            simp2 = List.nub a
        assertEqualM "Must be 3-length" 3 (length simp)
        assertEqualM "Must be 3-length" 3 (length simp2)
    , test "nubOrd-Prop-PEq" $ do
        let a = [ PEq (Lit 0x0) (ReadWord (Lit 0x0) (AbstractBuf "txdata"))
                , PEq (Lit 0x0) (ReadWord (Lit 0x1) (AbstractBuf "txdata"))
                , PEq (Lit 0x0) (ReadWord (Lit 0x2) (AbstractBuf "txdata"))
                , PEq (Lit 0x0) (ReadWord (Lit 0x0) (AbstractBuf "txdata"))]
        let simp = nubOrd a
            simp2 = List.nub a
        assertEqualM "Must be 3-length" 3 (length simp)
        assertEqualM "Must be 3-length" 3 (length simp2)
    -- we run these without the simplifier inside `checkSatWithProps`, so
    -- we can test the SMT solver's ability to handle sign extension
    , test "sign-extend-conc-1" $ do
      let p = Expr.sex (Lit 0) (Lit 0xff)
      assertEqualM "stuff" p (Expr.simplify (Sub (Lit 0) (Lit 1)))
      let p2 = Expr.sex (Lit 30) (Lit 0xff)
      assertEqualM "stuff" p2 (Lit 0xff)
      let p3 = Expr.sex (Lit 1) (Lit 0xff)
      assertEqualM "stuff" p3 (Lit 0xff)
      let p4 = Expr.sex (Lit 0) (Lit 0x1)
      assertEqualM "stuff" p4 (Lit 0x1)
      let p5 = Expr.sex (Lit 0) (Lit 0x0)
      assertEqualM "stuff" p5 (Lit 0x0)
    , testNoSimplify "sign-extend-1" $ do
        let p = (PEq (Lit 1) (SLT (Lit 1774544) (SEx (Lit 2) (Lit 1774567))))
        let simp = Expr.simplifyProps [p]
        assertEqualM "Must simplify to PBool True" simp []
        withDefaultSolver $ \s -> do
          res <- checkSatWithProps s [p]
          _ <- case res of
            Cex c -> pure c
            _ -> liftIO $ assertFailure "Must be satisfiable!"
          pure ()
    , testNoSimplify "sign-extend-2" $ do
      let p = (PEq (Lit 1) (SLT (SEx (Lit 2) (Var "arg1")) (Lit 0)))
      withDefaultSolver $ \s -> do
        res <- checkSatWithProps s [p]
        _ <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        pure()
    , testNoSimplify "sign-extend-3" $ do
      let p = PAnd
                (PEq (Lit 1) (SLT (SEx (Lit 2) (Var "arg1")) (Lit 115792089237316195423570985008687907853269984665640564039457584007913128752664)))
                (PEq (Var "arg1") (SEx (Lit 2) (Var "arg1")))
      withDefaultSolver $ \s -> do
        res <- checkSatWithProps s [p]
        _ <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        pure()
    , testProperty "sign-extend-vs-smt" $ \(a :: W256, b :: W256) -> propNoSimp $ do
        let p = (PEq (Var "arg1") (SEx (Lit (a `mod` 50)) (Lit b)))
        withDefaultSolver $ \s -> do
          res <- checkSatWithProps s [p]
          cex <- case res of
            Cex c -> pure c
            _ -> liftIO $ assertFailure "Must be satisfiable!"
          let res1 = fromRight (internalError "cannot be") $ subModel cex (Var "arg1")
          res1W <- case res1 of
            Lit x -> pure x
            _ -> internalError "Expected Lit"
          let res2 = Expr.simplifyProps [p]
          res2W <- case res2 of
            [PEq (Lit x) (Var "arg1")] -> pure x
            _ -> internalError "Expected PEq"
          assertEqualM "Must be equivalent concrete values" res1W res2W
  ]
  , testGroup "simplification-working"
  [
    test "PEq-and-PNot-PEq-1" $ do
      let a = [PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1"))]
      assertEqualM "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
    , test "PEq-and-PNot-PEq-2" $ do
      let a = [PEq (Var "arg1") (Lit 0x539),PNeg (PEq (Lit 0x539) (Var "arg1"))]
      assertEqualM "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
    , test "PEq-and-PNot-PEq-3" $ do
      let a = [PEq (Var "arg1") (Lit 0x539),PNeg (PEq (Var "arg1") (Lit 0x539))]
      assertEqualM "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
    , test "prop-simp-bool1" $ do
      let
        a = successGen [PAnd (PBool True) (PBool False)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen [PBool False]) b
    , test "prop-simp-bool2" $ do
      let
        a = successGen [POr (PBool True) (PBool False)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "prop-simp-LT" $ do
      let
        a = successGen [PLT (Lit 1) (Lit 2)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "prop-simp-GEq" $ do
      let
        a = successGen [PGEq (Lit 1) (Lit 2)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen [PBool False]) b
    , test "prop-simp-liteq-false" $ do
      let
        a = [PEq (LitByte 10) (LitByte 12)]
        b = Expr.simplifyProps a
      assertEqualM "Must simplify to PBool" ([PBool False]) b
    , test "prop-simp-concbuf-false" $ do
      let
        a = [PEq (ConcreteBuf "a") (ConcreteBuf "ab")]
        b = Expr.simplifyProps a
      assertEqualM "Must simplify to PBool" ([PBool False]) b
    , test "prop-simp-sort-eq-arguments" $ do
      let
        a = [PEq (Var "a") (Var "b"), PEq (Var "b") (Var "a")]
        b = Expr.simplifyProps a
      assertEqualM "Must reorder and nubOrd" (length b) 1
    , test "expr-simp-and-commut-assoc" $ do
      let
        a = And (Lit 4) (And (Lit 5) (Var "a"))
        b = Expr.simplify a
      assertEqualM "Must reorder and perform And" (And (Lit 4) (Var "a")) b
    , test "expr-simp-order-eqbyte" $ do
      let
        a = EqByte (ReadByte (Lit 1) (AbstractBuf "b")) (ReadByte (Lit 1) (AbstractBuf "a"))
        b = Expr.simplify a
      assertEqualM "Must order eqbyte params" b (EqByte (ReadByte (Lit 1) (AbstractBuf "a")) (ReadByte (Lit 1) (AbstractBuf "b")))
    , test "prop-simp-demorgan-pneg-pand" $ do
      let
        a = [PNeg (PAnd (PEq (Lit 4) (Var "a")) (PEq (Lit 5) (Var "b")))]
        b = Expr.simplifyProps a
      assertEqualM "Must apply demorgan" b [POr (PNeg (PEq (Lit 4) (Var "a"))) (PNeg (PEq (Lit 5) (Var "b")))]
    , test "prop-simp-demorgan-pneg-por" $ do
      let
        a = [PNeg (POr (PEq (Lit 4) (Var "a")) (PEq (Lit 5) (Var "b")))]
        b = Expr.simplifyProps a
      assertEqualM "Must apply demorgan" [PNeg (PEq (Lit 4) (Var "a")), PNeg (PEq (Lit 5) (Var "b"))] b
    , test "prop-simp-lit0-or-both-0" $ do
      let
        a = [PEq (Lit 0) (Or (Var "a") (Var "b"))]
        b = Expr.simplifyProps a
      assertEqualM "Must apply demorgan" [PEq (Lit 0) (Var "a"), PEq (Lit 0) (Var "b")] b
    , test "prop-simp-multiple" $ do
      let
        a = successGen [PBool False, PBool True]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen [PBool False]) b
    , test "prop-simp-expr" $ do
      let
        a = successGen [PEq (Add (Lit 1) (Lit 2)) (Sub (Lit 4) (Lit 1))]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "prop-simp-impl" $ do
      let
        a = successGen [PImpl (PBool False) (PEq (Var "abc") (Var "bcd"))]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "propSimp-no-duplicate1" $ do
      let a = [PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)), PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x63) (Var "arg2"),PEq (Lit 0x539) (Var "arg1"),PEq TxValue (Lit 0x0),PEq (IsZero (Eq (Lit 0x63) (Var "arg2"))) (Lit 0x0)]
      let simp = Expr.simplifyProps a
      assertEqualM "must not duplicate" simp (nubOrd simp)
      assertEqualM "We must be able to remove all duplicates" (length $ nubOrd simp) (length $ List.nub simp)
    , test "propSimp-no-duplicate2" $ do
      let a = [PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1")),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0)),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqualM "must not duplicate" simp (nubOrd simp)
      assertEqualM "must not duplicate" (length simp) (length $ List.nub simp)
    , test "full-order-prop1" $ do
      let a = [PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1")),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0)),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqualM "We must be able to remove all duplicates" (length $ nubOrd simp) (length $ List.nub simp)
    , test "full-order-prop2" $ do
      let a =[PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x63) (Var "arg2"),PEq (Lit 0x539) (Var "arg1"),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x63) (Var "arg2"))) (Lit 0x0),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqualM "must not duplicate" simp (nubOrd simp)
      assertEqualM "We must be able to remove all duplicates" (length $ nubOrd simp) (length $ List.nub simp)
  ]
  , testGroup "calling-solvers"
  [ test "no-error-on-large-buf" $ do
      -- These two tests generates a very large buffer that previously would cause an internalError when
      -- printed via "formatCex". We should be able to print it now.
      Just c <- solcRuntime "MyContract" [i|
          contract MyContract {
            function fun(bytes calldata a) external pure {
              if (a.length > 0x800000000000) {
                assert(false);
              }
            }
           } |]
      (_, [Cex cex]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      putStrLnM $ "Cex found:" <> T.unpack (formatCex (AbstractBuf "txdata") Nothing (snd cex))
    , test "no-error-on-large-buf-pure-print" $ do
      let bufs = Map.singleton (AbstractBuf "txdata")
                  (EVM.Types.Comp Write {byte = 1, idx = 0x27, next = Base {byte = 0x66, length = 0xffff000000000000000}})
      let mycex = SMTCex {vars = mempty
                         , addrs = mempty
                         , buffers = bufs
                         , store = mempty
                         , blockContext = mempty
                         , txContext = Map.fromList [(TxValue,0x0)]}
      putStrLnM $ "Cex found:" <> T.unpack (formatCex (AbstractBuf "txdata") Nothing mycex)
    , test "correct-model-for-empty-buffer" $ do
      withDefaultSolver $ \s -> do
        let props = [(PEq (BufLength (AbstractBuf "b")) (Lit 0x0))]
        res <- checkSatWithProps s props
        (cex) <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        let value = fromRight (error "cannot be") $ subModel cex (AbstractBuf "b")
        assertEqualM "Buffer must be empty" (ConcreteBuf "") value
    , test "correct-model-for-non-empty-buffer-of-all-zeroes" $ do
      withDefaultSolver $ \s -> do
        let props = [(PAnd (PEq (ReadByte (Lit 0x0) (AbstractBuf "b")) (LitByte 0x0)) (PEq (BufLength (AbstractBuf "b")) (Lit 0x1)))]
        res <- checkSatWithProps s props
        (cex) <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        let value = fromRight (error "cannot be") $ subModel cex (AbstractBuf "b")
        assertEqualM "Buffer must have size 1 and contain zero byte" (ConcreteBuf "\0") value
    , test "buffer-shrinking-does-not-loop" $ do
      withDefaultSolver $ \s -> do
        let props = [(PGT (BufLength (AbstractBuf "b")) (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb4))]
        res <- checkSatWithProps s props
        let
          sat = case res of
            Cex _ -> True
            _ -> False
        assertBoolM "Must be satisfiable!" sat
    , test "can-get-value-unrelated-to-large-buffer" $ do
      withDefaultSolver $ \s -> do
        let props = [(PEq (Var "a") (Lit 0x1)), (PGT (BufLength (AbstractBuf "b")) (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb4))]
        res <- checkSatWithProps s props
        cex :: SMTCex <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        let value = subModel cex (Var "a")
        assertEqualM "Can get value out of model in the presence of large buffer!" value (Right $ Lit 0x1)
    , test "no-duplicates-with-concrete-keccak" $ do
      let props = [(PGT (Var "a") (Keccak (ConcreteBuf "abcdef"))), (PGT (Var "b") (Keccak (ConcreteBuf "abcdef")))]
      conf <- readConfig
      let SMT2 script _ _ = fromRight (internalError "Must succeed") (assertProps conf props)
      assertBoolM "There were duplicate commands in SMT encoding" $ not (hasDuplicateCommands script)
    , test "no-duplicates-with-read-assumptions" $ do
      let props = [(PGT (ReadWord (Lit 2) (AbstractBuf "test")) (Lit 0)), (PGT (Expr.padByte $ ReadByte (Lit 10) (AbstractBuf "test")) (Expr.padByte $ LitByte 1))]
      conf <- readConfig
      let SMT2 script _ _ = fromRight (internalError "Must succeed") (assertProps conf props)
      assertBoolM "There were duplicate lines in SMT encoding" $ not (hasDuplicateCommands script)
     , test "all-concrete-keccaks-discovered" $ do
      let buf1 = (Keccak (ConcreteBuf "abc"))
          eq = (Eq buf1 (Lit 0x12))
          buf2 = WriteWord eq (Lit 0x0) mempty
          props = [PEq (Keccak buf2) (Lit 0x123)]
          concrete = concreteKeccaks props
      assertEqualM "Must find two keccaks" 2 (length concrete)
    , testCase "store-over-concrete-buffer" $ runEnv (testEnv {config = testEnv.config {simp = False}}) $ do
      let
        as = AbstractStore (SymAddr "test") Nothing
        cs = ConcreteStore $ Map.fromList [(0x1,0x2)]
        e1 = SLoad (Lit 0x1) (SStore (Lit 0x8) (SLoad (Lit 0x40) as) cs)
        eq = PEq e1 (Lit 0x0)
      conf <- readConfig
      let SMT2 _ (CexVars _ _ _ storeReads _ _) _ = fromRight (internalError "Must succeed") (assertProps conf [eq])
      let expected = StorageReads $ Map.singleton (SymAddr "test", Nothing) (Set.singleton (Lit 0x40))
      assertEqualM "Reads must be properly collected" storeReads expected
    , test "all-abstract-reads-detected" $ do
      let mystore = (AbstractStore (SymAddr "test") Nothing)
      let props = [PGT (SLoad (Lit 2) mystore) (SLoad (Lit 0) mystore)]
      conf <- readConfig
      let SMT2 _ cexVars _ = fromRight (internalError "Must succeed") (assertProps conf props)
      let (StorageReads m) = cexVars.storeReads
      case Map.lookup ((SymAddr "test"), Nothing) m of
        Nothing -> assertBoolM "Address missing from storage reads" False
        Just storeReads -> assertBoolM "Did not collect all abstract reads!" $ (Set.size storeReads) == 2
  ]
  , testGroup "equivalence-checking"
    [
      test "eq-simple-diff" $ do
        Just a <- solcRuntime "C"
          [i|
            contract C {
              function stuff() public returns (uint256) {
                return 4;
              }
            }
          |]
        Just b <- solcRuntime "C"
          [i|
            contract C {
              function stuff() public returns (uint256) {
                return 5;
              }
            }
          |]
        withSolvers Bitwuzla 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing a b defaultVeriOpts calldata False
          assertBoolM "Must have a difference" (any (isCex . fst) eq.res)
          let cexs = mapMaybe (getCex . fst) eq.res
          assertEqualM "Must have exactly one cex" (length cexs) 1
      -- diverging gas overapproximations are caught
      -- previously, they had the same name (gas_...), so they compared equal
      , test "eq-divergent-overapprox-gas" $ do
        Just a <- solcRuntime "C"
          [i|
            contract C {
              uint x;
              function stuff(uint a) public returns (uint256) {
                unchecked { x = a * 2; }
                return gasleft();
              }
            }
          |]
        Just b <- solcRuntime "C"
          [i|
            contract C {
              uint x;
              function stuff(uint a) public returns (uint256) {
                unchecked { x = a + a; }
                return gasleft();
              }
            }
          |]
        withSolvers Bitwuzla 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing a b defaultVeriOpts calldata False
          assertBoolM "Must have a difference" (any (isCex . fst) eq.res)
          let cexs = mapMaybe (getCex . fst) eq.res
          assertEqualM "Must have exactly one cex" (length cexs) 1
      -- diverging gas overapproximations are caught
      -- previously, CALL fresh variables were the same so they compared equal
      , test "eq-divergent-overapprox-call" $ do
        Just a <- solcRuntime "C"
          [i|
            contract C {
              function checkval(address inputAddr, uint256 x, uint256 y) public returns (bool) {
                  bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, y);
                  (bool success, bytes memory returnData) = inputAddr.staticcall(data);
                  return success;
              }
            }
          |]
        Just b <- solcRuntime "C"
          [i|
            contract C {
              function checkval(address inputAddr, uint256 x, uint256 y) public returns (bool) {
                  bytes memory data = abi.encodeWithSignature("add(uint256,uint256)", x, x);
                  (bool success, bytes memory returnData) = inputAddr.staticcall(data);
                  return success;
              }
            }
          |]
        withSolvers Bitwuzla 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing a b defaultVeriOpts calldata False
          assertBoolM "Must have a difference" (any (isCex . fst) eq.res)
          let cexs = mapMaybe (getCex . fst) eq.res
          assertEqualM "Must have exactly one cex" (length cexs) 1
      -- check bug https://github.com/argotorg/hevm/issues/679
      , test "eq-issue-with-length-cex-bug679" $ do
        let a = fromJust (hexByteString "5f610100526020610100f3")
            b = fromJust (hexByteString "5f356101f40115610100526020610100f3")
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing a b defaultVeriOpts calldata False
          assertBoolM "Must have a difference" (any (isCex . fst) eq.res)
          let cexs :: [SMTCex] = mapMaybe (getCex . fst) eq.res
          cex <- case cexs of
            [cex] -> pure cex
            _     -> liftIO $ assertFailure "Must have exactly one cex"
          let def = fromRight (error "cannot be") $ defaultSymbolicValues $ subModel cex (AbstractBuf "txdata")
          let buf = prettyBuf $ Expr.concKeccakSimpExpr def
          assertBoolM "Must start with specific string" (T.isPrefixOf "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0c" buf)
      , test "eq-yul-simple-cex" $ do
        Right aPrgm <- liftIO $ yul ""
          [i|
          {
            calldatacopy(0, 0, 32)
            switch mload(0)
            case 0 { }
            case 1 { }
            default { invalid() }
          }
          |]
        Right bPrgm <- liftIO $ yul ""
          [i|
          {
            calldatacopy(0, 0, 32)
            switch mload(0)
            case 0 { }
            case 2 { }
            default { invalid() }
          }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertBoolM "Must have a difference" (any (isCex . fst) eq.res)
      , test "constructor-same-deployed-diff" $ do
        Just initA <- solidity "C"
          [i|
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
        Just initB <- solidity "C"
          [i|
            contract C {
              uint public immutable NUMBER;
              constructor(uint a) {
                NUMBER = 4;
              }
              function stuff(uint b) public returns (uint256) {
                unchecked {return 4*b+NUMBER;}
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing initA initB defaultVeriOpts calldata True
          assertBoolM "Must have difference, we return different values" (all (isCex . fst) eq.res)
      , test "constructor-same-deployed-diff2" $ do
        Just initA <- solidity "C"
          [i|
            contract C {
              uint public immutable NUMBER;
              constructor(uint a) {
                NUMBER = 4;
              }
              function stuff(uint b) public returns (uint256) {
                unchecked{return 4*b+NUMBER;}
              }
            }
          |]
        Just initB <- solidity "C"
          [i|
            contract C {
              uint public immutable NUMBER;
              constructor(uint a) {
                NUMBER = 4;
              }
              function stuff(uint b) public returns (uint256) {
                unchecked {return 4*b+NUMBER;}
              }
              function stuff_other(uint b) public returns (uint256) {
                unchecked {return 2*b+NUMBER;}
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing initA initB defaultVeriOpts calldata True
          assertBoolM "Must have difference, we return different values" (all (isCex . fst) eq.res)
      , test "constructor-same-deployed-diff3" $ do
        Just initA <- solidity "C"
          [i|
            contract C {
              uint public immutable NUMBER;
              constructor(uint a) {
                NUMBER = 4;
              }
              function stuff(uint b) public returns (uint256) {
                unchecked{return 4*b+NUMBER;}
              }
            }
          |]
        Just initB <- solidity "C"
          [i|
            contract C {
              uint public immutable NUMBER;
              constructor(uint a) {
                NUMBER = 4;
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing initA initB defaultVeriOpts calldata True
          assertBoolM "Must have difference, we return different values" (all (isCex . fst) eq.res)
      -- We set x to be 0 on deployment. Default value is also 0. So they are equivalent
      -- We cannot deal with symbolic code. However, the below will generate symbolic code,
      -- because of the parameter in the constructor that is set to NUMBER in the deployed code.
      -- Hence, this test is ignored.
      , ignoreTest $ test "constructor-diff-deploy" $ do
        Just initA <- solidity "C"
          [i|
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
        Just initB <- solidity "C"
          [i|
            contract C {
              uint public immutable NUMBER;
              constructor(uint a) {
                NUMBER = a*2;
              }
              function stuff(uint b) public returns (uint256) {
                return NUMBER;
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing initA initB defaultVeriOpts calldata True
          assertBoolM "Must have difference" (all (isCex . fst) eq.res)
      -- We set x to be 0 on deployment. Default value is also 0. So they are equivalent
      , test "constructor-implicit" $ do
        Just initA <- solidity "C"
          [i|
            contract C {
              uint immutable x;
              function stuff(uint a) public returns (uint256) {
                unchecked {return 8+a;}
              }
            }
          |]
        Just initB <- solidity "C"
          [i|
            contract C {
              uint immutable x;
              constructor() {
                x = 0;
              }
              function stuff(uint a) public returns (uint256) {
                unchecked {return a+8;}
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing initA initB defaultVeriOpts calldata True
          putStrLnM $ "Equivalence result: " <> show eq
          assertEqualM "Must have no difference" [] (map fst eq.res)
      -- We set x to be 3 vs 0 (default) on deployment.
      , test "constructor-differing" $ do
        Just initA <- solidity "C"
          [i|
            contract C {
              uint x;
              function stuff(uint a) public returns (uint256) {
                unchecked {return a+x;}
              }
            }
          |]
        Just initB <- solidity "C"
          [i|
            contract C {
              uint x;
              constructor() {
                x = 3;
              }
              function stuff(uint a) public returns (uint256) {
                unchecked {return a+x;}
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing initA initB defaultVeriOpts calldata True
          let cexes = filter (isCex . fst) eq.res
          assertBoolM "Must have a difference" (not $ null cexes)
      , test "eq-sol-exp-qed" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract C {
              function a(uint8 x) public returns (uint8 b) {
                unchecked {
                  b = x*2;
                }
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract C {
              function a(uint8 x) public returns (uint8 b) {
                unchecked {
                  b = x<<1;
                }
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertEqualM "Must have no difference" [] (map fst eq.res)
      ,
      test "eq-balance-differs" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
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
        Just bPrgm <- solcRuntime "C"
          [i|
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }
            contract C {
              function f() public {
                new Send{value:1}(payable(address(0x0)));
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertBoolM "Must differ" (all (isCex . fst) eq.res)
      ,
      -- TODO: this fails because we don't check equivalence of deployed contracts
      expectFail $ test "eq-handles-contract-deployment" $ do
        Just aPrgm <- solcRuntime "B"
          [i|
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
                parent.call(abi.encode(B.drain.selector));
              }
            }

            contract B {
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
        Just bPrgm <- solcRuntime "D"
          [i|
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }

            contract C {
              address parent;
              constructor(address p) {
                  parent = p;
              }
            }

            contract D {
              address child;
              function a() public {
                child = address(new C(address(this)));
              }
              function drain() public {
                require(msg.sender == child);
                new Send{value: address(this).balance}(payable(address(0x0)));
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertBoolM "Must differ" (any (isCex . fst) eq.res)
      ,
      test "eq-unknown-addr" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract C {
              address addr;
              function a(address a, address b) public {
                addr = a;
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract C {
              address addr;
              function a(address a, address b) public {
                addr = b;
              }
            }
          |]
        withSolvers Z3 3 1 Nothing $ \s -> do
          cd <- mkCalldata (Just (Sig "a(address,address)" [AbiAddressType, AbiAddressType])) []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts cd False
          assertEqualM "Must be different" (any (isCex . fst) eq.res) True
      ,
      test "eq-sol-exp-cex" $ do
        Just aPrgm <- solcRuntime "C"
            [i|
              contract C {
                function a(uint8 x) public returns (uint8 b) {
                  unchecked {
                    b = x*2+1;
                  }
                }
              }
            |]
        Just bPrgm <- solcRuntime "C"
          [i|
              contract C {
                function a(uint8 x) public returns (uint8 b) {
                  unchecked {
                    b =  x<<1;
                  }
                }
              }
          |]
        withSolvers Bitwuzla 3 1 Nothing $ \s -> do
          calldata <- mkCalldata Nothing []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertEqualM "Must be different" (any (isCex . fst) eq.res) True
      ,
      test "eq-storage-write-to-static-array-uint128" $ do
        Just aPrgm <- solcRuntime "C"
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
        Just bPrgm <- solcRuntime "C"
          [i|
              contract C {
                uint128[5] arr;
                function set(uint i, uint128 v) external returns (uint) {
                  arr[i] = v;
                  return 0;
                }
              }
          |]
        withSolvers Bitwuzla 1 1 Nothing $ \s -> do
          calldata <- mkCalldata (Just (Sig "set(uint256,uint128)" [AbiUIntType 256, AbiUIntType 128])) []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertEqualM "Must have no difference" [] (map fst eq.res)
      ,
      test "eq-storage-write-to-static-array-uint8" $ do
        Just aPrgm <- solcRuntime "C"
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
        Just bPrgm <- solcRuntime "C"
          [i|
              contract C {
                uint8[10] arr;
                function set(uint i, uint8 v) external returns (uint) {
                  arr[i] = v;
                  return 0;
                }
              }
          |]
        withSolvers Bitwuzla 1 1 Nothing $ \s -> do
          calldata <- mkCalldata (Just (Sig "set(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertEqualM "Must have no difference" [] (map fst eq.res)
      ,
      test "eq-storage-write-to-static-array-uint32" $ do
        Just aPrgm <- solcRuntime "C"
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
        Just bPrgm <- solcRuntime "C"
          [i|
              contract C {
                uint32[5] arr;
                function set(uint i, uint32 v) external returns (uint) {
                  arr[i] = v;
                  return 0;
                }
              }
          |]
        withSolvers Bitwuzla 1 1 Nothing $ \s -> do
          calldata <- mkCalldata (Just (Sig "set(uint256,uint32)" [AbiUIntType 256, AbiUIntType 32])) []
          eq <- equivalenceCheck s Nothing aPrgm bPrgm defaultVeriOpts calldata False
          assertEqualM "Must have no difference" [] (map fst eq.res)
      , test "eq-all-yul-optimization-tests" $ do
        let opts = (defaultVeriOpts :: VeriOpts) { iterConf = defaultIterConf {maxIter = Just 5, askSmtIters = 20, loopHeuristic = Naive }}
            ignoredTests =
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
                    , "yulOptimizerTests/fullInliner/large_function_multi_use.yul"
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
                    , "yulOptimizerTests/fullSuite/transient_storage.yul"
                    , "yulOptimizerTests/unusedPruner/transient_storage.yul"

                    -- Bug in solidity, fixed in newer versions:
                    -- https://github.com/ethereum/solidity/issues/15397#event-14116827816
                    , "no_move_transient_storage.yul"
                    ]

        solcRepo <- liftIO $ fromMaybe (internalError "cannot find solidity repo") <$> (lookupEnv "HEVM_SOLIDITY_REPO")
        let testDir = solcRepo <> "/test/libyul/yulOptimizerTests"
        dircontents <- liftIO $ System.Directory.listDirectory testDir
        let
          fullpaths = map ((testDir ++ "/") ++) dircontents
          recursiveList :: [FilePath] -> [FilePath] -> IO [FilePath]
          recursiveList (a:ax) b =  do
              isdir <- doesDirectoryExist a
              case isdir of
                True  -> do
                    fs <- System.Directory.listDirectory a
                    let fs2 = map ((a ++ "/") ++) fs
                    recursiveList (ax++fs2) b
                False -> recursiveList ax (a:b)
          recursiveList [] b = pure b
        files <- liftIO $ recursiveList fullpaths []
        let filesFiltered = filter (\file -> not $ any (`List.isInfixOf` file) ignoredTests) files

        -- Takes one file which follows the Solidity Yul optimizer unit tests format,
        -- extracts both the nonoptimized and the optimized versions, and checks equivalence.
        forM_ filesFiltered (\f-> do
          liftIO $ print f
          origcont <- liftIO $ readFile f
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
          start <- liftIO $ getCurrentTime
          putStrLnM $ "Checking file: " <> f
          conf <- readConfig
          when conf.debug $ liftIO $ do
            putStrLnM "-------------Original Below-----------------"
            mapM_ putStrLn unfiltered
            putStrLnM "------------- Filtered A + Symb below-----------------"
            mapM_ putStrLn filteredASym
            putStrLnM "------------- Filtered B + Symb below-----------------"
            mapM_ putStrLn filteredBSym
            putStrLnM "------------- END -----------------"
          Right aPrgm <- liftIO $ yul "" $ T.pack $ unlines filteredASym
          Right bPrgm <- liftIO $ yul "" $ T.pack $ unlines filteredBSym
          procs <- liftIO $ getNumProcessors
          withSolvers CVC5 (unsafeInto procs) 1 (Just 100) $ \s -> do
            calldata <- mkCalldata Nothing []
            eq <- equivalenceCheck s Nothing aPrgm bPrgm opts calldata False
            let res = map fst eq.res
            end <- liftIO $ getCurrentTime
            case any isCex res of
              False -> liftIO $ do
                print $ "OK. Took " <> (show $ diffUTCTime end start) <> " seconds"
                let timeouts = filter isUnknown res
                let errors = filter isError res
                unless (null timeouts && null errors) $ do
                  putStrLnM $ "But " <> (show $ length timeouts) <> " timeout(s) and " <>  (show $ length errors) <> " error(s) occurred"
                  internalError "Encountered timeout(s) and/or error(s)"
              True -> liftIO $ do
                putStrLnM $ "Not OK: " <> show f <> " Got: " <> show res
                internalError "Was NOT equivalent"
           )
    ]
  ]
  where
    (===>) = assertSolidityComputation

checkEquivProp :: App m => Prop -> Prop -> m Bool
checkEquivProp a b = fmap (fromMaybe True) $ checkEquivBase (\l r -> PNeg (PImpl l r .&& PImpl r l)) a b True

checkEquivPropAndLHS :: App m => Prop -> Prop -> m Bool
checkEquivPropAndLHS orig simp = do
  let lhsConst = Expr.checkLHSConstProp simp
  equiv <- checkEquivProp orig simp
  pure $ lhsConst && equiv

checkEquiv :: (Typeable a, App m) => Expr a -> Expr a -> m Bool
checkEquiv a b = do
  opts <- readConfig
  if a == b then pure True else do
    when (opts.debug) $ liftIO $ putStrLn $ "Checking equivalence of " <> show a <> " and " <> show b
    x <- checkEquivBase (./=) a b True
    when (opts.debug) $ liftIO $ putStrLn $ "UNSAT check, expect True: " <> show x
    y <- checkEquivBase (.==) a b False
    when (opts.debug) $ liftIO $ putStrLn $ "SAT check, expect False: " <> show y
    pure $ (fromMaybe True x) && not (fromMaybe False y)

checkEquivAndLHS :: (Typeable a, App m) => Expr a -> Expr a -> m Bool
checkEquivAndLHS orig simp = do
  opts <- readConfig
  let lhsConst =  Expr.checkLHSConst simp
  when (opts.debug) $ liftIO $ putStrLn $ "LHS const: " <> show lhsConst
  equiv <- checkEquiv orig simp
  pure $ lhsConst && equiv

checkEquivBase :: (Eq a, App m) => (a -> a -> Prop) -> a -> a -> Bool -> m (Maybe Bool)
checkEquivBase mkprop l r expect = do
  config <- readConfig
  let noSimplifyEnv = Env {config = config {simp = False}}
  liftIO $ runEnv noSimplifyEnv $ do
    withSolvers Z3 1 1 (Just 1) $ \solvers -> do
      res <- checkSatWithProps solvers [mkprop l r]
      let ret = case res of
            Qed -> Just True
            Cex {} -> Just False
            Error _ -> Just (not expect)
            Unknown _ -> Nothing
      when (ret == Just (not expect)) $ liftIO $ print res
      pure ret

-- | Takes a runtime code and calls it with the provided calldata

-- | Takes a creation code and some calldata, runs the creation code, and calls the resulting contract with the provided calldata
runSimpleVM :: App m => ByteString -> ByteString -> m (Maybe ByteString)
runSimpleVM x ins = do
  loadVM x >>= \case
    Nothing -> pure Nothing
    Just vm -> do
     let calldata = (ConcreteBuf ins)
         vm' = set (#state % #calldata) calldata vm
     res <- Stepper.interpret (Fetch.zero 0 Nothing) vm' Stepper.execFully
     case res of
       Right (ConcreteBuf bs) -> pure $ Just bs
       s -> internalError $ show s

-- | Takes a creation code and returns a vm with the result of executing the creation code
loadVM :: App m => ByteString -> m (Maybe (VM Concrete))
loadVM x = do
  vm <- liftIO $ stToIO $ vmForEthrunCreation x
  vm1 <- Stepper.interpret (Fetch.zero 0 Nothing) vm Stepper.runFully
  case vm1.result of
    Just (VMSuccess (ConcreteBuf targetCode)) -> do
      let target = vm1.state.contract
      vm2 <- Stepper.interpret (Fetch.zero 0 Nothing) vm1 (prepVm target targetCode)
      writeTrace vm2
      pure $ Just vm2
    _ -> pure Nothing
  where
    prepVm target targetCode = Stepper.evm $ do
      replaceCodeOfSelf (RuntimeCode $ ConcreteRuntimeCode targetCode)
      resetState
      assign (#state % #gas) 0xffffffffffffffff -- kludge
      execState (loadContract target) <$> get >>= put
      get

hex :: ByteString -> ByteString
hex s =
  case BS16.decodeBase16Untyped s of
    Right x -> x
    Left e -> internalError $ T.unpack e

singleContract :: Text -> Text -> IO (Maybe ByteString)
singleContract x s =
  solidity x [i|
    pragma experimental ABIEncoderV2;
    contract ${x} { ${s} }
  |]

defaultDataLocation :: AbiType -> Text
defaultDataLocation t =
  if (case t of
        AbiBytesDynamicType -> True
        AbiStringType -> True
        AbiArrayDynamicType _ -> True
        AbiArrayType _ _ -> True
        _ -> False)
  then "memory"
  else ""

runFunction :: App m => Text -> ByteString -> m (Maybe ByteString)
runFunction c input = do
  x <- liftIO $ singleContract "X" c
  runSimpleVM (fromJust x) input

runStatements :: App m => Text -> [AbiValue] -> AbiType -> m (Maybe ByteString)
runStatements stmts args t = do
  let params =
        T.intercalate ", "
          (map (\(x, c) -> abiTypeSolidity (abiValueType x)
                             <> " " <> defaultDataLocation (abiValueType x)
                             <> " " <> T.pack [c])
            (zip args "abcdefg"))
      s =
        "foo(" <> T.intercalate ","
                    (map (abiTypeSolidity . abiValueType) args) <> ")"

  runFunction [i|
    function foo(${params}) public pure returns (${abiTypeSolidity t} ${defaultDataLocation t} x) {
      ${stmts}
    }
  |] (abiMethod s (AbiTuple $ V.fromList args))

getStaticAbiArgs :: Int -> VM Symbolic -> [Expr EWord]
getStaticAbiArgs n vm =
  let cd = vm.state.calldata
  in decodeStaticArgs 4 n cd

-- includes shaving off 4 byte function sig
decodeAbiValues :: [AbiType] -> ByteString -> [AbiValue]
decodeAbiValues types bs =
  let xy = case decodeAbiValue (AbiTupleType $ V.fromList types) (BS.fromStrict (BS.drop 4 bs)) of
        AbiTuple xy' -> xy'
        _ -> internalError "AbiTuple expected"
  in V.toList xy

-- abi types that are supported in the symbolic abi encoder
newtype SymbolicAbiType = SymbolicAbiType AbiType
  deriving (Eq, Show)

newtype SymbolicAbiVal = SymbolicAbiVal AbiValue
  deriving (Eq, Show)

instance Arbitrary SymbolicAbiVal where
  arbitrary = do
    SymbolicAbiType ty <- arbitrary
    SymbolicAbiVal <$> genAbiValue ty

instance Arbitrary SymbolicAbiType where
  arbitrary = SymbolicAbiType <$> frequency
    [ (5, (AbiUIntType . (* 8)) <$> choose (1, 32))
    , (5, (AbiIntType . (* 8)) <$> choose (1, 32))
    , (5, pure AbiAddressType)
    , (5, pure AbiBoolType)
    , (5, AbiBytesType <$> choose (1,32))
    , (1, do SymbolicAbiType ty <- scale (`div` 2) arbitrary
             AbiArrayType <$> (choose (1, 30)) <*> pure ty
      )
    ]

newtype Bytes = Bytes ByteString
  deriving Eq

instance Show Bytes where
  showsPrec _ (Bytes x) _ = show (BS.unpack x)

instance Arbitrary Bytes where
  arbitrary = fmap (Bytes . BS.pack) arbitrary

newtype RLPData = RLPData RLP
  deriving (Eq, Show)

-- bias towards bytestring to try to avoid infinite recursion
instance Arbitrary RLPData where
  arbitrary = frequency
   [(5, do
           Bytes bytes <- arbitrary
           return $ RLPData $ BS bytes)
   , (1, do
         k <- choose (0,10)
         ls <- vectorOf k arbitrary
         return $ RLPData $ List [r | RLPData r <- ls])
   ]

instance Arbitrary Word128 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary Word160 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary Word256 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary W64 where
  arbitrary = fmap W64 arbitrary

instance Arbitrary W256 where
  arbitrary = fmap W256 arbitrary

instance Arbitrary Addr where
  arbitrary = fmap Addr arbitrary

instance Arbitrary (Expr EAddr) where
  arbitrary = oneof
    [ fmap LitAddr arbitrary
    , fmap SymAddr (genName "addr")
    ]

instance Arbitrary (Expr Storage) where
  arbitrary = sized genStorage

instance Arbitrary (Expr EWord) where
  arbitrary = sized defaultWord

instance Arbitrary (Expr Byte) where
  arbitrary = sized genByte

newtype SymbolicJoinBytes = SymbolicJoinBytes [Expr Byte]
  deriving (Eq, Show)

instance Arbitrary SymbolicJoinBytes where
  arbitrary = liftM SymbolicJoinBytes $ replicateM 32 arbitrary

joinBytesFromList :: [Expr Byte] -> Expr EWord
joinBytesFromList [a0, a1, a2, a3, a4, a5, a6, a7,
                   a8, a9, a10, a11, a12, a13, a14, a15,
                   a16, a17, a18, a19, a20, a21, a22, a23,
                   a24, a25, a26, a27, a28, a29, a30, a31] =
  JoinBytes a0 a1 a2 a3 a4 a5 a6 a7
            a8 a9 a10 a11 a12 a13 a14 a15
            a16 a17 a18 a19 a20 a21 a22 a23
            a24 a25 a26 a27 a28 a29 a30 a31
joinBytesFromList _ = internalError "List must contain exactly 32 elements"

instance Arbitrary (Expr Buf) where
  arbitrary = sized defaultBuf

instance Arbitrary (Expr End) where
  arbitrary = sized genEnd

instance Arbitrary (ContractCode) where
  arbitrary = oneof
    [ fmap UnknownCode arbitrary
    , liftM2 InitCode arbitrary arbitrary
    , fmap RuntimeCode arbitrary
    ]

instance Arbitrary (RuntimeCode) where
  arbitrary = oneof
    [ fmap ConcreteRuntimeCode arbitrary
    , fmap SymbolicRuntimeCode arbitrary
    ]

instance Arbitrary (V.Vector (Expr Byte)) where
  arbitrary = fmap V.fromList (listOf1 arbitrary)

instance Arbitrary (Expr EContract) where
  arbitrary = sized genEContract

-- LitOnly
newtype LitOnly a = LitOnly a
  deriving (Show, Eq)

newtype LitWord (sz :: Nat) = LitWord (Expr EWord)
  deriving (Show)

instance (KnownNat sz) => Arbitrary (LitWord sz) where
  arbitrary = LitWord <$> genLit (fromInteger v)
    where
      v = natVal (Proxy @sz)

instance Arbitrary (LitOnly (Expr Byte)) where
  arbitrary = LitOnly . LitByte <$> arbitrary

instance Arbitrary (LitOnly (Expr EWord)) where
  arbitrary = LitOnly . Lit <$> arbitrary

instance Arbitrary (LitOnly (Expr Buf)) where
  arbitrary = LitOnly . ConcreteBuf <$> arbitrary

genEContract :: Int -> Gen (Expr EContract)
genEContract sz = do
  c <- arbitrary
  b <- defaultWord sz
  n <- arbitrary
  s <- genStorage sz
  ts <- genStorage sz
  pure $ C {code=c, storage=s, tStorage=ts, balance=b, nonce=n}

-- ZeroDepthWord
newtype ZeroDepthWord = ZeroDepthWord (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary ZeroDepthWord where
  arbitrary = do
    fmap ZeroDepthWord . sized $ genWord 0

-- WriteWordBuf
newtype WriteWordBuf = WriteWordBuf (Expr Buf)
  deriving (Show, Eq)

instance Arbitrary WriteWordBuf where
  arbitrary = do
    let mkBuf = oneof
          [ pure $ ConcreteBuf ""       -- empty
          , fmap ConcreteBuf arbitrary  -- concrete
          , sized (genBuf 100)          -- overlapping writes
          , arbitrary                   -- sparse writes
          ]
    fmap WriteWordBuf mkBuf

-- GenCopySliceBuf
newtype GenCopySliceBuf = GenCopySliceBuf (Expr Buf)
  deriving (Show, Eq)

instance Arbitrary GenCopySliceBuf where
  arbitrary = do
    let mkBuf = oneof
          [ pure $ ConcreteBuf ""
          , fmap ConcreteBuf arbitrary
          , arbitrary
          ]
    fmap GenCopySliceBuf mkBuf

-- GenWriteStorageExpr
newtype GenWriteStorageExpr = GenWriteStorageExpr (Expr EWord, Expr Storage)
  deriving (Show, Eq)

instance Arbitrary GenWriteStorageExpr where
  arbitrary = do
    slot <- arbitrary
    let mkStore = oneof
          [ pure $ ConcreteStore mempty
          , fmap ConcreteStore arbitrary
          , do
              -- generate some write chains where we know that at least one
              -- write matches either the input addr, or both the input
              -- addr and slot
              let addWrites :: Expr Storage -> Int -> Gen (Expr Storage)
                  addWrites b 0 = pure b
                  addWrites b n = liftM3 SStore arbitrary arbitrary (addWrites b (n - 1))
              s <- arbitrary
              addMatch <- fmap (SStore slot) arbitrary
              let withMatch = addMatch s
              newWrites <- oneof [ pure 0, pure 1, fmap (`mod` 5) arbitrary ]
              addWrites withMatch newWrites
          , arbitrary
          ]
    store <- mkStore
    pure $ GenWriteStorageExpr (slot, store)

-- GenWriteByteIdx
newtype GenWriteByteIdx = GenWriteByteIdx (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenWriteByteIdx where
  arbitrary = do
    -- 1st: can never overflow an Int
    -- 2nd: can overflow an Int
    let mkIdx = frequency [ (10, genLit 1_000_000) , (1, fmap Lit arbitrary) ]
    fmap GenWriteByteIdx mkIdx

newtype LitProp = LitProp Prop
  deriving (Show, Eq)

instance Arbitrary LitProp where
  arbitrary = LitProp <$> sized (genProp True)


newtype StorageExp = StorageExp (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary StorageExp where
  arbitrary = StorageExp <$> (genStorageExp)

genStorageExp :: Gen (Expr EWord)
genStorageExp = do
  fromPos <- genSlot
  storage <- genStorageWrites
  pure $ SLoad fromPos storage

genSlot :: Gen (Expr EWord)
genSlot = frequency [ (1, do
                        buf <- genConcreteBufSlot 64
                        case buf of
                          (ConcreteBuf b) -> do
                            key <- genLit 10
                            pure $ Expr.MappingSlot b key
                          _ -> internalError "impossible"
                        )
                     -- map element
                     ,(2, do
                        l <- genLit 10
                        buf <- genConcreteBufSlot 64
                        pure $ Add (Keccak buf) l)
                    -- Array element
                     ,(2, do
                        l <- genLit 10
                        buf <- genConcreteBufSlot 32
                        pure $ Add (Keccak buf) l)
                     -- member of the Contract
                     ,(2, pure $ Lit 20)
                     -- array element
                     ,(2, do
                        arrayNum :: Int <- arbitrary
                        offs :: W256 <- arbitrary
                        pure $ Lit $ fst (Expr.preImages !! (arrayNum `mod` 3)) + (offs `mod` 3))
                     -- random stuff
                     ,(1, pure $ Lit (maxBound :: W256))
                     ]

-- Generates an N-long buffer, all with the same value, at most 8 different ones
genConcreteBufSlot :: Int -> Gen (Expr Buf)
genConcreteBufSlot len = do
  b :: Word8 <- arbitrary
  pure $ ConcreteBuf $ BS.pack ([ 0 | _ <- [0..(len-2)]] ++ [b])

genStorageWrites :: Gen (Expr Storage)
genStorageWrites = do
  toSlot <- genSlot
  val <- genLit (maxBound :: W256)
  store <- frequency [ (3, pure $ AbstractStore (SymAddr "") Nothing)
                     , (2, genStorageWrites)
                     ]
  pure $ SStore toSlot val store

instance Arbitrary Prop where
  arbitrary = sized (genProp False)

genProps :: Bool -> Int -> Gen [Prop]
genProps onlyLits sz2 = listOf $ genProp onlyLits sz2

genProp :: Bool -> Int -> Gen (Prop)
genProp _ 0 = PBool <$> arbitrary
genProp onlyLits sz = oneof
  [ liftM2 PEq subWord subWord
  , liftM2 PLT subWord subWord
  , liftM2 PGT subWord subWord
  , liftM2 PLEq subWord subWord
  , liftM2 PGEq subWord subWord
  , fmap PNeg subProp
  , liftM2 PAnd subProp subProp
  , liftM2 POr subProp subProp
  , liftM2 PImpl subProp subProp
  ]
  where
    subWord = if onlyLits then frequency [(2, Lit <$> arbitrary)
                                         ,(1, pure $ Lit 0)
                                         ,(1, pure $ Lit Expr.maxLit)
                                         ]
                          else genWord 1 (sz `div` 2)
    subProp = genProp onlyLits (sz `div` 2)

genByte :: Int -> Gen (Expr Byte)
genByte 0 = fmap LitByte arbitrary
genByte sz = oneof
  [ liftM2 IndexWord subWord subWord
  , liftM2 ReadByte subWord subBuf
  ]
  where
    subWord = defaultWord (sz `div` 10)
    subBuf = defaultBuf (sz `div` 10)

genLit :: W256 -> Gen (Expr EWord)
genLit bound = do
  w <- arbitrary
  pure $ Lit (w `mod` bound)

genNat :: Gen Int
genNat = fmap unsafeInto (arbitrary :: Gen Natural)

genName :: String -> Gen Text
-- In order not to generate SMT reserved words, we prepend with "esc_"
genName ty = fmap (T.pack . (("esc_" <> ty <> "_") <> )) $ listOf1 (oneof . (fmap pure) $ ['a'..'z'] <> ['A'..'Z'])

genEnd :: Int -> Gen (Expr End)
genEnd 0 = oneof
  [ fmap (Failure mempty mempty . UnrecognizedOpcode) arbitrary
  , pure $ Failure mempty mempty IllegalOverflow
  , pure $ Failure mempty mempty SelfDestruction
  ]
genEnd sz = oneof
  [ liftM3 Failure subProp (pure mempty) (fmap Revert subBuf)
  , liftM4 Success subProp (pure mempty) subBuf arbitrary
  -- TODO Partial
  ]
  where
    subBuf = defaultBuf (sz `div` 2)
    subProp = genProps False (sz `div` 2)

genWord :: Int -> Int -> Gen (Expr EWord)
genWord litFreq 0 = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
       , (1, pure 0)
       , (1, pure Expr.maxLit)
       , (1, arbitrary)
       ]
      pure $ Lit val
    )
  , (1, oneof
      [ pure Origin
      , pure Coinbase
      , pure Timestamp
      , pure BlockNumber
      , pure PrevRandao
      , pure GasLimit
      , pure ChainId
      , pure BaseFee
      --, liftM2 SelfBalance arbitrary arbitrary
      --, liftM2 Gas arbitrary arbitrary
      , fmap Lit arbitrary
      , fmap joinBytesFromList $ replicateM 32 arbitrary
      , fmap Var (genName "word")
      ]
    )
  ]
genWord litFreq sz = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
       , (1, arbitrary)
       ]
      pure $ Lit val
    )
  , (1, oneof
    [ liftM2 Add subWord subWord
    , liftM2 Sub subWord subWord
    , liftM2 Mul subWord subWord
    , liftM2 Div subWord subWord
    , liftM2 SDiv subWord subWord
    , liftM2 Mod subWord subWord
    , liftM2 SMod subWord subWord
    --, liftM3 AddMod subWord subWord subWord
    --, liftM3 MulMod subWord subWord subWord -- it works, but it's VERY SLOW
    --, liftM2 Exp subWord litWord
    , liftM2 SEx subWord subWord
    , liftM2 Min subWord subWord
    , liftM2 LT subWord subWord
    , liftM2 GT subWord subWord
    , liftM2 LEq subWord subWord
    , liftM2 GEq subWord subWord
    , liftM2 SLT subWord subWord
    --, liftM2 SGT subWord subWord
    , liftM2 Eq subWord subWord
    , fmap IsZero subWord
    , liftM2 And subWord subWord
    , liftM2 Or subWord subWord
    , liftM2 Xor subWord subWord
    , fmap Not subWord
    , liftM2 SHL subWord subWord
    , liftM2 SHR subWord subWord
    , liftM2 SAR subWord subWord
    , fmap BlockHash subWord
    --, liftM3 Balance arbitrary arbitrary subWord
    --, fmap CodeSize subWord
    --, fmap ExtCodeHash subWord
    , fmap Keccak subBuf
    , fmap SHA256 subBuf
    , liftM2 SLoad subWord subStore
    , liftM2 ReadWord genReadIndex subBuf
    , fmap BufLength subBuf
    , do
      one <- subByte
      two <- subByte
      three <- subByte
      four <- subByte
      five <- subByte
      six <- subByte
      seven <- subByte
      eight <- subByte
      nine <- subByte
      ten <- subByte
      eleven <- subByte
      twelve <- subByte
      thirteen <- subByte
      fourteen <- subByte
      fifteen <- subByte
      sixteen <- subByte
      seventeen <- subByte
      eighteen <- subByte
      nineteen <- subByte
      twenty <- subByte
      twentyone <- subByte
      twentytwo <- subByte
      twentythree <- subByte
      twentyfour <- subByte
      twentyfive <- subByte
      twentysix <- subByte
      twentyseven <- subByte
      twentyeight <- subByte
      twentynine <- subByte
      thirty <- subByte
      thirtyone <- subByte
      thirtytwo <- subByte
      pure $ JoinBytes
        one two three four five six seven eight nine ten
        eleven twelve thirteen fourteen fifteen sixteen
        seventeen eighteen nineteen twenty twentyone
        twentytwo twentythree twentyfour twentyfive
        twentysix twentyseven twentyeight twentynine
        thirty thirtyone thirtytwo
    ])
  ]
 where
   subWord = genWord litFreq (sz `div` 5)
   subBuf = defaultBuf (sz `div` 10)
   subStore = genStorage (sz `div` 10)
   subByte = genByte (sz `div` 10)
   genReadIndex = do
    o :: (Expr EWord) <- subWord
    pure $ case o of
      Lit w -> Lit $ w `mod` into (maxBound :: Word64)
      _ -> o

genWordArith :: Int -> Int -> Gen (Expr EWord)
genWordArith litFreq 0 = frequency
  [ (litFreq, fmap Lit arbitrary)
  , (1, oneof [ fmap Lit arbitrary ])
  ]
genWordArith litFreq sz = frequency
  [ (litFreq, fmap Lit arbitrary)
  , (20, frequency
    [ (20, liftM2 Add  subWord subWord)
    , (20, liftM2 Sub  subWord subWord)
    , (20, liftM2 Mul  subWord subWord)
    , (20, liftM2 SEx  subWord subWord)
    , (20, liftM2 Xor  subWord subWord)
    -- these reduce variability
    , (3 , liftM2 Min  subWord subWord)
    , (3 , liftM2 Div  subWord subWord)
    , (3 , liftM2 SDiv subWord subWord)
    , (3 , liftM2 Mod  subWord subWord)
    , (3 , liftM2 SMod subWord subWord)
    , (3 , liftM2 SHL  subWord subWord)
    , (3 , liftM2 SHR  subWord subWord)
    , (3 , liftM2 SAR  subWord subWord)
    , (3 , liftM2 Or   subWord subWord)
    -- comparisons, reducing variability greatly
    , (1 , liftM2 LEq  subWord subWord)
    , (1 , liftM2 GEq  subWord subWord)
    , (1 , liftM2 SLT  subWord subWord)
    --(1, , liftM2 SGT subWord subWord
    , (1 , liftM2 Eq   subWord subWord)
    , (1 , liftM2 And  subWord subWord)
    , (1 , fmap IsZero subWord        )
    -- Expensive below
    --(1,  liftM3 AddMod subWord subWord subWord
    --(1,  liftM3 MulMod subWord subWord subWord
    --(1,  liftM2 Exp subWord litWord
    ])
  ]
 where
   subWord = genWordArith (litFreq `div` 2) (sz `div` 2)


-- Finds SLoad -> SStore. This should not occur in most scenarios
-- as we can simplify them away
badStoresInExpr :: [Expr a] -> Bool
badStoresInExpr exprs = any (getAny . foldExpr match mempty) exprs
  where
      match (SLoad _ (SStore _ _ _)) = Any True
      match _ = Any False

defaultBuf :: Int -> Gen (Expr Buf)
defaultBuf = genBuf (4_000_000)

defaultWord :: Int -> Gen (Expr EWord)
defaultWord = genWord 10

maybeBoundedLit :: W256 -> Gen (Expr EWord)
maybeBoundedLit bound = do
  o <- (arbitrary :: Gen (Expr EWord))
  pure $ case o of
        Lit w -> Lit $ w `mod` bound
        _ -> o

genBuf :: W256 -> Int -> Gen (Expr Buf)
genBuf _ 0 = oneof
  [ fmap AbstractBuf (genName "buf")
  , fmap ConcreteBuf arbitrary
  ]
genBuf bound sz = oneof
  [ liftM3 WriteWord (maybeBoundedLit bound) subWord subBuf
  , liftM3 WriteByte (maybeBoundedLit bound) subByte subBuf
  -- we don't generate copyslice instances where:
  --   - size is abstract
  --   - size > 100 (due to unrolling in SMT.hs)
  --   - literal dstOffsets are > 4,000,000 (due to unrolling in SMT.hs)
  -- n.b. that 4,000,000 is the theoretical maximum memory size given a 30,000,000 block gas limit
  , liftM5 CopySlice genReadIndex (maybeBoundedLit bound) smolLitWord subBuf subBuf
  ]
  where
    -- copySlice gets unrolled in the generated SMT so we can't go too crazy here
    smolLitWord = do
      w <- arbitrary
      pure $ Lit (w `mod` 100)
    subWord = defaultWord (sz `div` 5)
    subByte = genByte (sz `div` 10)
    subBuf = genBuf bound (sz `div` 10)
    genReadIndex = do
      o :: (Expr EWord) <- subWord
      pure $ case o of
        Lit w -> Lit $ w `mod` into (maxBound :: Word64)
        _ -> o

genStorage :: Int -> Gen (Expr Storage)
genStorage 0 = oneof
  [ liftM2 AbstractStore arbitrary (pure Nothing)
  , fmap ConcreteStore $ resize 5 arbitrary
  ]
genStorage sz = liftM3 SStore key val subStore
  where
    subStore = genStorage (sz `div` 10)
    val = defaultWord (sz `div` 5)
    key = genStorageKey

genStorageKey :: Gen (Expr EWord)
genStorageKey = frequency
     -- array slot
    [ (4, liftM2 Expr.ArraySlotWithOffs (genByteStringKey 32) (genLit 5))
    , (4, fmap Expr.ArraySlotZero (genByteStringKey 32))
     -- mapping slot
    , (8, liftM2 Expr.MappingSlot (genByteStringKey 64) (genLit 5))
     -- small slot
    , (4, genLit 20)
    -- unrecognized slot type
    , (1, genLit 5)
    ]

genByteStringKey :: W256 -> Gen (ByteString)
genByteStringKey len = do
  b :: Word8 <- arbitrary
  pure $ BS.pack ([ 0 | _ <- [0..(len-2)]] ++ [b `mod` 5])

-- GenWriteStorageLoad
newtype GenWriteStorageLoad = GenWriteStorageLoad (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenWriteStorageLoad where
  arbitrary = do
    load <- genStorageLoad 10
    pure $ GenWriteStorageLoad load

    where
      genStorageLoad :: Int -> Gen (Expr EWord)
      genStorageLoad sz = liftM2 SLoad key subStore
        where
          subStore = genStorage (sz `div` 10)
          key = genStorageKey

data Invocation
  = SolidityCall Text [AbiValue]
  deriving Show

assertSolidityComputation :: App m => Invocation -> AbiValue -> m ()
assertSolidityComputation (SolidityCall s args) x =
  do y <- runStatements s args (abiValueType x)
     liftIO $ assertEqual (T.unpack s)
       (fmap Bytes (Just (encodeAbiValue x)))
       (fmap Bytes y)

bothM :: (Monad m) => (a -> m b) -> (a, a) -> m (b, b)
bothM f (a, a') = do
  b  <- f a
  b' <- f a'
  return (b, b')

applyPattern :: String -> TestTree  -> TestTree
applyPattern p = localOption (TestPattern (parseExpr p))

checkBadCheatCode :: Text -> Postcondition
checkBadCheatCode sig _ = \case
  (Failure _ c (Revert _)) -> case mapMaybe findBadCheatCode (concatMap flatten c.traces) of
    (s:_) -> (ConcreteBuf $ into s.unFunctionSelector) ./= (ConcreteBuf $ selector sig)
    _ -> PBool True
  _ -> PBool True
  where
    findBadCheatCode :: Trace -> Maybe FunctionSelector
    findBadCheatCode Trace { tracedata = td } = case td of
      ErrorTrace (BadCheatCode _ s) -> Just s
      _ -> Nothing

allBranchesFail :: App m => ByteString -> Maybe Sig -> m (Either [SMTCex] [Expr End])
allBranchesFail = checkPost p
  where
    p _ = \case
      Success _ _ _ _ -> PBool False
      _ -> PBool True

reachableUserAsserts :: App m => ByteString -> Maybe Sig -> m (Either [SMTCex] [Expr End])
reachableUserAsserts = checkPost (checkAssertions [0x01])

checkPost :: App m => Postcondition -> ByteString -> Maybe Sig -> m (Either [SMTCex] [Expr End])
checkPost post c sig = do
  (e, res) <- withDefaultSolver $ \s -> verifyContract s c sig [] defaultVeriOpts Nothing post
  let cexs = snd <$> mapMaybe getCex res
  case cexs of
    [] -> pure $ Right e
    cs -> pure $ Left cs

successGen :: [Prop] -> Expr End
successGen props = Success props mempty (ConcreteBuf "") mempty

-- gets the expected concrete values for symbolic abi testing
expectedConcVals :: Text -> AbiValue -> SMTCex
expectedConcVals nm val = case val of
  AbiUInt {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiInt {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiAddress {} -> mempty { addrs = Map.fromList [(SymAddr nm, truncateToAddr (mkWord val))] }
  AbiBool {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiBytes {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiArray _ _ vals -> mconcat . V.toList . V.imap (\(T.pack . show -> idx) v -> expectedConcVals (nm <> "-a-" <> idx) v) $ vals
  AbiTuple vals -> mconcat . V.toList . V.imap (\(T.pack . show -> idx) v -> expectedConcVals (nm <> "-t-" <> idx) v) $ vals
  _ -> internalError $ "unsupported Abi type " <> show nm <> " val: " <> show val <> " val type: " <> showAlter val
  where
    mkWord = word . encodeAbiValue

hexStringToByteString :: String -> BS.ByteString
hexStringToByteString hexStr
    | odd (length hexStr) = error "Hex string has an odd length"
    | otherwise = case traverse hexPairToByte (pairs hexStr) of
        Just bytes -> (BS.pack bytes)
        Nothing -> error "Invalid hex string"
  where
    -- Convert a pair of hex characters to a byte
    hexPairToByte :: (Char, Char) -> Maybe Word8
    hexPairToByte (c1, c2) = do
        b1 <- hexCharToDigit c1
        b2 <- hexCharToDigit c2
        return $ fromIntegral (b1 * 16 + b2)

    -- Convert a single hex character to its integer value
    hexCharToDigit :: Char -> Maybe Int
    hexCharToDigit c
        | c >= '0' && c <= '9' = Just (digitToInt c)
        | c >= 'a' && c <= 'f' = Just (digitToInt c)
        | c >= 'A' && c <= 'F' = Just (digitToInt c)
        | otherwise = Nothing

    -- Split a string into pairs of characters
    pairs :: [a] -> [(a, a)]
    pairs [] = []
    pairs (x:y:xs) = (x, y) : pairs xs
    pairs _ = error "Unexpected odd length"
