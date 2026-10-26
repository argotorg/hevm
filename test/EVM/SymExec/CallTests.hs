{-# LANGUAGE QuasiQuotes #-}

module EVM.SymExec.CallTests (tests) where

import Control.Monad
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Control.Exception (ErrorCall(..), throwIO, try)
import System.Timeout (timeout)
import Data.ByteString qualified as BS
import Data.Either
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import Witch (into)

import EVM.ABI
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (hexByteString)
import EVM.Solidity
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.SymExec.Calldata
import EVM.SymExec.Cex
import EVM.CexReplay
import EVM.Types hiding (Env)
import EVM.Effects

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testGroup "Symbolic Addresses"
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
            let ca = fromJust (Map.lookup (SymAddr "create-entrypoint-0") store)
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
          check a (SymAddr "create-entrypoint-0")
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
          check a (SymAddr "create-entrypoint-0")
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
        (paths, _) <- withDefaultSolver $ \s ->
          verifyContract s c Nothing [] defaultVeriOpts Nothing (checkAssertions [0x1])
        assertBoolM "the cheatcode must leave the path partial" (hasCheatCodeFailed "load(address,bytes32)" paths)
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
        (paths, _) <- withDefaultSolver $ \s ->
          verifyContract s c Nothing [] defaultVeriOpts Nothing (checkAssertions [0x1])
        assertBoolM "the cheatcode must leave the path partial" (hasCheatCodeFailed "store(address,bytes32,bytes32)" paths)
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
        let addrs = [T.pack . show . Addr $ a | a <- [0x0..0x11] ++ [0x100]]
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
                assert(msg.sender != address(0x12));
              }
            }
          |]
        Just b <- solcRuntime "B"
          [i|
            contract B {
              function f() external {
                assert(block.coinbase != address(0x13));
              }
            }
          |]
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function f() external {
                assert(tx.origin != address(0x14));
              }
            }
          |]
        Just d <- solcRuntime "D"
          [i|
            contract D {
              function f() external {
                assert(address(this) != address(0x15));
              }
            }
          |]
        [acex,bcex,ccex,dcex] <- forM [a,b,c,d] $ \con -> do
          Left [cex] <- reachableUserAsserts con Nothing
          assertEqualM "wrong number of addresses" 1 (length (Map.keys cex.addrs))
          pure cex

        assertEqualM "wrong model for a" (Addr 0x12) (fromJust $ Map.lookup (SymAddr "caller") acex.addrs)
        assertEqualM "wrong model for b" (Addr 0x13) (fromJust $ Map.lookup (SymAddr "coinbase") bcex.addrs)
        assertEqualM "wrong model for c" (Addr 0x14) (fromJust $ Map.lookup (SymAddr "origin") ccex.addrs)
        assertEqualM "wrong model for d" (Addr 0x15) (fromJust $ Map.lookup (SymAddr "entrypoint") dcex.addrs)
    ]
  , testGroup "Symbolic execution"
      [
     test "create-returns-symbolic-size" $ do
        -- initcode returns and(callvalue, 0xf) bytes; the parent asserts the
        -- created code is not 5 bytes long
        let c = fromJust $ hexByteString
                  "7f600f34165ff300000000000000000000000000000000000000000000000000005f5260065f5f35f03b600514603157005bfe"
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        assertBoolM "unexpected partial execution" $ not (any isPartial e)
        assertBoolM "5-byte code must be reachable" $ any isCex ret
    , test "worker-exception-propagates" $ do
        let c = fromJust $ hexByteString "00"
            throwingHandler _ _ = liftIO $ throwIO (ErrorCall "worker boom")
        vm <- liftIO $ stToIO $ abstractVM (ConcreteBuf "", []) c Nothing False
        let iterConf = IterConfig { maxIter = Nothing, maxConcreteIter = Nothing, askSmtIters = 1, loopHeuristic = StackBased }
        res <- withDefaultSolver $ \s -> withRunInIO $ \runInIO -> timeout 30000000 $
                 (try (runInIO (interpret (Fetch.noRpcFetcher s) iterConf vm runExpr throwingHandler)) :: IO (Either ErrorCall [()]))
        case res of
          Just (Left (ErrorCall msg)) -> assertEqualM "rethrown error" "worker boom" msg
          Just (Right _) -> liftIO $ assertFailure "expected the worker's exception"
          Nothing -> liftIO $ assertFailure "interpret hung after a worker exception"
    , test "address-sized-memory-access-charges-gas" $ do
        -- deploys ADDRESS PUSH0 RETURN: the return size is the address, as a WAddr
        Just vm <- loadVM (fromJust $ hexByteString "62305ff35f526003601df3")
        res <- Stepper.interpret (Fetch.zero 0 Nothing 1024) vm Stepper.execFully
        case res of
          Left _ -> pure ()
          r -> liftIO $ assertFailure $ "returning 2^160 bytes must fail, got " <> show r
    , test "decomposed-cex-storage-replays" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              mapping(uint256 => uint256) m;
              mapping(uint256 => uint256) n;
              function f(uint256 x) external view { assert(!(m[x] == 3 && n[x] == 4)); }
            } |]
        ((cd, cdProps), _) <- mkCalldata (Just (Sig "f(uint256)" [AbiUIntType 256])) []
        vm <- liftIO $ stToIO $ abstractVM (cd, cdProps) c Nothing False
        let post = checkAssertions defaultPanicCodes
        withDefaultSolver $ \s -> do
          (_, res) <- verify s (Fetch.oracle s Nothing Fetch.noRpc) defaultVeriOpts vm post Nothing
          case mapMaybe getCex res of
            [(leaf, cex)] -> do
              let x = maybe 0 (word . BS.take 32 . BS.drop 4) (cexCalldata cd cex)
                  slot p = keccak' (word256Bytes x <> word256Bytes p)
                  st = Map.findWithDefault mempty (SymAddr "entrypoint") cex.store
              assertEqualM "m[x] at its real slot" (Just 3) (Map.lookup (slot 0) st)
              assertEqualM "n[x] at its real slot" (Just 4) (Map.lookup (slot 1) st)
              replayed <- replaySymCex (Fetch.oracle s Nothing Fetch.noRpc) post vm leaf cex
              assertEqualM "replay" (Right True) replayed
            r -> liftIO $ assertFailure $ "expected one counterexample, got " <> show r
    , test "require-test" $ do
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
        pure ()
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
       pure ()
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
       pure ()
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
      (_, []) <- withDefaultSolver $ \s ->
        checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      pure ()
    , test "call-to-unknown-code-writes-output-region" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function f(address a) public view {
                uint r;
                assembly {
                    mstore(0, 0x42)
                    pop(staticcall(gas(), a, 0, 0, 0, 32))
                    r := mload(0)
                }
                assert(r == 0x42);
            }
        }
        |]
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(address)" [AbiAddressType])) [] defaultVeriOpts
      assertBoolM "the output of the callee must overwrite memory" (any isCex ret)
    , test "call-to-unknown-code-short-output-keeps-memory" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
            function f(address a) public view {
                uint r;
                uint first;
                uint size;
                assembly {
                    mstore(0, 0x42)
                    pop(staticcall(gas(), a, 0, 0, 0, 32))
                    r := mload(0)
                    size := returndatasize()
                    if eq(size, 1) {
                        returndatacopy(0x20, 0, 1)
                        first := mload(0x20)
                    }
                }
                if (size == 0) assert(r == 0x42);
                if (size == 1) assert(r == first | 0x42);
            }
        }
        |]
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(address)" [AbiAddressType])) [] defaultVeriOpts
      assertEqualM "only the bytes the callee returned are overwritten" [] ret
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
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
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
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
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
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
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
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
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
  ]
  ]

hasCheatCodeFailed :: Text -> [Expr End] -> Bool
hasCheatCodeFailed sig = any $ \case
  Partial _ _ (CheatCodeFailed _ _ s _) -> into s.unFunctionSelector == selector sig
  _ -> False
