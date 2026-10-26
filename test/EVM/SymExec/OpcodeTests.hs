{-# LANGUAGE QuasiQuotes #-}

module EVM.SymExec.OpcodeTests (tests) where

import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Data.Bits hiding (And, Xor)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String.Here
import Test.Tasty
import Test.Tasty.HUnit

import Optics.Core hiding (pre, re, elements)

import EVM
import EVM.ABI
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (hexText)
import EVM.SMT
import EVM.Solidity
import EVM.Solvers
import EVM.SymExec
import EVM.Types hiding (Env)
import EVM.Effects

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testGroup "Symbolic execution"
      [ test "jump-symbolic" $ do
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
      (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
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
        pure ()
     ,
     test "opcode-clz" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function clz_test(uint256 x) internal pure returns (uint256 result) {
                  assembly {
                      result := clz(x)
                  }
              }

              function fun() external pure {
                assert(clz_test(0) == 256);
                assert(clz_test(1) == 255);
                assert(clz_test(2) == 254);
                assert(clz_test(2) == 254);
                // 61853446846231190821175268292818646713405929256851257084424727564423478318049
                // is larger than 2**255, so CLZ should be 0
                assert(clz_test(61853446846231190821175268292818646713405929256851257084424727564423478318049) == 0);
                // 1402344919110095602128912437416037586276662158775737295210557361797392888602
                // is larger than 2**249 but smaller than 2**250, so CLZ should be 6
                assert(clz_test(1402344919110095602128912437416037586276662158775737295210557361797392888602) == 6);
              }
             }
            |]
        (_, r) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun()" [])) [] defaultVeriOpts
        assertEqualM "CLZ. expected QED"  [] r
     ,
     test "opcode-clz-negative-test" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function clz_test(uint256 x) internal pure returns (uint256 result) {
                  assembly {
                      result := clz(x)
                  }
              }

              function fun() external pure {
                assert(clz_test(0) == 255); // wrong, should be 256
              }
             }
            |]
        (_, r) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun()" [])) [] defaultVeriOpts
        case r of
          [Cex _] -> assertEqualM "CLZ. expected CEX" () ()
          _ -> liftIO $ assertFailure "CLZ. Expected exactly one Cex"
     ,
     test "opcode-clz-negative-test2" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function clz_test(uint256 x) internal pure returns (uint256 result) {
                  assembly {
                      result := clz(x)
                  }
              }

              function fun() external pure {
                // 22 = 10110 -- i.e. 5 bits
                assert(clz_test(22) == 250); // should be 251: 256 - 5 = 251
              }
             }
            |]
        (_, r) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun()" [])) [] defaultVeriOpts
        case r of
          [Cex _] -> assertEqualM "CLZ. expected CEX" () ()
          _ -> liftIO $ assertFailure "CLZ. Expected exactly one Cex"
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
        pure ()
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
        pure ()
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
        pure ()
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
          (_, [Cex _]) -> do
            assertEqualM "Addition is not commutative... that's wrong" False True
          (_, []) -> pure ()
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
        pure ()
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
        (_, []) <- withDefaultSolver $ \s ->
          verifyContract s safeAdd sig [] defaultVeriOpts (Just pre) post
        pure ()
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
        (_, []) <- withDefaultSolver $ \s ->
          verifyContract s safeAdd (Just (Sig "add(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts (Just pre) post
        pure ()
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
        (_, []) <- withDefaultSolver $ \s ->
          verifyContract s c sig [] defaultVeriOpts (Just pre) post
        pure ()
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
            (_, []) <- withSolvers Z3 4 Nothing defMemLimit $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "hello(address)" [AbiAddressType])) [] defaultVeriOpts
            pure ()
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
          pure ()
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
          assertEqualM "Catch storage collisions" x y
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
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          pure ()
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
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "deposit(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          pure ()
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
          pure ()
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
          pure ()
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
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          pure ()
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
          (_, []) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withBitwuzlaSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
            (calldata, _) <- mkCalldata (Just (Sig "call_A()" [])) []
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
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "kecc(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "kecc(uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
          (_, []) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          pure ()
        ,
        test "safemath-distributivity-yul" $ do
          let yulsafeDistributivity = hex "6355a79a6260003560e01c14156016576015601f565b5b60006000fd60a1565b603d602d604435600435607c565b6039602435600435607c565b605d565b6052604b604435602435605d565b600435607c565b141515605a57fe5b5b565b6000828201821115151560705760006000fd5b82820190505b92915050565b6000818384048302146000841417151560955760006000fd5b82820290505b92915050565b"
          (calldata, _) <- mkCalldata (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) []
          vm <- liftIO $ stToIO $ abstractVM calldata yulsafeDistributivity Nothing False
          (_, []) <-  withDefaultSolver $ \s -> verify s (Fetch.noRpcFetcher s) defaultVeriOpts vm (checkAssertions defaultPanicCodes) Nothing
          pure ()
        ,
        -- Native arithmetic proves this identity without costly abstraction refinement.
        testCase "safemath-distributivity-sol" $ runEnv (testEnv { config = testEnv.config { abstractArith = False } }) $ do
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

          (_, []) <- withSolvers Bitwuzla 1 (Just 99999999) defMemLimit $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          pure ()
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
        ,
        test "storage-decompose-array-below-small-slot" $ do
          -- runtime bytecode from issue #1086
          let c = hexText "0x60806040526004361060ab57635cb32be560e11b5f1960e01b5f35160360ab5760206004360312341760ab5760016004351160ab57600154600160401b81101560af576002549060015f526001810160015560018160205f200155606060e7565b606660e7565b60015481101560c05760ff9160999160015f52600260043515179060205f200154108060ff195f5416175f551501610137565b90549060031b1c161560d2575f604051f35b5f5ffd5b50634e487b7160e01b5f52604160df565b5050634e487b7160e01b5f52603260df565b634e487b7160e01b5f5260015b60045260245ffd5b600254600160401b811061010b575050634e487b7160e01b5f52604160045260245ffd5b60025f526001810160025560f88160051c60205f20019160031b1660ff6001821b911b19825416179055565b6002548110610156575050634e487b7160e01b5f52603260045260245ffd5b60025f52601f81169060051c60205f20019156fea2646970667358221220822df62052651071edfff3b72f120ff46df11bd05f5206f43d69ce0ae82c110764736f6c637816736f6c783a302e312e383b736f6c633a302e382e33340047"
          (calldata, _) <- mkCalldata (Just (Sig "check_entrypoint(bool)" [AbiBoolType])) []
          vm <- liftIO $ stToIO $ loadEmptySymVM (RuntimeCode (ConcreteRuntimeCode c)) (Lit 0) calldata
          (_, []) <- withDefaultSolver $ \s ->
            verify s (Fetch.noRpcFetcher s) defaultVeriOpts vm (checkAssertions defaultPanicCodes) Nothing
          pure ()
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
          pure ()
  ]
  ]

withCVC5Solver :: App m => (SolverGroup -> m a) -> m a
withCVC5Solver = withSolvers CVC5 3 Nothing defMemLimit

getStaticAbiArgs :: Int -> VM Symbolic -> [Expr EWord]
getStaticAbiArgs n vm =
  let cd = vm.state.calldata
  in decodeStaticArgs 4 n cd
