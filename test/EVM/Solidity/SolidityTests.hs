{-# LANGUAGE QuasiQuotes #-}

module EVM.Solidity.SolidityTests (tests) where

import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Control.Monad.Reader (ReaderT)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Either
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Tuple.Extra
import Data.Vector qualified as V
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Test.Tasty.HUnit
import Text.ParserCombinators.ReadP (readP_to_S)
import Witch (unsafeInto)

import Optics.Core hiding (pre, re, elements)

import EVM.ABI
import EVM.Assembler
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Solidity
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.SymExec.Calldata
import EVM.SymExec.Cex
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Expr (maybeLitByteSimp)

import EVM.Test.Helpers
import EVM.Test.Asm (AsmOp(..), asm)

tests :: [TestTree]
tests =
  [ testGroup "Solidity-Expressions"
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
              frag = [symAbiArg 64 "y" (AbiTupleType $ V.fromList [abiValueType y])]
              (hevmEncoded, _) = first (Expr.drop 4) $ combineFragments frag (ConcreteBuf "")
              expectedVals = expectedConcVals "y" (AbiTuple . V.fromList $ [y])
              hevmConcretePre = fromRight (error "cannot happen") $ subModel expectedVals hevmEncoded
              hevmConcrete = case Expr.simplify hevmConcretePre of
                               ConcreteBuf b -> b
                               buf -> internalError ("valMap: " <> show expectedVals <> "\ny:" <> show y <> "\n" <> "buf: " <> show buf)
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

  , testGroup "Dynamic-bytes-concretization"
    [ test "bytes-length-cex" $ do
        -- A function that asserts bytes.length == 0 should have a counterexample
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(bytes calldata data) public pure {
                assert(data.length == 0);
              }
            } |]
        let sig = Just $ Sig "fun(bytes)" [AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        -- bytes args don't produce a per-path Partial; they attach a program-wide Caveat
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should find counterexample" 1 numCexes
    , test "bytes-content-cex" $ do
        -- Should find bytes starting with 0xdead
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(bytes calldata data) public pure {
                if (data.length >= 2) {
                  assert(data[0] != 0xde || data[1] != 0xad);
                }
              }
            } |]
        let sig = Just $ Sig "fun(bytes)" [AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should find counterexample" 1 numCexes
    , test "bytes-no-cex" $ do
        -- A trivially true assertion should have no counterexample (but still partial)
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(bytes calldata data) public pure {
                assert(data.length <= data.length);
              }
            } |]
        let sig = Just $ Sig "fun(bytes)" [AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should have no counterexample" 0 numCexes
    , test "bytes-with-uint-arg" $ do
        -- bytes alongside a uint256 argument
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(uint256 x, bytes calldata data) public pure {
                if (data.length > 0 && x == 42) {
                  assert(false);
                }
              }
            } |]
        let sig = Just $ Sig "fun(uint256,bytes)" [AbiUIntType 256, AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should find counterexample" 1 numCexes
    -- Tests that bugs beyond maxDynSize are reported via a caveat, not as false passes
    , test "bytes-beyond-bound-length-check" $ do
        -- Bug only triggers when bytes.length > 100; with default maxDynSize=64, should NOT find cex
        -- but must report a caveat (input domain was bounded)
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(bytes calldata data) public pure {
                if (data.length > 100) {
                  assert(false);
                }
              }
            } |]
        let sig = Just $ Sig "fun(bytes)" [AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should not find cex (bug is beyond bound)" 0 numCexes
    , test "bytes-beyond-bound-content-check" $ do
        -- Bug triggers only when byte at index 80 has a specific value; beyond default maxDynSize=64
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(bytes calldata data) public pure {
                if (data.length > 80 && data[80] == 0xff) {
                  assert(false);
                }
              }
            } |]
        let sig = Just $ Sig "fun(bytes)" [AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should not find cex (bug is beyond bound)" 0 numCexes
    , test "bytes-beyond-bound-sum-check" $ do
        -- Bug triggers when sum of first 128 bytes overflows; requires > 64 bytes
        Just c <- solcRuntime "C" [i|
            contract C {
              function fun(bytes calldata data) public pure {
                if (data.length >= 128) {
                  uint256 sum = 0;
                  for (uint i = 0; i < 128; i++) {
                    sum += uint8(data[i]);
                  }
                  assert(sum < 1000);
                }
              }
            } |]
        let sig = Just $ Sig "fun(bytes)" [AbiBytesDynamicType]
        (e, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        (_, caveats) <- mkCalldata sig []
        assertBoolM "bounded dyn arg must not produce a synthetic partial" $ not (any isPartial e)
        assertBoolM "bounded dyn arg must produce a caveat" $ not (null caveats)
        let numCexes = sum $ map (fromEnum . isCex) ret
        assertEqualM "should not find cex (bug requires 128 bytes, bound is 64)" 0 numCexes
    ]

  , testGroup "Concrete-args"
    [ testProperty "arg-roundtrip" $ forAll (arbitrary >>= \t -> (,) t <$> genAbiValue t) $
      \(t, v) -> makeAbiValue t (renderArg v) === v
    , testProperty "concrete-args-calldata" $ forAll genArgs $ \vs -> prop $ do
        let types = map abiValueType vs
            sig = "f(" <> T.intercalate "," (map abiTypeSolidity types) <> ")"
            expected = selector sig <> encodeAbiValue (AbiTuple (V.fromList vs))
        (cd, _, _) <- symCalldata sig types (map renderArg vs) (AbstractBuf "txdata")
        let got = [Expr.readByte (Lit (unsafeInto k)) cd | k <- [0 .. BS.length expected - 1]]
        assertEqualM "calldata mismatch" (map LitByte (BS.unpack expected)) got
    , test "negative-int-arg" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function g(int8 x) external pure { assert(x >= 0); }
            } |]
        let sig = Just $ Sig "g(int8)" [AbiIntType 8]
        (_, neg) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig ["-1"] defaultVeriOpts
        assertEqualM "-1 must violate the assertion" 1 (sum $ map (fromEnum . isCex) neg)
        (_, pos) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig ["5"] defaultVeriOpts
        assertEqualM "5 must not violate the assertion" 0 (sum $ map (fromEnum . isCex) pos)
    , test "int-arg-out-of-range" $ do
        let parses v = not . null $ [x | (x, "") <- readP_to_S (parseAbiValue (AbiIntType 8)) v]
        assertBoolM "-128 is an int8" $ parses "-128"
        assertBoolM "127 is an int8" $ parses "127"
        assertBoolM "-129 is not an int8" $ not (parses "-129")
        assertBoolM "0xff is not an int8" $ not (parses "0xff")
    , test "dynamic-and-static-args" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function t(bytes memory a, uint256 y, string memory b, uint8[2] memory c) external pure {
                assert(!(a.length == 33 && a[32] == 0x42 && bytes(b).length == 2 && bytes(b)[1] == "z" && c[1] == 7 && y > 100));
              }
            } |]
        let sig = Just $ Sig "t(bytes,uint256,string,uint8[2])"
                    [AbiBytesDynamicType, AbiUIntType 256, AbiStringType, AbiArrayType 2 (AbiUIntType 8)]
            a = "0x" <> concat (replicate 32 "00") <> "42"
            check args = fmap snd $ withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig args defaultVeriOpts
        symY <- check [a, "<symbolic>", "\"yz\"", "[0,7]"]
        assertEqualM "symbolic y must reach the assertion" 1 (sum $ map (fromEnum . isCex) symY)
        concY <- check [a, "50", "\"yz\"", "[0,7]"]
        assertEqualM "y = 50 must not reach the assertion" 0 (sum $ map (fromEnum . isCex) concY)
    , test "bytesN-arg" $ do
        Just c <- solcRuntime "C" [i|
            contract C {
              function h(bytes32 x, uint256 y) external pure { assert(x != bytes32(y)); }
            } |]
        let sig = Just $ Sig "h(bytes32,uint256)" [AbiBytesType 32, AbiUIntType 256]
        (_, ret) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c sig ["0x" <> replicate 63 '0' <> "1"] defaultVeriOpts
        assertEqualM "y = 1 must violate the assertion" 1 (sum $ map (fromEnum . isCex) ret)
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
        withSolvers Bitwuzla 1 Nothing defMemLimit $ \s -> do
          let calldata = (WriteWord (Lit 0x0) (Var "u") (ConcreteBuf ""), [])
          initVM <- liftIO $ stToIO $ abstractVM calldata initCode Nothing True
          let iterConf = IterConfig {maxIter=Nothing, maxConcreteIter=Nothing, askSmtIters=1, loopHeuristic=StackBased }
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
        (_, res) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        assertEqualM "Must be QED" [] res
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
        (_, [Cex _]) <- withDefaultSolver $
          \s -> checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
        pure ()
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
          let iterConf = IterConfig {maxIter=Nothing, maxConcreteIter=Nothing, askSmtIters=1, loopHeuristic=StackBased }
          paths <- interpret (Fetch.noRpcFetcher s) iterConf vm runExpr noopPathHandler
          let exprSimp = map Expr.simplify paths
          assertBoolM "expected partial execution" (any isPartial exprSimp)
    ]
  , testGroup "Unresolved link detection"
    [ testCase "holes-detected" $
        assertBool "linker hole not detected" (containsLinkerHole "608060405273__$f3cbc3eb14e5bd0705af404abcf6f741ec$__63ab5c1ffe")
    , testCase "no-false-positives" $
        assertBool "false positive" (not $ containsLinkerHole "0x6080604052348015600f57600080fd5b50")
    , testCase "hole-of-the-wrong-length" $
        assertBool "false positive" (not $ containsLinkerHole "73__$f3cbc3eb14e5bd0705af404abcf6f741e$__")
    ]

  , testGroup "metadata stripper" $
    [ testCase ("strips-" <> name) $ do
        let code = asm [I (OpPush (Lit 1)), I OpPop, I OpStop] <> hex "fe"
        assertEqual "failed to strip metadata" code (stripBytecodeMetadata (code <> meta))
    | (name, meta) <-
      [ ("bzzr0-solc-0.5.8", hex "a165627a7a72305820" <> metadataHash 32 <> hex "0029")
      , ("bzzr0-solc-0.5.9", hex "a265627a7a72305820" <> metadataHash 32 <> solcVersion "000509" <> hex "0032")
      , ("bzzr1-solc-0.5.11", hex "a265627a7a72315820" <> metadataHash 32 <> solcVersion "00050b" <> hex "0032")
      , ("ipfs-solc-0.6.0", hex "a264697066735822" <> metadataHash 34 <> solcVersion "000606" <> hex "0033")
      ]
    ] ++
    [ testCase "strips-metadata-before-constructor-args" $ do
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
  ]
  where
    (===>) = assertSolidityComputation

prop :: Testable prop => ReaderT Env IO prop -> Property
prop a = ioProperty $ runEnv testEnv a

-- | Takes a creation code and some calldata, runs the creation code, and calls the resulting contract with the provided calldata
runSimpleVM :: App m => ByteString -> ByteString -> m (Maybe ByteString)
runSimpleVM x ins = do
  loadVM x >>= \case
    Nothing -> pure Nothing
    Just vm -> do
     let calldata = (ConcreteBuf ins)
         vm' = set (#state % #calldata) calldata vm
     res <- Stepper.interpret (Fetch.zero 0 Nothing 1024) vm' Stepper.execFully
     case res of
       Right (ConcreteBuf bs) -> pure $ Just bs
       s -> internalError $ show s

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

-- | An '--arg' string that 'makeAbiValue' parses back to the value
renderArg :: AbiValue -> String
renderArg = \case
  AbiString s -> show (map (toEnum . fromIntegral) (BS.unpack s) :: String)
  AbiArrayDynamic _ v -> "[" <> List.intercalate "," (renderArg <$> V.toList v) <> "]"
  AbiArray _ _ v -> "[" <> List.intercalate "," (renderArg <$> V.toList v) <> "]"
  v -> show v

genArgs :: Gen [AbiValue]
genArgs = do
  n <- chooseInt (1, 4)
  vectorOf n (scale (`div` 2) arbitrary)

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

-- | Stands in for the swarm or ipfs hash in solc's CBOR metadata
metadataHash :: Int -> ByteString
metadataHash n = BS.replicate n 0xab

solcVersion :: ByteString -> ByteString
solcVersion v = hex ("64736f6c6343" <> v)
