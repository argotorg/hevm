{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE QuasiQuotes #-}

module EVM.Basic.BasicTests (tests) where

import Control.Monad
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSLazy
import Data.Binary.Put (runPut)
import Data.Binary.Get (runGetOrFail)
import Data.Maybe
import Data.String.Here
import Data.Text qualified as T
import Data.Vector qualified as V
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Test.Tasty.HUnit
import Text.ParserCombinators.ReadP (readP_to_S)
import Witch (into)

import EVM
import EVM.ABI
import EVM.Assembler
import EVM.ConsoleLog (formatConsoleLog)
import EVM.Exec
import EVM.Fetch qualified as Fetch
import EVM.Format (hexText)
import EVM.Precompiled
import EVM.RLP
import EVM.Solidity
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Expr.Generator ()
import EVM.Expr (maybeLitByteSimp)

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testGroup "Console log formatting"
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
  , testGroup "StorageTests"
    [ test "accessStorage uses fetchedStorage" $ do
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
    , test "ABI-decode-follows-offsets" $ do
        let w :: Integer -> BS.ByteString
            w n = word256Bytes (fromInteger n)
            pad b = b <> BS.replicate (32 - BS.length b) 0
            -- tails are not back to back: a junk word sits between the head and them
            enc = w 0x60 <> w 0xa0 <> w 0xdead
               <> w 1 <> pad (hex "00")
               <> w 2 <> pad (hex "1122")
        assertEqualM "decoded"
          (AbiTuple $ V.fromList [AbiBytesDynamic (hex "00"), AbiBytesDynamic (hex "1122")])
          (decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType, AbiBytesDynamicType]) (BSLazy.fromStrict enc))
    , test "ABI-function-roundtrip" $ do
        -- Test that AbiFunction encodes/decodes correctly
        let addr = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef
        let sel = 0x12345678
        let funcVal = AbiFunction addr sel
        case runGetOrFail (getAbi AbiFunctionType) (runPut (putAbi funcVal)) of
          Right ("", _, decoded) -> assertEqualM "Function roundtrip failed" funcVal decoded
          Left (_, _, err) -> internalError $ "Decoding error: " <> err
          Right (leftover, _, _) -> internalError $ "Leftover bytes: " <> show leftover
    , test "ABI-function-encoding" $ do
        -- Test that AbiFunction encodes to correct 32-byte padded format
        let addr = 0x1234567890abcdef1234567890abcdef12345678
        let sel = 0xaabbccdd
        let funcVal = AbiFunction addr sel
        let encoded = BSLazy.toStrict $ runPut (putAbi funcVal)
        -- Should be 32 bytes: 20 addr + 4 selector + 8 padding
        assertEqualM "Encoded length should be 32" 32 (BS.length encoded)
        -- First 20 bytes should be address
        assertEqualM "Address bytes" (hex "1234567890abcdef1234567890abcdef12345678") (BS.take 20 encoded)
        -- Next 4 bytes should be selector
        assertEqualM "Selector bytes" (hex "aabbccdd") (BS.take 4 $ BS.drop 20 encoded)
        -- Last 8 bytes should be zero padding
        assertEqualM "Padding bytes" (BS.replicate 8 0) (BS.drop 24 encoded)
    , test "ABI-function-parsing" $ do
        -- Test parseAbiValue for function type
        let hexStr = "0x1234567890abcdef1234567890abcdef12345678aabbccdd"
        case readP_to_S (parseAbiValue AbiFunctionType) hexStr of
          [(AbiFunction addr sel, "")] -> do
            assertEqualM "Parsed address" 0x1234567890abcdef1234567890abcdef12345678 addr
            assertEqualM "Parsed selector" 0xaabbccdd sel
          [] -> internalError "Failed to parse function value"
          other -> internalError $ "Unexpected parse result: " <> show other
    , test "ABI-function-parsing-rejects-wrong-length" $ do
        -- 23 bytes (too short)
        let shortHex = "0x1234567890abcdef1234567890abcdef123456aabbcc"
        case readP_to_S (parseAbiValue AbiFunctionType) shortHex of
          [] -> pure ()  -- Expected: parsing should fail
          _ -> internalError "Should reject 23-byte function value"
        -- 25 bytes (too long)
        let longHex = "0x1234567890abcdef1234567890abcdef12345678aabbccddee"
        case readP_to_S (parseAbiValue AbiFunctionType) longHex of
          [(_, "")] -> internalError "Should reject 25-byte function value"
          _ -> pure ()  -- Expected: either fails or has leftover
    , test "ABI-bytes-parsing-validates-length" $ do
        -- bytes4 should require exactly 4 bytes
        let fourBytes = "0xaabbccdd"
        case readP_to_S (parseAbiValue (AbiBytesType 4)) fourBytes of
          [(AbiBytes 4 bs, "")] -> assertEqualM "bytes4 value" (hex "aabbccdd") bs
          _ -> internalError "Failed to parse bytes4"
        -- bytes4 should reject 3 bytes
        let threeBytes = "0xaabbcc"
        case readP_to_S (parseAbiValue (AbiBytesType 4)) threeBytes of
          [] -> pure ()  -- Expected: parsing should fail
          _ -> internalError "Should reject 3-byte value for bytes4"
    , test "ABI-user-defined-enum-type" $ do
        -- User-defined types like enums (e.g. "Order.OrderType") should parse as uint8
        assertEqualM "qualified enum" (Just (AbiUIntType 8)) (parseTypeName mempty "Order.OrderType")
        assertEqualM "simple enum" (Just (AbiUIntType 8)) (parseTypeName mempty "MyEnum")
        -- Should also work with array suffixes
        assertEqualM "enum array" (Just (AbiArrayDynamicType (AbiUIntType 8))) (parseTypeName mempty "Order.OrderType[]")
        -- Standard types should still work
        assertEqualM "uint256" (Just (AbiUIntType 256)) (parseTypeName mempty "uint256")
        assertEqualM "address" (Just AbiAddressType) (parseTypeName mempty "address")
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
          , test "fail on v other than 27 or 28" $ forM_ [0x1d, 0x1e] $ \v -> do
              let
                h = BS.replicate 31 0 <> BS.singleton 1
                vw = BS.replicate 31 0 <> BS.singleton v
                r = BS.replicate 31 0 <> BS.singleton 2
                s = BS.replicate 31 0 <> BS.singleton 1
              assertEqualM "v must be rejected" Nothing (execute 1 (h <> vw <> r <> s) 32)
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
      , testGroup "Unimplemented"
          [ test "concrete call gives NonexistentPrecompile" $ forM_ [0x0a, 0x10, 0x11, 0x100 :: Addr] $ \a -> do
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
              vm' <- Stepper.interpret (Fetch.zero 0 Nothing 1024) vm Stepper.runFully
              case vm'.result of
                Just (VMFailure (NonexistentPrecompile a')) -> assertEqualM "wrong address" a a'
                r -> liftIO $ assertFailure $ "unexpected result for " <> show a <> ": " <> show r
          , test "symbolic call gives partial" $ do
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
    , testProperty "word256" $ \a ->
        word256 a == slow_word256 a
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
  ]

-- includes shaving off 4 byte function sig
decodeAbiValues :: [AbiType] -> ByteString -> [AbiValue]
decodeAbiValues types bs =
  let xy = case decodeAbiValue (AbiTupleType $ V.fromList types) (BS.fromStrict (BS.drop 4 bs)) of
        AbiTuple xy' -> xy'
        _ -> internalError "AbiTuple expected"
  in V.toList xy

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
