module EVM.Encoding.EncodingTests (tests) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSLazy
import Data.Binary.Put (runPut)
import Data.Binary.Get (runGetOrFail)
import Data.Vector qualified as V
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Text.ParserCombinators.ReadP (readP_to_S)

import EVM.ABI
import EVM.RLP
import EVM.Types hiding (Env)
import EVM.Expr.Generator ()

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testGroup "ABI"
    [ testProperty "put-get-inverse" $ \x ->
        case runGetOrFail (getAbi (abiValueType x)) (runPut (putAbi x)) of
          Right ("", _, x') -> x' == x
          _ -> False
    , test "negative-small-int" $ do
        let bs = hex "ffffd6" -- -42 as int24
        let padded = BS.replicate (32 - BS.length bs) 0 <> bs -- padded to 32 bytes
        let withSelector = BS.replicate 4 0 <> padded -- added extra 4 bytes, simulating selector
        case decodeAbiValues [AbiIntType 24] withSelector of
          [AbiInt 24 val] -> assertEqualM "Incorrectly decoded int24 value" (-42) val
          _ -> internalError "Error in decoding function"
    , test "decode-follows-offsets" $ do
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
    , test "function-roundtrip" $ do
        -- Test that AbiFunction encodes/decodes correctly
        let addr = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef
        let sel = 0x12345678
        let funcVal = AbiFunction addr sel
        case runGetOrFail (getAbi AbiFunctionType) (runPut (putAbi funcVal)) of
          Right ("", _, decoded) -> assertEqualM "Function roundtrip failed" funcVal decoded
          Left (_, _, err) -> internalError $ "Decoding error: " <> err
          Right (leftover, _, _) -> internalError $ "Leftover bytes: " <> show leftover
    , test "function-encoding" $ do
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
    , test "function-parsing" $ do
        -- Test parseAbiValue for function type
        let hexStr = "0x1234567890abcdef1234567890abcdef12345678aabbccdd"
        case readP_to_S (parseAbiValue AbiFunctionType) hexStr of
          [(AbiFunction addr sel, "")] -> do
            assertEqualM "Parsed address" 0x1234567890abcdef1234567890abcdef12345678 addr
            assertEqualM "Parsed selector" 0xaabbccdd sel
          [] -> internalError "Failed to parse function value"
          other -> internalError $ "Unexpected parse result: " <> show other
    , test "function-parsing-rejects-wrong-length" $ do
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
    , test "bytes-parsing-validates-length" $ do
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
    , test "user-defined-enum-type" $ do
        -- User-defined types like enums (e.g. "Order.OrderType") should parse as uint8
        assertEqualM "qualified enum" (Just (AbiUIntType 8)) (parseTypeName mempty "Order.OrderType")
        assertEqualM "simple enum" (Just (AbiUIntType 8)) (parseTypeName mempty "MyEnum")
        -- Should also work with array suffixes
        assertEqualM "enum array" (Just (AbiArrayDynamicType (AbiUIntType 8))) (parseTypeName mempty "Order.OrderType[]")
        -- Standard types should still work
        assertEqualM "uint256" (Just (AbiUIntType 256)) (parseTypeName mempty "uint256")
        assertEqualM "address" (Just AbiAddressType) (parseTypeName mempty "address")
    ]
  , testGroup "Byte/word encoding"
    [ testProperty "padLeft-length" $ \n (Bytes bs) ->
        BS.length (padLeft n bs) == max n (BS.length bs)
    , testProperty "padLeft-identity" $ \(Bytes bs) ->
        padLeft (BS.length bs) bs == bs
    , testProperty "padRight-length" $ \n (Bytes bs) ->
        BS.length (padLeft n bs) == max n (BS.length bs)
    , testProperty "padRight-identity" $ \(Bytes bs) ->
        padLeft (BS.length bs) bs == bs
    , testProperty "padLeft-zeroing" $ \(NonNegative n) (Bytes bs) ->
        let x = BS.take n (padLeft (BS.length bs + n) bs)
            y = BS.replicate n 0
        in x == y
    , testProperty "word256Bytes" $ \w ->
        word256Bytes w == slow_word256Bytes w
    , testProperty "word160Bytes" $ \a ->
        word160Bytes a == slow_word160Bytes a
    , testProperty "word256" $ \a ->
        word256 a == slow_word256 a
    ]
  , testGroup "RLP encodings"
    [ testProperty "decode-is-a-retraction-bytes" $ \(Bytes bs) ->
      rlpdecode (rlpencode (BS bs)) == Just (BS bs)
    , testProperty "encode-is-a-partial-inverse-bytes" $ \(Bytes bs) ->
        case rlpdecode bs of
          Just r -> rlpencode r == bs
          Nothing -> True
    ,  testProperty "decode-is-a-retraction-rlp" $ \(RLPData r) ->
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
