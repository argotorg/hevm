module EVM.ConsoleLog
  ( formatConsoleLog
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Lazy (toStrict)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text, pack, intercalate)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T

import EVM.ABI (AbiType(..), AbiValue(..), decodeBuf, AbiVals(..))
import EVM.Types (Expr(..), EType(..), FunctionSelector(..), abiKeccak, word32)

-- | Try to decode and format a console.log calldata buffer.
-- Returns a human-readable representation of the log message.
formatConsoleLog :: Expr Buf -> Text
formatConsoleLog (ConcreteBuf bs) = formatConsoleLogBS bs
formatConsoleLog _ = "<symbolic console.log>"

formatConsoleLogBS :: ByteString -> Text
formatConsoleLogBS bs
  | BS.length bs < 4 = "console::log()"
  | otherwise =
      let selector = FunctionSelector (word32 (BS.unpack (BS.take 4 bs)))
          payload = BS.drop 4 bs
      in case Map.lookup selector consoleLogSigs of
        Just (_, types) ->
          case decodeBuf types (ConcreteBuf payload) of
            (CAbi vals, _) -> "console::log(" <> intercalate ", " (map showAbiVal vals) <> ")"
            _ -> "console::log(" <> hexBS bs <> ")"
        Nothing -> "console::log(" <> hexBS bs <> ")"
  where
    hexBS b = "0x" <> T.decodeUtf8 (toStrict (toLazyByteString (byteStringHex b)))

-- | Format an ABI value for console output
showAbiVal :: AbiValue -> Text
showAbiVal (AbiString s) = T.pack (show (Char8.unpack s))
showAbiVal (AbiAddress addr) = pack (show addr)
showAbiVal (AbiBool b) = if b then "true" else "false"
showAbiVal v = pack (show v)

-- | Map from 4-byte selector to (display name, parameter types) for all
-- console.log overloads.
consoleLogSigs :: Map FunctionSelector (Text, [AbiType])
consoleLogSigs = Map.fromList
  [ sig "log()"                  []
  -- single param
  , sig "log(bool)"              [AbiBoolType]
  , sig "log(address)"           [AbiAddressType]
  , sig "log(uint256)"           [AbiUIntType 256]
  , sig "log(int256)"            [AbiIntType 256]
  , sig "log(string)"            [AbiStringType]
  , sig "log(bytes)"             [AbiBytesDynamicType]
  -- two params
  , sig "log(bool,bool)"                [AbiBoolType, AbiBoolType]
  , sig "log(bool,address)"             [AbiBoolType, AbiAddressType]
  , sig "log(bool,uint256)"             [AbiBoolType, AbiUIntType 256]
  , sig "log(bool,string)"              [AbiBoolType, AbiStringType]
  , sig "log(address,bool)"             [AbiAddressType, AbiBoolType]
  , sig "log(address,address)"          [AbiAddressType, AbiAddressType]
  , sig "log(address,uint256)"          [AbiAddressType, AbiUIntType 256]
  , sig "log(address,string)"           [AbiAddressType, AbiStringType]
  , sig "log(uint256,bool)"             [AbiUIntType 256, AbiBoolType]
  , sig "log(uint256,address)"          [AbiUIntType 256, AbiAddressType]
  , sig "log(uint256,uint256)"          [AbiUIntType 256, AbiUIntType 256]
  , sig "log(uint256,string)"           [AbiUIntType 256, AbiStringType]
  , sig "log(string,bool)"              [AbiStringType, AbiBoolType]
  , sig "log(string,address)"           [AbiStringType, AbiAddressType]
  , sig "log(string,uint256)"           [AbiStringType, AbiUIntType 256]
  , sig "log(string,string)"            [AbiStringType, AbiStringType]
  , sig "log(string,int256)"            [AbiStringType, AbiIntType 256]
  -- three params
  , sig "log(bool,bool,bool)"                   [AbiBoolType, AbiBoolType, AbiBoolType]
  , sig "log(bool,bool,address)"                [AbiBoolType, AbiBoolType, AbiAddressType]
  , sig "log(bool,bool,uint256)"                [AbiBoolType, AbiBoolType, AbiUIntType 256]
  , sig "log(bool,bool,string)"                 [AbiBoolType, AbiBoolType, AbiStringType]
  , sig "log(bool,address,bool)"                [AbiBoolType, AbiAddressType, AbiBoolType]
  , sig "log(bool,address,address)"             [AbiBoolType, AbiAddressType, AbiAddressType]
  , sig "log(bool,address,uint256)"             [AbiBoolType, AbiAddressType, AbiUIntType 256]
  , sig "log(bool,address,string)"              [AbiBoolType, AbiAddressType, AbiStringType]
  , sig "log(bool,uint256,bool)"                [AbiBoolType, AbiUIntType 256, AbiBoolType]
  , sig "log(bool,uint256,address)"             [AbiBoolType, AbiUIntType 256, AbiAddressType]
  , sig "log(bool,uint256,uint256)"             [AbiBoolType, AbiUIntType 256, AbiUIntType 256]
  , sig "log(bool,uint256,string)"              [AbiBoolType, AbiUIntType 256, AbiStringType]
  , sig "log(bool,string,bool)"                 [AbiBoolType, AbiStringType, AbiBoolType]
  , sig "log(bool,string,address)"              [AbiBoolType, AbiStringType, AbiAddressType]
  , sig "log(bool,string,uint256)"              [AbiBoolType, AbiStringType, AbiUIntType 256]
  , sig "log(bool,string,string)"               [AbiBoolType, AbiStringType, AbiStringType]
  , sig "log(address,bool,bool)"                [AbiAddressType, AbiBoolType, AbiBoolType]
  , sig "log(address,bool,address)"             [AbiAddressType, AbiBoolType, AbiAddressType]
  , sig "log(address,bool,uint256)"             [AbiAddressType, AbiBoolType, AbiUIntType 256]
  , sig "log(address,bool,string)"              [AbiAddressType, AbiBoolType, AbiStringType]
  , sig "log(address,address,bool)"             [AbiAddressType, AbiAddressType, AbiBoolType]
  , sig "log(address,address,address)"          [AbiAddressType, AbiAddressType, AbiAddressType]
  , sig "log(address,address,uint256)"          [AbiAddressType, AbiAddressType, AbiUIntType 256]
  , sig "log(address,address,string)"           [AbiAddressType, AbiAddressType, AbiStringType]
  , sig "log(address,uint256,bool)"             [AbiAddressType, AbiUIntType 256, AbiBoolType]
  , sig "log(address,uint256,address)"          [AbiAddressType, AbiUIntType 256, AbiAddressType]
  , sig "log(address,uint256,uint256)"          [AbiAddressType, AbiUIntType 256, AbiUIntType 256]
  , sig "log(address,uint256,string)"           [AbiAddressType, AbiUIntType 256, AbiStringType]
  , sig "log(address,string,bool)"              [AbiAddressType, AbiStringType, AbiBoolType]
  , sig "log(address,string,address)"           [AbiAddressType, AbiStringType, AbiAddressType]
  , sig "log(address,string,uint256)"           [AbiAddressType, AbiStringType, AbiUIntType 256]
  , sig "log(address,string,string)"            [AbiAddressType, AbiStringType, AbiStringType]
  , sig "log(uint256,bool,bool)"                [AbiUIntType 256, AbiBoolType, AbiBoolType]
  , sig "log(uint256,bool,address)"             [AbiUIntType 256, AbiBoolType, AbiAddressType]
  , sig "log(uint256,bool,uint256)"             [AbiUIntType 256, AbiBoolType, AbiUIntType 256]
  , sig "log(uint256,bool,string)"              [AbiUIntType 256, AbiBoolType, AbiStringType]
  , sig "log(uint256,address,bool)"             [AbiUIntType 256, AbiAddressType, AbiBoolType]
  , sig "log(uint256,address,address)"          [AbiUIntType 256, AbiAddressType, AbiAddressType]
  , sig "log(uint256,address,uint256)"          [AbiUIntType 256, AbiAddressType, AbiUIntType 256]
  , sig "log(uint256,address,string)"           [AbiUIntType 256, AbiAddressType, AbiStringType]
  , sig "log(uint256,uint256,bool)"             [AbiUIntType 256, AbiUIntType 256, AbiBoolType]
  , sig "log(uint256,uint256,address)"          [AbiUIntType 256, AbiUIntType 256, AbiAddressType]
  , sig "log(uint256,uint256,uint256)"          [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256]
  , sig "log(uint256,uint256,string)"           [AbiUIntType 256, AbiUIntType 256, AbiStringType]
  , sig "log(uint256,string,bool)"              [AbiUIntType 256, AbiStringType, AbiBoolType]
  , sig "log(uint256,string,address)"           [AbiUIntType 256, AbiStringType, AbiAddressType]
  , sig "log(uint256,string,uint256)"           [AbiUIntType 256, AbiStringType, AbiUIntType 256]
  , sig "log(uint256,string,string)"            [AbiUIntType 256, AbiStringType, AbiStringType]
  , sig "log(string,bool,bool)"                 [AbiStringType, AbiBoolType, AbiBoolType]
  , sig "log(string,bool,address)"              [AbiStringType, AbiBoolType, AbiAddressType]
  , sig "log(string,bool,uint256)"              [AbiStringType, AbiBoolType, AbiUIntType 256]
  , sig "log(string,bool,string)"               [AbiStringType, AbiBoolType, AbiStringType]
  , sig "log(string,address,bool)"              [AbiStringType, AbiAddressType, AbiBoolType]
  , sig "log(string,address,address)"           [AbiStringType, AbiAddressType, AbiAddressType]
  , sig "log(string,address,uint256)"           [AbiStringType, AbiAddressType, AbiUIntType 256]
  , sig "log(string,address,string)"            [AbiStringType, AbiAddressType, AbiStringType]
  , sig "log(string,uint256,bool)"              [AbiStringType, AbiUIntType 256, AbiBoolType]
  , sig "log(string,uint256,address)"           [AbiStringType, AbiUIntType 256, AbiAddressType]
  , sig "log(string,uint256,uint256)"           [AbiStringType, AbiUIntType 256, AbiUIntType 256]
  , sig "log(string,uint256,string)"            [AbiStringType, AbiUIntType 256, AbiStringType]
  , sig "log(string,string,bool)"               [AbiStringType, AbiStringType, AbiBoolType]
  , sig "log(string,string,address)"            [AbiStringType, AbiStringType, AbiAddressType]
  , sig "log(string,string,uint256)"            [AbiStringType, AbiStringType, AbiUIntType 256]
  , sig "log(string,string,string)"             [AbiStringType, AbiStringType, AbiStringType]
  -- four params (most common combinations)
  , sig "log(bool,bool,bool,bool)"                      [AbiBoolType, AbiBoolType, AbiBoolType, AbiBoolType]
  , sig "log(bool,bool,bool,address)"                   [AbiBoolType, AbiBoolType, AbiBoolType, AbiAddressType]
  , sig "log(bool,bool,bool,uint256)"                   [AbiBoolType, AbiBoolType, AbiBoolType, AbiUIntType 256]
  , sig "log(bool,bool,bool,string)"                    [AbiBoolType, AbiBoolType, AbiBoolType, AbiStringType]
  , sig "log(address,address,address,address)"          [AbiAddressType, AbiAddressType, AbiAddressType, AbiAddressType]
  , sig "log(address,address,address,uint256)"          [AbiAddressType, AbiAddressType, AbiAddressType, AbiUIntType 256]
  , sig "log(address,address,address,string)"           [AbiAddressType, AbiAddressType, AbiAddressType, AbiStringType]
  , sig "log(uint256,uint256,uint256,uint256)"          [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256]
  , sig "log(uint256,uint256,uint256,string)"           [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiStringType]
  , sig "log(string,string,string,string)"              [AbiStringType, AbiStringType, AbiStringType, AbiStringType]
  , sig "log(string,string,string,uint256)"             [AbiStringType, AbiStringType, AbiStringType, AbiUIntType 256]
  , sig "log(string,string,string,address)"             [AbiStringType, AbiStringType, AbiStringType, AbiAddressType]
  , sig "log(string,string,string,bool)"                [AbiStringType, AbiStringType, AbiStringType, AbiBoolType]
  , sig "log(string,uint256,uint256,uint256)"           [AbiStringType, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256]
  , sig "log(string,address,address,address)"           [AbiStringType, AbiAddressType, AbiAddressType, AbiAddressType]
  , sig "log(string,bool,bool,bool)"                    [AbiStringType, AbiBoolType, AbiBoolType, AbiBoolType]
  , sig "log(string,string,uint256,uint256)"            [AbiStringType, AbiStringType, AbiUIntType 256, AbiUIntType 256]
  , sig "log(string,uint256,string,uint256)"            [AbiStringType, AbiUIntType 256, AbiStringType, AbiUIntType 256]
  , sig "log(string,address,uint256,uint256)"           [AbiStringType, AbiAddressType, AbiUIntType 256, AbiUIntType 256]
  , sig "log(string,uint256,address,uint256)"           [AbiStringType, AbiUIntType 256, AbiAddressType, AbiUIntType 256]
  , sig "log(string,bool,string,string)"                [AbiStringType, AbiBoolType, AbiStringType, AbiStringType]
  , sig "log(string,string,address,address)"            [AbiStringType, AbiStringType, AbiAddressType, AbiAddressType]
  , sig "log(string,address,string,address)"            [AbiStringType, AbiAddressType, AbiStringType, AbiAddressType]
  , sig "log(string,address,address,string)"            [AbiStringType, AbiAddressType, AbiAddressType, AbiStringType]
  , sig "log(string,uint256,uint256,string)"            [AbiStringType, AbiUIntType 256, AbiUIntType 256, AbiStringType]
  , sig "log(string,uint256,string,string)"             [AbiStringType, AbiUIntType 256, AbiStringType, AbiStringType]
  , sig "log(string,string,uint256,string)"             [AbiStringType, AbiStringType, AbiUIntType 256, AbiStringType]
  , sig "log(string,address,uint256,string)"            [AbiStringType, AbiAddressType, AbiUIntType 256, AbiStringType]
  , sig "log(string,uint256,address,string)"            [AbiStringType, AbiUIntType 256, AbiAddressType, AbiStringType]
  , sig "log(string,address,string,uint256)"            [AbiStringType, AbiAddressType, AbiStringType, AbiUIntType 256]
  , sig "log(string,string,address,uint256)"            [AbiStringType, AbiStringType, AbiAddressType, AbiUIntType 256]
  , sig "log(string,address,string,string)"             [AbiStringType, AbiAddressType, AbiStringType, AbiStringType]
  , sig "log(string,bool,address,address)"              [AbiStringType, AbiBoolType, AbiAddressType, AbiAddressType]
  , sig "log(string,bool,uint256,uint256)"              [AbiStringType, AbiBoolType, AbiUIntType 256, AbiUIntType 256]
  , sig "log(string,bool,string,uint256)"               [AbiStringType, AbiBoolType, AbiStringType, AbiUIntType 256]
  , sig "log(string,bool,uint256,string)"               [AbiStringType, AbiBoolType, AbiUIntType 256, AbiStringType]
  , sig "log(string,bool,address,string)"               [AbiStringType, AbiBoolType, AbiAddressType, AbiStringType]
  , sig "log(string,bool,string,address)"               [AbiStringType, AbiBoolType, AbiStringType, AbiAddressType]
  , sig "log(string,bool,uint256,address)"              [AbiStringType, AbiBoolType, AbiUIntType 256, AbiAddressType]
  , sig "log(string,bool,address,uint256)"              [AbiStringType, AbiBoolType, AbiAddressType, AbiUIntType 256]
  , sig "log(string,bool,bool,string)"                  [AbiStringType, AbiBoolType, AbiBoolType, AbiStringType]
  , sig "log(string,bool,bool,address)"                 [AbiStringType, AbiBoolType, AbiBoolType, AbiAddressType]
  , sig "log(string,bool,bool,uint256)"                 [AbiStringType, AbiBoolType, AbiBoolType, AbiUIntType 256]
  ]
  where
    sig :: ByteString -> [AbiType] -> (FunctionSelector, (Text, [AbiType]))
    sig s types = (abiKeccak s, (pack (Char8.unpack s), types))
