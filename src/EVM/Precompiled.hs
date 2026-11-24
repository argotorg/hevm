{-# LANGUAGE CPP #-}
module EVM.Precompiled (execute, supported) where

import Control.Monad (guard)
import Crypto.Hash (Digest, Keccak_256, hash)
import Crypto.Number.ModArithmetic (expFast, inverse)
import Crypto.Number.Serialize (os2ip, i2ospOf_)
import Crypto.PubKey.ECC.Prim (pointAddTwoMuls)
import Crypto.PubKey.ECC.Types (Curve(..), CurvePrime(..), CurveCommon(..), CurveName(..), Point(..), getCurveByName)
import Data.ByteArray qualified as BA
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS

import Foreign.C
import Foreign.Ptr
import Foreign.ForeignPtr

import System.IO.Unsafe

import EVM.Types (internalError)

foreign import ccall unsafe "ethjet"
  ethjet
    :: CInt                  -- operation
    -> Ptr CChar -> CSize    -- input
    -> Ptr CChar -> CSize    -- output
    -> IO CInt               -- 1 if good

-- | Whether this build can run the given precompiled contract. The wasm build has no
-- libff, so it cannot run the BN254 precompiles.
supported :: Int -> Bool
#if defined(wasm32_HOST_ARCH)
supported n = n `notElem` [0x6, 0x7, 0x8]
#else
supported _ = True
#endif

-- | Run a given precompiled contract: ECRECOVER in Haskell, the others with the C library.
execute
  :: Int                -- ^ The number of the precompiled contract
  -> ByteString         -- ^ The input buffer
  -> Int                -- ^ The desired output size
  -> Maybe ByteString   -- ^ Hopefully, the output buffer
execute 0x1 input 32 = ecrecover input
execute 0x1 _ _ = Nothing
execute contract input outputSize =

  -- This code looks messy because of the pointer handling,
  -- but it's actually simple.
  --
  -- We use `unsafePerformIO` because the contracts are pure.

  unsafePerformIO . BS.useAsCStringLen input $
    \(inputPtr, inputSize) -> do
       outputForeignPtr <- mallocForeignPtrBytes outputSize
       withForeignPtr outputForeignPtr $ \outputPtr -> do
         status <- ethjet (fromIntegral contract)
           inputPtr (fromIntegral inputSize)
           outputPtr (fromIntegral outputSize)

         case status of
           1 -> Just <$> BS.packCStringLen (outputPtr, outputSize)
           _ -> pure Nothing

-- | The ECRECOVER precompile, accepting what libsecp256k1 accepts: 128 bytes of hash, v,
-- r and s, with v 27 or 28 and r and s in [1, n).
ecrecover :: ByteString -> Maybe ByteString
ecrecover input = do
  guard (BS.length input == 128)
  let (h, rest) = BS.splitAt 32 input
      (v, rs) = BS.splitAt 32 rest
      (rBytes, sBytes) = BS.splitAt 32 rs
      r = os2ip rBytes
      s = os2ip sBytes
      e = os2ip h `mod` n
      recid = toInteger (BS.last v) - 27
  guard (BS.all (== 0) (BS.take 31 v))
  guard (recid == 0 || recid == 1)
  guard (r > 0 && r < n && s > 0 && s < n)
  let y2 = (r * r * r + 7) `mod` p
      -- p = 3 mod 4, so this is the square root of y2 if it has one
      y0 = expFast y2 ((p + 1) `div` 4) p
      y = if odd y0 == (recid == 1) then y0 else p - y0
  guard ((y0 * y0) `mod` p == y2)
  rInv <- inverse r n
  case pointAddTwoMuls curve ((negate e * rInv) `mod` n) g ((s * rInv) `mod` n) (Point r y) of
    PointO -> Nothing
    Point qx qy ->
      let digest = BA.convert (hash (i2ospOf_ 32 qx <> i2ospOf_ 32 qy :: ByteString) :: Digest Keccak_256)
      in Just (BS.replicate 12 0 <> BS.drop 12 digest)
  where
    curve = getCurveByName SEC_p256k1
    (p, n, g) = case curve of
      CurveFP (CurvePrime prime cc) -> (prime, ecc_n cc, ecc_g cc)
      _ -> internalError "secp256k1 is a prime curve"
