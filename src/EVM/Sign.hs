{-|
Module      : Helper functions to sign a transaction and derive address from
Description :        for the EVM given a secret key
-}
module EVM.Sign where

import Data.ByteString qualified as BS
import Data.Maybe (fromMaybe)
import Data.Word
import Crypto.Hash qualified as Crypto
import Crypto.PubKey.ECC.ECDSA (signDigestWith, PrivateKey(..), Signature(..))
import Crypto.PubKey.ECC.Types (getCurveByName, CurveName(..), Point(..))
import Crypto.PubKey.ECC.Generate (generateQ)
import Witch (unsafeInto)

import EVM.ABI (encodeAbiValue, AbiValue(..))
import EVM.Types
import EVM.Expr (exprToAddr)
import EVM.Precompiled

-- Given a secret key, generates the address
deriveAddr :: Integer -> Maybe Addr
deriveAddr sk =
  case pubPoint of
    PointO -> Nothing
    Point x y ->
      -- See yellow paper #286
      let pub = BS.concat [ encodeInt x, encodeInt y ]
          addr = Lit . W256 . word256 . BS.drop 12 . BS.take 32 . keccakBytes $ pub
      in exprToAddr addr
  where
    curve = getCurveByName SEC_p256k1
    pubPoint = generateQ curve sk
    encodeInt = encodeAbiValue . AbiUInt 256 . fromInteger

sign :: W256 -> Integer -> (Word8, W256, W256)
sign hash sk = (v, r, s)
  where
    -- setup curve params
    curve = getCurveByName SEC_p256k1
    priv = PrivateKey curve sk
    digest = fromMaybe
      (internalError $ "could produce a digest from " <> show hash)
      (Crypto.digestFromByteString (word256Bytes hash))

    -- sign message
    sig = ethsign priv digest
    r = unsafeInto $ sign_r sig
    s = unsafeInto lowS

    -- this is a little bit sad, but crypton doesn't give us back a v value
    -- so we compute it by guessing one, and then seeing if that gives us the right answer from ecrecover
    v = if ecrec 28 r s hash == deriveAddr sk
        then 28
        else 27

    -- we always use the lower S value to conform with EIP2 (re: ECDSA transaction malleability)
    -- https://eips.ethereum.org/EIPS/eip-2
    secpOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 :: Integer
    lowS = if sign_s sig > secpOrder `div` 2
           then secpOrder - sign_s sig
           else sign_s sig

-- | We don't want to introduce the machinery needed to sign with a random nonce,
-- so we just use the same nonce every time (420). This is obviously very
-- insecure, but fine for testing purposes.
ethsign :: PrivateKey -> Crypto.Digest Crypto.Keccak_256 -> Signature
ethsign sk digest = go 420
  where
    go k = case signDigestWith k sk digest of
       Nothing  -> go (k + 1)
       Just sig -> sig

ecrec :: W256 -> W256 -> W256 -> W256 -> Maybe Addr
ecrec v r s e = unsafeInto . word <$> EVM.Precompiled.execute 1 input 32
  where input = BS.concat (word256Bytes <$> [e, v, r, s])
