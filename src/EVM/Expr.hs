{-# LANGUAGE PatternSynonyms #-}

{-|
   Helper functions for working with Expr instances.
   All functions here will return a concrete result if given a concrete input.
-}
module EVM.Expr where

import Prelude hiding (LT, GT)
import Control.Monad (unless, when)
import Control.Monad.ST (ST)
import Control.Monad.State (put, get, execState, State)
import Data.Bits hiding (And, Xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.DoubleWord (Int256, Word256(Word256), Word128(Word128))
import Data.List
import Data.Map qualified as LMap
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe, isJust, fromMaybe)
import Data.Semigroup (Any, Any(..), getAny)
import Data.Typeable
import Data.Vector qualified as V
import Data.Vector (Vector)
import Data.Vector.Mutable qualified as MV
import Data.Vector.Mutable (MVector)
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.ByteString
import Data.Word (Word8, Word32)
import Witch (unsafeInto, into, tryInto)
import Data.Containers.ListUtils (nubOrd)

import Optics.Core

import EVM.Traversals
import EVM.Types

-- ** Constants **

maxLit :: W256
maxLit = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

maxLitSigned :: W256
maxLitSigned = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

minLitSigned :: W256
minLitSigned = 0x8000000000000000000000000000000000000000000000000000000000000000

-- ** Stack Ops ** ---------------------------------------------------------------------------------


op1 :: (Expr EWord -> Expr EWord)
    -> (W256 -> W256)
    -> Expr EWord -> Expr EWord
op1 _ concrete (Lit x) = Lit (concrete x)
op1 symbolic _ x = symbolic x

op2 :: (Expr EWord -> Expr EWord -> Expr EWord)
    -> (W256 -> W256 -> W256)
    -> Expr EWord -> Expr EWord -> Expr EWord
op2 _ concrete (Lit x) (Lit y) = Lit (concrete x y)
op2 symbolic _ x y = symbolic x y

op3 :: (Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord)
    -> (W256 -> W256 -> W256 -> W256)
    -> Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
op3 _ concrete (Lit x) (Lit y) (Lit z) = Lit (concrete x y z)
op3 symbolic _ x y z = symbolic x y z

-- | If a given binary op is commutative, then we always order the arguments.
-- This makes writing pattern matches in the simplifier easier.
-- It will also force Lit to be the 1st argument, since Lit is the 1st element of Expr (see Types.hs).
normArgs :: (Expr EWord -> Expr EWord -> Expr EWord) -> (W256 -> W256 -> W256) -> Expr EWord -> Expr EWord -> Expr EWord
normArgs sym conc l r = if l <= r then doOp l r else doOp r l
  where
    doOp = op2 sym conc

-- Integers

add :: Expr EWord -> Expr EWord -> Expr EWord
add = normArgs Add (+)

sub :: Expr EWord -> Expr EWord -> Expr EWord
sub = op2 Sub (-)

mul :: Expr EWord -> Expr EWord -> Expr EWord
mul = normArgs Mul (*)

div :: Expr EWord -> Expr EWord -> Expr EWord
div = op2 Div (\x y -> if y == 0 then 0 else Prelude.div x y)

sdiv :: Expr EWord -> Expr EWord -> Expr EWord
sdiv = op2 SDiv (\x y -> let sx, sy :: Int256
                             sx = fromIntegral x
                             sy = fromIntegral y
                         in if y == 0 then 0 else fromIntegral (sx `quot` sy))

mod :: Expr EWord -> Expr EWord -> Expr EWord
mod = op2 Mod (\x y -> if y == 0 then 0 else x `Prelude.mod` y)

smod :: Expr EWord -> Expr EWord -> Expr EWord
smod = op2 SMod (\x y ->
  let sx, sy :: Int256
      sx = fromIntegral x
      sy = fromIntegral y
  in if y == 0
     then 0
     else fromIntegral (sx `rem` sy))

addmod :: Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
addmod = op3 AddMod (\x y z ->
  if z == 0 then 0
  else fromIntegral $ (into @Word512 x + into y) `Prelude.mod` into z)

mulmod :: Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
mulmod = op3 MulMod (\x y z ->
  if z == 0 then 0
  else fromIntegral $ (into @Word512 x * into y) `Prelude.mod` into z)

exp :: Expr EWord -> Expr EWord -> Expr EWord
exp = op2 Exp (^)

sex :: Expr EWord -> Expr EWord -> Expr EWord
sex = op2 SEx (\bytes x ->
  if bytes >= 32 then x
  else let n = unsafeInto bytes * 8 + 7 in
    if testBit x n
    then x .|. complement (bit n - 1)
    else x .&. (bit n - 1))

-- Booleans

lt :: Expr EWord -> Expr EWord -> Expr EWord
lt = op2 LT (\x y -> if x < y then 1 else 0)

gt :: Expr EWord -> Expr EWord -> Expr EWord
gt = op2 GT (\x y -> if x > y then 1 else 0)

leq :: Expr EWord -> Expr EWord -> Expr EWord
leq = op2 LEq (\x y -> if x <= y then 1 else 0)

geq :: Expr EWord -> Expr EWord -> Expr EWord
geq = op2 GEq (\x y -> if x >= y then 1 else 0)

slt :: Expr EWord -> Expr EWord -> Expr EWord
slt = op2 SLT (\x y ->
  let sx, sy :: Int256
      sx = fromIntegral x
      sy = fromIntegral y
  in if sx < sy then 1 else 0)

sgt :: Expr EWord -> Expr EWord -> Expr EWord
sgt = op2 SGT (\x y ->
  let sx, sy :: Int256
      sx = fromIntegral x
      sy = fromIntegral y
  in if sx > sy then 1 else 0)

eq :: Expr EWord -> Expr EWord -> Expr EWord
eq = normArgs Eq (\x y -> if x == y then 1 else 0)

iszero :: Expr EWord -> Expr EWord
iszero = op1 IsZero (\x -> if x == 0 then 1 else 0)

-- Bits

and :: Expr EWord -> Expr EWord -> Expr EWord
and = normArgs And (.&.)

or :: Expr EWord -> Expr EWord -> Expr EWord
or = normArgs Or (.|.)

xor :: Expr EWord -> Expr EWord -> Expr EWord
xor = normArgs Xor Data.Bits.xor

not :: Expr EWord -> Expr EWord
not = op1 Not complement

shl :: Expr EWord -> Expr EWord -> Expr EWord
shl = op2 SHL (\x y -> if x >= 256 then 0 else shiftL y (fromIntegral x))

shr :: Expr EWord -> Expr EWord -> Expr EWord
shr = op2
  (\x y -> case (x, y) of
             -- simplify function selector checks
             (Lit 0xe0, ReadWord (Lit idx) buf)
               -> joinBytes (
                    replicate 28 (LitByte 0) <>
                      [ readByte (Lit idx) buf
                      , readByte (Lit $ idx + 1) buf
                      , readByte (Lit $ idx + 2) buf
                      , readByte (Lit $ idx + 3) buf])
             _ -> SHR x y)
  (\x y -> if x > 256 then 0 else shiftR y (fromIntegral x))

sar :: Expr EWord -> Expr EWord -> Expr EWord
sar = op2 SAR (\x y ->
  let msb = testBit y 255
      asSigned = fromIntegral y :: Int256
  in if x >= 255 then
       if msb then maxBound else 0
     else
       fromIntegral $ shiftR asSigned (fromIntegral x))

clz :: Expr EWord -> Expr EWord
clz = op1 CLZ (\x -> if x == 0 then 256 else fromIntegral $ countLeadingZeros x)

-- Props

peq :: (Typeable a) => Expr a -> Expr a -> Prop
peq (Lit x) (Lit y) = PBool (x == y)
peq (LitAddr x) (LitAddr y) = PBool (x == y)
peq (LitByte x) (LitByte y) = PBool (x == y)
peq (ConcreteBuf x) (ConcreteBuf y) = PBool (x == y)
peq (ConcreteStore x) (ConcreteStore y) = PBool (x == y)
peq a b
  | a == b = PBool True
  | otherwise = let args = sort [a, b]
     in PEq (args !! 0) (args !! 1)

pleq :: Expr EWord -> Expr EWord -> Prop
pleq (Lit a) (Lit b) = PBool (a <= b)
pleq a b
  | a == b = PBool True
  | otherwise = PLEq a b

-- ** Bufs ** --------------------------------------------------------------------------------------


-- | Extracts the byte at a given index from a Buf.
--
-- We do our best to return a concrete value wherever possible, but fallback to
-- an abstract expression if necessary. Note that a Buf is an infinite
-- structure, so reads outside of the bounds of a ConcreteBuf return 0. This is
-- inline with the semantics of calldata and memory, but not of returndata.

-- fully concrete reads
readByte :: Expr EWord -> Expr Buf -> Expr Byte
readByte (Lit x) (ConcreteBuf b)
  = if x <= unsafeInto (maxBound :: Int) && i < BS.length b
    then LitByte (BS.index b i)
    else LitByte 0x0
  where
    i :: Int
    i = case x of
          (W256 (Word256 _ (Word128 _ x'))) -> unsafeInto x'

readByte i@(Lit x) (WriteByte (Lit idx) val src)
  = if x == idx
    then val
    else readByte i src
readByte i@(Lit x) (WriteByte (And (Lit idx) _) _ src)
  | x > idx = readByte i src
readByte i@(Lit x) (WriteWord (Lit idx) val src)
  = if x - idx < 32
    then case val of
           (Lit _) -> indexWord (Lit $ x - idx) val
           _ -> IndexWord (Lit $ x - idx) val
    else readByte i src
-- reading a byte that is lower than the dstOffset of a CopySlice, so it's just reading from dst
readByte i@(Lit x) (CopySlice _ (Lit dstOffset) _ _ dst) | dstOffset > x =
  readByte i dst
readByte i@(Lit x) (CopySlice (Lit srcOffset) (Lit dstOffset) (Lit size) src dst)
  = if x - dstOffset < size
    then readByte (Lit $ x - (dstOffset - srcOffset)) src
    else readByte i dst
readByte i@(Lit x) buf@(CopySlice _ (Lit dstOffset) (Lit size) _ dst)
  -- the byte we are trying to read is completely outside of the sliced region
  = if x - dstOffset >= size
    then readByte i dst
    else ReadByte (Lit x) buf

-- fully abstract reads
readByte i buf = ReadByte i buf


-- | Reads n bytes starting from idx in buf and returns a left padded word
--
-- If n is >= 32 this is the same as readWord
readBytes :: Int -> Expr EWord -> Expr Buf -> Expr EWord
readBytes (Prelude.min 32 -> n) idx buf
  = joinBytes [readByte (add idx (Lit . unsafeInto $ i)) buf | i <- [0 .. n - 1]]

-- | Reads the word starting at idx from the given buf
readWord :: Expr EWord -> Expr Buf -> Expr EWord
readWord idx buf@(AbstractBuf _) = ReadWord idx buf
readWord idx b@(WriteWord idx' val buf)
  -- the word we are trying to read exactly matches a WriteWord
  | idx == idx' = val
  | otherwise = case (idx, idx') of
    (Lit i, Lit i') ->
      if i' - i >= 32 && i' - i <= (maxBound :: W256) - 31
      -- the region we are trying to read is completely outside of the WriteWord
      then readWord idx buf
      -- the region we are trying to read partially overlaps the WriteWord
      else readWordFromBytes idx b
    -- we do not have enough information to statically determine whether or not
    -- the region we want to read overlaps the WriteWord
    _ -> readWordFromBytes idx b
readWord i@(Lit idx) (WriteByte (Lit idx') _ buf)
  | idx' < idx || (idx' >= idx + 32 && idx <= (maxBound :: W256) - 32) = readWord i buf
-- reading a Word that is lower than the dstOffset-32 of a CopySlice, so it's just reading from dst
readWord i@(Lit x) (CopySlice _ (Lit dstOffset) _ _ dst) | dstOffset >= x+32 = readWord i dst
readWord i@(Lit x) (CopySlice _ (Lit dstOffset) (Lit size) _ dst) | x >= dstOffset + size = readWord i dst
readWord (Lit idx) b@(CopySlice (Lit srcOff) (Lit dstOff) (Lit size) src dst)
  -- the region we are trying to read is enclosed in the sliced region
  | (idx - dstOff) < size && 32 <= size - (idx - dstOff) = readWord (Lit $ srcOff + (idx - dstOff)) src
  -- the region we are trying to read is completely outside of the sliced region
  | (idx - dstOff) >= size && (idx - dstOff) <= (maxBound :: W256) - 31 = readWord (Lit idx) dst
  -- the region we are trying to read partially overlaps the sliced region
  | otherwise = readWordFromBytes (Lit idx) b
readWord i b = readWordFromBytes i b

-- Attempts to read a concrete word from a buffer by reading 32 individual bytes and joining them together
-- returns an abstract ReadWord expression if a concrete word cannot be constructed
readWordFromBytes :: Expr EWord -> Expr Buf -> Expr EWord
readWordFromBytes (Lit idx) (ConcreteBuf bs) =
  case tryInto idx of
    Left _ -> Lit 0
    Right i -> Lit $ word $ padRight 32 $ BS.take 32 $ BS.drop i bs
readWordFromBytes idx buf@(AbstractBuf _) = ReadWord idx buf
readWordFromBytes i@(Lit idx) buf = let
    bytes = [readByte (Lit i') buf | i' <- [idx .. idx + 31]]
  in if all isLitByte bytes
     then Lit (bytesToW256 . mapMaybe maybeLitByteSimp $ bytes)
     else ReadWord i buf
readWordFromBytes idx buf = ReadWord idx buf

{- | Copies a slice of src into dst.

        0           srcOffset       srcOffset + size     length src
        ┌--------------┬------------------┬-----------------┐
   src: |              | ------ sl ------ |                 |
        └--------------┴------------------┴-----------------┘

        0     dstOffset       dstOffset + size     length dst
        ┌--------┬------------------┬-----------------┐
   dst: |   hd   |                  |       tl        |
        └--------┴------------------┴-----------------┘
-}

-- The maximum number of bytes we will expand as part of simplification
--     this limits the amount of memory we will use while simplifying to ~1 GB / rewrite
--     note that things can still stack up, e.g. N such rewrites could eventually eat
--     N*1GB.
maxBytes :: W256
maxBytes = into (maxBound :: Word32) `Prelude.div` 8

maxWord256 :: W256
maxWord256 = W256 (maxBound :: Word256)

copySlice :: Expr EWord -> Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf -> Expr Buf

-- Copying zero bytes is a no-op
copySlice _ _ (Lit 0) _ dst = dst

-- copying 32 bytes can be rewritten to a WriteWord on dst (e.g. CODECOPY of args during constructors)
copySlice srcOffset dstOffset (Lit 32) src dst = writeWord dstOffset (readWord srcOffset src) dst

-- Fully concrete copy
copySlice a@(Lit srcOffset) b@(Lit dstOffset) c@(Lit size) d@(ConcreteBuf src) e@(ConcreteBuf dst)
  | dstOffset < maxBytes
  , size < maxBytes =
      let hd = padRight (unsafeInto dstOffset) $ BS.take (unsafeInto dstOffset) dst
          sl = if srcOffset > unsafeInto (BS.length src)
            then BS.replicate (unsafeInto size) 0
            else padRight (unsafeInto size) $ BS.take (unsafeInto size) (BS.drop (unsafeInto srcOffset) src)
          tl = BS.drop (unsafeInto dstOffset + unsafeInto size) dst
      in ConcreteBuf $ hd <> sl <> tl
  | otherwise = CopySlice a b c d e

-- concrete indices & abstract src (may produce a concrete result if we are
-- copying from a concrete region of src)
copySlice s@(Lit srcOffset) d@(Lit dstOffset) sz@(Lit size) src ds@(ConcreteBuf dst)
  | dstOffset < maxBytes, size < maxBytes, srcOffset + (size-1) > srcOffset = let
    hd = padRight (unsafeInto dstOffset) $ BS.take (unsafeInto dstOffset) dst
    sl = [readByte (Lit i) src | i <- [srcOffset .. srcOffset + (size - 1)]]
    tl = BS.drop (unsafeInto dstOffset + unsafeInto size) dst
    in if all isLitByte sl
       then ConcreteBuf $ hd <> (BS.pack . (mapMaybe maybeLitByteSimp) $ sl) <> tl
       else CopySlice s d sz src ds
  | otherwise = CopySlice s d sz src ds

-- abstract indices
copySlice srcOffset dstOffset size src dst = CopySlice srcOffset dstOffset size src dst


writeByte :: Expr EWord -> Expr Byte -> Expr Buf -> Expr Buf
writeByte (Lit offset) (LitByte val) (ConcreteBuf "")
  | offset < maxBytes
  = ConcreteBuf $ BS.replicate (unsafeInto offset) 0 <> BS.singleton val
writeByte o@(Lit offset) b@(LitByte byte) buf@(ConcreteBuf src)
  | offset < maxBytes
    = ConcreteBuf $ (padRight (unsafeInto offset) $ BS.take (unsafeInto offset) src)
                 <> BS.pack [byte]
                 <> BS.drop (unsafeInto offset + 1) src
  | otherwise = WriteByte o b buf
writeByte offset byte src = WriteByte offset byte src


writeWord :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
writeWord o@(Lit offset) (WAddr (LitAddr val)) b@(ConcreteBuf _)
  | offset < maxBytes && offset + 32 < maxBytes
  = writeWord o (Lit $ into val) b
writeWord (Lit offset) (Lit val) (ConcreteBuf "")
  | offset < maxBytes && offset + 32 < maxBytes
  = ConcreteBuf $ BS.replicate (unsafeInto offset) 0 <> word256Bytes val
writeWord o@(Lit offset) v@(Lit val) buf@(ConcreteBuf src)
  | offset < maxBytes && offset + 32 < maxBytes
    = ConcreteBuf $ (padRight (unsafeInto offset) $ BS.take (unsafeInto offset) src)
                 <> word256Bytes val
                 <> BS.drop ((unsafeInto offset) + 32) src
  | otherwise = WriteWord o v buf
writeWord idx val b@(WriteWord idx' val' buf)
  -- if the indices match exactly then we just replace the value in the current write and return
  | idx == idx' = WriteWord idx val buf
  | otherwise
    = case (idx, idx') of
        (Lit i, Lit i') -> if i >= i' + 32
                           -- if we can statically determine that the write at
                           -- idx doesn't overlap the write at idx', then we
                           -- push the write down we only consider writes where
                           -- i > i' to avoid infinite loops in this routine.
                           -- This also has the nice side effect of imposing a
                           -- canonical ordering on write chains, making exact
                           -- syntactic equalities between abstract terms more
                           -- likely to occur
                           then WriteWord idx' val' (writeWord idx val buf)
                           -- if we cannot statically determine freedom from
                           -- overlap, then we just return an abstract term
                           else WriteWord idx val b
        -- if we cannot determine statically that the write at idx' is out of
        -- bounds for idx, then we return an abstract term
        _ -> WriteWord idx val b
writeWord offset val src = WriteWord offset val src


-- | Returns the length of a given buffer
--
-- If there are any writes to abstract locations, or CopySlices with an
-- abstract size or dstOffset, an abstract expression will be returned.
bufLength :: Expr Buf -> Expr EWord
bufLength = bufLengthEnv mempty False

bufLengthEnv :: Map.Map Int (Expr Buf) -> Bool -> Expr Buf -> Expr EWord
bufLengthEnv env useEnv buf = go (Lit 0) buf
  where
    go :: Expr EWord -> Expr Buf -> Expr EWord
    go l (ConcreteBuf b) = EVM.Expr.max l (Lit (unsafeInto . BS.length $ b))
    go l (AbstractBuf b) = EVM.Expr.max l (BufLength (AbstractBuf b))
    go l (WriteWord idx _ b) = go (EVM.Expr.max l (add idx (Lit 32))) b
    go l (WriteByte idx _ b) = go (EVM.Expr.max l (add idx (Lit 1))) b
    go l (CopySlice _ _ (Lit 0) _ dst) = go l dst
    go l (CopySlice _ dstOffset size _ dst) = go (EVM.Expr.max l (add dstOffset size)) dst

    go l (GVar (BufVar a)) | useEnv =
      case Map.lookup a env of
        Just b -> go l b
        Nothing -> internalError "cannot compute length of open expression"
    go l (GVar (BufVar a)) = EVM.Expr.max l (BufLength (GVar (BufVar a)))

-- | Return the minimum possible length of a buffer. In the case of an
-- abstract buffer, it is the largest write that is made on a concrete
-- location. Parameterized by an environment for buffer variables.
minLength :: Map.Map Int (Expr Buf) -> Expr Buf -> Maybe Integer
minLength bufEnv = go 0
  where
    go :: W256 -> Expr Buf -> Maybe Integer
    -- base cases
    go l (AbstractBuf _) = if l == 0 then Nothing else Just $ into l
    go l (ConcreteBuf b) = Just . into $ Prelude.max (unsafeInto . BS.length $ b) l
    -- writes to a concrete index
    go l (WriteWord (Lit idx) _ b) = go (Prelude.max l (idx + 32)) b
    go l (WriteByte (Lit idx) _ b) = go (Prelude.max l (idx + 1)) b
    go l (CopySlice _ (Lit dstOffset) (Lit size) _ dst) = go (Prelude.max (dstOffset + size) l) dst
    -- writes to an abstract index are ignored
    go l (WriteWord _ _ b) = go l b
    go l (WriteByte _ _ b) = go l b
    go l (CopySlice _ _ _ _ b) = go l b
    go l (GVar (BufVar a)) = do
      b <- Map.lookup a bufEnv
      go l b

-- returns the largest prefix that is guaranteed to be concrete (if one exists)
-- partial: will hard error if we encounter an input buf with a concrete size > 500mb
-- partial: will hard error if the prefix is > 500mb
concretePrefix :: Expr Buf -> Vector Word8
concretePrefix b = V.create $ do
    v <- MV.new (fromMaybe 1024 inputLen)
    (filled, v') <- go 0 v
    pure $ MV.take filled v'
  where

    -- if our prefix is > 500mb then we have other issues and should just bail...
    maxIdx :: Num i => i
    maxIdx = 500 * (10 ^ (6 :: Int))

    -- attempts to compute a concrete length for the input buffer
    inputLen :: Maybe Int
    inputLen = case bufLength b of
      Lit s -> if s > maxIdx
        then internalError "concretePrefix: input buffer size exceeds 500mb"
        -- unsafeInto: s is <= 500,000,000
        else Just (unsafeInto s)
      _ -> Nothing

    -- recursively reads successive bytes from `b` until we reach a symbolic
    -- byte returns the large index read from and a reference to the mutable
    -- vec (might not be the same as the input because of the call to grow)
    go :: forall s . Int -> MVector s Word8 -> ST s (Int, MVector s Word8)
    go i v
      -- if the prefix is very large then bail
      | i >= maxIdx = internalError "concretePrefix: prefix size exceeds 500mb"
      -- if the input buffer has a concrete size, then don't read past the end
      | Just mr <- inputLen, i >= mr = pure (i, v)
      -- double the size of the vector if we've reached the end
      | i >= MV.length v = do
        v' <- MV.grow v (MV.length v)
        go i v'
      -- read the byte at `i` in `b` into `v` if it is concrete, or halt if we've reached a symbolic byte
      -- unsafeInto: i will always be positive
      | otherwise = case readByte (Lit . unsafeInto $ i) b of
          LitByte byte -> do
            MV.write v i byte
            go (i+1) v
          _ -> pure (i, v)


word256At :: Expr EWord -> Lens (Expr Buf) (Expr Buf) (Expr EWord) (Expr EWord)
word256At i = lens getter setter where
  getter = readWord i
  setter m x = writeWord i x m

-- | Returns the first n bytes of buf
take :: W256 -> Expr Buf -> Expr Buf
take n = slice (Lit 0) (Lit n)


-- | Returns everything but the first n bytes of buf
drop :: W256 -> Expr Buf -> Expr Buf
drop n buf = slice (Lit n) (sub (bufLength buf) (Lit n)) buf

slice :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
slice offset size src = copySlice offset (Lit 0) size src mempty


toList :: Expr Buf -> Maybe (V.Vector (Expr Byte))
toList (AbstractBuf _) = Nothing
toList (ConcreteBuf bs) = Just $ V.fromList $ LitByte <$> BS.unpack bs
toList buf = case bufLength buf of
  Lit l -> if l <= unsafeInto (maxBound :: Int)
              then Just $ V.generate (unsafeInto l) (\i -> readByte (Lit $ unsafeInto i) buf)
              else internalError "overflow when converting buffer to list"
  _ -> Nothing

fromList :: V.Vector (Expr Byte) -> Expr Buf
fromList bs = case all isLitByte bs of
  True -> ConcreteBuf . vectorToByteString . VS.convert $ V.map getLitByte bs
  -- we want to minimize the size of the resulting expression, so we do two passes:
  --   1. write all concrete bytes to some base buffer
  --   2. write all symbolic writes on top of this buffer
  -- this is safe because each write in the input vec is to a single byte at a distinct location
  -- runs in O(2n) time, and has pretty minimal allocation & copy overhead in
  -- the concrete part (a single preallocated vec, with no copies)
  False -> V.ifoldl' applySymWrites (ConcreteBuf concreteBytes) bs
  where
    getLitByte :: (Expr Byte) -> Word8
    getLitByte (LitByte w) = w
    getLitByte _ = internalError "Impossible!"

    concreteBytes :: ByteString
    concreteBytes = vectorToByteString $ VS.generate (V.length bs) (\idx ->
      case bs V.! idx of
        LitByte b -> b
        _ -> 0)

    applySymWrites :: Expr Buf -> Int -> Expr Byte -> Expr Buf
    applySymWrites buf _ (LitByte _) = buf
    applySymWrites buf idx by = WriteByte (Lit $ unsafeInto idx) by buf

instance Semigroup (Expr Buf) where
  (ConcreteBuf a) <> (ConcreteBuf b) = ConcreteBuf $ a <> b
  a <> b = copySlice (Lit 0) (bufLength a) (bufLength b) b a

instance Monoid (Expr Buf) where
  mempty = ConcreteBuf ""

-- | Removes any irrelevant writes when reading from a buffer
simplifyReads :: Expr a -> Expr a
simplifyReads = \case
  ReadWord (Lit idx) b -> readWord (Lit idx) b
  ReadByte (Lit idx) b -> readByte (Lit idx) b
  a -> a

-- ** Storage ** -----------------------------------------------------------------------------------


readStorage' :: Expr EWord -> Expr Storage -> Expr EWord
readStorage' loc store = case readStorage loc store of
                           Just v -> v
                           Nothing -> Lit 0

-- | Reads the word at the given slot from the given storage expression.
--
-- Note that we return a Nothing instead of a 0x0 if we are reading from a
-- store that is backed by a ConcreteStore or an EmptyStore and there have been
-- no explicit writes to the requested slot. This makes implementing rpc
-- storage lookups much easier. If the store is backed by an AbstractStore we
-- always return a symbolic value.
--
-- This does not strip writes that cannot possibly match a read, in case there are
-- some write(s) in between that it cannot statically determine to be removable, because
-- it will early-abort. So (load idx1 (store idx1 (store idx1 (store idx0)))) will not strip
-- the idx0 store, in case things in between cannot be stripped. See simplify-storage-map-todo
-- test for an example where this happens. Note that decomposition solves this, though late in
-- the simplification lifecycle (just before SMT generation, which can be too late)
readStorage :: Expr EWord -> Expr Storage -> Maybe (Expr EWord)
readStorage w st = go (simplifyNoLitToKeccak w) (simplifyNoLitToKeccak st)
  where
    go :: Expr EWord -> Expr Storage -> Maybe (Expr EWord)
    go _ (GVar _) = internalError "Can't read from a GVar"
    go slot s@(AbstractStore _ _) = Just $ SLoad slot s
    go (Lit l) (ConcreteStore s) = Lit <$> Map.lookup l s
    go slot store@(ConcreteStore _) = Just $ SLoad slot store
    go slot s@(SStore prevSlot val prev) = case (prevSlot, slot) of
      -- if address and slot match then we return the val in this write
      _ | prevSlot == slot -> Just val
      (a, b) | surelyEqual a b -> Just val
      (a, b) | surelyNotEqual a b -> go slot prev

      -- slot is for a map + map -> skip write
      (MappingSlot idA _, MappingSlot idB _)       | isMap' idB, isMap' idA, idsDontMatch idA idB  -> go slot prev
      (MappingSlot idA keyA, MappingSlot idB keyB) | isMap' idB, isMap' idA, surelyNotEqual keyA keyB -> go slot prev

      -- special case of array + map -> skip write
      (ArraySlotWithOffs idA _, Keccak k)          | isMap k, isArray idA -> go slot prev
      (ArraySlotWithOffs2 idA _ _, Keccak k)       | isMap k, isArray idA -> go slot prev
      (ArraySlotZero idA, Keccak k)                | isMap k, isArray idA -> go slot prev

      -- special case of map + array -> skip write
      (Keccak k, ArraySlotWithOffs idA _)          | isMap k, isArray idA -> go slot prev
      (Keccak k, ArraySlotWithOffs2 idA _ _)       | isMap k, isArray idA -> go slot prev
      (ArraySlotWithOffs idA _, Keccak k)          | isMap k, isArray idA -> go slot prev
      (ArraySlotWithOffs2 idA _ _, Keccak k)       | isMap k, isArray idA -> go slot prev

      -- Fixed SMALL value will never match Keccak (well, it might, but that's VERY low chance)
      (Lit a, Keccak _) | a < 256 -> go slot prev
      (Keccak _, Lit a) | a < 256 -> go slot prev

      -- the chance of adding a value <= 2^32 to any given keccack output
      -- leading to an overflow is effectively zero. the chance of an overflow
      -- occurring here is 2^32/2^256 = 2^-224, which is close enough to zero
      -- for our purposes. This lets us completely simplify reads from write
      -- chains involving writes to arrays at literal offsets.
      (Lit a, Add (Lit b) (Keccak _)) | a < 256, b < maxW32 -> go slot prev
      (Add (Lit a) (Keccak _) ,Lit b) | b < 256, a < maxW32 -> go slot prev

      -- Finding two Keccaks that are < 256 away from each other should be VERY hard
      -- This simplification allows us to deal with maps of structs
      (Add (Lit a2) (Keccak _), Add (Lit b2) (Keccak _)) | a2 /= b2, abs (a2-b2) < 256 -> go slot prev
      (Add (Lit a2) (Keccak _), (Keccak _)) | a2 > 0, a2 < 256 -> go slot prev
      ((Keccak _), Add (Lit b2) (Keccak _)) | b2 > 0, b2 < 256 -> go slot prev

      -- zero offs vs zero offs
      (ArraySlotZero idA, ArraySlotZero idB)                   | isArray idA, isArray idB, idA /= idB -> go slot prev

      -- zero offs vs non-zero offs
      (ArraySlotZero idA, ArraySlotWithOffs idB _)             | isArray idA, isArray idB, idA /= idB -> go slot prev
      (ArraySlotZero idA, ArraySlotWithOffs idB (Lit offB))    | isArray idA, idA == idB, offB /= 0  -> go slot prev
      (ArraySlotZero idA, ArraySlotWithOffs2 idB _ _)          | isArray idA, isArray idB, idA /= idB -> go slot prev

      -- non-zero offs vs zero offs
      (ArraySlotWithOffs idA _, ArraySlotZero idB)             | isArray idA, isArray idB, idA /= idB -> go slot prev
      (ArraySlotWithOffs idA (Lit offA), ArraySlotZero idB)    | isArray idA, idA == idB, offA /= 0  -> go slot prev

      -- non-zero offs vs non-zero offs, different ids
      (ArraySlotWithOffs idA _, ArraySlotWithOffs idB _)       | isArray idA, isArray idB, idA /= idB -> go slot prev

      -- non-zero offs vs non-zero offs, same ids
      (ArraySlotWithOffs idA a, ArraySlotWithOffs idB b)                       | isArray idA, idA == idB,
        surelyNotEqual a b -> go slot prev
      (ArraySlotWithOffs idB offB2, ArraySlotWithOffs2 idA offA1 offA2)        | isArray idA, idA == idB,
        surelyNotEqual (Add (Lit offA1) offA2) offB2 -> go slot prev
      (ArraySlotWithOffs2 idA offA1 offA2, ArraySlotWithOffs idB offB2)        | isArray idA, idA == idB,
        surelyNotEqual (Add (Lit offA1) offA2) offB2 -> go slot prev
      (ArraySlotWithOffs2 idA offA1 offA2, ArraySlotWithOffs2 idB offB1 offB2) | isArray idA, idA == idB,
        surelyNotEqual (Add (Lit offA1) offA2) (Add (Lit offB1) offB2) -> go slot prev

      -- we are unable to determine statically whether or not we can safely move deeper in the write chain, so return an abstract term
      _ -> Just $ SLoad slot s

    maxW32 :: W256
    maxW32 = into (maxBound :: Word32)
    isArray :: ByteString -> Bool
    isArray b = BS.length b == 32
    isMap :: Expr Buf -> Bool
    isMap b = bufLength b == Lit 64
    isMap' :: ByteString -> Bool
    isMap' b = BS.length b == 64
    surelyNotEqual :: Expr EWord -> Expr EWord -> Bool
    surelyNotEqual a b = case (simplifyNoLitToKeccak (Sub a b)) of
      Lit k | k > 0 -> True
      _ -> False
    surelyEqual :: Expr EWord -> Expr EWord -> Bool
    surelyEqual a b = simplifyNoLitToKeccak (Sub a b) == Lit 0


-- storage slots for maps are determined by (keccak (bytes32(key) ++ bytes32(id)))
pattern MappingSlot :: ByteString -> Expr EWord -> Expr EWord
pattern MappingSlot idx key = Keccak (WriteWord (Lit 0) key (ConcreteBuf idx))

-- storage slots for arrays are determined by (keccak(bytes32(id)) + offset)
-- note that `normArgs` puts the Lit as the 1st argument to `Add`
pattern ArraySlotWithOffs :: ByteString -> Expr EWord -> Expr EWord
pattern ArraySlotWithOffs id offset = Add offset (Keccak (ConcreteBuf id))

pattern ArraySlotWithOffs2 :: ByteString -> W256 -> Expr EWord -> Expr EWord
pattern ArraySlotWithOffs2 id offs1 offs2 = Add (Lit offs1) (Add offs2 (Keccak (ConcreteBuf id)))

-- special pattern to match the 0th element because the `Add` term gets simplified out
pattern ArraySlotZero :: ByteString -> Expr EWord
pattern ArraySlotZero id = Keccak (ConcreteBuf id)
-- checks if two mapping ids match or not
idsDontMatch :: ByteString -> ByteString -> Bool
idsDontMatch a b = BS.length a >= 64 && BS.length b >= 64 && diff32to64Byte a b
  where
    diff32to64Byte :: ByteString -> ByteString -> Bool
    diff32to64Byte x y = x32 /= y32
      where
       x32 = BS.take 32 $ BS.drop 32 x
       y32 = BS.take 32 $ BS.drop 32 y

slotPos :: Word8 -> ByteString
slotPos pos = BS.replicate 31 0 <> BS.singleton pos

-- Optimized litToArrayPreimage using the pre-computed map
litToArrayPreimage :: W256 -> Maybe (Word8, W256)
litToArrayPreimage val =
  -- Find the largest 'imageHashKey' in our map such that 'imageHashKey <= val'.
  case Map.lookupLE val preImageLookupMap of
    Just (foundImageHashKey, array_id) ->
      -- 'foundImageHashKey' is one of the keccak hashes from preImagesSource.
      -- 'array_id' is the original Word8 (0-255) that produced this hash.

      -- We have found an 'foundImageHashKey' such that 'foundImageHashKey <= val'.
      -- Now we must check if 'val' is also within the 256-byte range starting at 'foundImageHashKey',
      -- i.e., 'val <= foundImageHashKey + 255'.
      if val <= foundImageHashKey + 255 then
        Just (array_id, val - foundImageHashKey) -- Return the id and the offset from the hash
      else
        -- 'val' is greater than the upper bound for 'foundImageHashKey'.
        -- Since 'foundImageHashKey' was the largest key <= 'val', no other
        -- (smaller) key in the map could satisfy the condition for its interval if this one doesn't.
        Nothing
    Nothing ->
      -- No key in 'preImageLookupMap' is less than or equal to 'val'.
      -- This implies 'val' is smaller than all computed 'image' hashes.
      Nothing

litToKeccak :: Expr a -> Expr a
litToKeccak e = mapExpr go e
  where
    go :: Expr a -> Expr a
    go orig@(Lit key) = case litToArrayPreimage key of
      Just (array, offset) -> ArraySlotWithOffs (slotPos array) (Lit offset)
      _ -> orig
    go otherNode = otherNode

-- | Writes a value to a key in a storage expression.
--
-- Concrete writes on top of a concrete or empty store will produce a new
-- ConcreteStore, otherwise we add a new write to the storage expression.
writeStorage :: Expr EWord -> Expr EWord -> Expr Storage -> Expr Storage
writeStorage k@(Lit key) v@(Lit val) store = case store of
  ConcreteStore s -> ConcreteStore (Map.insert key val s)
  _ -> SStore k v store
writeStorage key val store@(SStore key' val' prev)
     = if key == key'
       -- if we're overwriting an existing location, then drop the write
       then SStore key val prev
       else case (key, key') of
              -- if we can know statically that the new write doesn't overlap with the existing write, then we continue down the write chain
              -- we impose an ordering relation on the writes that we push down to ensure termination when this routine is called from the simplifier
              (Lit k, Lit k') -> if k > k'
                                 then SStore key' val' (writeStorage key val prev)
                                 else SStore key val store
              -- otherwise stack a new write on top of the the existing write chain
              _ -> SStore key val store
writeStorage key val store = SStore key val store

-- Used to check if the underlying concrete store contains a key. Used to decide
-- if we need to fetch a storage slot from RPC or not
concStoreContains :: Expr EWord -> Expr Storage -> Bool
concStoreContains k@(Lit key) store = case store of
  ConcreteStore s -> Map.member key s
  SStore _ _ s -> concStoreContains k s
  AbstractStore _ _ -> internalError "cannot read deeply into an AbstractStore"
  GVar _ -> internalError "cannot read to a GVar"
concStoreContains _ _ = internalError "readDeepStorage only supports concrete keys"

getAddr :: Expr Storage -> Maybe (Expr EAddr)
getAddr (SStore _ _ p) = getAddr p
getAddr (AbstractStore a _) = Just a
getAddr (ConcreteStore _) = Nothing
getAddr (GVar _) = internalError "cannot determine addr of a GVar"

getLogicalIdx :: Expr Storage -> Maybe W256
getLogicalIdx (SStore _ _ p) = getLogicalIdx p
getLogicalIdx (AbstractStore _ idx) = idx
getLogicalIdx (ConcreteStore _) = Nothing
getLogicalIdx (GVar _) = internalError "cannot determine addr of a GVar"


-- ** Whole Expression Simplification ** -----------------------------------------------------------


data StorageType = SmallSlot | Array | Map | Mixed | UNK
  deriving (Show, Eq)

-- We can't currently decompose cases when the FULL returned state is equated
-- This is because the decomposition would need to take into account that ALL
-- maps/arrays/small-slots need to be equivalent. This could be done, but is left
-- as a TODO. Currently this only affects equivalence checking as there is no
-- EVM bytecode to compare the FULL state, so such comparison could only be
-- generated via hevm itself
safeToDecomposeProp :: Prop -> Bool
safeToDecomposeProp p = isJust $ mapPropM' findPEqStore p
  where
    findPEqStore :: Prop -> Maybe Prop
    findPEqStore = \case
      (PEq (SStore {}) (SStore {})) -> Nothing
      (PEq (AbstractStore {}) (SStore {})) -> Nothing
      (PEq (SStore {}) (AbstractStore {})) -> Nothing
      (PEq (AbstractStore {}) (AbstractStore {})) -> Nothing
      a -> Just a

-- This checks if the decomposition is possible by making sure there is no
-- mixture of different types of accesses such as array/map/small-slot.
safeToDecompose :: Expr a -> Maybe ()
safeToDecompose inp = if result /= Mixed then Just () else Nothing
  where
    result = execState (safeToDecomposeRunner inp) UNK

    safeToDecomposeRunner :: forall a. Expr a -> State StorageType ()
    safeToDecomposeRunner a = go a

    go :: forall b. Expr b -> State StorageType ()
    go e@(SLoad (MappingSlot x _) _) = if BS.length x == 64 then setMap e else setMixed e
    go e@(SLoad (Keccak x) _) = case bufLength x of
                                  Lit 32 -> setArray e
                                  Lit 64 -> setMap e
                                  _ -> setMixed e
    go e@(SLoad (ArraySlotWithOffs x _) _) = if BS.length x == 32 then setArray e else setMixed e
    go e@(SLoad (ArraySlotWithOffs2 x _ _) _) = if BS.length x == 32 then setArray e else setMixed e
    go e@(SLoad (Lit x) _) | x < 256 = setSmall e
    go e@(SLoad _ _) = setMixed e
    go e@(SStore (MappingSlot x _) _ _) = if BS.length x == 64 then setMap e else setMixed e
    go e@(SStore (Keccak x) _ _) =  case bufLength x of
                                  Lit 32 -> setArray e
                                  Lit 64 -> setMap e
                                  _ -> setMixed e
    go e@(SStore (ArraySlotWithOffs x _) _ _) = if BS.length x == 32 then setArray e else setMixed e
    go e@(SStore (ArraySlotWithOffs2 x _ _) _ _) = if BS.length x == 32 then setArray e else setMixed e
    go e@(SStore (Lit x) _ _) | x < 256 = setSmall e
    go e@(SStore _ _ _) = setMixed e
    go _ = pure ()

    -- Helper functions for detecting mixed load/store
    setMixed _ = do
      put Mixed
      pure ()
    setMap _ = do
      s <- get
      case s of
        Array -> put Mixed
        SmallSlot -> put Mixed
        UNK -> put Map
        _ -> pure ()
      pure ()
    setArray _ = do
      s <- get
      case s of
        Map -> put Mixed
        SmallSlot -> put Mixed
        UNK -> put Array
        _ -> pure ()
      pure ()
    setSmall _ = do
      s <- get
      case s of
        Map -> put Mixed
        Array -> put Mixed
        UNK -> put SmallSlot
        _ -> pure ()
      pure ()

-- | Splits storage into logical sub-stores if (1) all SLoad->SStore* chains are one of:
--     (1a) Lit < 256, (1b) MappingSlot, (1c) ArraySlotWithOffs, (1d) ArraySlotZero
--  and (2) there is no mixing of different types (e.g. Map with Array) within
--  the same SStore -> SLoad* chain
--
--  Mixing (2) and (3) are attempted to be prevented (if possible) as part of the rewrites
--  done by the `readStorage` function that is ran before this. If there is still mixing here,
--  we abort with a Nothing.
--
--  We do NOT rewrite stand-alone `SStore`-s (i.e. SStores that are not read), since
--  they are often used to describe a post-state, and are not dispatched as-is to
--  the solver
decomposeStorage :: Expr a -> Maybe (Expr a)
decomposeStorage = go
  where
    go :: Expr a -> Maybe (Expr a)
    go (SLoad key store) = tryRewrite key store
    go e = Just e

    tryRewrite :: Expr EWord -> Expr Storage -> Maybe (Expr EWord)
    tryRewrite origKey store = case inferLogicalIdx origKey of
      Just (idx, key) -> do
        base <- setLogicalBase idx store
        pure (SLoad key base)
      _ -> Nothing

    -- NOTE: we use (Maybe W256) for idx here, because for small slot numbers we want to keep the
    -- Logical Store value a Nothing
    inferLogicalIdx :: Expr EWord -> Maybe (Maybe W256, Expr EWord)
    inferLogicalIdx = \case
      Lit a | a >= 256 -> Nothing
      Lit a -> Just (Nothing, Lit a)
      -- maps
      (Keccak (ConcreteBuf k)) | BS.length k == 64 -> do
        let key = idxToWord (BS.take 32 k)
            idx = Lit $ idxToWord (BS.drop 32 k)
        Just (Just key, idx)
      (MappingSlot idx key) | BS.length idx == 64 -> Just (Just $ idxToWord idx, key)
      -- arrays
      (ArraySlotWithOffs idx offset) | BS.length idx == 32 -> Just (Just $ idxToWord64 idx, offset)
      (ArraySlotWithOffs2 idx offs1 offs2) | BS.length idx == 32 -> Just (Just $ idxToWord64 idx, Add (Lit offs1) offs2)
      (ArraySlotZero idx) | BS.length idx == 32 -> Just (Just $ idxToWord64 idx, Lit 0)
      _ -> Nothing

    idxToWord :: ByteString -> W256
    idxToWord = W256 . word256 . (BS.takeEnd 32)
    -- Arrays take the whole `id` and keccak it. It's supposed to be 64B
    idxToWord64 :: ByteString -> W256
    idxToWord64 = W256 . word256 . (BS.takeEnd 64)

    -- Updates the logical base store of the given expression if it is safe to do so
    setLogicalBase :: Maybe W256 -> Expr Storage -> Maybe (Expr Storage)

    setLogicalBase idx (AbstractStore addr Nothing) = Just $ AbstractStore addr idx
    setLogicalBase idx (AbstractStore addr idx2) | idx == idx2 = Just $ AbstractStore addr idx
    setLogicalBase _ (AbstractStore _ _) = internalError "we only rewrite idx once, on load"
    setLogicalBase idx (SStore k v prevStorage) = do
      (idx2, key2) <- inferLogicalIdx k
      b <- setLogicalBase idx prevStorage
      -- If it's not the same IDX, we can skip. This is possible because there are no
      -- mixed arrays/maps/small-slots, as checked by safeToDecompose
      if idx == idx2 then Just (SStore key2 v b)
      else setLogicalBase idx b

    -- empty concrete base is safe to reuse without any rewriting
    setLogicalBase _ s@(ConcreteStore m) | Map.null m = Just s

    -- if the existing base is concrete but we have writes to only keys < 256
    -- then we can safely rewrite the base to an empty ConcreteStore (safe because we assume keccack(x) > 256)
    setLogicalBase _ (ConcreteStore store) =
      if all (< 256) (Map.keys store)
      then Just (ConcreteStore mempty)
      else Nothing
    setLogicalBase _ (GVar _) = internalError "Unexpected GVar"


-- | Simple recursive match based AST simplification
-- Note: may not terminate!
simplify :: Expr a -> Expr a
simplify e = untilFixpoint (simplifyNoLitToKeccak . litToKeccak) e

simplifyNoLitToKeccak :: Expr a -> Expr a
simplifyNoLitToKeccak l@(Lit _) = l
simplifyNoLitToKeccak s@(ConcreteStore _) = s
simplifyNoLitToKeccak e = untilFixpoint (mapExpr go) e
  where
    go :: Expr a -> Expr a

    go (Failure a b c) = Failure (simplifyProps a) b c
    go (Partial a b c) = Partial (simplifyProps a) b c
    go (Success a b c d) = Success (simplifyProps a) b c d

    -- redundant CopySlice
    go (CopySlice (Lit 0x0) (Lit 0x0) (Lit 0x0) _ dst) = dst
    -- We write over dst with data from src. As long as we read from where we write, and
    --    it's the same size, we can just skip the 2nd CopySlice
    go (CopySlice readOff dstOff size2 (CopySlice srcOff writeOff size1 src _) dst) |
      size1 == size2 && readOff == writeOff = CopySlice srcOff dstOff size1 src dst
    -- overwrite empty buf with a buf, return is the buf
    go (CopySlice (Lit 0) (Lit 0) (BufLength src1) src2 (ConcreteBuf "")) | src1 == src2 = src1

    -- simplify storage
    go (SLoad slot store) = readStorage' slot store
    go (SStore slot val store) = writeStorage slot val store

    -- simplify buffers
    go o@(ReadWord (Lit _) _) = simplifyReads o
    go (ReadWord idx buf) = readWord idx buf
    go o@(ReadByte (Lit _) _) = simplifyReads o
    go (ReadByte idx buf) = readByte idx buf
    go (BufLength buf) = bufLength buf

    go (WriteWord a b c) = writeWord a b c

    go (WriteByte a b c) = writeByte a b c

    -- eliminate a CopySlice if the resulting buffer is the same as the src buffer
    go (CopySlice (Lit 0) (Lit 0) (Lit s) src (ConcreteBuf ""))
      | bufLength src == (Lit s) = src

    -- truncate some concrete source buffers to the portion relevant for the CopySlice if we're copying a fully concrete region
    go orig@(CopySlice srcOff@(Lit n) dstOff size@(Lit sz)
        -- It doesn't matter what wOffs we write to, because only the first
        -- n+sz of ConcreteBuf will be used by CopySlice
        (WriteWord wOff value (ConcreteBuf buf)) dst)
          -- Let's not deal with overflow
          | n+sz >= n
          , n+sz >= sz
          , n+sz <= maxBytes
            = (CopySlice srcOff dstOff size
                (WriteWord wOff value (ConcreteBuf simplifiedBuf)) dst)
          | otherwise = orig
            where simplifiedBuf = BS.take (unsafeInto (n+sz)) buf
    go (CopySlice a b c d f) = copySlice a b c d f

    go (JoinBytes (LitByte a0)  (LitByte a1)  (LitByte a2)  (LitByte a3)
      (LitByte a4)  (LitByte a5)  (LitByte a6)  (LitByte a7)
      (LitByte a8)  (LitByte a9)  (LitByte a10) (LitByte a11)
      (LitByte a12) (LitByte a13) (LitByte a14) (LitByte a15)
      (LitByte a16) (LitByte a17) (LitByte a18) (LitByte a19)
      (LitByte a20) (LitByte a21) (LitByte a22) (LitByte a23)
      (LitByte a24) (LitByte a25) (LitByte a26) (LitByte a27)
      (LitByte a28) (LitByte a29) (LitByte a30) (LitByte a31)) =
        let b =  map fromIntegral [a0, a1, a2, a3 ,a4, a5, a6, a7
                                  ,a8, a9, a10, a11 ,a12, a13, a14, a15
                                  ,a16, a17, a18, a19 ,a20, a21, a22, a23
                                  ,a24, a25, a26, a27 ,a28, a29, a30, a31]
        in Lit (constructWord256 b)

    go (IndexWord a b) = indexWord a b


    go (SEx a (SEx a2 b)) | a == a2  = sex a b
    go (SEx _ (Lit 0)) = Lit 0
    go (SEx a b) = sex a b

    -- IsZero
    go (IsZero (IsZero (IsZero a))) = iszero a
    go (IsZero (IsZero (LT x y))) = lt x y
    go (IsZero (IsZero (Eq x y))) = eq x y
    go (IsZero (IsZero a)) = lt (Lit 0) a
    go (IsZero (Xor x y)) = eq x y
    go (IsZero (Sub a b)) = eq a b
    go (IsZero (Or a b)) = EVM.Expr.and (iszero a) (iszero b)
    go (IsZero a) = iszero a

    -- ITE (if-then-else) simplification for path merging
    go (ITE (Lit 0) _ f) = f
    go (ITE (Lit _) t _) = t
    go (ITE _ t f) | t == f = t
    go (ITE c (ITE c' a _) d) | c == c' = ITE c a d -- nested same condition in then
    go (ITE c a (ITE c' _ d)) | c == c' = ITE c a d -- nested same condition in else

    -- syntactic Eq reduction
    go (Eq (Lit a) (Lit b))
      | a == b = Lit 1
      | otherwise = Lit 0
    go (Eq (Lit 0) (Sub a b)) = eq a b
    go (Eq (Lit 0) (Xor a b)) = eq a b
    go (Eq (Add a b) c)
      | a == c = iszero b
      | b == c = iszero a
    go (Eq (Sub a b) c)
      | a == c = iszero b
    go (Eq (Xor a b) c)
      | a == c = iszero b
      | b == c = iszero a

    go (Eq (Lit 0) a) = iszero a
    go (Eq a b)
      | a == b = Lit 1
      | otherwise = eq a b

    -- COMPARISONS
    -- First special cases

    -- we write at least 32, so if x <= 32, it's FALSE
    go o@(EVM.Types.LT (BufLength (WriteWord {})) (Lit x))
      | x <= 32 = Lit 0
      | otherwise = o
    -- we write at least 32, so if x < 32, it's TRUE
    go o@(EVM.Types.LT (Lit x) (BufLength (WriteWord {})))
      | x < 32 = Lit 1
      | otherwise = o

    -- If a >= b then the value of the `Max` expression can never be < b
    go o@(LT (Max (Lit a) _) (Lit b))
      | a >= b = Lit 0
      | otherwise = o
    go o@(SLT (Sub (Max (Lit a) _) (Lit b)) (Lit c))
      = let sa, sb, sc :: Int256
            sa = fromIntegral a
            sb = fromIntegral b
            sc = fromIntegral c
        in if sa >= sb && sa - sb >= sc
           then Lit 0
           else o

    -- normalize all comparisons in terms of (S)LT
    go (EVM.Types.GT a b) = lt b a
    go (EVM.Types.GEq a b) = iszero (lt a b)
    go (EVM.Types.LEq a b) = iszero (lt b a)
    go (SGT a b) = slt b a

    -- LT
    go (EVM.Types.LT _ (Lit 0)) = Lit 0
    go (EVM.Types.LT (Lit a) _) | a == maxLit = Lit 0
    go (EVM.Types.LT a (Lit 1)) = iszero a
    go (EVM.Types.LT a b) = lt a b

    -- SLT
    go (SLT _ (Lit a)) | a == minLitSigned = Lit 0
    go (SLT (Lit a) _) | a == maxLitSigned = Lit 0
    go (SLT a b) = slt a b

    -- Masking as as per Solidity bit-packing of e.g. function parameters
    go (And (Lit mask1) (Or (And (Lit mask2) _) x)) | (mask1 .&. mask2 == 0)
         = And (Lit mask1) x

    -- address masking
    go (And (Lit 0xffffffffffffffffffffffffffffffffffffffff) a@(WAddr _)) = a

    -- literal addresses
    go (WAddr (LitAddr a)) = Lit $ into a

    -- Mod
    go (Mod _ (Lit 0)) = Lit 0
    go (Mod _ (Lit 1)) = Lit 0
    go (SMod _ (Lit 0)) = Lit 0
    go (SMod _ (Lit 1)) = Lit 0
    go (Mod a b) | a == b = Lit 0
    go (SMod a b) | a == b = Lit 0
    go (Mod (Lit 0) _) = Lit 0
    go (SMod (Lit 0) _) = Lit 0

    -- MulMod
    go (MulMod (Lit 0) _ _) = Lit 0
    go (MulMod _ (Lit 0) _) = Lit 0
    go (MulMod _ _ (Lit 0)) = Lit 0
    go (MulMod a b c) = mulmod a b c

    -- AddMod
    go (AddMod (Lit 0) a b) = Mod a b
    go (AddMod a (Lit 0) b) = Mod a b
    go (AddMod _ _ (Lit 0)) = Lit 0
    go (AddMod a b c) = addmod a b c

    -- Triple And (must be before 3-way sort below)
    go (And (Lit a) (And (Lit b) c)) = And (EVM.Expr.and (Lit a) (Lit b)) c

    -- double add/sub.
    -- Notice that everything is done mod 2**256. So for example:
    -- (a-b)+c observes the same arithmetic equalities as we are used to
    --         in infinite integers. In fact, it can be re-written as:
    -- (a+(W256Max-b)+c), which is the same as:
    -- (a+c+(W256Max-b)), which is the same as:
    -- (a+(c-b))
    -- In other words, subtraction is just adding a much larger number.
    --    So 3-1 mod 6 = 3+(6-1) mod 6 = 3+5 mod 6 = 5+3 mod 6 = 2
    -- Notice: all Add is normalized, hence the 1st argument is
    --    expected to be Lit, if any. Hence `orig` needs to be the
    --    2nd argument for Add. However, Sub is not normalized
    -- add + sub NOTE: every combination of Sub is needed (2)
    go (Add (Lit x) (Sub (Lit y) orig)) = sub (Lit (x+y)) orig
    go (Add (Lit x) (Sub orig (Lit y))) = add (Lit (x-y)) orig
    -- sub + sub NOTE: every combination of Sub is needed (2x2)
    go (Sub (Lit x) (Sub (Lit y) orig)) = add (Lit (x-y)) orig
    go (Sub (Lit x) (Sub orig (Lit y))) = sub (Lit (x+y)) orig
    go (Sub (Sub (Lit x) orig) (Lit y)) = sub (Lit (x-y)) orig
    go (Sub (Sub orig (Lit x)) (Lit y)) = sub orig (Lit (x+y))
    -- sub + add NOTE: every combination of Sub is needed (2)
    go (Sub (Lit x) (Add (Lit y) orig)) = sub (Lit (x-y)) orig
    go (Sub (Add (Lit x) orig) (Lit y) ) = add (Lit (x-y)) orig

    -- Add+Add / Mul+Mul / Xor+Xor simplifications, taking
    --     advantage of associativity and commutativity
    -- Since Lit is smallest in the ordering, it will always be the first argument
    --     hence these will collect Lits. See `simp-assoc..` tests
    go (Add (Lit a) (Add (Lit b) x)) = add (Lit (a+b)) x
    go (Mul (Lit a) (Mul (Lit b) x)) = mul (Lit (a*b)) x
    go (Xor (Lit a) (Xor (Lit b) x)) = EVM.Expr.xor (Lit (Data.Bits.xor a b)) x
    go (Add (Add a b) c) = add (l !! 0) (add (l !! 1) (l !! 2))
      where l = sort [a, b, c]
    go (Add a (Add b c)) = add (l !! 0) (add (l !! 1) (l !! 2))
      where l = sort [a, b, c]
    go (Mul (Mul a b) c) = mul (l !! 0) (mul (l !! 1) (l !! 2))
      where l = sort [a, b, c]
    go (Mul a (Mul b c)) = mul (l !! 0) (mul (l !! 1) (l !! 2))
      where l = sort [a, b, c]
    go (Xor (Xor a b) c) = x (l !! 0) (x (l !! 1) (l !! 2))
      where l = sort [a, b, c]
            x = EVM.Expr.xor
    go (Xor a (Xor b c)) = x (l !! 0) (x (l !! 1) (l !! 2))
      where l = sort [a, b, c]
            x = EVM.Expr.xor
    go (Or (Or a b) c) = o (l !! 0) (o (l !! 1) (l !! 2))
      where l = sort [a, b, c]
            o = EVM.Expr.or
    go (Or a (Or b c)) = o (l !! 0) (o (l !! 1) (l !! 2))
      where l = sort [a, b, c]
            o = EVM.Expr.or
    go (And (And a b) c) = an (l !! 0) (an (l !! 1) (l !! 2))
      where l = sort [a, b, c]
            an = EVM.Expr.and
    go (And a (And b c)) = an (l !! 0) (an (l !! 1) (l !! 2))
      where l = sort [a, b, c]
            an = EVM.Expr.and

    -- redundant add / sub
    go (Sub (Add a b) c)
      | a == c = b
      | b == c = a
      | otherwise = sub (add a b) c

    -- canonicalize Sub to top level
    go (Add a (Sub b c)) = sub (add a b) c
    go (Sub (Sub a b) c) = sub a (add b c)
    go (Sub a (Sub b c)) = add (sub a b) c

    -- Negation: ~x + 1 = 0 - x (two's complement)
    go (Add (Lit 1) (Not b)) = Sub (Lit 0) b

    -- add / sub identities
    go (Add a b)
      | b == (Lit 0) = a
      | a == (Lit 0) = b
      | otherwise = add a b
    go (Sub a b)
      | a == b = Lit 0
      | b == (Lit 0) = a
      | otherwise = sub a b

    -- XOR normalization
    go (Xor (Lit 0) a) = a
    go (Xor (Lit a) b) | a == maxLit = EVM.Expr.not b
    go (Xor a b) | a == b = Lit 0

    go (Xor a  b) = EVM.Expr.xor a b

    -- Not simplification
    go (EVM.Types.Not (EVM.Types.Not a)) = a
    go (Not a) = EVM.Expr.not a

    -- EqByte
    go (EqByte a b) = eqByte a b

    -- SHL / SHR / SAR
    go (SHL (Lit n) (SHR (Lit m) x))
      | n == m && n < 256 = EVM.Expr.and (Lit (shiftL maxLit (fromIntegral n))) x
    go (SHR (Lit n) (SHL (Lit m) x))
      | n == m && n < 256 = EVM.Expr.and (Lit (shiftR maxLit (fromIntegral n))) x
    go (SHL (Lit a) _) | a >= 256 = Lit 0
    go (SHL a v)
      | a == (Lit 0) = v
      | v == (Lit 0) = v
      | otherwise = shl a v
    go (SHR (Lit a) _) | a >= 256 = Lit 0
    go (SHR a v)
      | a == (Lit 0) = v
      | v == (Lit 0) = v
      | otherwise = shr a v
    go (SAR _ (Lit v)) | v == maxBound = Lit v
    go (SAR a v)
       | a == (Lit 0) = v
       | v == (Lit 0) = v
       | otherwise = sar a v
    go (CLZ v) = clz v

    -- Bitwise AND & OR. These MUST preserve bitwise equivalence
    go (And a (Or b _)) | a == b = a
    go (And a (Or _ b)) | a == b = a
    go (And a (Xor b c))
      | a == b = EVM.Expr.and a (EVM.Expr.not c)
      | a == c = EVM.Expr.and a (EVM.Expr.not b)
    go (And (Xor b c) a)
      | a == b = EVM.Expr.and a (EVM.Expr.not c)
      | a == c = EVM.Expr.and a (EVM.Expr.not b)
    go (And a (Or b c))
      | a == b = a
      | a == c = a
    go (And (Or b c) a)
      | a == b = a
      | a == c = a

    go (And a b)
      | a == b = a
      | b == (Not a) || a == (Not b) = Lit 0
      | a == (Lit 0) || b == (Lit 0) = Lit 0
      | a == (Lit maxLit) = b
      | b == (Lit maxLit) = a
      | otherwise = EVM.Expr.and a b
    go (Or a (And b _)) | a == b = a
    go (Or a (And _ b)) | a == b = a

    go (Or a (Xor b c))
      | a == b = EVM.Expr.or a c
      | a == c = EVM.Expr.or a b
    go (Or (Xor b c) a)
      | a == b = EVM.Expr.or a c
      | a == c = EVM.Expr.or a b
    go (Or a b)
      | a == b = a
      | a == (Lit 0) = b
      | b == (Lit 0) = a
      | a == (Lit maxLit) || b == (Lit maxLit) = Lit maxLit
      | otherwise = EVM.Expr.or a b


    -- Some trivial min / max eliminations
    go (Max a b) = EVM.Expr.max a b
    go (Min a b) = case (a, b) of
                     (Lit 0, _) -> Lit 0
                     _ -> EVM.Expr.min a b


    -- Some trivial mul eliminations
    go (Mul a b) = case (a, b) of
                     (Lit 0, _) -> Lit 0
                     (Lit 1, _) -> b
                     (Lit v, _) | v == maxLit -> Sub (Lit 0) b
                     _ -> mul a b

    -- Some trivial (s)div eliminations
    go (Div (Lit 0) _) = Lit 0 -- divide 0 by anything (including 0) is zero in EVM
    go (Div _ (Lit 0)) = Lit 0 -- divide anything by 0 is zero in EVM
    go (Div a (Lit 1)) = a
    go (SDiv (Lit 0) _) = Lit 0 -- divide 0 by anything (including 0) is zero in EVM
    go (SDiv _ (Lit 0)) = Lit 0 -- divide anything by 0 is zero in EVM
    go (SDiv a (Lit 1)) = a
    -- NOTE: Div x x is NOT 1, because Div 0 0 is 0, not 1.

    --- Some trivial exp eliminations
    go (Exp _ (Lit 0)) = Lit 1 -- everything, including 0, to the power of 0 is 1
    go (Exp a (Lit 1)) = a -- everything, including 0, to the power of 1 is itself
    go (Exp (Lit 1) _) = Lit 1 -- 1 to any value (including 0) is 1
    -- NOTE: we can't simplify (Lit 0)^k. If k is 0 it's 1, otherwise it's 0.
    --       this is encoded in SMT.hs instead, via an SMT "ite"
    --
    -- A special pattern sometimes generated from Solidity that uses exponentiation to simulate bit shift.
    -- We can rewrite the exponentiation into a bit-shift under certain conditions.
    go (Exp (Lit 0x100) offset@(Mul (Lit a) (Mod _ (Lit b))))
      | a * b <= 32 && (maxWord256 `Prelude.div` a) > b = shl (mul (Lit 8) offset) (Lit 1)
    go (Exp (Lit 0x100) offset@(Mod _ (Lit 32))) = (shl (mul (Lit 8) offset)) (Lit 1)
    go (Exp (Lit 2) k) = shl k (Lit 1)
    go (Exp a b) = EVM.Expr.exp a b

    -- simple div/mod/add/sub
    go (Div  o1 o2) = EVM.Expr.div  o1 o2
    go (SDiv o1 o2) = EVM.Expr.sdiv o1 o2
    go (Mod  o1 o2) = EVM.Expr.mod  o1 o2
    go (SMod o1 o2) = EVM.Expr.smod o1 o2

    go a = a


-- ** Prop Simplification ** -----------------------------------------------------------------------


simplifyProps :: [Prop] -> [Prop]
simplifyProps ps = if cannotBeSat then [PBool False] else simplified
  where
    simplified = untilFixpoint goOne ps
    cannotBeSat = PBool False `elem` simplified
    goOne :: [Prop] -> [Prop]
    goOne = remRedundantProps . map simplifyProp . constPropagate . flattenProps


-- | Evaluate the provided proposition down to its most concrete result
-- Also simplifies the inner Expr, if it exists
simplifyProp :: Prop -> Prop
simplifyProp prop =
  let new = mapProp' go (simpInnerExpr prop)
  in if (new == prop) then prop else simplifyProp new
  where
    isBoolLike :: Expr EWord -> Bool
    isBoolLike = \case
      LT{} -> True
      SLT{} -> True
      Eq{} -> True
      IsZero{} -> True
      GT{} -> internalError "Should not encounter GT at this point!"
      LEq{} -> internalError "Should not encounter LEq at this point!"
      GEq{} -> internalError "Should not encounter GEq at this point!"
      _ -> False
    go :: Prop -> Prop

    -- Rewrite PGT/GEq to PLT/PLEq
    go (PGT a b) = PLT b a
    go (PGEq a b) = PLEq b a

    -- PLT/PLEq comparisons
    go (PLT  (Var _) (Lit 0)) = PBool False
    go (PLEq (Lit 0) _) = PBool True
    go (PLEq (WAddr _) (Lit 1461501637330902918203684832716283019655932542975)) = PBool True
    go (PLEq _ (Lit x)) | x == maxLit = PBool True
    go (PLT  (Lit val) (Var _)) | val == maxLit = PBool False
    go (PLEq (Var _) (Lit val)) | val == maxLit = PBool True
    go (PLT a b) | a == b = PBool False
    go (PLT (Lit l) (Lit r)) = PBool (l < r)
    go (PLEq a b) | a == b = PBool True
    go (PLEq (Lit l) (Lit r)) = PBool (l <= r)
    go (PLEq a (Max b _)) | a == b = PBool True
    go (PLEq a (Max _ b)) | a == b = PBool True
    go (PLEq (Sub a b) c) | a == c = PLEq b a
    go (PLEq a (Lit 0)) = peq (Lit 0) a
    go (PLT (Max (Lit a) b) (Lit c)) | a < c = PLT b (Lit c)

    go (PLT (Lit 0) e)
      | isBoolLike e = peq (Lit 1) e

    -- all possible simplifications for PLT and PLEq have to be covered by this point
    go p@(PLT {}) = p
    go p@(PLEq {}) = p

    go (PEq (Lit 1) (Eq a b)) = peq a b
    go (PEq (Lit 1) (LT a b)) = PLT a b
    go (PEq (Lit 1) (IsZero e)) = PEq (Lit 0) e

    go (PEq (Lit 0) (IsZero e))
      | isBoolLike e = PEq (Lit 1) e
    go (PEq (Lit 0) (IsZero e)) = PNeg (PEq (Lit 0) e)
    go (PEq (Lit 0) (Eq a b)) = PNeg (peq a b)
    go (PEq (Lit 0) (LT a b)) = PLEq b a

    go (PEq (Lit 0) (Sub a b)) = peq a b
    go (PEq (Lit 0) (Or a b)) = peq (Lit 0) a `PAnd` peq (Lit 0) b
    go (PEq a1 (Add a2 y)) | a1 == a2 = peq (Lit 0) y
    go (PEq l r) = peq l r

    go (POr (PLEq a1 (Lit b)) (PLEq (Lit c) a2)) | a1 == a2 && c == b+1 = PBool True

    -- negations
    go (PNeg (PBool b)) = PBool (Prelude.not b)
    go (PNeg (PNeg a)) = a
    go (PNeg (PGT a b)) = PLEq a b
    go (PNeg (PGEq a b)) = PLT a b
    go (PNeg (PLT a b)) = PLEq b a
    go (PNeg (PLEq a b)) = PLT b a
    go (PNeg (PAnd a b)) = POr (PNeg a) (PNeg b)
    go (PNeg (POr a b)) = PAnd (PNeg a) (PNeg b)
    go (PNeg (PEq (Lit 1) e))
      | isBoolLike e = PEq (Lit 0) e
    go (PNeg (PEq (Lit 0) e))
      | isBoolLike e = PEq (Lit 1) e

    -- And/Or
    go (PAnd (PBool l) (PBool r)) = PBool (l && r)
    go (PAnd (PBool False) _) = PBool False
    go (PAnd _ (PBool False)) = PBool False
    go (PAnd (PBool True) x) = x
    go (PAnd x (PBool True)) = x
    go (POr (PBool True) _) = PBool True
    go (POr _ (PBool True)) = PBool True
    go (POr (PBool l) (PBool r)) = PBool (l || r)
    go (POr x (PBool False)) = x
    go (POr (PBool False) x) = x

    -- Absoption rules
    go (PAnd a (POr b _)) | a == b = a
    go (PAnd a (POr _ b)) | a == b = a
    go (POr a (PAnd b _)) | a == b = a
    go (POr a (PAnd _ b)) | a == b = a

    -- Imply
    go (PImpl _ (PBool True)) = PBool True
    go (PImpl (PBool True) b) = b
    go (PImpl (PBool False) _) = PBool True
    go (PImpl a b) | a == b = PBool True


    go p = p


    -- Applies `simplify` to the inner part of a Prop, e.g.
    -- (PEq (Add (Lit 1) (Lit 2)) (Var "a")) becomes
    -- (PEq (Lit 3) (Var "a")
    simpInnerExpr :: Prop -> Prop
    -- rewrite everything as LEq or LT
    simpInnerExpr (PGEq a b) = simpInnerExpr (PLEq b a)
    simpInnerExpr (PGT a b) = simpInnerExpr (PLT b a)
    -- simplifies the inner expression
    simpInnerExpr (PEq a b) = PEq (simplify a) (simplify b)
    simpInnerExpr (PLT a b) = PLT (simplify a) (simplify b)
    simpInnerExpr (PLEq a b) = PLEq (simplify a) (simplify b)
    simpInnerExpr (PNeg a) = PNeg (simpInnerExpr a)
    simpInnerExpr (PAnd a b) = PAnd (simpInnerExpr a) (simpInnerExpr b)
    simpInnerExpr (POr a b) = POr (simpInnerExpr a) (simpInnerExpr b)
    simpInnerExpr (PImpl a b) = PImpl (simpInnerExpr a) (simpInnerExpr b)
    simpInnerExpr orig@(PBool _) = orig

-- Makes [PAnd a b] into [a,b]
flattenProps :: [Prop] -> [Prop]
flattenProps [] = []
flattenProps (a:ax) = case a of
  PAnd x1 x2 -> flattenProps [x1] ++ flattenProps [x2] ++ flattenProps ax
  x -> x:flattenProps ax

-- removes redundant (constant True/False) props
remRedundantProps :: [Prop] -> [Prop]
remRedundantProps p = nubOrd $ collapseFalse . filter (\x -> x /= PBool True) $ p
  where
    collapseFalse ps = if isJust $ find (== PBool False) ps then [PBool False] else ps


-- ** Conversions ** -------------------------------------------------------------------------------


litAddr :: Addr -> Expr EWord
litAddr = Lit . into

exprToAddr :: Expr EWord -> Maybe Addr
exprToAddr (Lit x) = Just (unsafeInto x)
exprToAddr _ = Nothing

-- TODO: make this smarter, probably we will need to use the solver here?
wordToAddr :: Expr EWord -> Maybe (Expr EAddr)
wordToAddr e = case (concKeccakSimpExpr e) of
  WAddr a -> Just a
  Lit a -> Just $ LitAddr (truncateToAddr a)
  _ -> Nothing

litCode :: BS.ByteString -> [Expr Byte]
litCode bs = fmap LitByte (BS.unpack bs)


-- ** Helpers ** -----------------------------------------------------------------------------------


-- Is the given expr a literal byte?
isLitByte :: Expr Byte -> Bool
isLitByte (LitByte _) = True
isLitByte _ = False

-- Is the given expr a literal word?
isLitWord :: Expr EWord -> Bool
isLitWord (Lit _) = True
isLitWord (WAddr (LitAddr _)) = True
isLitWord _ = False

isSuccess :: Expr End -> Bool
isSuccess = \case
  Success {} -> True
  _ -> False

isFailure :: Expr End -> Bool
isFailure = \case
  Failure {} -> True
  _ -> False

isPartial :: Expr End -> Bool
isPartial = \case
  Partial {} -> True
  _ -> False

isSymAddr :: Expr EAddr -> Bool
isSymAddr (SymAddr _) = True
isSymAddr _ = False

-- | Returns the byte at idx from the given word.
indexWord :: Expr EWord -> Expr EWord -> Expr Byte
-- Simplify masked reads:
--
--
--                reads across the mask boundary
--                return an abstract expression
--                            │
--                            │
--   reads outside of         │             reads over the mask read
--   the mask return 0        │             from the underlying word
--          │                 │                       │
--          │           ┌─────┘                       │
--          ▼           ▼                             ▼
--        ┌───┐       ┌─┬─┬─────────────────────────┬───┬──────────────┐
--        │   │       │ │ │                         │   │              │    mask
--        │   │       │ └─┼─────────────────────────┼───┼──────────────┘
--        │   │       │   │                         │   │
--    ┌───┼───┼───────┼───┼─────────────────────────┼───┼──────────────┐
--    │   │┼┼┼│       │┼┼┼│                         │┼┼┼│              │    w
--    └───┴───┴───────┴───┴─────────────────────────┴───┴──────────────┘
--   MSB                                                              LSB
--    ────────────────────────────────────────────────────────────────►
--    0                                                               31
--
--                    indexWord 0 reads from the MSB
--                    indexWord 31 reads from the LSB
--
indexWord i@(Lit idx) e@(And (Lit mask) w)
  -- if the mask is all 1s then read from the underlying word
  -- we need this case to avoid overflow
  | mask == fullWordMask = indexWord (Lit idx) w
  -- if the index is a read from the masked region then read from the underlying word
  | idx <= 31
  , isPower2 (mask + 1)
  , isByteAligned mask
  , idx >= unmaskedBytes
    = indexWord (Lit idx) w
  -- if the read is outside of the masked region return 0
  | idx <= 31
  , isPower2 (mask + 1)
  , isByteAligned mask
  , idx < unmaskedBytes
    = LitByte 0
  -- if the mask is not a power of 2, or it does not align with a byte boundary return an abstract expression
  | idx <= 31 = IndexWord i e
  -- reads outside the range of the source word return 0
  | otherwise = LitByte 0
  where
    isPower2 n = n .&. (n-1) == 0
    fullWordMask = (2 ^ (256 :: W256)) - 1
    unmaskedBytes = fromIntegral $ (countLeadingZeros mask) `Prelude.div` 8
    isByteAligned m = (countLeadingZeros m) `Prelude.mod` 8 == 0
-- This pattern happens in Solidity for function selectors. Since Lit 0xfff... (28 bytes of 0xff)
-- is masking the function selector, it can be simplified to just the function selector bytes. Remember,
-- indexWord takes the MSB i-th byte when called with (indexWord i).
indexWord (Lit a) (Or funSel (And (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff) _)) | a < 4 =
  indexWord (Lit a) funSel
indexWord (Lit idx) (Lit w)
  | idx <= 31 = LitByte . fromIntegral $ shiftR w (248 - unsafeInto idx * 8)
  | otherwise = LitByte 0
indexWord (Lit idx) (JoinBytes zero        one        two       three
                               four        five       six       seven
                               eight       nine       ten       eleven
                               twelve      thirteen   fourteen  fifteen
                               sixteen     seventeen  eighteen  nineteen
                               twenty      twentyone  twentytwo twentythree
                               twentyfour  twentyfive twentysix twentyseven
                               twentyeight twentynine thirty    thirtyone)
  | idx == 0 = zero
  | idx == 1 = one
  | idx == 2 = two
  | idx == 3 = three
  | idx == 4 = four
  | idx == 5 = five
  | idx == 6 = six
  | idx == 7 = seven
  | idx == 8 = eight
  | idx == 9 = nine
  | idx == 10 = ten
  | idx == 11 = eleven
  | idx == 12 = twelve
  | idx == 13 = thirteen
  | idx == 14 = fourteen
  | idx == 15 = fifteen
  | idx == 16 = sixteen
  | idx == 17 = seventeen
  | idx == 18 = eighteen
  | idx == 19 = nineteen
  | idx == 20 = twenty
  | idx == 21 = twentyone
  | idx == 22 = twentytwo
  | idx == 23 = twentythree
  | idx == 24 = twentyfour
  | idx == 25 = twentyfive
  | idx == 26 = twentysix
  | idx == 27 = twentyseven
  | idx == 28 = twentyeight
  | idx == 29 = twentynine
  | idx == 30 = thirty
  | idx == 31 = thirtyone
  | otherwise = LitByte 0
indexWord idx w = IndexWord idx w


padByte :: Expr Byte -> Expr EWord
padByte (LitByte b) = Lit . bytesToW256 $ [b]
padByte b = joinBytes [b]

-- | Converts a list of bytes into a W256.
-- TODO: semantics if the input is too large?
bytesToW256 :: [Word8] -> W256
bytesToW256 = word . BS.pack

padBytesLeft :: Int -> [Expr Byte] -> [Expr Byte]
padBytesLeft n bs
  | length bs > n = Prelude.take n bs
  | length bs == n = bs
  | otherwise = padBytesLeft n (LitByte 0 : bs)

joinBytes :: [Expr Byte] -> Expr EWord
joinBytes bs
  | all isLitByte bs = Lit . bytesToW256 . (mapMaybe maybeLitByteSimp) $ bs
  | otherwise = let
      bytes = padBytesLeft 32 bs
    in JoinBytes
      (bytes !! 0)  (bytes !! 1)  (bytes !! 2)  (bytes !! 3)
      (bytes !! 4)  (bytes !! 5)  (bytes !! 6)  (bytes !! 7)
      (bytes !! 8)  (bytes !! 9)  (bytes !! 10) (bytes !! 11)
      (bytes !! 12) (bytes !! 13) (bytes !! 14) (bytes !! 15)
      (bytes !! 16) (bytes !! 17) (bytes !! 18) (bytes !! 19)
      (bytes !! 20) (bytes !! 21) (bytes !! 22) (bytes !! 23)
      (bytes !! 24) (bytes !! 25) (bytes !! 26) (bytes !! 27)
      (bytes !! 28) (bytes !! 29) (bytes !! 30) (bytes !! 31)

eqByte :: Expr Byte -> Expr Byte -> Expr EWord
eqByte (LitByte x) (LitByte y) = Lit $ if x == y then 1 else 0
eqByte x y = if x < y then EqByte x y else EqByte y x

min :: Expr EWord -> Expr EWord -> Expr EWord
min x y = normArgs Min Prelude.min x y

max :: Expr EWord -> Expr EWord -> Expr EWord
max (Lit 0) y = y
max x (Lit 0) = x
max x y = normArgs Max Prelude.max x y

allLit :: [Expr Byte] -> Bool
allLit = all isLitByte

-- | True if the given expression contains any node that satisfies the
-- input predicate
containsNode :: (forall a. Expr a -> Bool) -> Expr b -> Bool
containsNode p = getAny . foldExpr go (Any False)
  where
    go :: Expr a -> Any
    go node | p node  = Any True
    go _ = Any False

inRange :: Int -> Expr EWord -> Prop
inRange sz e = if sz == 256 then PBool True else PLEq e (Lit $ 2 ^ sz - 1)

-- | images of keccak(bytes32(x)) where 0 <= x < 256
preImages :: [(W256, Word8)]
preImages = [(keccak' (word256Bytes . into $ i), i) | i <- [0..255]]

-- | images of keccak(bytes32(x)) where 0 <= x < 256
preImageLookupMap :: Map.Map W256 Word8
preImageLookupMap = Map.fromList preImages

data ConstState = ConstState
  { values :: Map.Map (Expr EWord) W256
  , lowerBounds :: Map.Map (Expr EWord) W256
  , upperBounds :: Map.Map (Expr EWord) W256
  , canBeSat :: Bool
  }
  deriving (Show)

-- | Performs constant propagation
constPropagate :: [Prop] -> [Prop]
constPropagate ps =
 let consts = collectConsts ps emptyState
 in if consts.canBeSat then substitute consts ps ++ fixVals consts
    else [PBool False]
  where
    -- Fixes the values of the constants
    fixVals :: ConstState -> [Prop]
    fixVals cs = Map.foldrWithKey (\k v acc -> peq (Lit v) k : acc) [] cs.values

    -- Substitutes the constants in the props.
    -- NOTE: will create PEq (Lit x) (Lit x) if x is a constant
    --       hence we need the fixVals function to add them back in
    substitute :: ConstState -> [Prop] -> [Prop]
    substitute cs ps2 = map (mapProp (subsGo cs)) ps2
    subsGo :: ConstState -> Expr a -> Expr a
    subsGo cs (Var v) = case Map.lookup (Var v) cs.values of
      Just x -> Lit x
      Nothing -> Var v
    subsGo _ x = x

    -- Collects all the constants in the given props, and sets canBeSat to False if UNSAT
    collectConsts ps2 startState = execState (mapM go ps2) startState
    emptyState = ConstState mempty mempty mempty True
    conflictState = ConstState mempty mempty mempty False
    conflict = put conflictState

    setExactValue :: Expr EWord -> W256 -> State ConstState ()
    setExactValue e v = do
      s <- get
      case Map.lookup e s.values of
        Just old -> when (old /= v) conflict
        _ -> put s { values = Map.insert e v s.values }

    updateLower :: Expr EWord -> W256 -> State ConstState ()
    updateLower a l = do
      s <- get
      let currentL = fromMaybe 0 (Map.lookup a s.lowerBounds)
          currentU = fromMaybe maxLit (Map.lookup a s.upperBounds)
          newL = Prelude.max currentL l
      if newL > currentU
        then conflict
        else put s { lowerBounds = Map.insert a newL s.lowerBounds }
      when (newL == currentU) $ setExactValue a newL

    updateUpper :: Expr EWord -> W256 -> State ConstState ()
    updateUpper a u = do
      s <- get
      let currentL = fromMaybe 0 (Map.lookup a s.lowerBounds)
          currentU = fromMaybe maxLit (Map.lookup a s.upperBounds)
          newU = Prelude.min currentU u
      if currentL > newU
        then conflict
        else put s { upperBounds = Map.insert a newU s.upperBounds }
      -- Check if equal to lower, then it's a constant
      when (currentL == newU) $ setExactValue a newU

    genericEq :: Expr EWord -> W256 -> State ConstState ()
    genericEq a v = do
      setExactValue a v
      updateLower a v
      updateUpper a v

    go :: Prop -> State ConstState ()
    go = \case
        -- signed inequalities
        PEq (Lit 1) term@(SLT a (Lit 0)) -> do
            genericEq term 1
            updateLower a minLitSigned
        PEq (Lit 1) term@(SLT (Lit 0) a) -> do
            genericEq term 1
            updateLower a 1
            updateUpper a maxLitSigned

        -- normal equality propagation
        PEq (Lit l) a -> genericEq a l
        PEq a (Lit l) -> genericEq a l

        PNeg (PEq (Lit l) a) -> do
          s <- get
          case Map.lookup a s.values of
            Just l2 -> when (l == l2) conflict
            Nothing -> pure ()
        PNeg (PEq a b@(Lit _)) -> go $ PNeg (PEq b a)

        -- inequalities (with overflow checks to prevent wraparound)
        -- PLT a (Lit b) means a < b, so a <= b-1
        PLT a (Lit b) ->
          if b == 0
            then conflict
            else updateUpper a (b - 1)
        -- PLT (Lit a) b means a < b, so b >= a+1
        PLT (Lit a) b ->
          if a == maxLit
            then conflict
            else updateLower b (a + 1)
        -- PLEq a (Lit b) means a <= b
        PLEq a (Lit b) -> updateUpper a b
        PLEq (Lit a) b -> updateLower b a
        -- PGT a (Lit b) means a > b, so a >= b+1
        PGT a (Lit b) ->
          if b == maxLit
            then conflict
            else updateLower a (b + 1)
        -- PGT (Lit a) b means a > b, so b <= a-1
        PGT (Lit a) b ->
          if a == 0
            then conflict
            else updateUpper b (a - 1)
        -- PGEq a (Lit b) means a >= b
        PGEq a (Lit b) -> updateLower a b
        PGEq (Lit a) b -> updateUpper b a

        PAnd a b -> do
          go a
          go b
        POr a b -> do
          s <- get
          let
            v1 = collectConsts [a] s
            v2 = collectConsts [b] s
          unless v1.canBeSat $ go b
          unless v2.canBeSat $ go a
        PBool False -> conflict
        _ -> pure ()

-- Concretize & simplify Keccak expressions until fixed-point.
concKeccakSimpExpr :: Expr a -> Expr a
concKeccakSimpExpr orig = untilFixpoint (simplifyNoLitToKeccak . (mapExpr concKeccakOnePass)) (simplify orig)

-- Concretize Keccak in Props, but don't simplify
-- Needed because if it also simplified, we may not find some simplification errors, as
-- simplification would always be ON
concKeccakProps :: [Prop] -> [Prop]
concKeccakProps orig = untilFixpoint (map (mapProp concKeccakOnePass)) orig

-- As above, but also simplify, to fixedpoint
concKeccakSimpProps :: [Prop] -> [Prop]
concKeccakSimpProps orig = untilFixpoint (simplifyProps . map (mapProp concKeccakOnePass)) orig

-- Simplifies in case the input to the Keccak is of specific array/map format and
--            can be simplified into a concrete value
-- Turns (Keccak ConcreteBuf) into a Lit
concKeccakOnePass :: Expr a -> Expr a
concKeccakOnePass (Keccak (ConcreteBuf bs)) = Lit (keccak' bs)
concKeccakOnePass orig@(Keccak (CopySlice (Lit 0) (Lit 0) (Lit 64) orig2@(WriteWord (Lit 0) _ (ConcreteBuf bs)) (ConcreteBuf ""))) =
  case (BS.length bs, (copySlice (Lit 0) (Lit 0) (Lit 64) (simplify orig2) (ConcreteBuf ""))) of
    (64, ConcreteBuf a) -> Lit (keccak' a)
    _ -> orig
concKeccakOnePass x = x

lhsConstHelper :: Expr a -> Maybe ()
lhsConstHelper = go
  where
    go :: Expr a -> Maybe ()
    go (Mul _ (Lit _)) = Nothing
    go (Add _ (Lit _)) = Nothing
    go (Min _ (Lit _)) = Nothing
    go (Max _ (Lit _)) = Nothing
    go (Eq _ (Lit _))  = Nothing
    go (And _ (Lit _)) = Nothing
    go (Or _ (Lit _))  = Nothing
    go (Xor _ (Lit _)) = Nothing
    go _ = Just ()

-- Commutative operators should have the constant on the LHS
checkLHSConstProp :: Prop -> Bool
checkLHSConstProp a = isJust $ mapPropM_ lhsConstHelper a

-- Commutative operators should have the constant on the LHS
checkLHSConst :: Expr a -> Bool
checkLHSConst a = isJust $ mapExprM_ lhsConstHelper a

maybeLitByteSimp :: Expr Byte -> Maybe Word8
maybeLitByteSimp (LitByte x) = Just x
maybeLitByteSimp e = case concKeccakSimpExpr e of
  LitByte x -> Just x
  _ -> Nothing

maybeLitWordSimp :: Expr EWord -> Maybe W256
maybeLitWordSimp (Lit w) = Just w
maybeLitWordSimp (WAddr (LitAddr w)) = Just (into w)
maybeLitWordSimp e = case concKeccakSimpExpr e of
  Lit w -> Just w
  WAddr (LitAddr w) -> Just (into w)
  _ -> Nothing

maybeLitAddrSimp :: Expr EAddr -> Maybe Addr
maybeLitAddrSimp (LitAddr a) = Just a
maybeLitAddrSimp e = case concKeccakSimpExpr e of
  LitAddr a -> Just a
  _ -> Nothing

maybeConcStoreSimp :: Expr Storage -> Maybe (LMap.Map W256 W256)
maybeConcStoreSimp (ConcreteStore s) = Just s
maybeConcStoreSimp e = case concKeccakSimpExpr e of
  ConcreteStore s -> Just s
  _ -> Nothing
