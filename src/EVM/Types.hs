{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module EVM.Types where

import Prelude hiding (Foldable(..))

import GHC.Stack (HasCallStack, prettyCallStack, callStack)
import GHC.ByteOrder (targetByteOrder, ByteOrder(..))
import Control.Arrow ((>>>))
import Control.Monad (mzero)
import Control.Monad.ST (ST, RealWorld)
import Control.Monad.State.Strict (StateT)
import Crypto.Hash (hash, Keccak_256, Digest)
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.Bifunctor (first)
import Data.Bits (Bits, FiniteBits, shiftR, shift, shiftL, (.&.), (.|.), toIntegralSized)
import Data.Binary qualified as Binary
import Data.ByteArray qualified as BA
import Data.Char
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Internal (unsafeCreate)
import Data.ByteString.Lazy (toStrict)
import Data.Data
import Data.Int (Int64)
import Data.Word (Word8, Word32, Word64, byteSwap32, byteSwap64)
import Data.DoubleWord
import Data.DoubleWord.TH
import Data.Foldable (Foldable(..))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.IntMap.Strict qualified as IM
import Data.IORef (IORef, newIORef, readIORef, writeIORef, atomicModifyIORef')
import GHC.Records (HasField(..))
import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Serialize qualified as Cereal
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Tree (Forest)
import Data.Tree.Zipper qualified as Zipper
import Data.Vector qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable (STVector)
import Foreign.Ptr (castPtr, plusPtr)
import Foreign.Storable (poke)
import Numeric (readHex, showHex)
import Options.Generic
import Optics.TH
import EVM.FeeSchedule (FeeSchedule (..))
import Data.Kind (Type)

import Text.Regex.TDFA qualified as Regex
import Text.Read qualified
import Witch


-- Template Haskell --------------------------------------------------------------------------


-- We need a 512-bit word for doing ADDMOD and MULMOD with full precision.
mkUnpackedDoubleWord "Word512" ''Word256 "Int512" ''Int256 ''Word256
  [''Typeable, ''Data, ''Generic]



-- Conversions -------------------------------------------------------------------------------------


-- We ignore hlint to suppress the warnings about `fromIntegral` and friends here
#ifndef __HLINT__

instance From Addr Integer where from = fromIntegral
instance From Addr W256 where from = fromIntegral
instance From Int256 Integer where from = fromIntegral
instance From Nibble Int where from = fromIntegral
instance From W256 Integer where from = fromIntegral
instance From W256 Word512 where from = fromIntegral
instance From Word8 W256 where from = fromIntegral
instance From Word8 Word256 where from = fromIntegral
instance From Word32 W256 where from = fromIntegral
instance From Word32 Word256 where from = fromIntegral
instance From Word32 ByteString where from = toStrict . Binary.encode
instance From Word64 W256 where from = fromIntegral
instance From W64 W256 where from = fromIntegral
instance From Word256 Integer where from = fromIntegral
instance From Word256 W256 where from = fromIntegral

instance TryFrom Int W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Int Word256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Int256 W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Integer W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Integer Addr where tryFrom = maybeTryFrom toIntegralSized
-- TODO: hevm relies on this behavior
instance TryFrom W256 Addr where tryFrom = Right . fromIntegral
instance TryFrom W256 FunctionSelector where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Int where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Int64 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Int256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Word32 where tryFrom = maybeTryFrom toIntegralSized
-- TODO: hevm relies on this behavior
instance TryFrom W256 Word64 where tryFrom = Right . fromIntegral
instance TryFrom W256 W64 where tryFrom = Right . fromIntegral
instance TryFrom Word160 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Int where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Int256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Word32 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word512 W256 where tryFrom = maybeTryFrom toIntegralSized

truncateToAddr :: W256 -> Addr
truncateToAddr = fromIntegral

#endif


-- Symbolic IR -------------------------------------------------------------------------------------


-- phantom type tags for AST construction
data EType
  = Buf
  | Storage
  | Log
  | EWord
  | EAddr
  | EContract
  | Byte
  | End
  deriving (Typeable)

-- Variables referring to a global environment
data GVar (a :: EType) where
  BufVar :: Int -> GVar Buf
  StoreVar :: Int -> GVar Storage

deriving instance Show (GVar a)
deriving instance Eq (GVar a)
deriving instance Ord (GVar a)

{- |
  Expr implements an abstract representation of an EVM program

  This type can give insight into the provenance of a term which is useful,
  both for the aesthetic purpose of printing terms in a richer way, but also to
  allow optimizations on the AST instead of letting the SMT solver do all the
  heavy lifting.

  Memory, calldata, and returndata are all represented as a Buf. Semantically
  speaking a Buf is a byte array with of size 2^256.

  Bufs have two base constructors:
    - AbstractBuf:    all elements are fully abstract values
    - ConcreteBuf bs: all elements past (length bs) are zero

  Bufs can be read from with:
    - ReadByte idx buf: read the byte at idx from buf
    - ReadWord idx buf: read the byte at idx from buf

  Bufs can be written to with:
    - WriteByte idx val buf: write val to idx in buf
    - WriteWord idx val buf: write val to idx in buf
    - CopySlice srcOffset dstOffset size src dst:
        overwrite dstOffset -> dstOffset + size in dst with srcOffset -> srcOffset + size from src

  Note that the shared usage of `Buf` does allow for the construction of some
  badly typed Expr instances (e.g. an MSTORE on top of the contents of calldata
  instead of some previous instance of memory), we accept this for the
  sake of simplifying pattern matches against a Buf expression.

  Storage expressions are similar, but instead of writing regions of bytes, we
  write a word to a particular key in a given addresses storage. Note that as
  with a Buf, writes can be sequenced on top of concrete, empty and fully
  abstract starting states.

  One important principle is that of local context: e.g. each term representing
  a write to a Buf / Storage / Logs will always contain a copy of the state
  that is being added to, this ensures that all context relevant to a given
  operation is contained within the term that represents that operation.

  When dealing with Expr instances we assume that concrete expressions have
  been reduced to their smallest possible representation (i.e. a `Lit`,
  `ConcreteBuf`, or `ConcreteStore`). Failure to adhere to this invariant will
  result in your concrete term being treated as symbolic, and may produce
  unexpected errors. In the future we may wish to consider encoding the
  concreteness of a given term directly in the type of that term, since such
  type level shenanigans tends to complicate implementation, we skip this for
  now.
-}
-- Two-level Expr representation -------------------------------------------------------------------
--
-- 'Expr' is a fixpoint of the shallow functor 'ExprF', with a hash-consing id attached to every
-- node. Compared with the flat GADT this buys three things:
--
--   * the structural key used for hash-consing is just @ExprF (Const Int) a@ with a DERIVED
--     Eq/Ord, so there are no hand-assigned constructor tag numbers that must be kept unique,
--     and no Payload type enumerating the scalar fields;
--   * Eq/Ord on Expr become an O(1) id comparison with a structural fallback, replacing ~150
--     lines of hand-written instances, the exprRank table, and the reallyUnsafePtrEquality#
--     fast paths;
--   * every structural traversal is derived from a single 'htraverse' rather than each pass
--     re-listing all 72 constructors.
--
-- Only ExprF is parameterized over the child carrier. Prop, ContractCode, TraceContext, EvmError
-- and PartialExec stay concrete: End / EContract / Log nodes are never structurally interned
-- (they are unique by construction), so their payloads never end up in a hash-consing key.
-- Traversals reach the Exprs nested inside them explicitly, exactly as they did before.

-- | Singleton for the Expr index. Lets a node pick its intern table, and lets a traversal rebuild
-- a node at a statically unknown index, both without unsafeCoerce.
data SEType (a :: EType) where
  SEWord     :: SEType EWord
  SByte      :: SEType Byte
  SBuf       :: SEType Buf
  SStorage   :: SEType Storage
  SEAddr     :: SEType EAddr
  SEContract :: SEType EContract
  SEnd       :: SEType End
  SLog       :: SEType Log

deriving instance Show (SEType a)
deriving instance Eq (SEType a)
deriving instance Ord (SEType a)

-- | A GVar's index is fixed by its own constructor, so the GVar pattern synonym needs no extra
-- constraint on its builder.
gvarEType :: GVar a -> SEType a
gvarEType = \case
  BufVar _   -> SBuf
  StoreVar _ -> SStorage

-- | The shallow functor: one layer of Expr, with children at an arbitrary carrier @r@.
-- Instantiated at @Expr@ for real terms and at @Const Int@ for hash-consing keys.
data ExprF (r :: EType -> Type) (a :: EType) where

  -- identifiers

  -- | Literal words
  LitF            :: {-# UNPACK #-} !W256 -> ExprF r EWord
  -- | Variables
  VarF            :: Text -> ExprF r EWord
  -- | variables introduced during the CSE pass
  GVarF           :: GVar a -> ExprF r a

  -- bytes

  LitByteF        :: {-# UNPACK #-} !Word8 -> ExprF r Byte
  IndexWordF      :: r EWord -> r EWord -> ExprF r Byte
  EqByteF         :: r Byte  -> r Byte  -> ExprF r EWord

  JoinBytesF      :: r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> r Byte -> r Byte -> r Byte -> r Byte
                  -> ExprF r EWord

  -- control flow
  -- [Prop] / TraceContext / PartialExec / EvmError stay concrete: End nodes are never interned,
  -- and traversals descend into them explicitly (see EVM.Traversals).

  PartialF        :: [Prop] -> TraceContext -> PartialExec -> ExprF r End
  FailureF        :: [Prop] -> TraceContext -> EvmError -> ExprF r End
  SuccessF        :: [Prop] -> TraceContext -> r Buf -> Map (r EAddr) (r EContract) -> ExprF r End

  -- integers

  AddF            :: r EWord -> r EWord -> ExprF r EWord
  SubF            :: r EWord -> r EWord -> ExprF r EWord
  MulF            :: r EWord -> r EWord -> ExprF r EWord
  DivF            :: r EWord -> r EWord -> ExprF r EWord
  SDivF           :: r EWord -> r EWord -> ExprF r EWord
  ModF            :: r EWord -> r EWord -> ExprF r EWord
  SModF           :: r EWord -> r EWord -> ExprF r EWord
  AddModF         :: r EWord -> r EWord -> r EWord -> ExprF r EWord
  MulModF         :: r EWord -> r EWord -> r EWord -> ExprF r EWord
  ExpF            :: r EWord -> r EWord -> ExprF r EWord
  SExF            :: r EWord -> r EWord -> ExprF r EWord
  MinF            :: r EWord -> r EWord -> ExprF r EWord
  MaxF            :: r EWord -> r EWord -> ExprF r EWord

  -- booleans

  LTF             :: r EWord -> r EWord -> ExprF r EWord
  GTF             :: r EWord -> r EWord -> ExprF r EWord
  LEqF            :: r EWord -> r EWord -> ExprF r EWord
  GEqF            :: r EWord -> r EWord -> ExprF r EWord
  SLTF            :: r EWord -> r EWord -> ExprF r EWord
  SGTF            :: r EWord -> r EWord -> ExprF r EWord
  EqF             :: r EWord -> r EWord -> ExprF r EWord
  IsZeroF         :: r EWord -> ExprF r EWord

  -- conditional (if-then-else for path merging)
  ITEF            :: r EWord -> r EWord -> r EWord -> ExprF r EWord

  -- bits

  AndF            :: r EWord -> r EWord -> ExprF r EWord
  OrF             :: r EWord -> r EWord -> ExprF r EWord
  XorF            :: r EWord -> r EWord -> ExprF r EWord
  NotF            :: r EWord -> ExprF r EWord
  SHLF            :: r EWord -> r EWord -> ExprF r EWord
  SHRF            :: r EWord -> r EWord -> ExprF r EWord
  SARF            :: r EWord -> r EWord -> ExprF r EWord
  CLZF            :: r EWord -> ExprF r EWord

  -- Hashes

  KeccakF         :: r Buf -> ExprF r EWord

  -- block context

  OriginF         :: ExprF r EWord
  BlockHashF      :: r EWord -> ExprF r EWord
  CoinbaseF       :: ExprF r EWord
  TimestampF      :: ExprF r EWord
  BlockNumberF    :: ExprF r EWord
  PrevRandaoF     :: ExprF r EWord
  GasLimitF       :: ExprF r EWord
  ChainIdF        :: ExprF r EWord
  BaseFeeF        :: ExprF r EWord

  -- tx context

  TxValueF        :: ExprF r EWord

  -- frame context

  BalanceF        :: r EAddr -> ExprF r EWord

  GasF            :: Text               -- prefix needed to distinguish during equivalence checking
                  -> Int                -- fresh gas variable
                  -> ExprF r EWord

  -- code

  CodeSizeF       :: r EAddr -> ExprF r EWord
  CodeHashF       :: r EAddr -> ExprF r EWord

  -- logs

  LogEntryF       :: r EWord            -- address
                  -> r Buf              -- data
                  -> [r EWord]          -- topics
                  -> ExprF r Log

  -- Contract
  -- ContractCode stays concrete for the same reason as [Prop]: EContract nodes are not interned.
  -- Positional rather than a record, so no field selectors are generated here; the record API is
  -- restored by the 'C' pattern synonym plus the HasField instances below.

  CF              :: ContractCode
                  -> r Storage          -- storage
                  -> r Storage          -- tStorage
                  -> r EWord            -- balance
                  -> Maybe W64          -- nonce
                  -> ExprF r EContract

  -- addresses

  SymAddrF        :: Text -> ExprF r EAddr
  LitAddrF        :: Addr -> ExprF r EAddr
  WAddrF          :: r EAddr -> ExprF r EWord

  -- storage

  ConcreteStoreF  :: (Map W256 W256) -> ExprF r Storage
  AbstractStoreF  :: r EAddr -> Maybe W256 -> ExprF r Storage

  SLoadF          :: r EWord -> r Storage -> ExprF r EWord
  SStoreF         :: r EWord -> r EWord -> r Storage -> ExprF r Storage

  -- buffers

  ConcreteBufF    :: ByteString -> ExprF r Buf
  AbstractBufF    :: Text -> ExprF r Buf

  ReadWordF       :: r EWord -> r Buf -> ExprF r EWord
  ReadByteF       :: r EWord -> r Buf -> ExprF r Byte
  WriteWordF      :: r EWord -> r EWord -> r Buf -> ExprF r Buf
  WriteByteF      :: r EWord -> r Byte  -> r Buf -> ExprF r Buf

  CopySliceF      :: r EWord            -- src offset
                  -> r EWord            -- dst offset
                  -> r EWord            -- size
                  -> r Buf              -- src
                  -> r Buf              -- dst
                  -> ExprF r Buf

  BufLengthF      :: r Buf -> ExprF r EWord

-- The point of the whole exercise: these are derived, so adding a constructor to ExprF cannot
-- silently produce a wrong key, a wrong ordering, or a comparison that says a term differs from
-- itself. Contrast the previous hand-written Eq, whose `go _ _ = False` catch-all would have
-- answered False for a new constructor compared with itself, with no warning.
-- Show is written out rather than derived so that it prints the ORIGINAL constructor names,
-- without the F suffix that distinguishes ExprF's constructors from the pattern synonyms. This
-- output is user-facing: counterexample dumps show symbolic addresses via show.
instance (forall b. Show (r b)) => Show (ExprF r a) where
  showsPrec d = \case
    LitF x1 ->
      showParen (d > 10) $ showString "Lit " . showsPrec 11 x1
    VarF x1 ->
      showParen (d > 10) $ showString "Var " . showsPrec 11 x1
    GVarF x1 ->
      showParen (d > 10) $ showString "GVar " . showsPrec 11 x1
    LitByteF x1 ->
      showParen (d > 10) $ showString "LitByte " . showsPrec 11 x1
    IndexWordF x1 x2 ->
      showParen (d > 10) $ showString "IndexWord " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    EqByteF x1 x2 ->
      showParen (d > 10) $ showString "EqByte " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    JoinBytesF x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 ->
      showParen (d > 10) $ showString "JoinBytes " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3 . showChar ' ' . showsPrec 11 x4 . showChar ' ' . showsPrec 11 x5 . showChar ' ' . showsPrec 11 x6 . showChar ' ' . showsPrec 11 x7 . showChar ' ' . showsPrec 11 x8 . showChar ' ' . showsPrec 11 x9 . showChar ' ' . showsPrec 11 x10 . showChar ' ' . showsPrec 11 x11 . showChar ' ' . showsPrec 11 x12 . showChar ' ' . showsPrec 11 x13 . showChar ' ' . showsPrec 11 x14 . showChar ' ' . showsPrec 11 x15 . showChar ' ' . showsPrec 11 x16 . showChar ' ' . showsPrec 11 x17 . showChar ' ' . showsPrec 11 x18 . showChar ' ' . showsPrec 11 x19 . showChar ' ' . showsPrec 11 x20 . showChar ' ' . showsPrec 11 x21 . showChar ' ' . showsPrec 11 x22 . showChar ' ' . showsPrec 11 x23 . showChar ' ' . showsPrec 11 x24 . showChar ' ' . showsPrec 11 x25 . showChar ' ' . showsPrec 11 x26 . showChar ' ' . showsPrec 11 x27 . showChar ' ' . showsPrec 11 x28 . showChar ' ' . showsPrec 11 x29 . showChar ' ' . showsPrec 11 x30 . showChar ' ' . showsPrec 11 x31 . showChar ' ' . showsPrec 11 x32
    PartialF x1 x2 x3 ->
      showParen (d > 10) $ showString "Partial " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    FailureF x1 x2 x3 ->
      showParen (d > 10) $ showString "Failure " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    SuccessF x1 x2 x3 x4 ->
      showParen (d > 10) $ showString "Success " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3 . showChar ' ' . showsPrec 11 x4
    AddF x1 x2 ->
      showParen (d > 10) $ showString "Add " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SubF x1 x2 ->
      showParen (d > 10) $ showString "Sub " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    MulF x1 x2 ->
      showParen (d > 10) $ showString "Mul " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    DivF x1 x2 ->
      showParen (d > 10) $ showString "Div " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SDivF x1 x2 ->
      showParen (d > 10) $ showString "SDiv " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    ModF x1 x2 ->
      showParen (d > 10) $ showString "Mod " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SModF x1 x2 ->
      showParen (d > 10) $ showString "SMod " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    AddModF x1 x2 x3 ->
      showParen (d > 10) $ showString "AddMod " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    MulModF x1 x2 x3 ->
      showParen (d > 10) $ showString "MulMod " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    ExpF x1 x2 ->
      showParen (d > 10) $ showString "Exp " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SExF x1 x2 ->
      showParen (d > 10) $ showString "SEx " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    MinF x1 x2 ->
      showParen (d > 10) $ showString "Min " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    MaxF x1 x2 ->
      showParen (d > 10) $ showString "Max " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    LTF x1 x2 ->
      showParen (d > 10) $ showString "LT " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    GTF x1 x2 ->
      showParen (d > 10) $ showString "GT " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    LEqF x1 x2 ->
      showParen (d > 10) $ showString "LEq " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    GEqF x1 x2 ->
      showParen (d > 10) $ showString "GEq " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SLTF x1 x2 ->
      showParen (d > 10) $ showString "SLT " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SGTF x1 x2 ->
      showParen (d > 10) $ showString "SGT " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    EqF x1 x2 ->
      showParen (d > 10) $ showString "Eq " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    IsZeroF x1 ->
      showParen (d > 10) $ showString "IsZero " . showsPrec 11 x1
    ITEF x1 x2 x3 ->
      showParen (d > 10) $ showString "ITE " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    AndF x1 x2 ->
      showParen (d > 10) $ showString "And " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    OrF x1 x2 ->
      showParen (d > 10) $ showString "Or " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    XorF x1 x2 ->
      showParen (d > 10) $ showString "Xor " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    NotF x1 ->
      showParen (d > 10) $ showString "Not " . showsPrec 11 x1
    SHLF x1 x2 ->
      showParen (d > 10) $ showString "SHL " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SHRF x1 x2 ->
      showParen (d > 10) $ showString "SHR " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SARF x1 x2 ->
      showParen (d > 10) $ showString "SAR " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    CLZF x1 ->
      showParen (d > 10) $ showString "CLZ " . showsPrec 11 x1
    KeccakF x1 ->
      showParen (d > 10) $ showString "Keccak " . showsPrec 11 x1
    OriginF          -> showString "Origin"        
    BlockHashF x1 ->
      showParen (d > 10) $ showString "BlockHash " . showsPrec 11 x1
    CoinbaseF        -> showString "Coinbase"      
    TimestampF       -> showString "Timestamp"     
    BlockNumberF     -> showString "BlockNumber"   
    PrevRandaoF      -> showString "PrevRandao"    
    GasLimitF        -> showString "GasLimit"      
    ChainIdF         -> showString "ChainId"       
    BaseFeeF         -> showString "BaseFee"       
    TxValueF         -> showString "TxValue"       
    BalanceF x1 ->
      showParen (d > 10) $ showString "Balance " . showsPrec 11 x1
    GasF x1 x2 ->
      showParen (d > 10) $ showString "Gas " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    CodeSizeF x1 ->
      showParen (d > 10) $ showString "CodeSize " . showsPrec 11 x1
    CodeHashF x1 ->
      showParen (d > 10) $ showString "CodeHash " . showsPrec 11 x1
    LogEntryF x1 x2 x3 ->
      showParen (d > 10) $ showString "LogEntry " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    CF x1 x2 x3 x4 x5 ->
      showParen (d > 10) $ showString "C " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3 . showChar ' ' . showsPrec 11 x4 . showChar ' ' . showsPrec 11 x5
    SymAddrF x1 ->
      showParen (d > 10) $ showString "SymAddr " . showsPrec 11 x1
    LitAddrF x1 ->
      showParen (d > 10) $ showString "LitAddr " . showsPrec 11 x1
    WAddrF x1 ->
      showParen (d > 10) $ showString "WAddr " . showsPrec 11 x1
    ConcreteStoreF x1 ->
      showParen (d > 10) $ showString "ConcreteStore " . showsPrec 11 x1
    AbstractStoreF x1 x2 ->
      showParen (d > 10) $ showString "AbstractStore " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SLoadF x1 x2 ->
      showParen (d > 10) $ showString "SLoad " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    SStoreF x1 x2 x3 ->
      showParen (d > 10) $ showString "SStore " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    ConcreteBufF x1 ->
      showParen (d > 10) $ showString "ConcreteBuf " . showsPrec 11 x1
    AbstractBufF x1 ->
      showParen (d > 10) $ showString "AbstractBuf " . showsPrec 11 x1
    ReadWordF x1 x2 ->
      showParen (d > 10) $ showString "ReadWord " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    ReadByteF x1 x2 ->
      showParen (d > 10) $ showString "ReadByte " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2
    WriteWordF x1 x2 x3 ->
      showParen (d > 10) $ showString "WriteWord " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    WriteByteF x1 x2 x3 ->
      showParen (d > 10) $ showString "WriteByte " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3
    CopySliceF x1 x2 x3 x4 x5 ->
      showParen (d > 10) $ showString "CopySlice " . showsPrec 11 x1 . showChar ' ' . showsPrec 11 x2 . showChar ' ' . showsPrec 11 x3 . showChar ' ' . showsPrec 11 x4 . showChar ' ' . showsPrec 11 x5
    BufLengthF x1 ->
      showParen (d > 10) $ showString "BufLength " . showsPrec 11 x1
deriving instance (forall b. Eq (r b)) => Eq (ExprF r a)
deriving instance (forall b. Ord (r b)) => Ord (ExprF r a)

-- | An Expr node: its hash-consing identity, its index singleton, and one layer of structure.
--
-- @ident == 0@ means "no identity assigned" (hash-consing disabled, or the node predates the
-- flag being switched on). Ids are globally unique and never reused, including across
-- 'resetHashCons', so a non-zero id is a sound witness of term identity forever.
data Expr (a :: EType) = Expr
  { ident :: {-# UNPACK #-} !Int
  , ety   :: !(SEType a)
  , node  :: !(ExprF Expr a)
  }

-- | Structural key: one layer, children replaced by their ids. Shallow by construction, so a
-- lookup never compares whole subterms.
type ExprKey = ExprF (Const Int)

-- Eq/Ord in two lines each. The id check is only a fast path -- it fires when both nodes are
-- interned and identical -- and everything else falls through to the derived structural
-- comparison on ExprF, which recurses back through these instances.
instance Eq (Expr a) where
  x == y = (x.ident /= 0 && x.ident == y.ident) || x.node == y.node
  {-# INLINE (==) #-}

instance Ord (Expr a) where
  compare x y
    | x.ident /= 0 && x.ident == y.ident = Prelude.EQ
    | otherwise = Prelude.compare x.node y.node
  {-# INLINE compare #-}

-- NOTE: this prints the ExprF constructor names, which carry an F suffix (@AddF@ rather than
-- @Add@). Show output is cosmetic here -- it is not used to build SMT or as a map key -- but it
-- is a visible change in error messages, and a hand-written instance restoring the old names is
-- a worthwhile follow-up.
instance Show (Expr a) where
  showsPrec d x = showsPrec d x.node

-- | The single generic traversal over a node's children. Everything structural in EVM.Traversals
-- is derived from this.
--
-- The @forall x. Ord (s x)@ constraint exists only because SuccessF carries a Map keyed by an
-- Expr, and rebuilding a Map needs Ord on its keys.
htraverse
  :: forall f r s a
   . (Applicative f, forall x. Ord (s x))
  => (forall x. r x -> f (s x)) -> ExprF r a -> f (ExprF s a)
htraverse f = \case
  LitF w             -> pure (LitF w)
  VarF t             -> pure (VarF t)
  GVarF g            -> pure (GVarF g)
  LitByteF w         -> pure (LitByteF w)
  IndexWordF a b     -> IndexWordF <$> f a <*> f b
  EqByteF a b        -> EqByteF <$> f a <*> f b
  JoinBytesF b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
             b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 ->
    JoinBytesF <$> f b0 <*> f b1 <*> f b2 <*> f b3 <*> f b4 <*> f b5 <*> f b6 <*> f b7
               <*> f b8 <*> f b9 <*> f b10 <*> f b11 <*> f b12 <*> f b13 <*> f b14 <*> f b15
               <*> f b16 <*> f b17 <*> f b18 <*> f b19 <*> f b20 <*> f b21 <*> f b22 <*> f b23
               <*> f b24 <*> f b25 <*> f b26 <*> f b27 <*> f b28 <*> f b29 <*> f b30 <*> f b31
  PartialF ps tc pe  -> pure (PartialF ps tc pe)
  FailureF ps tc e   -> pure (FailureF ps tc e)
  SuccessF ps tc b m -> SuccessF ps tc <$> f b <*> traverseMap m
  AddF a b           -> AddF <$> f a <*> f b
  SubF a b           -> SubF <$> f a <*> f b
  MulF a b           -> MulF <$> f a <*> f b
  DivF a b           -> DivF <$> f a <*> f b
  SDivF a b          -> SDivF <$> f a <*> f b
  ModF a b           -> ModF <$> f a <*> f b
  SModF a b          -> SModF <$> f a <*> f b
  AddModF a b c      -> AddModF <$> f a <*> f b <*> f c
  MulModF a b c      -> MulModF <$> f a <*> f b <*> f c
  ExpF a b           -> ExpF <$> f a <*> f b
  SExF a b           -> SExF <$> f a <*> f b
  MinF a b           -> MinF <$> f a <*> f b
  MaxF a b           -> MaxF <$> f a <*> f b
  LTF a b            -> LTF <$> f a <*> f b
  GTF a b            -> GTF <$> f a <*> f b
  LEqF a b           -> LEqF <$> f a <*> f b
  GEqF a b           -> GEqF <$> f a <*> f b
  SLTF a b           -> SLTF <$> f a <*> f b
  SGTF a b           -> SGTF <$> f a <*> f b
  EqF a b            -> EqF <$> f a <*> f b
  IsZeroF a          -> IsZeroF <$> f a
  ITEF a b c         -> ITEF <$> f a <*> f b <*> f c
  AndF a b           -> AndF <$> f a <*> f b
  OrF a b            -> OrF <$> f a <*> f b
  XorF a b           -> XorF <$> f a <*> f b
  NotF a             -> NotF <$> f a
  SHLF a b           -> SHLF <$> f a <*> f b
  SHRF a b           -> SHRF <$> f a <*> f b
  SARF a b           -> SARF <$> f a <*> f b
  CLZF a             -> CLZF <$> f a
  KeccakF a          -> KeccakF <$> f a
  OriginF            -> pure OriginF
  BlockHashF a       -> BlockHashF <$> f a
  CoinbaseF          -> pure CoinbaseF
  TimestampF         -> pure TimestampF
  BlockNumberF       -> pure BlockNumberF
  PrevRandaoF        -> pure PrevRandaoF
  GasLimitF          -> pure GasLimitF
  ChainIdF           -> pure ChainIdF
  BaseFeeF           -> pure BaseFeeF
  TxValueF           -> pure TxValueF
  BalanceF a         -> BalanceF <$> f a
  GasF p i           -> pure (GasF p i)
  CodeSizeF a        -> CodeSizeF <$> f a
  CodeHashF a        -> CodeHashF <$> f a
  LogEntryF a b ts   -> LogEntryF <$> f a <*> f b <*> traverse f ts
  CF co st ts bal n  -> (\st' ts' bal' -> CF co st' ts' bal' n) <$> f st <*> f ts <*> f bal
  SymAddrF t         -> pure (SymAddrF t)
  LitAddrF a         -> pure (LitAddrF a)
  WAddrF a           -> WAddrF <$> f a
  ConcreteStoreF m   -> pure (ConcreteStoreF m)
  AbstractStoreF a m -> AbstractStoreF <$> f a <*> pure m
  SLoadF a b         -> SLoadF <$> f a <*> f b
  SStoreF a b c      -> SStoreF <$> f a <*> f b <*> f c
  ConcreteBufF b     -> pure (ConcreteBufF b)
  AbstractBufF t     -> pure (AbstractBufF t)
  ReadWordF a b      -> ReadWordF <$> f a <*> f b
  ReadByteF a b      -> ReadByteF <$> f a <*> f b
  WriteWordF a b c   -> WriteWordF <$> f a <*> f b <*> f c
  WriteByteF a b c   -> WriteByteF <$> f a <*> f b <*> f c
  CopySliceF a b c d e -> CopySliceF <$> f a <*> f b <*> f c <*> f d <*> f e
  BufLengthF a       -> BufLengthF <$> f a
  where
    traverseMap :: Map (r EAddr) (r EContract) -> f (Map (s EAddr) (s EContract))
    traverseMap m =
      Map.fromList <$> traverse (\(k, v) -> (,) <$> f k <*> f v) (Map.toList m)

-- | Applicative used to fold over children without building a new node.
newtype AccF m b = AccF m

instance Functor (AccF m) where
  fmap _ (AccF m) = AccF m
instance Monoid m => Applicative (AccF m) where
  pure _ = AccF mempty
  AccF a <*> AccF b = AccF (a <> b)

-- | Dummy carrier for folds: htraverse's target only needs an Ord instance, never inspected.
data NoInfo (x :: EType) = NoInfo
instance Eq (NoInfo x) where _ == _ = True
instance Ord (NoInfo x) where compare _ _ = Prelude.EQ

-- | Fold over a node's immediate children.
hfoldMap :: forall m r a. Monoid m => (forall x. r x -> m) -> ExprF r a -> m
hfoldMap f n = case htraverse @(AccF m) @r @NoInfo (\c -> AccF (f c)) n of AccF m -> m

hmap :: (forall x. Ord (s x)) => (forall x. r x -> s x) -> ExprF r a -> ExprF s a
hmap f = runIdentity . htraverse (Identity . f)

-- | Immediate children of a node, type-erased.
childrenOf :: ExprF Expr a -> [SomeChild]
childrenOf = hfoldMap (\c -> [SomeChild c])

-- | A node's child with its index hidden, for folds over children.
data SomeChild = forall x. SomeChild (Expr x)

-- Hash-consing ------------------------------------------------------------------------------------
--
-- The tables live here rather than in EVM.HashCons because the pattern synonyms below construct
-- through 'mkWith', and EVM.HashCons imports EVM.Types.

-- | One table per interned index. EContract / End / Log are absent: those nodes are unique by
-- construction and are only given a fresh id.
data HCTables = HCTables
  { hcW    :: !(Map (ExprKey EWord) (Expr EWord))
  , hcBy   :: !(Map (ExprKey Byte) (Expr Byte))
  , hcBu   :: !(Map (ExprKey Buf) (Expr Buf))
  , hcSt   :: !(Map (ExprKey Storage) (Expr Storage))
  , hcAd   :: !(Map (ExprKey EAddr) (Expr EAddr))
  , hcNext :: !Int
  }

emptyHCTables :: HCTables
emptyHCTables = HCTables Map.empty Map.empty Map.empty Map.empty Map.empty 1  -- 0 is reserved

{-# NOINLINE hcTables #-}
hcTables :: IORef HCTables
hcTables = unsafePerformIO (newIORef emptyHCTables)

{-# NOINLINE hcEnabled #-}
hcEnabled :: IORef Bool
hcEnabled = unsafePerformIO (newIORef False)

-- | Turn construction-time hash-consing on or off.
--
-- IMPORTANT: this must be set before any Expr is constructed and not toggled afterwards. Nodes
-- built while it was off carry @ident == 0@, and 'mkWith' then refuses to key anything above
-- them (see the guard below), so flipping it on mid-run silently buys nothing.
setHashConsEnabled :: Bool -> IO ()
setHashConsEnabled = writeIORef hcEnabled

-- | Drop the tables between explorations. hcNext deliberately survives: ids are never reused, so
-- a node that outlives the reset can never collide with a newly built one.
resetHashCons :: IO ()
resetHashCons = do
  atomicModifyIORef' hcTables $ \t -> (emptyHCTables { hcNext = t.hcNext }, ())
  writeIORef hcMemos IM.empty

-- | Whether hash-consing is on. Takes the term so the read carries a data dependency and cannot
-- be floated out and shared across calls; the flag can change between explorations.
--
-- Only ever used to choose between two equivalent traversals, so a stale read costs performance
-- and never correctness.
hashConsEnabled :: Expr b -> Bool
hashConsEnabled x = unsafePerformIO (x `seq` readIORef hcEnabled)
{-# NOINLINE hashConsEnabled #-}

-- | Decidable equality on the index singleton. Used to recover a memoized result at the node's
-- own index; no unsafeCoerce required.
sameEType :: SEType a -> SEType b -> Maybe (a :~: b)
sameEType SEWord SEWord         = Just Refl
sameEType SByte SByte           = Just Refl
sameEType SBuf SBuf             = Just Refl
sameEType SStorage SStorage     = Just Refl
sameEType SEAddr SEAddr         = Just Refl
sameEType SEContract SEContract = Just Refl
sameEType SEnd SEnd             = Just Refl
sameEType SLog SLog             = Just Refl
sameEType _ _                   = Nothing

-- | Per-pass memo of simplification results: pass slot -> node id -> result. A node's result has
-- the same index as the node, and the stored singleton recovers it at that index.
data MemoVal = forall x. MemoVal !(SEType x) !(Expr x)

{-# NOINLINE hcMemos #-}
hcMemos :: IORef (IM.IntMap (IM.IntMap MemoVal))
hcMemos = unsafePerformIO (newIORef IM.empty)

lookupMemo :: Int -> Expr a -> IO (Maybe (Expr a))
lookupMemo slot e = do
  ms <- readIORef hcMemos
  pure $ case IM.lookup slot ms >>= IM.lookup e.ident of
    Nothing -> Nothing
    -- the index can only differ if two nodes shared an id, which cannot happen: ids are unique
    -- and never reused, including across resetHashCons
    Just (MemoVal s v) -> case sameEType s e.ety of
      Just Refl -> Just v
      Nothing   -> Nothing

insertMemo :: Int -> Expr a -> Expr a -> IO ()
insertMemo slot e r =
  atomicModifyIORef' hcMemos $ \ms ->
    (IM.insertWith IM.union slot (IM.singleton e.ident (MemoVal e.ety r)) ms, ())

-- | Which table a node of this index belongs in, if any.
data HCSlot a = HCSlot
  { slotGet :: HCTables -> Map (ExprKey a) (Expr a)
  , slotSet :: HCTables -> Map (ExprKey a) (Expr a) -> HCTables
  }

hcSlotFor :: SEType a -> Maybe (HCSlot a)
hcSlotFor = \case
  SEWord   -> Just (HCSlot (.hcW)  (\t m -> t { hcW  = m }))
  SByte    -> Just (HCSlot (.hcBy) (\t m -> t { hcBy = m }))
  SBuf     -> Just (HCSlot (.hcBu) (\t m -> t { hcBu = m }))
  SStorage -> Just (HCSlot (.hcSt) (\t m -> t { hcSt = m }))
  SEAddr   -> Just (HCSlot (.hcAd) (\t m -> t { hcAd = m }))
  _        -> Nothing

-- | The one smart constructor. Every pattern synonym below builds through it, so every
-- construction site in the codebase hash-conses without any call-site change.
mkWith :: SEType a -> ExprF Expr a -> Expr a
mkWith s n = unsafePerformIO $ do
  en <- readIORef hcEnabled
  if not en
    then pure (Expr 0 s n)
    else do
      let cs = childrenOf n
      -- Force every child to WHNF BEFORE the atomic section. Computing the structural key reads
      -- each child's ident; a child still held as an unevaluated mkWith thunk would re-enter
      -- atomicModifyIORef' on hcTables while the outer modify is in flight, and the RTS reports
      -- <<loop>> on the blackhole.
      mapM_ (\(SomeChild c) -> c `seq` pure ()) cs
      -- Soundness guard: ident 0 means "no identity", so two structurally DIFFERENT uninterned
      -- children both key as Const 0 and the nodes above them would be merged. Give any node
      -- with a 0-ident child a fresh unique id and keep it out of the table: we lose sharing
      -- above uninterned terms, never soundness.
      let keyable = all (\(SomeChild c) -> c.ident /= 0) cs
      case if keyable then hcSlotFor s else Nothing of
        Nothing -> do
          i <- atomicModifyIORef' hcTables $ \t -> (t { hcNext = t.hcNext + 1 }, t.hcNext)
          pure (Expr i s n)
        Just sl -> do
          let !k = hmap (Const . (.ident)) n
          atomicModifyIORef' hcTables $ \t ->
            case Map.lookup k (sl.slotGet t) of
              Just c -> (t, c)
              Nothing ->
                let i = t.hcNext
                    e = Expr i s n
                in ((sl.slotSet t (Map.insert k e (sl.slotGet t))) { hcNext = i + 1 }, e)
{-# NOINLINE mkWith #-}

-- | Rebuild a node at the same index as an existing one. Used by traversals, which always have
-- the original node in hand and so never need a KnownEType-style constraint.
remake :: Expr a -> ExprF Expr a -> Expr a
remake old n = mkWith old.ety n
{-# INLINE remake #-}

-- Pattern synonyms ---------------------------------------------------------------------------------
--
-- These restore the original constructor API, so no call site in the codebase changes.
--
-- Every signature is GADT-style: @() => (a ~ Idx) => ... -> Expr a@. The naive monomorphic form
-- @... -> Expr Idx@ also compiles, but matching it against a polymorphic @Expr a@ provides no
-- type refinement, which breaks every rule in EVM.Expr.simplify. In expression position a
-- pattern synonym has type @(CReq, CProv) => ...@, so the builder still works at the fixed index.

pattern Lit :: () => (a ~ EWord) => W256 -> Expr a
pattern Lit w <- Expr _ _ (LitF w) where Lit w = mkWith SEWord (LitF w)

pattern Var :: () => (a ~ EWord) => Text -> Expr a
pattern Var t <- Expr _ _ (VarF t) where Var t = mkWith SEWord (VarF t)

-- index-polymorphic, so no provided equality: matches at any index, like the original
pattern GVar :: GVar a -> Expr a
pattern GVar g <- Expr _ _ (GVarF g) where GVar g = mkWith (gvarEType g) (GVarF g)

pattern LitByte :: () => (a ~ Byte) => Word8 -> Expr a
pattern LitByte w <- Expr _ _ (LitByteF w) where LitByte w = mkWith SByte (LitByteF w)

pattern IndexWord :: () => (a ~ Byte) => Expr EWord -> Expr EWord -> Expr a
pattern IndexWord x y <- Expr _ _ (IndexWordF x y) where IndexWord x y = mkWith SByte (IndexWordF x y)

pattern EqByte :: () => (a ~ EWord) => Expr Byte -> Expr Byte -> Expr a
pattern EqByte x y <- Expr _ _ (EqByteF x y) where EqByte x y = mkWith SEWord (EqByteF x y)

pattern JoinBytes :: () => (a ~ EWord)
                  => Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                  -> Expr a
pattern JoinBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                  b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
  <- Expr _ _ (JoinBytesF b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                          b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31)
  where JoinBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                  b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
          = mkWith SEWord (JoinBytesF b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                                      b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31)

pattern Partial :: () => (a ~ End) => [Prop] -> TraceContext -> PartialExec -> Expr a
pattern Partial ps tc pe <- Expr _ _ (PartialF ps tc pe)
  where Partial ps tc pe = mkWith SEnd (PartialF ps tc pe)

pattern Failure :: () => (a ~ End) => [Prop] -> TraceContext -> EvmError -> Expr a
pattern Failure ps tc e <- Expr _ _ (FailureF ps tc e)
  where Failure ps tc e = mkWith SEnd (FailureF ps tc e)

pattern Success :: () => (a ~ End)
                => [Prop] -> TraceContext -> Expr Buf -> Map (Expr EAddr) (Expr EContract) -> Expr a
pattern Success ps tc b m <- Expr _ _ (SuccessF ps tc b m)
  where Success ps tc b m = mkWith SEnd (SuccessF ps tc b m)

pattern Add :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Add x y <- Expr _ _ (AddF x y) where Add x y = mkWith SEWord (AddF x y)

pattern Sub :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Sub x y <- Expr _ _ (SubF x y) where Sub x y = mkWith SEWord (SubF x y)

pattern Mul :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Mul x y <- Expr _ _ (MulF x y) where Mul x y = mkWith SEWord (MulF x y)

pattern Div :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Div x y <- Expr _ _ (DivF x y) where Div x y = mkWith SEWord (DivF x y)

pattern SDiv :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SDiv x y <- Expr _ _ (SDivF x y) where SDiv x y = mkWith SEWord (SDivF x y)

pattern Mod :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Mod x y <- Expr _ _ (ModF x y) where Mod x y = mkWith SEWord (ModF x y)

pattern SMod :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SMod x y <- Expr _ _ (SModF x y) where SMod x y = mkWith SEWord (SModF x y)

pattern AddMod :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr EWord -> Expr a
pattern AddMod x y z <- Expr _ _ (AddModF x y z) where AddMod x y z = mkWith SEWord (AddModF x y z)

pattern MulMod :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr EWord -> Expr a
pattern MulMod x y z <- Expr _ _ (MulModF x y z) where MulMod x y z = mkWith SEWord (MulModF x y z)

pattern Exp :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Exp x y <- Expr _ _ (ExpF x y) where Exp x y = mkWith SEWord (ExpF x y)

pattern SEx :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SEx x y <- Expr _ _ (SExF x y) where SEx x y = mkWith SEWord (SExF x y)

pattern Min :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Min x y <- Expr _ _ (MinF x y) where Min x y = mkWith SEWord (MinF x y)

pattern Max :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Max x y <- Expr _ _ (MaxF x y) where Max x y = mkWith SEWord (MaxF x y)

pattern LT :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern LT x y <- Expr _ _ (LTF x y) where LT x y = mkWith SEWord (LTF x y)

pattern GT :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern GT x y <- Expr _ _ (GTF x y) where GT x y = mkWith SEWord (GTF x y)

pattern LEq :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern LEq x y <- Expr _ _ (LEqF x y) where LEq x y = mkWith SEWord (LEqF x y)

pattern GEq :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern GEq x y <- Expr _ _ (GEqF x y) where GEq x y = mkWith SEWord (GEqF x y)

pattern SLT :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SLT x y <- Expr _ _ (SLTF x y) where SLT x y = mkWith SEWord (SLTF x y)

pattern SGT :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SGT x y <- Expr _ _ (SGTF x y) where SGT x y = mkWith SEWord (SGTF x y)

pattern Eq :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Eq x y <- Expr _ _ (EqF x y) where Eq x y = mkWith SEWord (EqF x y)

pattern IsZero :: () => (a ~ EWord) => Expr EWord -> Expr a
pattern IsZero x <- Expr _ _ (IsZeroF x) where IsZero x = mkWith SEWord (IsZeroF x)

pattern ITE :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr EWord -> Expr a
pattern ITE x y z <- Expr _ _ (ITEF x y z) where ITE x y z = mkWith SEWord (ITEF x y z)

pattern And :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern And x y <- Expr _ _ (AndF x y) where And x y = mkWith SEWord (AndF x y)

pattern Or :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Or x y <- Expr _ _ (OrF x y) where Or x y = mkWith SEWord (OrF x y)

pattern Xor :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern Xor x y <- Expr _ _ (XorF x y) where Xor x y = mkWith SEWord (XorF x y)

pattern Not :: () => (a ~ EWord) => Expr EWord -> Expr a
pattern Not x <- Expr _ _ (NotF x) where Not x = mkWith SEWord (NotF x)

pattern SHL :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SHL x y <- Expr _ _ (SHLF x y) where SHL x y = mkWith SEWord (SHLF x y)

pattern SHR :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SHR x y <- Expr _ _ (SHRF x y) where SHR x y = mkWith SEWord (SHRF x y)

pattern SAR :: () => (a ~ EWord) => Expr EWord -> Expr EWord -> Expr a
pattern SAR x y <- Expr _ _ (SARF x y) where SAR x y = mkWith SEWord (SARF x y)

pattern CLZ :: () => (a ~ EWord) => Expr EWord -> Expr a
pattern CLZ x <- Expr _ _ (CLZF x) where CLZ x = mkWith SEWord (CLZF x)

pattern Keccak :: () => (a ~ EWord) => Expr Buf -> Expr a
pattern Keccak x <- Expr _ _ (KeccakF x) where Keccak x = mkWith SEWord (KeccakF x)

pattern Origin :: () => (a ~ EWord) => Expr a
pattern Origin <- Expr _ _ OriginF where Origin = mkWith SEWord OriginF

pattern BlockHash :: () => (a ~ EWord) => Expr EWord -> Expr a
pattern BlockHash x <- Expr _ _ (BlockHashF x) where BlockHash x = mkWith SEWord (BlockHashF x)

pattern Coinbase :: () => (a ~ EWord) => Expr a
pattern Coinbase <- Expr _ _ CoinbaseF where Coinbase = mkWith SEWord CoinbaseF

pattern Timestamp :: () => (a ~ EWord) => Expr a
pattern Timestamp <- Expr _ _ TimestampF where Timestamp = mkWith SEWord TimestampF

pattern BlockNumber :: () => (a ~ EWord) => Expr a
pattern BlockNumber <- Expr _ _ BlockNumberF where BlockNumber = mkWith SEWord BlockNumberF

pattern PrevRandao :: () => (a ~ EWord) => Expr a
pattern PrevRandao <- Expr _ _ PrevRandaoF where PrevRandao = mkWith SEWord PrevRandaoF

pattern GasLimit :: () => (a ~ EWord) => Expr a
pattern GasLimit <- Expr _ _ GasLimitF where GasLimit = mkWith SEWord GasLimitF

pattern ChainId :: () => (a ~ EWord) => Expr a
pattern ChainId <- Expr _ _ ChainIdF where ChainId = mkWith SEWord ChainIdF

pattern BaseFee :: () => (a ~ EWord) => Expr a
pattern BaseFee <- Expr _ _ BaseFeeF where BaseFee = mkWith SEWord BaseFeeF

pattern TxValue :: () => (a ~ EWord) => Expr a
pattern TxValue <- Expr _ _ TxValueF where TxValue = mkWith SEWord TxValueF

pattern Balance :: () => (a ~ EWord) => Expr EAddr -> Expr a
pattern Balance x <- Expr _ _ (BalanceF x) where Balance x = mkWith SEWord (BalanceF x)

pattern Gas :: () => (a ~ EWord) => Text -> Int -> Expr a
pattern Gas p i <- Expr _ _ (GasF p i) where Gas p i = mkWith SEWord (GasF p i)

pattern CodeSize :: () => (a ~ EWord) => Expr EAddr -> Expr a
pattern CodeSize x <- Expr _ _ (CodeSizeF x) where CodeSize x = mkWith SEWord (CodeSizeF x)

pattern CodeHash :: () => (a ~ EWord) => Expr EAddr -> Expr a
pattern CodeHash x <- Expr _ _ (CodeHashF x) where CodeHash x = mkWith SEWord (CodeHashF x)

pattern LogEntry :: () => (a ~ Log) => Expr EWord -> Expr Buf -> [Expr EWord] -> Expr a
pattern LogEntry x y ts <- Expr _ _ (LogEntryF x y ts)
  where LogEntry x y ts = mkWith SLog (LogEntryF x y ts)

pattern C :: () => (a ~ EContract)
          => ContractCode -> Expr Storage -> Expr Storage -> Expr EWord -> Maybe W64 -> Expr a
pattern C co st ts bal n <- Expr _ _ (CF co st ts bal n)
  where C co st ts bal n = mkWith SEContract (CF co st ts bal n)

pattern SymAddr :: () => (a ~ EAddr) => Text -> Expr a
pattern SymAddr t <- Expr _ _ (SymAddrF t) where SymAddr t = mkWith SEAddr (SymAddrF t)

pattern LitAddr :: () => (a ~ EAddr) => Addr -> Expr a
pattern LitAddr x <- Expr _ _ (LitAddrF x) where LitAddr x = mkWith SEAddr (LitAddrF x)

pattern WAddr :: () => (a ~ EWord) => Expr EAddr -> Expr a
pattern WAddr x <- Expr _ _ (WAddrF x) where WAddr x = mkWith SEWord (WAddrF x)

pattern ConcreteStore :: () => (a ~ Storage) => Map W256 W256 -> Expr a
pattern ConcreteStore m <- Expr _ _ (ConcreteStoreF m)
  where ConcreteStore m = mkWith SStorage (ConcreteStoreF m)

pattern AbstractStore :: () => (a ~ Storage) => Expr EAddr -> Maybe W256 -> Expr a
pattern AbstractStore x m <- Expr _ _ (AbstractStoreF x m)
  where AbstractStore x m = mkWith SStorage (AbstractStoreF x m)

pattern SLoad :: () => (a ~ EWord) => Expr EWord -> Expr Storage -> Expr a
pattern SLoad x y <- Expr _ _ (SLoadF x y) where SLoad x y = mkWith SEWord (SLoadF x y)

pattern SStore :: () => (a ~ Storage) => Expr EWord -> Expr EWord -> Expr Storage -> Expr a
pattern SStore x y z <- Expr _ _ (SStoreF x y z) where SStore x y z = mkWith SStorage (SStoreF x y z)

pattern ConcreteBuf :: () => (a ~ Buf) => ByteString -> Expr a
pattern ConcreteBuf b <- Expr _ _ (ConcreteBufF b) where ConcreteBuf b = mkWith SBuf (ConcreteBufF b)

pattern AbstractBuf :: () => (a ~ Buf) => Text -> Expr a
pattern AbstractBuf t <- Expr _ _ (AbstractBufF t) where AbstractBuf t = mkWith SBuf (AbstractBufF t)

pattern ReadWord :: () => (a ~ EWord) => Expr EWord -> Expr Buf -> Expr a
pattern ReadWord x y <- Expr _ _ (ReadWordF x y) where ReadWord x y = mkWith SEWord (ReadWordF x y)

pattern ReadByte :: () => (a ~ Byte) => Expr EWord -> Expr Buf -> Expr a
pattern ReadByte x y <- Expr _ _ (ReadByteF x y) where ReadByte x y = mkWith SByte (ReadByteF x y)

pattern WriteWord :: () => (a ~ Buf) => Expr EWord -> Expr EWord -> Expr Buf -> Expr a
pattern WriteWord x y z <- Expr _ _ (WriteWordF x y z)
  where WriteWord x y z = mkWith SBuf (WriteWordF x y z)

pattern WriteByte :: () => (a ~ Buf) => Expr EWord -> Expr Byte -> Expr Buf -> Expr a
pattern WriteByte x y z <- Expr _ _ (WriteByteF x y z)
  where WriteByte x y z = mkWith SBuf (WriteByteF x y z)

pattern CopySlice :: () => (a ~ Buf)
                  => Expr EWord -> Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf -> Expr a
pattern CopySlice s d n src dst <- Expr _ _ (CopySliceF s d n src dst)
  where CopySlice s d n src dst = mkWith SBuf (CopySliceF s d n src dst)

pattern BufLength :: () => (a ~ EWord) => Expr Buf -> Expr a
pattern BufLength x <- Expr _ _ (BufLengthF x) where BufLength x = mkWith SEWord (BufLengthF x)

-- All 72 alternatives, so exhaustiveness checking keeps working. LT/GT/Eq are qualified to
-- disambiguate them from Prelude's Ordering constructors and Eq class.
{-# COMPLETE Lit, Var, GVar, LitByte, IndexWord, EqByte, JoinBytes, Partial, Failure, Success,
             Add, Sub, Mul, Div, SDiv, Mod, SMod, AddMod, MulMod, Exp, SEx, Min, Max,
             EVM.Types.LT, EVM.Types.GT, LEq, GEq, SLT, SGT, EVM.Types.Eq, IsZero, ITE,
             And, Or, Xor, Not, SHL, SHR, SAR, CLZ, Keccak, Origin, BlockHash, Coinbase,
             Timestamp, BlockNumber, PrevRandao, GasLimit, ChainId, BaseFee, TxValue, Balance,
             Gas, CodeSize, CodeHash, LogEntry, C, SymAddr, LitAddr, WAddr, ConcreteStore,
             AbstractStore, SLoad, SStore, ConcreteBuf, AbstractBuf, ReadWord, ReadByte,
             WriteWord, WriteByte, CopySlice, BufLength #-}

-- CF is positional, so the HasField instances the old record constructor generated have to be
-- written out. `GVar EContract` is uninhabited (GVar only has BufVar/StoreVar), so the empty
-- case is accepted and these stay total.
instance HasField "code" (Expr EContract) ContractCode where
  getField e = case e.node of CF c _ _ _ _ -> c; GVarF g -> case g of {}
instance HasField "storage" (Expr EContract) (Expr Storage) where
  getField e = case e.node of CF _ s _ _ _ -> s; GVarF g -> case g of {}
instance HasField "tStorage" (Expr EContract) (Expr Storage) where
  getField e = case e.node of CF _ _ t _ _ -> t; GVarF g -> case g of {}
instance HasField "balance" (Expr EContract) (Expr EWord) where
  getField e = case e.node of CF _ _ _ b _ -> b; GVarF g -> case g of {}
instance HasField "nonce" (Expr EContract) (Maybe W64) where
  getField e = case e.node of CF _ _ _ _ n -> n; GVarF g -> case g of {}



-- Existential Wrapper -----------------------------------------------------------------------------


data SomeExpr = forall a . Typeable a => SomeExpr (Expr a)

deriving instance Show SomeExpr

instance Eq SomeExpr where
  SomeExpr (a :: Expr b) == SomeExpr (c :: Expr d) =
    case eqT @b @d of
      Just Refl -> a == c
      Nothing -> False

instance Ord SomeExpr where
  compare (SomeExpr (a :: Expr b)) (SomeExpr (c :: Expr d)) =
    case eqT @b @d of
      Just Refl -> compare a c
      Nothing -> compare (toNum a) (toNum c)

toNum :: (Typeable a) => Expr a -> Int
toNum (_ :: Expr a) =
  case eqT @a @Buf of
    Just Refl -> 1
    Nothing -> case eqT @a @Storage of
      Just Refl -> 2
      Nothing -> case eqT @a @Log of
        Just Refl -> 3
        Nothing -> case eqT @a @EWord of
          Just Refl -> 4
          Nothing -> case eqT @a @Byte of
            Just Refl -> 5
            Nothing -> 6


-- Propostions -------------------------------------------------------------------------------------


-- The language of assertable expressions.
-- This is useful when generating SMT queries based on Expr instances, since
-- the translation of Eq and other boolean operators from Expr to SMT is an
-- (ite (eq a b) 1 0). We can use the boolean operators here to remove some
-- unescessary `ite` statements from our SMT encoding.
data Prop where
  PEq :: forall a . Typeable a => Expr a -> Expr a -> Prop
  PLT :: Expr EWord -> Expr EWord -> Prop
  PGT :: Expr EWord -> Expr EWord -> Prop
  PGEq :: Expr EWord -> Expr EWord -> Prop
  PLEq :: Expr EWord -> Expr EWord -> Prop
  PNeg :: Prop -> Prop
  PAnd :: Prop -> Prop -> Prop
  POr :: Prop -> Prop -> Prop
  PImpl :: Prop -> Prop -> Prop
  PBool :: Bool -> Prop
deriving instance (Show Prop)

infixr 3 .&&
(.&&) :: Prop -> Prop -> Prop
x .&& y = PAnd x y

infixr 2 .||
(.||) :: Prop -> Prop -> Prop
x .|| y = POr x y

infix 4 .<, .<=, .>, .>=
(.<) :: Expr EWord -> Expr EWord -> Prop
x .< y = PLT x y
(.<=) :: Expr EWord -> Expr EWord -> Prop
x .<= y = PLEq x y
(.>) :: Expr EWord -> Expr EWord -> Prop
x .> y = PGT x y
(.>=) :: Expr EWord -> Expr EWord -> Prop
x .>= y = PGEq x y

infix 4 .==, ./=
(.==) :: (Typeable a) => Expr a -> Expr a -> Prop
x .== y = PEq x y
(./=) :: (Typeable a) => Expr a -> Expr a -> Prop
x ./= y = PNeg (PEq x y)

pand :: [Prop] -> Prop
pand = foldl' PAnd (PBool True)

por :: [Prop] -> Prop
por = foldl' POr (PBool False)

instance Eq Prop where
  PBool a == PBool b = a == b
  PEq (a :: Expr x) (b :: Expr x) == PEq (c :: Expr y) (d :: Expr y)
    = case eqT @x @y of
       Just Refl -> a == c && b == d
       Nothing -> False
  PLT a b == PLT c d = a == c && b == d
  PGT a b == PGT c d = a == c && b == d
  PGEq a b == PGEq c d = a == c && b == d
  PLEq a b == PLEq c d = a == c && b == d
  PNeg a == PNeg b = a == b
  PAnd a b == PAnd c d = a == c && b == d
  POr a b == POr c d = a == c && b == d
  PImpl a b == PImpl c d = a == c && b == d
  _ == _ = False

instance Ord Prop where
  compare (PBool a) (PBool b) = compare a b
  compare (PEq (a :: Expr x) (b :: Expr x)) (PEq (c :: Expr y) (d :: Expr y)) =
    case eqT @x @y of
      Just Refl -> compare (a, b) (c, d)
      Nothing   -> compare (typeRep a) (typeRep c)
  compare (PNeg a) (PNeg b) = compare a b
  compare (PLT a1 b1) (PLT a2 b2) = compare (a1, b1) (a2, b2)
  compare (PGT a1 b1) (PGT a2 b2) = compare (a1, b1) (a2, b2)
  compare (PGEq a1 b1) (PGEq a2 b2) = compare (a1, b1) (a2, b2)
  compare (PLEq a1 b1) (PLEq a2 b2) = compare (a1, b1) (a2, b2)
  compare (PAnd a1 b1) (PAnd a2 b2) = compare (a1, b1) (a2, b2)
  compare (POr a1 b1) (POr a2 b2) = compare (a1, b1) (a2, b2)
  compare (PImpl a1 b1) (PImpl a2 b2) = compare (a1, b1) (a2, b2)
  compare a b = compare (tag a) (tag b)

    where
      tag :: Prop -> Int
      tag PBool{} = 0
      tag PEq{}   = 1
      tag PLT{}   = 2
      tag PGT{}   = 3
      tag PGEq{}  = 4
      tag PLEq{}  = 5
      tag PNeg{}  = 6
      tag PAnd{}  = 7
      tag POr{}   = 8
      tag PImpl{} = 9


isPBool :: Prop -> Bool
isPBool (PBool _) = True
isPBool _ = False


-- Errors ------------------------------------------------------------------------------------------

-- General error helper
type Err a = Either String a
getError :: Err a -> String
getError (Left a) = a
getError _ = internalError "getLeft on a Right"
getNonError :: Err a -> a
getNonError (Right a) = a
getNonError _ = internalError "getRight on a Left"

-- | Core EVM Error Types
data EvmError
  = BalanceTooLow (Expr EWord) (Expr EWord)
  | UnrecognizedOpcode Word8
  | SelfDestruction
  | StackUnderrun
  | BadJumpDestination
  | Revert (Expr Buf)
  | OutOfGas Word64 Word64
  | StackLimitExceeded
  | IllegalOverflow
  | StateChangeWhileStatic
  | InvalidMemoryAccess
  | CallDepthLimitReached
  | MaxCodeSizeExceeded W256 W256
  | MaxInitCodeSizeExceeded W256 (Expr EWord)
  | InvalidFormat
  | PrecompileFailure
  | NonexistentPrecompile Addr
  | ReturnDataOutOfBounds
  | NonceOverflow
  | BadCheatCode String FunctionSelector
  | NonexistentFork Int
  | AssumeCheatFailed
  deriving (Show, Eq, Ord)

evmErrToString :: EvmError -> String
evmErrToString = \case
  -- NOTE: error text made to closely match go-ethereum's errors.go file
  OutOfGas {}             -> "Out of gas"
  -- TODO "contract creation code storage out of gas" not handled
  CallDepthLimitReached   -> "Max call depth exceeded"
  BalanceTooLow {}        -> "Insufficient balance for transfer"
  -- TODO "contract address collision" not handled
  Revert {}               -> "Execution reverted"
  -- TODO "max initcode size exceeded" not handled
  MaxCodeSizeExceeded {}  -> "Max code size exceeded"
  BadJumpDestination      -> "Invalid jump destination"
  StateChangeWhileStatic  -> "Attempting to modify state while in static context"
  ReturnDataOutOfBounds   -> "Return data out of bounds"
  IllegalOverflow         -> "Gas uint64 overflow"
  UnrecognizedOpcode op   -> "Invalid opcode: 0x" <> showHex op ""
  NonceOverflow           -> "Nonce uint64 overflow"
  StackUnderrun           -> "Stack underflow"
  StackLimitExceeded      -> "Stack limit reached"
  InvalidMemoryAccess     -> "Write protection"
  (BadCheatCode err fun)  -> err <> " Cheatcode function selector: " <> show fun
  NonexistentFork fork    -> "Nonexistent fork: " <> show fork
  PrecompileFailure       -> "Precompile failure"
  err                     -> "hevm error: " <> show err


-- | Sometimes we can only partially execute a given program
data PartialExec
  = UnexpectedSymbolicArg { pc :: Int, addr :: Expr EAddr, opcode :: String, msg  :: String, args  :: [SomeExpr] }
  | MaxIterationsReached  { pc :: Int, addr :: Expr EAddr }
  | JumpIntoSymbolicCode  { pc :: Int, addr :: Expr EAddr, jumpDst :: Int }
  | PrecompileMissing     { pc :: Int, addr :: Expr EAddr, preAddr :: Addr }
  | CheatCodeMissing      { pc :: Int, addr :: Expr EAddr, selector :: FunctionSelector }
  | BranchTooDeep         { pc :: Int, addr :: Expr EAddr}
  deriving (Show, Eq, Ord)

-- | A program-wide soundness caveat. Unlike a 'PartialExec', a caveat does not
-- mark an execution path that we failed to explore: every reachable path was
-- explored fully. It records that the *space of inputs* was restricted, so the
-- result is only valid within that restriction. It is therefore attached to the
-- verification result as a whole, not to an individual 'Expr End' leaf.
data Caveat
  = DynArgBounded { maxSize :: Int }  -- ^ dynamic (bytes/string) calldata args were bounded to this many bytes
  deriving (Show, Eq, Ord)

-- | Effect types used by the vm implementation for side effects & control flow
data Effect t where
  Query :: Query t -> Effect t
  Branch :: BranchContext -> Effect Symbolic
deriving instance Show (Effect t)

-- | Queries halt execution until resolved through RPC calls or SMT queries
data Query t where
  PleaseFetchContract :: Addr -> BaseState -> (Contract -> EVM t ()) -> Query t
  PleaseFetchSlot     :: Addr -> W256 -> (W256 -> EVM t ()) -> Query t
  PleaseAskSMT        :: Expr EWord -> [Prop] -> (BranchCondition -> EVM Symbolic ()) -> Query Symbolic
  PleaseGetSols       :: Expr EWord -> Int -> [Prop] -> (Maybe [W256] -> EVM Symbolic ()) -> Query Symbolic
  PleaseDoFFI         :: [String] -> Map String String -> (ByteString -> EVM t ()) -> Query t
  PleaseReadEnv       :: String -> (String -> EVM t ()) -> Query t

data BranchContext where
  PleaseRunBoth :: (Bool -> EVM Symbolic ()) -> BranchContext
  PleaseRunAll  :: [Expr EWord] -> (Expr EWord -> EVM Symbolic ()) -> BranchContext

-- | The possible return values of a SMT query
data BranchCondition = Case Bool | UnknownBranch
  deriving Show

instance Show (Query t) where
  showsPrec _ = \case
    PleaseFetchContract addr base _ ->
      (("<EVM.Query: fetch contract " ++ show addr ++ show base ++ ">") ++)
    PleaseFetchSlot addr slot _ ->
      (("<EVM.Query: fetch slot "
        ++ show slot ++ " for "
        ++ show addr ++ ">") ++)
    PleaseAskSMT condition constraints _ ->
      (("<EVM.Query: ask SMT about "
        ++ show condition ++ " in context "
        ++ show constraints ++ ">") ++)
    PleaseGetSols expr numBytes constraints _ ->
      (("<EVM.Query: ask SMT "
        ++ "for " ++ show numBytes ++ " bytes "
        ++ "of W256 for expression "
        ++ show expr ++ " in context "
        ++ show constraints ++ ">") ++)
    PleaseDoFFI cmd env _ ->
      (("<EVM.Query: do ffi: " ++ (show cmd) ++ " env: " ++ (show env)) ++)
    PleaseReadEnv variable _ ->
      (("<EVM.Query: read env: " ++ variable) ++)

instance Show (BranchContext) where
  showsPrec _ = \case
    PleaseRunBoth _ ->
      (("<EVM.RunBoth: system running both paths") ++)

    PleaseRunAll _ _ ->
      (("<EVM.RunAll: system running all paths for Expr EWord-s") ++)

-- | The possible result states of a VM
data VMResult (t :: VMType) where
  Unfinished :: PartialExec -> VMResult Symbolic -- ^ Execution could not continue further
  VMFailure :: EvmError -> VMResult t            -- ^ An operation failed
  VMSuccess :: (Expr Buf) -> VMResult t          -- ^ Reached STOP, RETURN, or end-of-code
  HandleEffect :: (Effect t) -> VMResult t     -- ^ An effect must be handled for execution to continue

deriving instance Show (VMResult t)


-- VM State ----------------------------------------------------------------------------------------

-- | State tracking for speculative merge execution
data MergeState = MergeState
  { msActive          :: Bool   -- ^ Inside speculative execution
  , msRemainingBudget :: Int    -- ^ Instructions remaining in budget
  } deriving (Show, Eq, Generic)

defaultMergeState :: MergeState
defaultMergeState = MergeState False 0

-- | An active vm.expectRevert / vm.expectPartialRevert expectation set by a
-- cheat call. Consumed when the matching frame returns/reverts.
data ExpectedRevert = ExpectedRevert
  { reason         :: Maybe (Expr Buf)
  -- ^ Nothing matches any revert data; Just expected matches concrete bytes.
  , depth          :: Int
  -- ^ length of vm.frames at the cheat call. The matching boundary is the
  -- frame popping back down to this depth (i.e. the next outer subcall).
  , partialMatch   :: Bool
  -- ^ True for expectPartialRevert (compares only first 4 bytes of actual).
  , reverter       :: Maybe (Expr EAddr)
  -- ^ Nothing matches any reverter; Just want enforces actualReverter equals
  -- this address.
  , actualReverter :: Maybe (Expr EAddr)
  -- ^ The first contract observed reverting in a non-CREATE frame after the
  -- expectation was set. Captured on the first FrameReverted that arrives in a
  -- CALL frame; subsequent reverts (bubble-ups) do not overwrite it. Used at
  -- the matching boundary to compare against the expected reverter.
  }
  deriving (Show, Generic)

data VMType = Symbolic | Concrete

type family Gas (t :: VMType) = r | r -> t where
  Gas Symbolic = ()
  Gas Concrete = Word64

-- | The state of a stepwise EVM execution
data VM (t :: VMType) = VM
  { result         :: Maybe (VMResult t)
  , state          :: FrameState t
  , frames         :: [Frame t]
  , env            :: Env
  , block          :: Block
  , tx             :: TxState
  , logs           :: [Expr Log]
  , traces         :: Zipper.TreePos Zipper.Empty Trace
  , pathsVisited   :: PathsVisited
  , burned         :: !(Gas t)
  , iterations     :: Map CodeLocation (Int, [Expr EWord])
  -- ^ how many times we've visited a loc, and what the contents of the stack were when we were there last
  , constraints    :: [Prop]
  , config         :: RuntimeConfig
  , forks          :: Seq ForkState
  , currentFork    :: Int
  , srcLookup      :: Maybe SrcLookup
  , labels         :: Map Addr Text
  , osEnv          :: Map String String
  , freshVar       :: Int
  -- ^ used to generate fresh symbolic variable names for overapproximations
  --   during symbolic execution. See e.g. OpStaticcall
  , exploreDepth   :: Int
  , keccakPreImgs  :: Set (ByteString, W256)
  , mergeState     :: MergeState
  , expectedRevert :: Maybe ExpectedRevert
  -- ^ Active expectRevert/expectPartialRevert expectation, if any.
  }
  deriving (Generic)

data ForkState = ForkState
  { env :: Env
  , block :: Block
  , pathsVisited :: PathsVisited
  , urlOrAlias :: String
  }
  deriving (Show, Generic)

deriving instance Show (VM Symbolic)
deriving instance Show (VM Concrete)

-- | Alias for the type of e.g. @exec1@.
type EVM (t :: VMType) a = StateT (VM t) (ST RealWorld) a

-- | The VM base state (i.e. should new contracts be created with abstract balance / storage?)
data BaseState
  = EmptyBase
  | AbstractBase
  deriving (Show)

-- | A callback for looking up source location info given the contracts map,
-- an address, and a PC
newtype SrcLookup = SrcLookup (Map (Expr EAddr) Contract -> Expr EAddr -> Int -> String)

instance Show SrcLookup where
  show _ = "<SrcLookup Info>"

-- | Run a SrcLookup to get source location info, with a fallback for when
-- no SrcLookup is available.
runSrcLookup :: Maybe SrcLookup -> Map (Expr EAddr) Contract -> Expr EAddr -> Int -> String
runSrcLookup Nothing _ addr pc = " at addr: " <> show addr <> " at pc: " <> show pc
runSrcLookup (Just (SrcLookup f)) contracts addr pc = f contracts addr pc

-- | Configuration options that need to be consulted at runtime
data RuntimeConfig = RuntimeConfig
  { allowFFI :: Bool
  , baseState :: BaseState
  }
  deriving (Show)

-- | An entry in the VM's "call/create stack"
data Frame (t :: VMType) = Frame
  { context :: FrameContext
  , state   :: FrameState t
  }

deriving instance Show (Frame Symbolic)
deriving instance Show (Frame Concrete)

-- | Call/create info
data FrameContext
  = CreationContext
    { address         :: Expr EAddr
    , codehash        :: Expr EWord
    , createreversion :: Map (Expr EAddr) Contract
    , subState        :: SubState
    }
  | CallContext
    { target        :: Expr EAddr
    , context       :: Expr EAddr
    , offset        :: Expr EWord
    , size          :: Expr EWord
    , codehash      :: Expr EWord
    , abi           :: Maybe W256
    , calldata      :: Expr Buf
    , callreversion :: Map (Expr EAddr) Contract
    , subState      :: SubState
    }
  deriving (Eq, Ord, Show, Generic)

-- | The "accrued substate" across a transaction
data SubState = SubState
  { selfdestructs       :: [Expr EAddr]
  , touchedAccounts     :: [Expr EAddr]
  , accessedAddresses   :: Set (Expr EAddr)
  , accessedStorageKeys :: Set (Expr EAddr, W256)
  , refunds             :: [(Expr EAddr, Word64)]
  , createdContracts    :: Set (Expr EAddr)
  -- in principle we should include logs here, but do not for now
  }
  deriving (Eq, Ord, Show)

-- | The "registers" of the VM along with memory and data stack
data FrameState (t :: VMType) = FrameState
  { contract     :: Expr EAddr
  , codeContract :: Expr EAddr
  , code         :: ContractCode
  , pc           :: {-# UNPACK #-} !Int -- program counter in BYTES (not ops). PUSH ops will increment pc by more than 1
  , stack        :: [Expr EWord]
  , memory       :: Memory
  , memorySize   :: Word64
  , calldata     :: Expr Buf
  , callvalue    :: Expr EWord
  , caller       :: Expr EAddr
  , gas          :: !(Gas t)
  , returndata   :: Expr Buf
  , static       :: Bool
  , overrideCaller :: Maybe (Expr EAddr)
  , resetCaller  :: Bool
  }
  deriving (Generic)

deriving instance Show (FrameState Symbolic)
deriving instance Show (FrameState Concrete)

data Memory
  = ConcreteMemory (MutableMemory)
  | SymbolicMemory !(Expr Buf)

instance Show (Memory) where
  show (ConcreteMemory _) = "<can't show mutable memory>"
  show (SymbolicMemory m) = show m

type MutableMemory = STVector RealWorld Word8

-- | The state that spans a whole transaction
data TxState = TxState
  { gasprice    :: W256
  , gaslimit    :: Word64
  , priorityFee :: W256
  , origin      :: Expr EAddr
  , toAddr      :: Expr EAddr
  , value       :: Expr EWord
  , subState    :: SubState
  , isCreate    :: Bool
  , txReversion :: Map (Expr EAddr) Contract
  , txdataFloorGas :: Word64
  }
  deriving (Show)

-- | Various environmental data
data Env = Env
  { contracts      :: Map (Expr EAddr) Contract
  , chainId        :: W256
  , freshAddresses :: Int
  , freshGasVals :: Int
  }
  deriving (Show, Generic)

-- | Data about the block
data Block = Block
  { coinbase    :: Expr EAddr
  , timestamp   :: Expr EWord
  , number      :: Expr EWord
  , prevRandao  :: W256
  , gaslimit    :: Word64
  , baseFee     :: W256
  , maxCodeSize :: W256
  , schedule    :: FeeSchedule Word64
  } deriving (Show, Generic)

-- | Full contract state
data Contract = Contract
  { code        :: ContractCode
  , storage     :: Expr Storage
  , tStorage    :: Expr Storage
  , origStorage :: Expr Storage
  , balance     :: Expr EWord
  , nonce       :: Maybe W64
  , codehash    :: Expr EWord
  , opIxMap     :: VS.Vector Int -- ^ map from byte index to op index
  , codeOps     :: V.Vector (Int, Op)
  , external    :: Bool
  }
  deriving (Show, Eq, Ord)

class VMOps (t :: VMType) where
  burn' :: Gas t -> EVM t () -> EVM t ()
  -- TODO: change to EvmWord t
  burnExp :: Expr EWord -> EVM t () -> EVM t ()
  burnSha3 :: Expr EWord -> EVM t () -> EVM t ()
  burnCalldatacopy :: Expr EWord -> EVM t () -> EVM t ()
  burnCodecopy :: Expr EWord -> EVM t () -> EVM t ()
  burnExtcodecopy :: Expr EAddr -> Expr EWord -> EVM t () -> EVM t ()
  burnReturndatacopy :: Expr EWord -> EVM t () -> EVM t ()
  burnLog :: Expr EWord -> Word8 -> EVM t () -> EVM t ()

  initialGas :: Gas t
  ensureGas :: Word64 -> EVM t () -> EVM t ()
  -- TODO: change to EvmWord t
  gasTryFrom :: Expr EWord -> Either () (Gas t)

  -- Gas cost of create, including hash cost if needed
  costOfCreate :: FeeSchedule Word64 -> Gas t -> Expr EWord -> Bool -> (Gas t, Gas t)

  costOfCall
    :: FeeSchedule Word64 -> Bool -> Expr EWord -> Gas t -> Gas t -> Expr EAddr
    -> (Word64 -> Word64 -> EVM t ()) -> EVM t ()

  reclaimRemainingGasAllowance :: VM t -> EVM t ()
  payRefunds :: EVM t ()
  pushGas :: EVM t ()
  enoughGas :: Word64 -> Gas t -> Bool
  subGas :: Gas t -> Word64 -> Gas t
  toGas :: Word64 -> Gas t

  whenSymbolicElse :: EVM t a -> EVM t a -> EVM t a

  partial :: PartialExec -> EVM t ()
  branch :: Maybe Int -> Expr EWord -> (Bool -> EVM t ()) -> EVM t ()
  manySolutions :: Maybe Int -> Expr EWord -> Int -> (Maybe W256 -> EVM t ()) -> EVM t ()

-- Bytecode Representations ------------------------------------------------------------------------


-- | A unique id for a given pc
type CodeLocation = (Expr EAddr, Int)
type PathsVisited = Map (CodeLocation, Int) Bool


-- Bytecode Representations ------------------------------------------------------------------------


{- |
  A contract is either in creation (running its "constructor") or
  post-creation, and code in these two modes is treated differently
  by instructions like @EXTCODEHASH@, so we distinguish these two
  code types.

  The definition follows the structure of code output by solc. We need to use
  some heuristics here to deal with symbolic data regions that may be present
  in the bytecode since the fully abstract case is impractical:

  - initcode has concrete code, followed by an abstract data "section"
  - runtimecode has a fixed length, but may contain fixed size symbolic regions (due to immutable)

  hopefully we do not have to deal with dynamic immutable before we get a real data section...
-}
data ContractCode
  = UnknownCode (Expr EAddr)       -- ^ Fully abstract code, keyed on an address to give consistent results for e.g. extcodehash
  | InitCode ByteString (Expr Buf) -- ^ "Constructor" code, during contract creation
  | RuntimeCode RuntimeCode        -- ^ "Instance" code, after contract creation
  deriving (Show, Eq, Ord)

-- | We have two variants here to optimize the fully concrete case.
-- ConcreteRuntimeCode just wraps a ByteString
-- SymbolicRuntimeCode is a fixed length vector of potentially symbolic bytes, which lets us handle symbolic pushdata (e.g. from immutable variables in solidity).
data RuntimeCode
  = ConcreteRuntimeCode ByteString
  | SymbolicRuntimeCode (V.Vector (Expr Byte))
  deriving (Eq, Ord)
instance Show RuntimeCode
  where
    show = \case
      ConcreteRuntimeCode e -> "ConcreteRuntimeCode 0x" <> bsToHex e
      SymbolicRuntimeCode e -> show e

-- Execution Traces --------------------------------------------------------------------------------


data Trace = Trace
  { opIx      :: Int
  , contract  :: Contract
  , tracedata :: TraceData
  }
  deriving (Eq, Ord, Show, Generic)

data TraceData
  = EventTrace (Expr EWord) (Expr Buf) [Expr EWord]
  | FrameTrace FrameContext
  | ErrorTrace EvmError
  | EntryTrace Text
  | ReturnTrace (Expr Buf) FrameContext
  | ConsoleLog (Expr Buf)
  deriving (Eq, Ord, Show, Generic)

-- | Wrapper type containing vm traces and the context needed to pretty print them properly
data TraceContext = TraceContext
  { traces :: Forest Trace
  , contracts :: Map (Expr EAddr) Contract
  , labels :: Map Addr Text
  }
  deriving (Eq, Ord, Show, Generic)

instance Semigroup TraceContext where
  (TraceContext a b c) <> (TraceContext d e f) = TraceContext (a <> d) (b <> e) (c <> f)
instance Monoid TraceContext where
  mempty = TraceContext mempty mempty mempty


-- VM Initialization -------------------------------------------------------------------------------


-- | A specification for an initial VM state
data VMOpts (t :: VMType) = VMOpts
  { contract :: Contract
  , otherContracts :: [(Expr EAddr, Contract)]
  , calldata :: (Expr Buf, [Prop])
  , baseState :: BaseState
  , value :: Expr EWord
  , priorityFee :: W256
  , address :: Expr EAddr
  , caller :: Expr EAddr
  , origin :: Expr EAddr
  , gas :: Gas t
  , gaslimit :: Word64
  , number :: Expr EWord
  , timestamp :: Expr EWord
  , coinbase :: Expr EAddr
  , prevRandao :: W256
  , maxCodeSize :: W256
  , blockGaslimit :: Word64
  , gasprice :: W256
  , baseFee :: W256
  , schedule :: FeeSchedule Word64
  , chainId :: W256
  , create :: Bool
  , txAccessList :: Map (Expr EAddr) [W256]
  , allowFFI :: Bool
  , freshAddresses :: Int
  , beaconRoot :: W256
  , parentHash :: W256      -- EIP-2935 parent block hash
  , txdataFloorGas :: Word64
  }

deriving instance Show (VMOpts Symbolic)
deriving instance Show (VMOpts Concrete)


-- Opcodes -----------------------------------------------------------------------------------------


type Op = GenericOp (Expr EWord)

data GenericOp a
  = OpStop
  | OpAdd
  | OpMul
  | OpSub
  | OpDiv
  | OpSdiv
  | OpMod
  | OpSmod
  | OpAddmod
  | OpMulmod
  | OpExp
  | OpSignextend
  | OpLt
  | OpGt
  | OpSlt
  | OpSgt
  | OpEq
  | OpIszero
  | OpAnd
  | OpOr
  | OpXor
  | OpNot
  | OpByte
  | OpShl
  | OpShr
  | OpSar
  | OpClz
  | OpSha3
  | OpAddress
  | OpBalance
  | OpOrigin
  | OpCaller
  | OpCallvalue
  | OpCalldataload
  | OpCalldatasize
  | OpCalldatacopy
  | OpCodesize
  | OpCodecopy
  | OpGasprice
  | OpExtcodesize
  | OpExtcodecopy
  | OpReturndatasize
  | OpReturndatacopy
  | OpExtcodehash
  | OpBlockhash
  | OpCoinbase
  | OpTimestamp
  | OpNumber
  | OpPrevRandao
  | OpGaslimit
  | OpChainid
  | OpSelfbalance
  | OpBaseFee
  | OpBlobhash
  | OpBlobBaseFee
  | OpPop
  | OpMcopy
  | OpMload
  | OpMstore
  | OpMstore8
  | OpSload
  | OpSstore
  | OpTload
  | OpTstore
  | OpJump
  | OpJumpi
  | OpPc
  | OpMsize
  | OpGas
  | OpJumpdest
  | OpCreate
  | OpCall
  | OpStaticcall
  | OpCallcode
  | OpReturn
  | OpDelegatecall
  | OpCreate2
  | OpRevert
  | OpSelfdestruct
  | OpDup !Word8
  | OpSwap !Word8
  | OpLog !Word8
  | OpPush0
  | OpPush a
  | OpUnknown Word8
  deriving (Show, Eq, Ord, Functor)


-- | A model for a buffer, either in it's compressed form (for storing parsed
-- models from a solver), or as a bytestring (for presentation to users)
data BufModel
  = Comp CompressedBuf
  | Flat ByteString
  deriving (Eq)
instance Show BufModel where
  show (Comp c) = "Comp " <> show c
  show (Flat b) = "Flat 0x" <> bsToHex b

-- | This representation lets us store buffers of arbitrary length without
-- exhausting the available memory, it closely matches the format used by
-- smt-lib when returning models for arrays
data CompressedBuf
  = Base { byte :: Word8, length :: W256}
  | Write { byte :: Word8, idx :: W256, next :: CompressedBuf }
  deriving (Eq, Show)

-- | a final post shrinking cex, buffers here are all represented as concrete bytestrings
data SMTCex = SMTCex
  { vars :: Map (Expr EWord) W256
  , addrs :: Map (Expr EAddr) Addr
  , buffers :: Map (Expr Buf) BufModel
  , store :: Map (Expr EAddr) (Map W256 W256)
  , blockContext :: Map (Expr EWord) W256
  , txContext :: Map (Expr EWord) W256
  }
  deriving (Eq, Show)

instance Semigroup SMTCex where
  a <> b = SMTCex
    { vars = a.vars <> b.vars
    , addrs = a.addrs <> b.addrs
    , buffers = a.buffers <> b.buffers
    , store = a.store <> b.store
    , blockContext = a.blockContext <> b.blockContext
    , txContext = a.txContext <> b.txContext
    }

instance Monoid SMTCex where
  mempty = SMTCex
    { vars = mempty
    , addrs = mempty
    , buffers = mempty
    , store = mempty
    , blockContext = mempty
    , txContext = mempty
    }

data ReproducibleCex = ReproducibleCex
  { testName :: Text
  , callData :: ByteString
  }
  deriving (Eq)
instance Show ReproducibleCex where
  show (ReproducibleCex name data') =
    "ReproducibleCex { testName = " <> show name <>
    ", callData = 0x" <> bsToHex data' <> " }"

class GetUnknownStr a where
    getUnknownStr :: a -> String

instance GetUnknownStr String where
    getUnknownStr = id

instance GetUnknownStr (String, Expr End) where
    getUnknownStr (s, _) = s

data ProofResult a (b :: Type) where
    Qed :: ProofResult a b
    Cex :: a -> ProofResult a b
    Unknown :: GetUnknownStr b => b -> ProofResult a b
    Error :: String -> ProofResult a b

instance (Show a, Show b) => Show (ProofResult a b) where
  show Qed = "Qed"
  show (Cex c) = "Cex " <> show c
  show (Unknown u) = "Unknown " <> show u
  show (Error e) = "Error: " <> e

instance (Eq a, Eq b) => Eq (ProofResult a b) where
  x == y = case (x, y) of
    (Unknown u1, Unknown u2) -> u1 == u2
    (Error a, Error b)       -> a == b
    (Cex a, Cex b)           -> a == b
    (Qed, Qed)               -> True
    _                        -> False

type VerifyResult = ProofResult (Expr End, SMTCex) (String, Expr End)
type EquivResult = ProofResult SMTCex String
type SMTResult = ProofResult SMTCex String

getUnknown :: ProofResult a b -> Maybe b
getUnknown (Unknown a) = Just a
getUnknown _ = Nothing

isUnknown :: ProofResult a b -> Bool
isUnknown (Unknown _) = True
isUnknown _ = False

isError :: ProofResult a b -> Bool
isError (Error _) = True
isError _ = False

getResError :: ProofResult a b -> Maybe String
getResError (Error e) = Just e
getResError _ = Nothing

isCex :: ProofResult a b -> Bool
isCex (Cex _) = True
isCex _ = False

isQed :: ProofResult a b -> Bool
isQed Qed = True
isQed _ = False


-- Function Selectors ------------------------------------------------------------------------------

-- | https://docs.soliditylang.org/en/v0.8.19/abi-spec.html#function-selector
newtype FunctionSelector = FunctionSelector { unFunctionSelector :: Word32 }
  deriving (Bits, Num, Eq, Ord, Real, Enum, Integral)
instance Show FunctionSelector where show s = "0x" <> showHex s ""
instance Read FunctionSelector where
  readsPrec _ ('0':'x':s) = first FunctionSelector <$> readHex s
  readsPrec _ s = first FunctionSelector <$> readHex s


-- ByteString wrapper ------------------------------------------------------------------------------


-- Newtype wrapper for ByteString to allow custom instances
newtype ByteStringS = ByteStringS ByteString deriving (Eq, Generic)

instance Show ByteStringS where
  show (ByteStringS x) = ("0x" ++) . T.unpack . fromBinary $ x
    where
      fromBinary =
        T.decodeUtf8 . toStrict . toLazyByteString . byteStringHex

instance JSON.FromJSON ByteStringS where
  parseJSON (JSON.String x) =
    let x' = if "0x" `T.isPrefixOf` x then T.drop 2 x else x in
    case BS16.decodeBase16Untyped (T.encodeUtf8 x') of
                                Left _ -> mzero
                                Right bs -> pure (ByteStringS bs)
  parseJSON _ = mzero

instance JSON.ToJSON ByteStringS where
  toJSON (ByteStringS x) = JSON.String (T.pack $ "0x" ++ (concatMap (paddedShowHex 2) . BS.unpack $ x))


-- Word256 wrapper ---------------------------------------------------------------------------------


-- Newtype wrapper around Word256 to allow custom instances
newtype W256 = W256 Word256
  deriving
    ( Num, Integral, Real, Ord, Bits
    , Generic, FiniteBits, Enum, Eq , Bounded
    )

instance Read W256 where
  readsPrec _ "0x" = [(0, "")]
  readsPrec n s = first W256 <$> readsPrec n s

instance Show W256 where
  showsPrec _ s = ("0x" ++) . showHex s

instance JSON.ToJSON W256 where
  toJSON x = JSON.String  $ T.pack ("0x" ++ pad ++ cutshow)
    where
      cutshow = drop 2 $ show x
      pad = replicate (64 - length (cutshow)) '0'

instance JSON.ToJSONKey W256 where
  toJSONKey = JSON.toJSONKeyText $ \x ->
    let cutshow = drop 2 $ show x
        pad = replicate (64 - length cutshow) '0'
    in T.pack ("0x" ++ pad ++ cutshow)

instance JSON.FromJSON W256 where
  parseJSON v = do
    s <- T.unpack <$> JSON.parseJSON v
    case reads s of
      [(x, "")]  -> pure x
      _          -> fail $ "invalid hex word (" ++ s ++ ")"

instance JSON.FromJSONKey W256 where
  fromJSONKey = JSON.FromJSONKeyTextParser $ \s ->
    case reads (T.unpack s) of
      [(x, "")]  -> pure x
      _          -> fail $ "invalid word (" ++ T.unpack s ++ ")"

wordField :: JSON.Object -> JSON.Key -> JSON.Parser W256
wordField x f = ((readNull 0) . T.unpack)
                  <$> (x JSON..: f)

instance ParseField W256
instance ParseFields W256
instance ParseRecord W256 where
  parseRecord = fmap getOnly parseRecord


-- Word64 wrapper ----------------------------------------------------------------------------------


newtype W64 = W64 Data.Word.Word64
  deriving
    ( Num, Integral, Real, Ord, Generic
    , Bits , FiniteBits, Enum, Eq , Bounded
    )

instance Read W64 where
  readsPrec _ "0x" = [(0, "")]
  readsPrec n s = first W64 <$> readsPrec n s

instance Show W64 where
  showsPrec _ s = ("0x" ++) . showHex s

instance JSON.ToJSON W64 where
  toJSON x = JSON.String  $ T.pack $ show x

instance JSON.FromJSON W64 where
  parseJSON v = do
    s <- T.unpack <$> JSON.parseJSON v
    case reads s of
      [(x, "")]  -> pure x
      _          -> fail $ "invalid hex word (" ++ s ++ ")"


word64Field :: JSON.Object -> JSON.Key -> JSON.Parser Word64
word64Field x f = ((readNull 0) . T.unpack)
                  <$> (x JSON..: f)


-- Addresses ---------------------------------------------------------------------------------------


newtype Addr = Addr { addressWord160 :: Word160 }
  deriving
    ( Num, Integral, Real, Ord, Enum
    , Eq, Generic, Bits, FiniteBits
    )

instance Read Addr where
  readsPrec _ ('0':'x':s) = readHex s
  readsPrec _ s = readHex s

instance Show Addr where
  showsPrec _ addr next =
    let hex = showHex addr next
        str = replicate (40 - length hex) '0' ++ hex
    in "0x" ++ toChecksumAddress str ++ drop 40 str

-- https://eips.ethereum.org/EIPS/eip-55
toChecksumAddress :: String -> String
toChecksumAddress addr = zipWith transform nibbles addr
  where
    nibbles = unpackNibbles . BS.take 20 $ keccakBytes (Char8.pack addr)
    transform nibble = if nibble >= 8 then toUpper else id

instance JSON.ToJSON Addr where
  toJSON = JSON.String . T.pack . show

instance JSON.FromJSON Addr where
  parseJSON v = do
    s <- T.unpack <$> JSON.parseJSON v
    case reads s of
      [(x, "")] -> pure x
      _         -> fail $ "invalid address (" ++ s ++ ")"

instance JSON.ToJSONKey Addr where
  toJSONKey = JSON.toJSONKeyText (addrKey)
    where
      addrKey :: Addr -> Text
      addrKey addr = T.pack $ replicate (40 - length hex) '0' ++ hex
        where
          hex = show addr

instance JSON.FromJSONKey Addr where
  fromJSONKey = JSON.FromJSONKeyTextParser $ \s ->
    case reads (T.unpack s) of
      [(x, "")] -> pure x
      _         -> fail $ "invalid word (" ++ T.unpack s ++ ")"

addrField :: JSON.Object -> JSON.Key -> JSON.Parser Addr
addrField x f = (read . T.unpack) <$> (x JSON..: f)

addrFieldMaybe :: JSON.Object -> JSON.Key -> JSON.Parser (Maybe Addr)
addrFieldMaybe x f = (Text.Read.readMaybe . T.unpack) <$> (x JSON..: f)

instance ParseField Addr
instance ParseFields Addr
instance ParseRecord Addr where
  parseRecord = fmap getOnly parseRecord


-- Nibbles -----------------------------------------------------------------------------------------


-- | A four bit value
newtype Nibble = Nibble Word8
  deriving (Num, Integral, Real, Ord, Enum, Eq, Bounded, Generic)

instance Show Nibble where
  show = (:[]) . intToDigit . into

-- Conversions -------------------------------------------------------------------------------------

word256 :: ByteString -> Word256
word256 xs | BS.length xs == 1 =
  -- optimize one byte pushes
  Word256 (Word128 0 0) (Word128 0 (into $ BS.head xs))
word256 xs = case Cereal.runGet m (padLeft 32 xs) of
               Left _ -> internalError "should not happen"
               Right x -> x
  where
    m = do a <- Cereal.getWord64be
           b <- Cereal.getWord64be
           c <- Cereal.getWord64be
           d <- Cereal.getWord64be
           pure $ Word256 (Word128 a b) (Word128 c d)

word :: ByteString -> W256
word = W256 . word256

fromBE :: (Integral a) => ByteString -> a
fromBE xs = if xs == mempty then 0
  else 256 * fromBE (BS.init xs)
       + (fromIntegral $ BS.last xs)

asBE :: (Integral a) => a -> ByteString
asBE 0 = mempty
asBE x = asBE (x `div` 256)
  <> BS.pack [fromIntegral $ x `mod` 256]

word256Bytes :: W256 -> ByteString
word256Bytes (W256 (Word256 (Word128 a b) (Word128 c d))) =
  unsafeCreate 32 $ \ptr -> do
    let ptr' = castPtr ptr
    poke (ptr' `plusPtr`  0) $ hton64 a
    poke (ptr' `plusPtr`  8) $ hton64 b
    poke (ptr' `plusPtr` 16) $ hton64 c
    poke (ptr' `plusPtr` 24) $ hton64 d

-- old, slower word256Bytes implementation, kept for differential fuzzing
slow_word256Bytes :: W256 -> ByteString
slow_word256Bytes (W256 (Word256 (Word128 a b) (Word128 c d))) =
  Cereal.encode (a, b, c, d)

word160Bytes :: Addr -> ByteString
word160Bytes (Addr (Word160 a (Word128 b c))) =
  unsafeCreate 20 $ \ptr -> do
    let ptr' = castPtr ptr
    poke (ptr' `plusPtr`  0) $ hton32 a
    poke (ptr' `plusPtr`  4) $ hton64 b
    poke (ptr' `plusPtr` 12) $ hton64 c

-- old, slower word160Bytes implementation, kept for differential fuzzing
slow_word160Bytes :: Addr -> ByteString
slow_word160Bytes (Addr (Word160 a (Word128 b c))) =
  Cereal.encode (a, b, c)

hton32 :: Word32 -> Word32
hton32 | targetByteOrder == LittleEndian = byteSwap32
       | otherwise = id
{-# INLINE hton32 #-}

hton64 :: Word64 -> Word64
hton64 | targetByteOrder == LittleEndian = byteSwap64
       | otherwise = id
{-# INLINE hton64 #-}

-- Get first and second Nibble from byte
hi, lo :: Word8 -> Nibble
hi b = Nibble $ b `shiftR` 4
lo b = Nibble $ b .&. 0x0f

toByte :: Nibble -> Nibble -> Word8
toByte  (Nibble high) (Nibble low) = high `shift` 4 .|. low

unpackNibbles :: ByteString -> [Nibble]
unpackNibbles bs = BS.unpack bs >>= unpackByte
  where unpackByte b = [hi b, lo b]

-- Well-defined for even length lists only (plz dependent types)
packNibbles :: [Nibble] -> ByteString
packNibbles [] = mempty
packNibbles (n1:n2:ns) = BS.singleton (toByte n1 n2) <> packNibbles ns
packNibbles _ = internalError "can't pack odd number of nibbles"

toWord64 :: W256 -> Maybe Word64
toWord64 n =
  if n <= into (maxBound :: Word64)
    then let (W256 (Word256 _ (Word128 _ n'))) = n in Just n'
    else Nothing

bssToBs :: ByteStringS -> ByteString
bssToBs (ByteStringS bs) = bs


-- Function to construct a W256 from a list of 32 Word8 values
constructWord256 :: [Word8] -> W256
constructWord256 bytes
    | length bytes == 32 = W256 (Word256 (Word128 w256hi w256m1) (Word128 w256m0 w256lo))
    | otherwise = internalError "List must contain exactly 32 Word8 values"
  where
    w256hi = word8sToWord64 (take 8 bytes)
    w256m1 = word8sToWord64 (take 8 (drop 8 bytes))
    w256m0 = word8sToWord64 (take 8 (drop 16 bytes))
    w256lo = word8sToWord64 (take 8 (drop 24 bytes))
    word8sToWord64 :: [Word8] -> Word64
    word8sToWord64 = foldl' (\acc byte -> (acc `shiftL` 8) .|. fromIntegral byte) 0


-- Keccak hashing ----------------------------------------------------------------------------------


keccakBytes :: ByteString -> ByteString
keccakBytes =
  (hash :: ByteString -> Digest Keccak_256)
    >>> BA.convert

word32 :: [Word8] -> Word32
word32 xs = sum [ into x `shiftL` (8*n)
                | (n, x) <- zip [0..] (reverse xs) ]

keccak :: Expr Buf -> Expr EWord
keccak (ConcreteBuf bs) = Lit $ keccak' bs
keccak buf = Keccak buf

keccak' :: ByteString -> W256
keccak' = keccakBytes >>> BS.take 32 >>> word

abiKeccak :: ByteString -> FunctionSelector
abiKeccak =
  keccakBytes
    >>> BS.take 4
    >>> BS.unpack
    >>> word32
    >>> FunctionSelector


-- Utils -------------------------------------------------------------------------------------------

{- HLINT ignore internalError -}
internalError :: HasCallStack => [Char] -> a
internalError m = error $ "Internal Error: " ++ m ++ " -- " ++ (prettyCallStack callStack)

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = fmap concat (mapM f xs)

regexMatches :: Text -> Text -> Bool
regexMatches regexSource =
  let
    compOpts =
      Regex.defaultCompOpt { Regex.lastStarGreedy = True }
    execOpts =
      Regex.defaultExecOpt { Regex.captureGroups = False }
    regex = Regex.makeRegexOpts compOpts execOpts (T.unpack regexSource)
  in
    Regex.matchTest regex . Seq.fromList . T.unpack

readNull :: Read a => a -> String -> a
readNull x = fromMaybe x . Text.Read.readMaybe

padLeft :: Int -> ByteString -> ByteString
padLeft n xs = BS.replicate (n - BS.length xs) 0 <> xs

padLeft' :: Int -> V.Vector (Expr Byte) -> V.Vector (Expr Byte)
padLeft' n xs = V.replicate (n - length xs) (LitByte 0) <> xs

padRight :: Int -> ByteString -> ByteString
padRight n xs = xs <> BS.replicate (n - BS.length xs) 0

padRight' :: Int -> String -> String
padRight' n xs = xs <> replicate (n - length xs) '0'

-- We need this here instead of Format for cyclic import reasons...
formatString :: ByteString -> String
formatString bs =
  case T.decodeUtf8' (fst (BS.spanEnd (== 0) bs)) of
    Right s -> "\"" <> T.unpack s <> "\""
    Left _ -> "❮utf8 decode failed❯: " <> (show $ ByteStringS bs)

-- |'paddedShowHex' displays a number in hexadecimal and pads the number
-- with 0 so that it has a minimum length of @w@.
paddedShowHex :: (Show a, Integral a) => Int -> a -> String
paddedShowHex w n = pad ++ str
    where
     str = showHex n ""
     pad = replicate (w - length str) '0'


untilFixpoint :: Eq a => (a -> a) -> a -> a
untilFixpoint f a =
  let a' = f a in
    if a' == a
    then a
    else untilFixpoint f a'

bsToHex :: ByteString -> String
bsToHex bs = concatMap (paddedShowHex 2) (BS.unpack bs)

-- Used during forceAddr to deal with symbolic addresses
forceEAddrToEWord :: Expr EAddr -> Expr EWord
forceEAddrToEWord = \case
  LitAddr a -> Lit (into a)
  SymAddr a ->  WAddr (SymAddr a)
  _ -> internalError "Unexpected address type forced to EWord"

forceEWordToEAddr :: Expr 'EWord -> Expr 'EAddr
forceEWordToEAddr = \case
  Lit a -> LitAddr (truncateToAddr a)
  WAddr (SymAddr a) -> SymAddr a
  _ -> internalError "Unexpected EWord type forced to address"

forceLit :: Expr EWord -> W256
forceLit (Lit x) = x
forceLit x = internalError $ "concrete vm, shouldn't ever happen: " <> show x

-- Optics ------------------------------------------------------------------------------------------


makeFieldLabelsNoPrefix ''VM
makeFieldLabelsNoPrefix ''FrameState
makeFieldLabelsNoPrefix ''TxState
makeFieldLabelsNoPrefix ''SubState
makeFieldLabelsNoPrefix ''Trace
makeFieldLabelsNoPrefix ''VMOpts
makeFieldLabelsNoPrefix ''Frame
makeFieldLabelsNoPrefix ''FrameContext
makeFieldLabelsNoPrefix ''Contract
makeFieldLabelsNoPrefix ''Env
makeFieldLabelsNoPrefix ''Block
makeFieldLabelsNoPrefix ''RuntimeConfig
