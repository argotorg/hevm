module EVM.SMT.Types where

import Control.Monad.Trans.Maybe (MaybeT)
import Data.Map (Map)
import Data.Map qualified as Map (unionWith)
import Data.Set (Set)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder

import EVM.Types

type MaybeIO = MaybeT IO

-- | Controls how division/modulo operations are encoded into SMT.
-- 'ConcreteDivision' uses inline ite-check-zero with real SMT ops (existing behavior).
-- 'AbstractDivision' uses uninterpreted functions (evm_evm_div, etc.) for performance.
data DivEncoding = ConcreteDivision | AbstractDivision
  deriving (Show, Eq)

data SMTEntry = SMTCommand Builder | SMTComment Builder
  deriving (Eq)

newtype SMTScript = SMTScript [SMTEntry]
  deriving (Eq, Monoid, Semigroup)

-- Props are ONLY for pretty printing the query Props
data SMT2 = SMT2 SMTScript CexVars [Prop]
  deriving (Eq)

instance Semigroup SMT2 where
  (SMT2 a c d) <> (SMT2 a2 c2 d2) = SMT2 (a <> a2) (c <> c2) (d <> d2)

instance Monoid SMT2 where
  mempty = SMT2 mempty mempty mempty


newtype StorageReads = StorageReads (Map (Expr EAddr, Maybe W256) (Set (Expr EWord)))
  deriving (Eq, Show)

instance Semigroup StorageReads where
  StorageReads m1 <> StorageReads m2 =
    StorageReads (Map.unionWith (<>) m1 m2)

instance Monoid StorageReads where
  mempty = StorageReads mempty


-- | Data that we need to construct a nice counterexample
data CexVars = CexVars
  { -- | variable names that we need models for to reconstruct calldata
    calldata     :: [Text]
    -- | symbolic address names
  , addrs        :: [Text]
    -- | buffer names and guesses at their maximum size
  , buffers      :: Map Text (Expr EWord)
    -- | reads from abstract storage
  , storeReads   :: StorageReads
    -- | the names of any block context variables
  , blockContext :: [Text]
    -- | the names of any tx context variables
  , txContext    :: [Text]
  }
  deriving (Eq, Show)

instance Semigroup CexVars where
  (CexVars a b c d e f) <> (CexVars a2 b2 c2 d2 e2 f2) = CexVars (a <> a2) (b <> b2) (c <> c2) (d <> d2) (e <> e2) (f <> f2)

instance Monoid CexVars where
    mempty = CexVars
      { calldata = mempty
      , addrs = mempty
      , buffers = mempty
      , storeReads = mempty
      , blockContext = mempty
      , txContext = mempty
      }
