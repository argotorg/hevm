module EVM.SMT.Types where

import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder
import Data.Map (Map)
import Data.Set (Set)

import EVM.Types

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


-- | Data that we need to construct a nice counterexample
data CexVars = CexVars
  { -- | variable names that we need models for to reconstruct calldata
    calldata     :: [Text]
    -- | symbolic address names
  , addrs        :: [Text]
    -- | buffer names and guesses at their maximum size
  , buffers      :: Map Text (Expr EWord)
    -- | reads from abstract storage
  , storeReads   :: Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
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
