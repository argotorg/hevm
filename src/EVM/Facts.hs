{-# LANGUAGE PatternSynonyms #-}

-- Converts between Ethereum contract states and simple trees of
-- texts.  Dumps and loads such trees as Git repositories (the state
-- gets serialized as commits with folders and files).
--
-- Example state file hierarchy:
--
--   /0123...abc/balance      says "0x500"
--   /0123...abc/code         says "60023429..."
--   /0123...abc/nonce        says "0x3"
--   /0123...abc/storage/0x1  says "0x1"
--   /0123...abc/storage/0x2  says "0x0"
--
-- This format could easily be serialized into any nested record
-- syntax, e.g. JSON.

module EVM.Facts
  ( File (..)
  , Fact (..)
  , Data (..)
  , Path (..)
  , apply
  , applyCache
  , cacheFacts
  , contractFacts
  , vmFacts
  , factToFile
  , fileToFact
  ) where

import Prelude hiding (Foldable(..))

import EVM          (bytecode, initialContract, loadContract)
import EVM.Expr     (writeStorage)
import EVM.Types

import Optics.Core
import Optics.State

import Control.Monad.State.Strict (execState)
import Control.Monad
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as BS16
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.Foldable (Foldable(..))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Ord (comparing)
import Text.Read (readMaybe)

-- We treat everything as ASCII byte strings because
-- we only use hex digits (and the letter 'x').
type ASCII = ByteString

-- When using string literals, default to infer the ASCII type.
default (ASCII)

-- We use the word "fact" to mean one piece of serializable
-- information about the state.
--
-- Note that Haskell allows this kind of union of records.
-- It's convenient here, but typically avoided.
data Fact
  = BalanceFact { addr :: Addr, what :: W256 }
  | NonceFact   { addr :: Addr, val :: W64 }
  | StorageFact { addr :: Addr, what :: W256, which :: W256 }
  | CodeFact    { addr :: Addr, blob :: ByteString }
  deriving (Eq, Show)

-- A fact path means something like "/0123...abc/storage/0x1",
-- or alternatively "contracts['0123...abc'].storage['0x1']".
data Path = Path [ASCII] ASCII
  deriving (Eq, Ord, Show)

-- A fact data is the content of a file.  We encapsulate it
-- with a newtype to make it easier to change the representation
-- (to use bytestrings, some sum type, or whatever).
newtype Data = Data { dataASCII :: ASCII }
  deriving (Eq, Ord, Show)

-- We use the word "file" to denote a serialized value at a path.
data File = File { filePath :: Path, fileData :: Data }
  deriving (Eq, Ord, Show)

class AsASCII a where
  dump :: a -> ASCII
  load :: ASCII -> Maybe a

instance AsASCII Addr where
  dump = Char8.pack . show
  load = readMaybe . Char8.unpack

instance AsASCII W64 where
  dump = Char8.pack . show
  load = readMaybe . Char8.unpack

instance AsASCII W256 where
  dump = Char8.pack . show
  load = readMaybe . Char8.unpack

instance AsASCII ByteString where
  dump x = BS16.encodeBase16' x <> "\n"
  load x =
    case BS16.decodeBase16 . mconcat . BS.split 10 $ x of
      Right y -> Just y
      _       -> Nothing

type Err a = Either String a

toLitW :: Expr EWord -> Err W256
toLitW = \case
  Lit w -> Right w
  w -> Left $ "cannot serialize symbolic word: " <> show w

toLitStore :: Expr Storage -> Err (Map W256 W256)
toLitStore = \case
  ConcreteStore s -> Right s
  s -> Left $ "cannot serialize symbolic store: " <> show s

toLitAddr :: Expr EAddr -> Err Addr
toLitAddr = \case
  LitAddr a -> Right a
  a -> Left $ "cannot serialize symbolic addr: " <> show a

contractFacts :: Addr -> Contract -> Err [Fact]
contractFacts a x = case (view bytecode x, x.nonce) of
  (Just (ConcreteBuf b), Just n) -> do
    bal <- toLitW x.balance
    store <- toLitStore x.storage
    pure $
      storageFacts a store ++
      [ BalanceFact a bal
      , NonceFact   a n
      , CodeFact    a b
      ]
  _ -> Left "cannot serialize symbolic contracts"


storageFacts :: Addr -> Map W256 W256 -> [Fact]
storageFacts a store = map f (Map.toList store)
  where
    f :: (W256, W256) -> Fact
    f (k, v) = StorageFact
      { addr  = a
      , what  = v
      , which = k
      }

cacheFacts :: Cache -> Err (Set Fact)
cacheFacts c = do
  let cs = Map.toList c.fetched
  facts <- concatMapM (uncurry contractFacts) cs
  pure $ Set.fromList facts

vmFacts :: VM s -> Err (Set Fact)
vmFacts vm = do
  let cs = Map.toList vm.env.contracts
  cs' <- forM cs $ \(k,v) -> do
    k' <- toLitAddr k
    pure (k', v)
  Set.fromList <$> concatMapM (uncurry contractFacts) cs'

-- Somewhat stupidly, this function demands that for each contract,
-- the code fact for that contract comes before the other facts for
-- that contract.  This is an incidental thing because right now we
-- always initialize contracts starting with the code (to calculate
-- the code hash and so on).
--
-- Therefore, we need to make sure to sort the fact set in such a way.
apply1 :: VM s -> Fact -> VM s
apply1 vm fact =
  case fact of
    CodeFact    {..} -> flip execState vm $ do
      let a = LitAddr addr
      assign (#env % #contracts % at a) (Just (EVM.initialContract (RuntimeCode (ConcreteRuntimeCode blob))))
      when (vm.state.contract == a) $ EVM.loadContract a
    StorageFact {..} ->
      vm & over (#env % #contracts % ix (LitAddr addr) % #storage) (writeStorage (Lit which) (Lit what))
    BalanceFact {..} ->
      vm & set (#env % #contracts % ix (LitAddr addr) % #balance) (Lit what)
    NonceFact   {..} ->
      vm & set (#env % #contracts % ix (LitAddr addr) % #nonce) (Just val)

apply2 :: VM s -> Fact -> VM s
apply2 vm fact =
  case fact of
    CodeFact    {..} -> flip execState vm $ do
      let a = LitAddr addr
      assign (#cache % #fetched % at addr) (Just (EVM.initialContract (RuntimeCode (ConcreteRuntimeCode blob))))
      when (vm.state.contract == a) $ EVM.loadContract a
    StorageFact {..} ->
        vm & over (#cache % #fetched % ix addr % #storage) (writeStorage (Lit which) (Lit what))
    BalanceFact {..} ->
      vm & set (#cache % #fetched % ix addr % #balance) (Lit what)
    NonceFact   {..} ->
      vm & set (#cache % #fetched % ix addr % #nonce) (Just val)

-- Sort facts in the right order for `apply1` to work.
instance Ord Fact where
  compare = comparing f
    where
    f :: Fact -> (Int, Addr, W256)
    f (CodeFact a _)      = (0, a, 0)
    f (BalanceFact a _)   = (1, a, 0)
    f (NonceFact a _)     = (2, a, 0)
    f (StorageFact a _ x) = (3, a, x)

-- Applies a set of facts to a VM.
apply :: VM s -> Set Fact -> VM s
apply =
  -- The set's ordering is relevant; see `apply1`.
  foldl' apply1
--
-- Applies a set of facts to a VM.
applyCache :: VM s -> Set Fact -> VM s
applyCache =
  -- The set's ordering is relevant; see `apply1`.
  foldl' apply2

factToFile :: Fact -> File
factToFile fact = case fact of
  StorageFact {..} -> mk ["storage"] (dump which) what
  BalanceFact {..} -> mk []          "balance"    what
  NonceFact   {..} -> mk []          "nonce"      val
  CodeFact    {..} -> mk []          "code"       blob
  where
    mk :: AsASCII a => [ASCII] -> ASCII -> a -> File
    mk prefix base a =
      File (Path (dump fact.addr : prefix) base)
           (Data $ dump a)

-- This lets us easier pattern match on serialized things.
-- Uses language extensions: `PatternSynonyms` and `ViewPatterns`.
pattern Load :: AsASCII a => a -> ASCII
pattern Load x <- (load -> Just x)

fileToFact :: File -> Maybe Fact
fileToFact = \case
  File (Path [Load a] "code")    (Data (Load x))
    -> Just (CodeFact a x)
  File (Path [Load a] "balance") (Data (Load x))
    -> Just (BalanceFact a x)
  File (Path [Load a] "nonce")   (Data (Load x))
    -> Just (NonceFact a x)
  File (Path [Load a, "storage"] (Load x)) (Data (Load y))
    -> Just (StorageFact a y x)
  _
    -> Nothing
