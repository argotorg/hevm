{- |
    Module: EVM.Keccak.Preimages
    Description: Keccak preimages of Solidity storage slots, and the keccak range hevm assumes

    hevm assumes that keccak is injective, that its results lie in [keccakMin, keccakMax], and
    that results of distinct inputs are at least fieldOffsetWindow apart. Under these
    assumptions a literal slot h + o, o < fieldOffsetWindow, has the preimage of h. Slots
    folded by the compiler hide all their intermediate hashes; 'recoverSlots' finds them for
    mappings with keys below 256 or given, at slots below 256, arrays at such slots, and either
    held directly in the other, and further levels whose parent is a known hash plus an offset
    below 'derivedOffsets'.
-}
module EVM.Keccak.Preimages
  ( Preimage(..)
  , toBytes
  , fromBytes
  , parentSlot
  , Table
  , fromRecorded
  , lookupSlot
  , smallArrays
  , recoverSlots
  , keccakMin
  , keccakMax
  , fieldOffsetWindow
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import EVM.Types

data Preimage
  = MappingPre W256 W256 -- ^ key, parent slot
  | ArrayPre W256        -- ^ parent slot
  | RawPre ByteString
  deriving (Show, Eq, Ord)

toBytes :: Preimage -> ByteString
toBytes = \case
  MappingPre key parent -> word256Bytes key <> word256Bytes parent
  ArrayPre parent -> word256Bytes parent
  RawPre bs -> bs

fromBytes :: ByteString -> Preimage
fromBytes bs = case BS.length bs of
  64 -> MappingPre (word (BS.take 32 bs)) (word (BS.drop 32 bs))
  32 -> ArrayPre (word bs)
  _ -> RawPre bs

parentSlot :: Preimage -> Maybe W256
parentSlot = \case
  MappingPre _ parent -> Just parent
  ArrayPre parent -> Just parent
  RawPre _ -> Nothing

-- | Hash to preimage
type Table = Map.Map W256 Preimage

fromRecorded :: Set (ByteString, W256) -> Table
fromRecorded s = Map.fromList [(h, fromBytes bs) | (bs, h) <- Set.toList s]

-- | The preimage, hash and offset of a slot that is a hash in the table plus a field offset
lookupSlot :: Table -> W256 -> Maybe (Preimage, W256, W256)
lookupSlot table slot = case Map.lookupLE slot table of
  Just (h, pre) | slot - h < fieldOffsetWindow -> Just (pre, h, slot - h)
  _ -> Nothing

keccakMin :: W256
keccakMin = 257

-- | So that adding a field offset does not wrap around to a small slot
keccakMax :: W256
keccakMax = maxBound - 256

fieldOffsetWindow :: W256
fieldOffsetWindow = 256

recoveryDepth :: Int
recoveryDepth = 3

-- | Field offsets and array indices tried on top of hashes that become parent slots
derivedOffsets :: W256
derivedOffsets = 16

-- | Preimages of the slots in targets, and of their parent slots. bigKeys are mapping keys
-- above 255 that occur in the query, known the hashes whose preimages it contains.
recoverSlots :: Set W256 -> [W256] -> Table -> Set (Preimage, W256)
recoverSlots targets0 bigKeys known = go recoveryDepth table0 (Map.keysSet known) mempty mempty targets0
  where
    keys = [0..255] <> bigKeys
    table0 = smallPreimages <> mappingTable bigKeys [0..255] <> known
    go :: Int -> Table -> Set W256 -> Set W256 -> Set W256 -> Set W256 -> Set (Preimage, W256)
    go depth table bases expanded done targets
      | Set.null targets = mempty
      | otherwise = Set.fromList [(pre, h) | (_, pre, h) <- hits] <> rest
      where
        hits = [(t, pre, h) | t <- Set.toList targets, Just (pre, h, _) <- [lookupSlot table t]]
        done' = done <> Set.fromList [t | (t, _, _) <- hits]
        parents = Set.fromList (filter (>= 256) (mapMaybe (\(_, pre, _) -> parentSlot pre) hits))
          `Set.difference` done'
        unresolved = targets `Set.difference` done'
        newBases = (bases <> Set.fromList [h | (_, _, h) <- hits]) `Set.difference` expanded
        derived = Set.toList newBases >>= \b -> map (b +) [0 .. derivedOffsets - 1]
        rest
          -- out of levels: only finish the parent chains of what was recovered
          | depth == 0 || Set.null newBases = go 0 table mempty expanded done' parents
          | otherwise = go (depth - 1)
              (table <> mappingTable keys derived <> arrayTable derived)
              mempty (expanded <> newBases) done' (unresolved <> parents)

-- | Arrays at slots below 256
smallArrays :: Table
smallArrays = arrayTable [0..255]

-- Shared across queries: mappings with small keys at small slots or held directly in an
-- array at a small slot, and arrays at small slots or held directly in such mappings
smallPreimages :: Table
smallPreimages = smallMappings <> smallArrays
  <> arrayTable (Map.keys smallMappings) <> mappingTable [0..255] (Map.keys smallArrays)
  where smallMappings = mappingTable [0..255] [0..255]

mappingTable :: [W256] -> [W256] -> Table
mappingTable keys parents = Map.fromList
  [(keccak' (toBytes pre), pre) | key <- keys, parent <- parents, let pre = MappingPre key parent]

arrayTable :: [W256] -> Table
arrayTable parents = Map.fromList [(keccak' (toBytes pre), pre) | parent <- parents, let pre = ArrayPre parent]
