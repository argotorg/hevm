{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}
module EVM.Keccak (keccakAssumptions, concreteKeccaks, findKeccakPropsExprs) where

import Control.Monad.State
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List (tails)

import EVM.Traversals
import EVM.Types
import EVM.Expr


newtype KeccakStore = KeccakStore
  { keccakExprs :: Set (Expr EWord) }
  deriving (Show)

keccakFinder :: forall a. Expr a -> State KeccakStore ()
keccakFinder = \case
  e@(Keccak _) -> modify (\s -> s{keccakExprs=Set.insert e s.keccakExprs})
  _ -> pure ()

findKeccakExpr :: forall a. Expr a -> State KeccakStore ()
findKeccakExpr e = mapExprM_ keccakFinder e

findKeccakProp :: Prop -> State KeccakStore ()
findKeccakProp p = mapPropM_ keccakFinder p

findKeccakPropsExprs :: [Prop] -> [Expr Buf] -> [Expr Storage] -> Set (Expr EWord)
findKeccakPropsExprs ps bufs stores = (execState action (KeccakStore mempty)).keccakExprs
  where
    action = do
      mapM_ findKeccakProp ps
      mapM_ findKeccakExpr bufs
      mapM_ findKeccakExpr stores


uniquePairs :: [a] -> [(a,a)]
uniquePairs xs = [(x,y) | (x:ys) <- Data.List.tails xs, y <- ys]

injProp :: (Expr EWord, Expr EWord) -> Prop
injProp (k1@(Keccak b1), k2@(Keccak b2)) =
  PImpl (PEq k1 k2) ((b1 .== b2) .&& (bufLength b1 .== bufLength b2))
injProp _ = internalError "expected keccak expression"


-- Takes a list of props, find all keccak occurrences and generates two kinds of assumptions:
--   1. Output range: That the output of the invocation is greater than 256 and
--      at most 2^256 - 257, so that adding a field offset does not wrap (needed to
--      avoid spurious counterexamples due to storage collisions with solidity
--      mappings & value type storage slots)
--   2. Injectivity: That keccak is an injective function (we avoid quantifiers
--      here by making this claim for each unique pair of keccak invocations
--      discovered in the input expressions)
keccakAssumptions :: [Expr EWord] -> [Prop]
keccakAssumptions keccaks = injectivity <> minValue <> minDiffOfPairs
  where
    ks = map concretizeKeccakParam keccaks
    keccakPairs = uniquePairs ks
    injectivity = map injProp keccakPairs
    minValue = map minProp ks
      where
        minProp :: Expr EWord -> Prop
        minProp k@(Keccak _) = PAnd (PGT k (Lit 256)) (PLT k (Lit (maxBound - 255)))
        minProp _ = internalError "expected keccak expression"
    minDiffOfPairs = map minDistance keccakPairs
     where
      minDistance :: (Expr EWord, Expr EWord) -> Prop
      minDistance (ka@(Keccak a), kb@(Keccak b)) = PImpl ((a ./= b) .|| (bufLength a ./= bufLength b)) (PAnd req1 req2)
        where
          req1 = (PGEq (Sub ka kb) (Lit 256))
          req2 = (PGEq (Sub kb ka) (Lit 256))
      minDistance _ = internalError "expected Keccak expression"

concretizeKeccakParam :: Expr EWord -> Expr EWord
concretizeKeccakParam (Keccak buf) = Keccak (concKeccakSimpExpr buf)
concretizeKeccakParam _ = internalError "Cannot happen"


type KeccakValue = (Expr Buf, W256)
concreteKeccaks :: [Prop] -> Set KeccakValue
concreteKeccaks ps = direct <> recoverSlots (Set.filter (>= 256) slots) bigKeys direct
  where
  direct = foldMap concreteKeccakProp ps
  (slots, keys) = foldMap (foldProp literals mempty) ps
  bigKeys = Set.toList $ Set.filter (> 255) keys
  literals :: forall a. Expr a -> (Set W256, Set W256)
  literals = \case
    SLoad (Lit k) _ -> (Set.singleton k, mempty)
    SStore (Lit k) _ _ -> (Set.singleton k, mempty)
    ConcreteStore m -> (Map.keysSet m, Set.fromList (Map.elems m))
    Lit w -> (mempty, Set.singleton w)
    -- a hash written as the parent slot of a mapping or array is only bytes in the input
    Keccak buf -> (Set.fromList [w | off <- [0, 32], Lit w <- [readWord (Lit off) buf]], mempty)
    _ -> mempty

  concreteKeccakProp :: Prop -> Set KeccakValue
  concreteKeccakProp p = foldProp compute Set.empty p

  compute :: forall a. Expr a -> Set KeccakValue
  compute = \case
    Keccak buf -> do
      let b = concKeccakSimpExpr buf
      case b of
        buff@(ConcreteBuf bs) -> Set.singleton (buff, keccak' bs)
        _ -> Set.empty
    _ -> Set.empty

-- | Preimages of compiler-folded slots, which contain no keccak term. A slot recovered as
-- keccak(pre) + o, o < 256, has its parent slot (the last word of pre) recovered too, so that
-- symbolic hashes over the parent can be related to it. Parents beyond the shared tables are
-- known or recovered hashes plus a small offset, searched for a bounded number of levels.
recoverSlots :: Set W256 -> [W256] -> Set KeccakValue -> Set KeccakValue
recoverSlots targets0 bigKeys direct = go recoveryDepth table0 (Set.map snd direct) mempty mempty targets0
  where
    keys = [0..255] <> bigKeys
    table0 = smallPreimages <> mappingPreimages bigKeys [0..255]
      <> Map.fromList [(h, bs) | (ConcreteBuf bs, h) <- Set.toList direct]
    go :: Int -> Map.Map W256 ByteString -> Set W256 -> Set W256 -> Set W256 -> Set W256 -> Set KeccakValue
    go depth table bases expanded done targets
      | Set.null targets = mempty
      | otherwise = Set.fromList [(ConcreteBuf pre, h) | (_, h, pre) <- hits] <> rest
      where
        hits = [ (t, h, pre) | t <- Set.toList targets
               , Just (h, pre) <- [Map.lookupLE t table], t - h < 256 ]
        done' = done <> Set.fromList [t | (t, _, _) <- hits]
        parents = Set.fromList [p | (_, _, pre) <- hits, let p = word (BS.takeEnd 32 pre), p >= 256]
          `Set.difference` done'
        unresolved = targets `Set.difference` done'
        newBases = (bases <> Set.fromList [h | (_, h, _) <- hits]) `Set.difference` expanded
        derived = Set.toList newBases >>= \b -> map (b +) [0 .. derivedOffsets - 1]
        rest
          -- out of levels: only finish the parent chains of what was recovered
          | depth == 0 || Set.null newBases = go 0 table mempty expanded done' parents
          | otherwise = go (depth - 1)
              (table <> mappingPreimages keys derived <> arrayPreimages derived)
              mempty (expanded <> newBases) done' (unresolved <> parents)

recoveryDepth :: Int
recoveryDepth = 3

-- | Field offsets and array indices tried on top of hashes that become parent slots
derivedOffsets :: W256
derivedOffsets = 16

-- Shared across queries: mappings with small keys at small slots or held directly in an
-- array at a small slot, and arrays at small slots or held directly in such mappings
smallPreimages :: Map.Map W256 ByteString
smallPreimages = smallMapping <> smallArray
  <> arrayPreimages (Map.keys smallMapping) <> mappingPreimages [0..255] (Map.keys smallArray)
  where
    smallMapping = mappingPreimages [0..255] [0..255]
    smallArray = arrayPreimages [0..255]

mappingPreimages :: [W256] -> [W256] -> Map.Map W256 ByteString
mappingPreimages keys parents = Map.fromList
  [ (keccak' pre, pre)
  | key <- keys, parent <- parents
  , let pre = word256Bytes key <> word256Bytes parent
  ]

arrayPreimages :: [W256] -> Map.Map W256 ByteString
arrayPreimages parents = Map.fromList [(keccak' pre, pre) | parent <- parents, let pre = word256Bytes parent]
