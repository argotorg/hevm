{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}
module EVM.Keccak (keccakAssumptions, concreteKeccaks, findKeccakPropsExprs) where

import Control.Monad.State
import Data.ByteString (ByteString)
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
--   1. Minimum output value: That the output of the invocation is greater than
--      256 (needed to avoid spurious counterexamples due to storage collisions
--      with solidity mappings & value type storage slots)
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
        minProp k@(Keccak _) = PGT k (Lit 256)
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
concreteKeccaks ps = foldMap concreteKeccakProp ps <> recovered
  where
  (slots, keys) = foldMap (foldProp literals mempty) ps
  preimages = smallMappingPreimages <> mappingPreimages (Set.toList $ Set.filter (> 255) keys)
  recovered = Set.fromList
    [ (ConcreteBuf pre, h)
    | slot <- Set.toList (Set.filter (>= 256) slots)
    , Just (h, pre) <- [Map.lookupLE slot preimages]
    , slot - h < 256
    ]
  literals :: forall a. Expr a -> (Set W256, Set W256)
  literals = \case
    SLoad (Lit k) _ -> (Set.singleton k, mempty)
    SStore (Lit k) _ _ -> (Set.singleton k, mempty)
    ConcreteStore m -> (Map.keysSet m, Set.fromList (Map.elems m))
    Lit w -> (mempty, Set.singleton w)
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

-- Shared across queries; compiler-folded mapping slots contain no keccak term.
smallMappingPreimages :: Map.Map W256 ByteString
smallMappingPreimages = mappingPreimages [0..255]

mappingPreimages :: [W256] -> Map.Map W256 ByteString
mappingPreimages keys = Map.fromList
  [ (keccak' pre, pre)
  | key <- keys, slot <- [0..255]
  , let pre = word256Bytes key <> word256Bytes slot
  ]
