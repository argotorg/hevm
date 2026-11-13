{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}
module EVM.Keccak (keccakAssumptions, concreteKeccaks, concreteKeccakValues, findKeccakPropsExprs) where

import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List (partition, tails)
import Witch (unsafeInto)

import EVM.Traversals
import EVM.Types
import EVM.Expr
import EVM.Keccak.Preimages


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

injProp :: Map.Map Int (Expr Buf) -> (Expr EWord, Expr EWord) -> Prop
injProp env (k1@(Keccak b1), k2@(Keccak b2)) = PImpl (PEq k1 k2) (sameInput env b1 b2)
injProp _ _ = internalError "expected keccak expression"

-- | The solver's arrays may differ past the hashed length, where keccak doesn't
-- look, so with a concrete length compare only the bytes it hashes, and assert
-- congruence: comparing whole arrays gives two hashes for one input.
sameInput :: Map.Map Int (Expr Buf) -> Expr Buf -> Expr Buf -> Prop
sameInput env a b = case (resolvedLength a, resolvedLength b) of
  (Lit la, Lit lb) | la /= lb -> PBool False
  (Lit n, lb) | n <= maxComparedLen -> lb .== Lit n .&& bytesEq n
  (la, Lit n) | n <= maxComparedLen -> la .== Lit n .&& bytesEq n
  (la, lb) -> (a .== b) .&& (la .== lb)
  where
    bytesEq 0 = PBool True
    bytesEq n = foldr1 (.&&) [chunk n i a .== chunk n i b | i <- [0, 32 .. n - 1]]
    chunk n o = readBytes (unsafeInto (Prelude.min 32 (n - o))) (Lit o)
    maxComparedLen = 1024
    -- the buffers are often variables, whose definitions have concrete lengths
    resolvedLength = bufLength . resolve
    resolve :: Expr Buf -> Expr Buf
    resolve = mapExpr (\case
      GVar (BufVar n) | Just def <- Map.lookup n env -> resolve def
      e -> e)

congruenceProp :: Map.Map Int (Expr Buf) -> (Expr EWord, Expr EWord) -> Prop
congruenceProp env (k1@(Keccak b1), k2@(Keccak b2)) = PImpl (sameInput env b1 b2) (PEq k1 k2)
congruenceProp _ _ = internalError "expected keccak expression"


-- Takes a list of props, find all keccak occurrences and generates two kinds of assumptions:
--   1. Output range: That the output of the invocation is in [keccakMin, keccakMax]
--      (needed to avoid spurious counterexamples due to storage collisions with
--      solidity mappings & value type storage slots)
--   2. Injectivity: That keccak is an injective function (we avoid quantifiers
--      here by making this claim for each unique pair of keccak invocations
--      discovered in the input expressions)
keccakAssumptions :: Map.Map Int (Expr Buf) -> [Expr EWord] -> [Prop]
keccakAssumptions env keccaks = injectivity <> congruence <> minValue <> minDiffOfPairs
  where
    -- Concrete hash values are asserted separately by the SMT encoder.
    (concrete, symbolic) = partition isConcrete (map concretizeKeccakParam keccaks)
    isConcrete (Keccak (ConcreteBuf _)) = True
    isConcrete _ = False
    keccakPairs = uniquePairs symbolic <> [(s, c) | s <- symbolic, c <- concrete]
    injectivity = map (injProp env) keccakPairs
    congruence = map (congruenceProp env) keccakPairs
    minValue = map minProp symbolic
      where
        minProp :: Expr EWord -> Prop
        minProp k@(Keccak _) = PAnd (PGEq k (Lit keccakMin)) (PLEq k (Lit keccakMax))
        minProp _ = internalError "expected keccak expression"
    minDiffOfPairs = map minDistance keccakPairs
     where
      minDistance :: (Expr EWord, Expr EWord) -> Prop
      minDistance (ka@(Keccak a), kb@(Keccak b)) = PImpl (PNeg (sameInput env a b)) (PAnd req1 req2)
        where
          req1 = (PGEq (Sub ka kb) (Lit fieldOffsetWindow))
          req2 = (PGEq (Sub kb ka) (Lit fieldOffsetWindow))
      minDistance _ = internalError "expected Keccak expression"

concretizeKeccakParam :: Expr EWord -> Expr EWord
concretizeKeccakParam (Keccak buf) = Keccak (concKeccakSimpExpr buf)
concretizeKeccakParam _ = internalError "Cannot happen"


type KeccakValue = (Expr Buf, W256)
concreteKeccaks :: [Prop] -> Set KeccakValue
concreteKeccaks ps = direct <> Set.map (\(pre, h) -> (ConcreteBuf (toBytes pre), h)) recovered
  where
  direct = foldMap concreteKeccakValues ps
  known = Map.fromList [(h, fromBytes bs) | (ConcreteBuf bs, h) <- Set.toList direct]
  recovered = recoverSlots (Set.filter (>= 256) slots) bigKeys known
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

-- | Concrete hashes present in a term, without recovering preimages of literals.
concreteKeccakValues :: TraversableTerm a => a -> Set KeccakValue
concreteKeccakValues = foldTerm compute Set.empty
  where
  compute :: forall a. Expr a -> Set KeccakValue
  compute = \case
    Keccak buf -> do
      let b = concKeccakSimpExpr buf
      case b of
        buff@(ConcreteBuf bs) -> Set.singleton (buff, keccak' bs)
        _ -> Set.empty
    _ -> Set.empty
