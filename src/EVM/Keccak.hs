{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}
module EVM.Keccak (keccakAssumptions, concreteKeccaks, findKeccakPropsExprs) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.List (tails)

import EVM.Traversals
import EVM.Types
import EVM.Expr


findKeccakPropsExprs :: [Prop] -> [Expr Buf] -> [Expr Storage] -> Set (Expr EWord)
findKeccakPropsExprs ps bufs stores =
  collectExprs keccakOf (concatMap propExprs ps <> map AnyExpr bufs <> map AnyExpr stores)
  where
    keccakOf :: Expr a -> Set (Expr EWord)
    keccakOf e@(Keccak _) = Set.singleton e
    keccakOf _ = mempty


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
concreteKeccaks ps = collectExprs compute (concatMap propExprs ps)
  where
  compute :: forall a. Expr a -> Set KeccakValue
  compute = \case
    Keccak buf -> do
      let b = concKeccakSimpExpr buf
      case b of
        buff@(ConcreteBuf bs) -> Set.singleton (buff, keccak' bs)
        _ -> Set.empty
    _ -> Set.empty
