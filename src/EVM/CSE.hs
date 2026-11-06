{- |
    Module: EVM.CSE
    Description: Common subexpression elimination for Expr ast
-}

module EVM.CSE (BufEnv, StoreEnv, eliminateExpr, eliminateProps, shareWords) where

import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as Map

import Control.Monad (forM_, unless, void, when)
import Data.IntMap.Strict (IntMap)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Text (Text)
import Data.Text qualified as T
import Data.IntMap.Strict qualified as IntMap
import Unsafe.Coerce (unsafeCoerce)

import EVM.HashCons (AnyExpr(..), hashConsExpr, nodeId)
import EVM.Traversals.Children (mapChildrenM, mapPropChildrenM)
import EVM.Types

-- maps expressions to variable names
data BuilderState = BuilderState
  { bufs :: Map (Expr Buf) Int
  , stores :: Map (Expr Storage) Int
  , count :: Int
  -- | the result of each canonical node already visited: a later visit finds the same names
  , memo :: IntMap AnyExpr
  }

type BufEnv = Map Int (Expr Buf)
type StoreEnv = Map Int (Expr Storage)

initState :: BuilderState
initState = BuilderState
  { bufs = mempty
  , stores = mempty
  , count = 0
  , memo = mempty
  }


go :: Expr a -> State BuilderState (Expr a)
go = \case
  -- buffers
  e@(WriteWord {}) -> do
    s <- get
    case Map.lookup e s.bufs of
      Just v -> pure $ GVar (BufVar v)
      Nothing -> do
        let
          next = s.count
          bs' = Map.insert e next s.bufs
        put $ s{bufs=bs', count=next+1}
        pure $ GVar (BufVar next)
  e@(WriteByte {}) -> do
    s <- get
    case Map.lookup e s.bufs of
      Just v -> pure $ GVar (BufVar v)
      Nothing -> do
        let
          next = s.count
          bs' = Map.insert e next s.bufs
        put $ s{bufs=bs', count=next+1}
        pure $ GVar (BufVar next)
  e@(CopySlice {}) -> do
    s <- get
    case Map.lookup e s.bufs of
      Just v -> pure $ GVar (BufVar v)
      Nothing -> do
        let
          next = s.count
          bs' = Map.insert e next s.bufs
        put $ s{count=next+1, bufs=bs'}
        pure $ GVar (BufVar next)
  -- storage
  e@(SStore {}) -> do
    s <- get
    case Map.lookup e s.stores of
      Just v -> pure $ GVar (StoreVar v)
      Nothing -> do
        let
          next = s.count
          ss' = Map.insert e next s.stores
        put $ s{count=next+1, stores=ss'}
        pure $ GVar (StoreVar next)
  e -> pure e

invertKeyVal :: forall a. Map a Int -> Map Int a
invertKeyVal =  Map.fromList . map (\(x, y) -> (y, x)) . Map.toList

-- | Common subexpression elimination pass for Expr
eliminateExpr' :: Expr a -> State BuilderState (Expr a)
eliminateExpr' = cse

-- | 'mapExprM' of 'go' visiting each shared node once, as walking a hash-consed DAG
-- as a tree is exponential in the depth of its sharing
cse :: Expr a -> State BuilderState (Expr a)
cse e = case nodeId e of
  Nothing -> step
  Just i -> gets (IntMap.lookup i . (.memo)) >>= \case
    -- equal ids are the same node, so of the same type
    Just (AnyExpr r) -> pure (unsafeCoerce r)
    Nothing -> do
      r <- step
      modify' (\s -> s { memo = IntMap.insert i (AnyExpr r) s.memo })
      pure r
  where
    -- hash-consed, so that 'shareWords' finds the rebuilt nodes by id too
    step = case e of
      C {} -> mapChildrenM cse e
      _ -> hashConsExpr <$> (mapChildrenM cse e >>= go)

eliminateExpr :: Expr a -> (Expr a, BufEnv, StoreEnv)
eliminateExpr e =
  let (e', st) = runState (eliminateExpr' e) initState in
  (e', invertKeyVal st.bufs, invertKeyVal st.stores)

-- | Common subexpression elimination pass for Prop
eliminateProp' :: Prop -> State BuilderState Prop
eliminateProp' = mapPropChildrenM cse

-- | Common subexpression elimination pass for list of Prop
eliminateProps' :: [Prop] -> State BuilderState [Prop]
eliminateProps' props = mapM eliminateProp' props


-- | Common subexpression elimination pass for list of Prop
eliminateProps :: [Prop] -> ([Prop], BufEnv, StoreEnv)
eliminateProps props =
  let (props', st) = runState (eliminateProps' props) initState in
  (props',  invertKeyVal st.bufs,  invertKeyVal st.stores)

-- | Names each word node that the props use more than once, so that encoding them writes
-- the name instead of repeating the term: as text, a shared term is as large as its tree.
-- Returns the props with those nodes replaced by variables, and the variables'
-- definitions, each after the ones it uses.
shareWords :: [Prop] -> ([Prop], [(Text, Expr EWord)])
shareWords ps = (ps', reverse st.defs)
  where
    uses = snd $ execState (mapM_ (mapPropChildrenM countUses) ps) (IntSet.empty, IntMap.empty)
    (ps', st) = runState (mapM (mapPropChildrenM share) ps) (ShareState mempty [] 0)

    countUses :: Expr a -> State (IntSet, IntMap Int) (Expr a)
    countUses e = do
      when (isComposite e) $ forM_ (nodeId e) $ \i -> modify' (fmap (IntMap.insertWith (+) i 1))
      case nodeId e of
        Just i -> do
          seen <- gets (IntSet.member i . fst)
          unless seen $ do
            modify' (\(s, m) -> (IntSet.insert i s, m))
            void (mapChildrenM countUses e)
        Nothing -> void (mapChildrenM countUses e)
      pure e

    share :: Expr a -> State ShareState (Expr a)
    share e = case nodeId e of
      Nothing -> mapChildrenM share e
      Just i -> gets (IntMap.lookup i . (.done)) >>= \case
        Just (AnyExpr r) -> pure (unsafeCoerce r)
        Nothing -> do
          r0 <- mapChildrenM share e
          r <- case exprType e of
            WordRep | isComposite e, IntMap.findWithDefault 0 i uses > 1 -> do
              n <- gets (.next)
              let name = "shared_word_" <> T.pack (show n)
              modify' (\s -> s { next = n + 1, defs = (name, r0) : s.defs })
              pure (Var name)
            _ -> pure r0
          modify' (\s -> s { done = IntMap.insert i (AnyExpr r) s.done })
          pure r

    isComposite :: Expr a -> Bool
    isComposite e = case exprType e of
      WordRep -> case e of
        Lit _ -> False
        Var _ -> False
        _ -> True
      _ -> False

data ShareState = ShareState
  { done :: IntMap AnyExpr
  , defs :: [(Text, Expr EWord)]
  , next :: Int
  }
