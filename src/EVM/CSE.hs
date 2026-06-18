{- |
    Module: EVM.CSE
    Description: Common subexpression elimination for Expr ast
-}

module EVM.CSE (BufEnv, StoreEnv, eliminateExpr, eliminateProps) where

import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as Map

import EVM.Traversals
import EVM.Types

-- maps expressions to variable names
data BuilderState = BuilderState
  { bufs :: Map (Expr Buf) Int
  , stores :: Map (Expr Storage) Int
  , count :: Int
  }
  deriving (Show)

type BufEnv = Map Int (Expr Buf)
type StoreEnv = Map Int (Expr Storage)

initState :: BuilderState
initState = BuilderState
  { bufs = mempty
  , stores = mempty
  , count = 0
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
  e@(StorageCopySlice {}) -> do
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
eliminateExpr' e = mapExprM go e

eliminateExpr :: Expr a -> (Expr a, BufEnv, StoreEnv)
eliminateExpr e =
  let (e', st) = runState (eliminateExpr' e) initState in
  (e', invertKeyVal st.bufs, invertKeyVal st.stores)

-- | Common subexpression elimination pass for Prop
eliminateProp' :: Prop -> State BuilderState Prop
eliminateProp' prop = mapPropM go prop

-- | Common subexpression elimination pass for list of Prop
eliminateProps' :: [Prop] -> State BuilderState [Prop]
eliminateProps' props = mapM eliminateProp' props


-- | Common subexpression elimination pass for list of Prop
eliminateProps :: [Prop] -> ([Prop], BufEnv, StoreEnv)
eliminateProps props =
  let (props', st) = runState (eliminateProps' props) initState in
  (props',  invertKeyVal st.bufs,  invertKeyVal st.stores)
