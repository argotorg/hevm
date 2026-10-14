{- |
    Module: EVM.Traversals
    Description: Generic traversal functions for Expr datatypes
-}
module EVM.Traversals where

import Prelude hiding (LT, GT)

import Control.Monad (void)
import Control.Monad.Identity (Identity(Identity), runIdentity)
import Data.Functor.Const (Const(..))
import GHC.StaticPtr (StaticPtr, deRefStaticPtr)

import EVM.Types
import EVM.HashCons (Rewrite, runRewrite, hashConsExpr, memoFixTraverse, hashConsEnabled)
import EVM.Traversals.Children

foldProp :: forall b . Monoid b => (forall a . Expr a -> b) -> b -> Prop -> b
foldProp f acc p = acc <> getConst (mapPropChildrenM (Const . foldExpr f mempty) p)

-- | Recursively folds a given function over a given expression, visiting the same terms as
-- 'mapExprM' in the same order
foldExpr :: forall b c . Monoid b => (forall a . Expr a -> b) -> b -> Expr c -> b
foldExpr f acc expr = acc <> go expr
  where
    go :: forall a . Expr a -> b
    go e = self <> getConst (mapChildrenM (Const . go) e)
      where self = case e of { C {} -> mempty; _ -> f e }

mapProp :: (forall a . Expr a -> Expr a) -> Prop -> Prop
mapProp f = \case
  PBool b -> PBool b
  PEq a b -> PEq (mapExpr f (f a)) (mapExpr f (f b))
  PLT a b -> PLT (mapExpr f (f a)) (mapExpr f (f b))
  PGT a b -> PGT (mapExpr f (f a)) (mapExpr f (f b))
  PLEq a b -> PLEq (mapExpr f (f a)) (mapExpr f (f b))
  PGEq a b -> PGEq (mapExpr f (f a)) (mapExpr f (f b))
  PNeg a -> PNeg (mapProp f a)
  PAnd a b -> PAnd (mapProp f a) (mapProp f b)
  POr a b -> POr (mapProp f a) (mapProp f b)
  PImpl a b -> PImpl (mapProp f a) (mapProp f b)

mapProp' :: (Prop -> Prop) -> Prop -> Prop
mapProp' f = \case
  PBool b -> f $ PBool b
  PEq a b -> f $ PEq a b
  PLT a b -> f $ PLT a b
  PGT a b -> f $ PGT a b
  PLEq a b -> f $ PLEq a b
  PGEq a b -> f $ PGEq a b
  PNeg a -> f $ PNeg (mapProp' f a)
  PAnd a b -> f $ PAnd (mapProp' f a) (mapProp' f b)
  POr a b -> f $ POr (mapProp' f a) (mapProp' f b)
  PImpl a b -> f $ PImpl (mapProp' f a) (mapProp' f b)


mapPropM' :: forall m . (Monad m) => (Prop -> m Prop) -> Prop -> m Prop
mapPropM' f = \case
  PBool b -> f $ PBool b
  PEq a b -> f $ PEq a b
  PLT a b -> f $ PLT a b
  PGT a b -> f $ PGT a b
  PLEq a b -> f $ PLEq a b
  PGEq a b -> f $ PGEq a b
  PNeg a -> do
    x <- mapPropM' f a
    f $ PNeg x
  PAnd a b -> do
    x <- mapPropM' f a
    y <- mapPropM' f b
    f $ PAnd x y
  POr a b -> do
    x <- mapPropM' f a
    y <- mapPropM' f b
    f $ POr x y
  PImpl a b -> do
    x <- mapPropM' f a
    y <- mapPropM' f b
    f $ PImpl x y

-- | hashConsExpr shares each rebuilt node as it is produced (bottom-up, O(1) per node since children
-- are already canonical), so passes built on mapExpr (notably Expr.simplify) never materialize the
-- unshared exponential tree. It is a no-op unless hash-consing is enabled (EVM.HashCons).
mapExpr :: (forall a . Expr a -> Expr a) -> Expr b -> Expr b
mapExpr f expr = runIdentity (mapExprM (Identity . hashConsExpr . f) expr)

-- | Like 'mapExpr', for the repeatedly-applied simplification passes: when hash-consing is
-- enabled, each distinct subterm is visited once and subterms already known to be fixpoints of
-- this pass are skipped in O(1). Falls back to plain mapExpr otherwise.
mapExprShared :: StaticPtr Rewrite -> Expr b -> Expr b
mapExprShared pass expr
  | hashConsEnabled expr = memoFixTraverse pass expr
  | otherwise = runIdentity (mapExprM (Identity . runRewrite (deRefStaticPtr pass)) expr)


-- Like mapExprM but allows a function of type `Expr a -> m ()` to be passed
mapExprM_ ::  Monad m => (forall a . Expr a -> m ()) -> Expr b -> m ()
mapExprM_ f expr = void ret
  where
    ret = mapExprM (fUpd f) expr
    fUpd :: Monad m => (Expr a -> m ()) -> (Expr a -> m (Expr a))
    fUpd action e = do
      action e
      pure e

mapExprM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Expr b -> m (Expr b)
mapExprM f expr = case expr of
  -- f is not applied to a contract itself
  C {} -> mapChildrenM (mapExprM f) expr
  _ -> mapChildrenM (mapExprM f) expr >>= f

-- Like mapPropM but allows a function of type `Expr a -> m ()` to be passed
mapPropM_ :: Monad m => (forall a . Expr a -> m ()) -> Prop -> m ()
mapPropM_ f expr = void ret
  where
    ret = mapPropM (fUpd f) expr
    fUpd :: Monad m => (Expr a -> m ()) -> (Expr a-> m (Expr a))
    fUpd action e = do
      action e
      pure e

mapPropM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Prop -> m Prop
mapPropM f = mapPropChildrenM (mapExprM f)

mapEContractM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Expr EContract -> m (Expr EContract)
mapEContractM _ g@(GVar _) = pure g
mapEContractM f c = mapChildrenM (mapExprM f) c

mapContractM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Contract -> m (Contract)
mapContractM f c = do
  code' <- mapCodeM f c.code
  storage' <- mapExprM f c.storage
  origStorage' <- mapExprM f c.origStorage
  balance' <- mapExprM f c.balance
  pure $ c { code = code', storage = storage', origStorage = origStorage', balance = balance' }

mapCodeM :: Monad m => (forall a . Expr a -> m (Expr a)) -> ContractCode -> m (ContractCode)
mapCodeM f = mapCodeChildrenM (mapExprM f)

-- | Generic operations over AST terms
class TraversableTerm a where
  mapTerm  :: (forall b. Expr b -> Expr b) -> a -> a
  foldTerm :: forall c. Monoid c => (forall b. Expr b -> c) -> c -> a -> c

instance TraversableTerm (Expr a) where
  mapTerm = mapExpr
  foldTerm = foldExpr

instance TraversableTerm Prop where
  mapTerm = mapProp
  foldTerm = foldProp
