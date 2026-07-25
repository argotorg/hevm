{- |
    Module: EVM.Traversals
    Description: Generic traversal functions for Expr datatypes
-}
module EVM.Traversals where

import Prelude hiding (LT, GT, Foldable(..))

import Control.Monad (forM, void)
import Control.Monad.Identity (Identity(Identity), runIdentity)
import Data.Foldable (Foldable(..))
import Data.Map.Strict qualified as Map
import System.IO.Unsafe (unsafePerformIO)

import EVM.Types

foldProp :: forall b . Monoid b => (forall a . Expr a -> b) -> b -> Prop -> b
foldProp f acc p = acc <> (go p)
  where
    go :: Prop -> b
    go = \case
      PBool _ -> mempty
      PEq a b -> (foldExpr f mempty a) <> (foldExpr f mempty b)
      PLT a b -> foldExpr f mempty a <> foldExpr f mempty b
      PGT a b -> foldExpr f mempty a <> foldExpr f mempty b
      PGEq a b -> foldExpr f mempty a <> foldExpr f mempty b
      PLEq a b -> foldExpr f mempty a <> foldExpr f mempty b
      PNeg a -> go a
      PAnd a b -> go a <> go b
      POr a b -> go a <> go b
      PImpl a b -> go a <> go b

foldEContract :: forall b . Monoid b => (forall a . Expr a -> b) -> b -> Expr EContract -> b
foldEContract f _ g@(GVar _) = f g
foldEContract f acc (C code storage tStorage balance _)
  =  acc
  <> foldCode f code
  <> foldExpr f mempty storage
  <> foldExpr f mempty tStorage
  <> foldExpr f mempty balance

foldCode :: forall b . Monoid b => (forall a . Expr a -> b) -> ContractCode -> b
foldCode f = \case
  RuntimeCode (ConcreteRuntimeCode _) -> mempty
  RuntimeCode (SymbolicRuntimeCode c) -> foldl' (foldExpr f) mempty c
  InitCode _ buf -> foldExpr f mempty buf
  UnknownCode addr -> foldExpr f mempty addr

-- | Recursively folds a given function over a given expression
-- Recursion schemes do this & a lot more, but defining them over GADT's isn't worth the hassle
-- | Fold f over every Expr node reachable from the given term.
--
-- The generic case is @f e <> children@, which 'hfoldMap' produces in constructor declaration
-- order -- the same order the previous ~150-line hand-written version used. Only constructors
-- reaching into non-child payloads are spelled out, with behaviour identical to before: C nodes
-- go to foldEContract (which re-includes acc and never applies f to the C node itself), and a
-- Failure carrying a Revert descends into the reverted buffer.
foldExpr :: forall b c . Monoid b => (forall a . Expr a -> b) -> b -> Expr c -> b
foldExpr f acc expr = acc <> (go expr)
  where
    go :: forall a . Expr a -> b
    go e = case e.node of
      CF {} -> foldEContract f acc e
      SuccessF a _ c d -> f e
                       <> foldl' (foldProp f) mempty a
                       <> go c
                       <> foldl' (foldExpr f) mempty (Map.keys d)
                       <> foldl' (foldEContract f) mempty d
      FailureF a _ (Revert c) -> f e <> (foldl' (foldProp f) mempty a) <> go c
      FailureF a _ _ -> f e <> (foldl' (foldProp f) mempty a)
      PartialF a _ _ -> f e <> (foldl' (foldProp f) mempty a)
      n -> f e <> hfoldMap go n

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

-- | Apply f at every Expr node, bottom-up.
--
-- Interning happens inside the Expr pattern synonyms now, so every node this rebuilds is shared
-- automatically; there is no separate internExpr step.
mapExpr :: (forall a . Expr a -> Expr a) -> Expr b -> Expr b
mapExpr f expr = runIdentity (mapExprM (Identity . f) expr)

-- | Like 'mapExpr', for repeatedly-applied simplification passes: when hash-consing is enabled
-- each distinct subterm is visited once per pass (identified by slot), so the cost is O(distinct
-- nodes) rather than O(logical size). Falls back to plain mapExpr otherwise.
mapExprShared :: Int -> (forall a . Expr a -> Expr a) -> Expr b -> Expr b
mapExprShared slot f expr
  | hashConsEnabled expr = memoFixTraverse slot f expr
  | otherwise = mapExpr f expr

-- Like mapExprM but allows a function of type `Expr a -> m ()` to be passed
mapExprM_ ::  Monad m => (forall a . Expr a -> m ()) -> Expr b -> m ()
mapExprM_ f expr = void ret
  where
    ret = mapExprM (fUpd f) expr
    fUpd :: Monad m => (Expr a -> m ()) -> (Expr a -> m (Expr a))
    fUpd action e = do
      action e
      pure e

-- | The one structural map, with the recursive call left open so a caller can wrap it.
-- 'mapExprM' ties the knot directly; 'memoFixTraverse' ties it through a memo table. This is
-- what used to be ~320 lines re-listing all 72 constructors, plus a second 200-line copy of the
-- same thing in EVM.HashCons.
--
-- Only constructors whose payloads are not children need spelling out. Their behaviour is
-- deliberately identical to the previous version, quirks included: no f is applied at a C node;
-- Success's map keys get f directly rather than recursively; and, unlike foldExpr, a Failure's
-- Revert buffer is not descended into.
mapExprMWith
  :: forall m . Monad m
  => (forall y . Expr y -> m (Expr y))   -- ^ how to recurse into a child
  -> (forall y . Expr y -> m (Expr y))   -- ^ what to apply at this node
  -> (forall x . Expr x -> m (Expr x))
mapExprMWith rec f = step
  where
    step :: forall x . Expr x -> m (Expr x)
    step e = case e.node of
      CF {} -> mapEContractMWith rec f e
      PartialF a b c -> do
        a' <- mapM (mapPropMWith rec) a
        f (remake e (PartialF a' b c))
      FailureF a b c -> do
        a' <- mapM (mapPropMWith rec) a
        f (remake e (FailureF a' b c))
      SuccessF a b c d -> do
        a' <- mapM (mapPropMWith rec) a
        c' <- rec c
        d' <- fmap Map.fromList $ forM (Map.toList d) $ \(k, v) -> do
                k' <- f k
                v' <- mapEContractMWith rec f v
                pure (k', v')
        f (remake e (SuccessF a' b c' d'))
      n -> do
        n' <- htraverse rec n
        f (remake e n')

mapExprM :: forall m b . Monad m => (forall a . Expr a -> m (Expr a)) -> Expr b -> m (Expr b)
mapExprM f = go
  where
    go :: forall x . Expr x -> m (Expr x)
    go = mapExprMWith go f

-- | Memoized structural map for a repeatedly-applied simplification pass.
--
-- Identical to 'mapExpr' except that results are cached per (pass slot, node id), so a shared
-- DAG is not re-walked as a tree. Sound for an f that is a pure function of node structure,
-- which every simplifier pass is. Nodes with @ident == 0@ (built while hash-consing was off)
-- have no cache key and are simply recomputed.
memoFixTraverse :: forall b . Int -> (forall x . Expr x -> Expr x) -> Expr b -> Expr b
memoFixTraverse slot f root = unsafePerformIO (go root)
  where
    go :: forall x . Expr x -> IO (Expr x)
    go e
      | e.ident == 0 = step e
      | otherwise = do
          hit <- lookupMemo slot e
          case hit of
            Just r -> pure r
            Nothing -> do
              r <- step e
              insertMemo slot e r
              pure r

    step :: forall x . Expr x -> IO (Expr x)
    step = mapExprMWith go applyF

    -- forced before it is stored: an unevaluated thunk in the memo would defeat the point
    applyF :: forall x . Expr x -> IO (Expr x)
    applyF x = let !r = f x in pure r
{-# NOINLINE memoFixTraverse #-}

-- Like mapPropM but allows a function of type `Expr a -> m ()` to be passed
mapPropM_ :: Monad m => (forall a . Expr a -> m ()) -> Prop -> m ()
mapPropM_ f expr = void ret
  where
    ret = mapPropM (fUpd f) expr
    fUpd :: Monad m => (Expr a -> m ()) -> (Expr a-> m (Expr a))
    fUpd action e = do
      action e
      pure e

mapPropMWith :: forall m . Monad m => (forall a . Expr a -> m (Expr a)) -> Prop -> m Prop
mapPropMWith rec = \case
  PBool b -> pure $ PBool b
  PEq a b -> PEq <$> rec a <*> rec b
  PLT a b -> PLT <$> rec a <*> rec b
  PGT a b -> PGT <$> rec a <*> rec b
  PLEq a b -> PLEq <$> rec a <*> rec b
  PGEq a b -> PGEq <$> rec a <*> rec b
  PNeg a -> PNeg <$> mapPropMWith rec a
  PAnd a b -> PAnd <$> mapPropMWith rec a <*> mapPropMWith rec b
  POr a b -> POr <$> mapPropMWith rec a <*> mapPropMWith rec b
  PImpl a b -> PImpl <$> mapPropMWith rec a <*> mapPropMWith rec b

mapPropM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Prop -> m Prop
mapPropM f = mapPropMWith (mapExprM f)

mapEContractMWith
  :: forall m . Monad m
  => (forall a . Expr a -> m (Expr a))
  -> (forall a . Expr a -> m (Expr a))
  -> Expr EContract -> m (Expr EContract)
mapEContractMWith rec f e = case e.node of
  GVarF _ -> pure e
  CF code storage tStorage balance nonce -> do
    code' <- mapCodeMWith rec f code
    storage' <- rec storage
    tStorage' <- rec tStorage
    balance' <- rec balance
    pure $ remake e (CF code' storage' tStorage' balance' nonce)

mapEContractM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Expr EContract -> m (Expr EContract)
mapEContractM f = mapEContractMWith (mapExprM f) f

mapContractM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Contract -> m (Contract)
mapContractM f c = do
  code' <- mapCodeM f c.code
  storage' <- mapExprM f c.storage
  origStorage' <- mapExprM f c.origStorage
  balance' <- mapExprM f c.balance
  pure $ c { code = code', storage = storage', origStorage = origStorage', balance = balance' }

mapCodeMWith
  :: forall m . Monad m
  => (forall a . Expr a -> m (Expr a))
  -> (forall a . Expr a -> m (Expr a))
  -> ContractCode -> m (ContractCode)
mapCodeMWith rec f = \case
  UnknownCode a -> fmap UnknownCode (f a)
  c@(RuntimeCode (ConcreteRuntimeCode _)) -> pure c
  RuntimeCode (SymbolicRuntimeCode c) -> do
    c' <- mapM rec c
    pure . RuntimeCode $ SymbolicRuntimeCode c'
  InitCode bs buf -> do
    buf' <- rec buf
    pure $ InitCode bs buf'

mapCodeM :: Monad m => (forall a . Expr a -> m (Expr a)) -> ContractCode -> m (ContractCode)
mapCodeM f = mapCodeMWith (mapExprM f) f

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
