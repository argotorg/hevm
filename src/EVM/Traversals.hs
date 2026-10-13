{- |
    Module: EVM.Traversals
    Description: Generic traversal functions for Expr datatypes
-}
module EVM.Traversals where

import Prelude hiding (LT, GT, Foldable(..))

import Control.Monad (void)
import Control.Monad.Identity (Identity(Identity), runIdentity)
import Data.Foldable (Foldable(..))
import Data.Map.Strict qualified as Map
import GHC.StaticPtr (StaticPtr, deRefStaticPtr)

import EVM.Types
import EVM.HashCons (Rewrite, runRewrite, hashConsExpr, memoFixTraverse, hashConsEnabled)
import EVM.Traversals.Children

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
foldExpr :: forall b c . Monoid b => (forall a . Expr a -> b) -> b -> Expr c -> b
foldExpr f acc expr = acc <> (go expr)
  where
    go :: forall a . Expr a -> b
    go = \case

      -- literals & variables

      e@(Lit _) -> f e
      e@(LitByte _) -> f e
      e@(Var _) -> f e
      e@(GVar _) -> f e

      -- contracts

      e@(C {}) -> foldEContract f acc e

      -- bytes

      e@(IndexWord a b) -> f e <> (go a) <> (go b)
      e@(EqByte a b) -> f e <> (go a) <> (go b)

      e@(JoinBytes
        zero one two three four five six seven
        eight nine ten eleven twelve thirteen fourteen fifteen
        sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
        twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone)
        -> f e
        <> (go zero) <> (go one) <> (go two) <> (go three)
        <> (go four) <> (go five) <> (go six) <> (go seven)
        <> (go eight) <> (go nine) <> (go ten) <> (go eleven)
        <> (go twelve) <> (go thirteen) <> (go fourteen)
        <> (go fifteen) <> (go sixteen) <> (go seventeen)
        <> (go eighteen) <> (go nineteen) <> (go twenty)
        <> (go twentyone) <> (go twentytwo) <> (go twentythree)
        <> (go twentyfour) <> (go twentyfive) <> (go twentysix)
        <> (go twentyseven) <> (go twentyeight) <> (go twentynine)
        <> (go thirty) <> (go thirtyone)

      -- control flow

      e@(Success a _ c d) -> f e
                          <> foldl' (foldProp f) mempty a
                          <> go c
                          <> foldl' (foldExpr f) mempty (Map.keys d)
                          <> foldl' (foldEContract f) mempty d
      e@(Failure a _ (Revert c)) -> f e <> (foldl' (foldProp f) mempty a) <> go c
      e@(Failure a _ _) -> f e <> (foldl' (foldProp f) mempty a)
      e@(Partial a _ _) -> f e <> (foldl' (foldProp f) mempty a)

      -- integers

      e@(Add a b) -> f e <> (go a) <> (go b)
      e@(Sub a b) -> f e <> (go a) <> (go b)
      e@(Mul a b) -> f e <> (go a) <> (go b)
      e@(Div a b) -> f e <> (go a) <> (go b)
      e@(SDiv a b) -> f e <> (go a) <> (go b)
      e@(Mod a b) -> f e <> (go a) <> (go b)
      e@(SMod a b) -> f e <> (go a) <> (go b)
      e@(AddMod a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(MulMod a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(Exp a b) -> f e <> (go a) <> (go b)
      e@(SEx a b) -> f e <> (go a) <> (go b)
      e@(Min a b) -> f e <> (go a) <> (go b)
      e@(Max a b) -> f e <> (go a) <> (go b)

      -- booleans

      e@(LT a b) -> f e <> (go a) <> (go b)
      e@(GT a b) -> f e <> (go a) <> (go b)
      e@(LEq a b) -> f e <> (go a) <> (go b)
      e@(GEq a b) -> f e <> (go a) <> (go b)
      e@(SLT a b) -> f e <> (go a) <> (go b)
      e@(SGT a b) -> f e <> (go a) <> (go b)
      e@(Eq a b) -> f e <> (go a) <> (go b)
      e@(IsZero a) -> f e <> (go a)
      e@(ITE c t el) -> f e <> (go c) <> (go t) <> (go el)

      -- bits

      e@(And a b) -> f e <> (go a) <> (go b)
      e@(Or a b) -> f e <> (go a) <> (go b)
      e@(Xor a b) -> f e <> (go a) <> (go b)
      e@(Not a) -> f e <> (go a)
      e@(SHL a b) -> f e <> (go a) <> (go b)
      e@(SHR a b) -> f e <> (go a) <> (go b)
      e@(SAR a b) -> f e <> (go a) <> (go b)
      e@(CLZ a) -> f e <> (go a)

      -- Hashes

      e@(Keccak a) -> f e <> (go a)

      -- block context

      e@(Origin) -> f e
      e@(Coinbase) -> f e
      e@(Timestamp) -> f e
      e@(BlockNumber) -> f e
      e@(PrevRandao) -> f e
      e@(GasLimit) -> f e
      e@(ChainId) -> f e
      e@(BaseFee) -> f e
      e@(BlockHash a) -> f e <> (go a)

      -- tx context

      e@(TxValue) -> f e

      -- frame context

      e@(Gas _ _) -> f e
      e@(Balance {}) -> f e

      -- code

      e@(CodeSize a) -> f e <> (go a)
      e@(CodeHash a) -> f e <> (go a)

      -- logs

      e@(LogEntry a b c) -> f e <> (go a) <> (go b) <> (foldl' (<>) mempty (fmap f c))

      -- storage

      e@(LitAddr _) -> f e
      e@(WAddr a) -> f e <> go a
      e@(SymAddr _) -> f e

      -- storage

      e@(ConcreteStore _) -> f e
      e@(AbstractStore _ _) -> f e
      e@(SLoad a b) -> f e <> (go a) <> (go b)
      e@(SStore a b c) -> f e <> (go a) <> (go b) <> (go c)

      -- buffers

      e@(ConcreteBuf _) -> f e
      e@(AbstractBuf _) -> f e
      e@(ReadWord a b) -> f e <> (go a) <> (go b)
      e@(ReadByte a b) -> f e <> (go a) <> (go b)
      e@(WriteWord a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(WriteByte a b c) -> f e <> (go a) <> (go b) <> (go c)

      e@(CopySlice a b c d g)
        -> f e
        <> (go a)
        <> (go b)
        <> (go c)
        <> (go d)
        <> (go g)
      e@(BufLength a) -> f e <> (go a)

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
