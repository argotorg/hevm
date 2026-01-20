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

      -- Hashes

      e@(Keccak a) -> f e <> (go a)
      e@(SHA256 a) -> f e <> (go a)

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

mapExpr :: (forall a . Expr a -> Expr a) -> Expr b -> Expr b
mapExpr f expr = runIdentity (mapExprM (Identity . f) expr)

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

  -- literals & variables

  Lit a -> f (Lit a)
  LitByte a -> f (LitByte a)
  Var a -> f (Var a)
  GVar s -> f (GVar s)

  -- addresses

  c@(C {}) -> mapEContractM f c

  -- addresses

  LitAddr a -> f (LitAddr a)
  SymAddr a -> f (SymAddr a)
  WAddr a -> do
    a' <- mapExprM f a
    f (WAddr a')

  -- bytes

  IndexWord a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (IndexWord a' b')
  EqByte a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (EqByte a' b')

  JoinBytes zero one two three four five six seven eight nine
    ten eleven twelve thirteen fourteen fifteen sixteen seventeen
    eighteen nineteen twenty twentyone twentytwo twentythree twentyfour
    twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone -> do
    zero' <- mapExprM f zero
    one' <- mapExprM f one
    two' <- mapExprM f two
    three' <- mapExprM f three
    four' <- mapExprM f four
    five' <- mapExprM f five
    six' <- mapExprM f six
    seven' <- mapExprM f seven
    eight' <- mapExprM f eight
    nine' <- mapExprM f nine
    ten' <- mapExprM f ten
    eleven' <- mapExprM f eleven
    twelve' <- mapExprM f twelve
    thirteen' <- mapExprM f thirteen
    fourteen' <- mapExprM f fourteen
    fifteen' <- mapExprM f fifteen
    sixteen' <- mapExprM f sixteen
    seventeen' <- mapExprM f seventeen
    eighteen' <- mapExprM f eighteen
    nineteen' <- mapExprM f nineteen
    twenty' <- mapExprM f twenty
    twentyone' <- mapExprM f twentyone
    twentytwo' <- mapExprM f twentytwo
    twentythree' <- mapExprM f twentythree
    twentyfour' <- mapExprM f twentyfour
    twentyfive' <- mapExprM f twentyfive
    twentysix' <- mapExprM f twentysix
    twentyseven' <- mapExprM f twentyseven
    twentyeight' <- mapExprM f twentyeight
    twentynine' <- mapExprM f twentynine
    thirty' <- mapExprM f thirty
    thirtyone' <- mapExprM f thirtyone
    f (JoinBytes zero' one' two' three' four' five' six' seven' eight' nine'
         ten' eleven' twelve' thirteen' fourteen' fifteen' sixteen' seventeen'
         eighteen' nineteen' twenty' twentyone' twentytwo' twentythree' twentyfour'
         twentyfive' twentysix' twentyseven' twentyeight' twentynine' thirty' thirtyone')

  -- control flow

  Failure a b c -> do
    a' <- mapM (mapPropM f) a
    f (Failure a' b c)
  Partial a b c -> do
    a' <- mapM (mapPropM f) a
    f (Partial a' b c)
  Success a b c d -> do
    a' <- mapM (mapPropM f) a
    c' <- mapExprM f c
    d' <- do
      let x = Map.toList d
      x' <- forM x $ \(k,v) -> do
        k' <- f k
        v' <- mapEContractM f v
        pure (k',v')
      pure $ Map.fromList x'
    f (Success a' b c' d')

  -- integers

  Add a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Add a' b')
  Sub a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Sub a' b')
  Mul a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Mul a' b')
  Div a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Div a' b')
  SDiv a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SDiv a' b')
  Mod a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Mod a' b')
  SMod a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SMod a' b')
  AddMod a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (AddMod a' b' c')
  MulMod a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (MulMod a' b' c')
  Exp a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Exp a' b')
  SEx a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SEx a' b')
  Min a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Min a' b')
  Max a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Max a' b')

  -- booleans

  LT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (LT a' b')
  GT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (GT a' b')
  LEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (LEq a' b')
  GEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (GEq a' b')
  SLT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SLT a' b')
  SGT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SGT a' b')
  Eq a b ->  do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Eq a' b')
  IsZero a -> do
    a' <- mapExprM f a
    f (IsZero a')
  ITE c t el -> do
    c' <- mapExprM f c
    t' <- mapExprM f t
    el' <- mapExprM f el
    f (ITE c' t' el')

  -- bits

  And a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (And a' b')
  Or a b ->  do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Or a' b')
  Xor a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Xor a' b')
  Not a -> do
    a' <- mapExprM f a
    f (Not a')
  SHL a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SHL a' b')
  SHR a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SHR a' b')
  SAR a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SAR a' b')


  -- Hashes

  Keccak a -> do
    a' <- mapExprM f a
    f (Keccak a')

  SHA256 a -> do
    a' <- mapExprM f a
    f (SHA256 a')

  -- block context

  Origin -> f Origin
  Coinbase -> f Coinbase
  Timestamp -> f Timestamp
  BlockNumber -> f BlockNumber
  PrevRandao -> f PrevRandao
  GasLimit -> f GasLimit
  ChainId -> f ChainId
  BaseFee -> f BaseFee
  BlockHash a -> do
    a' <- mapExprM f a
    f (BlockHash a')

  -- tx context

  TxValue -> f TxValue

  -- frame context

  Gas a b -> f (Gas a b)
  Balance a -> do
    a' <- mapExprM f a
    f (Balance a')

  -- code

  CodeSize a -> do
    a' <- mapExprM f a
    f (CodeSize a')
  CodeHash a -> do
    a' <- mapExprM f a
    f (CodeHash a')

  -- logs

  LogEntry a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapM (mapExprM f) c
    f (LogEntry a' b' c')

  -- storage

  ConcreteStore b -> f (ConcreteStore b)
  AbstractStore a b -> f (AbstractStore a b)
  SLoad a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SLoad a' b')
  SStore a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (SStore a' b' c')

  -- buffers

  ConcreteBuf a -> do
    f (ConcreteBuf a)
  AbstractBuf a -> do
    f (AbstractBuf a)
  ReadWord a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (ReadWord a' b')
  ReadByte a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (ReadByte a' b')
  WriteWord a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (WriteWord a' b' c')
  WriteByte a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (WriteByte a' b' c')

  CopySlice a b c d e -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    f (CopySlice a' b' c' d' e')

  BufLength a -> do
    a' <- mapExprM f a
    f (BufLength a')

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
mapPropM f = \case
  PBool b -> pure $ PBool b
  PEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    pure $ PEq a' b'
  PLT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    pure $ PLT a' b'
  PGT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    pure $ PGT a' b'
  PLEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    pure $ PLEq a' b'
  PGEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    pure $ PGEq a' b'
  PNeg a -> do
    a' <- mapPropM f a
    pure $ PNeg a'
  PAnd a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ PAnd a' b'
  POr a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ POr a' b'
  PImpl a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ PImpl a' b'


mapEContractM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Expr EContract -> m (Expr EContract)
mapEContractM _ g@(GVar _) = pure g
mapEContractM f (C code storage tStorage balance nonce) = do
  code' <- mapCodeM f code
  storage' <- mapExprM f storage
  tStorage' <- mapExprM f tStorage
  balance' <- mapExprM f balance
  pure $ C code' storage' tStorage' balance' nonce

mapContractM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Contract -> m (Contract)
mapContractM f c = do
  code' <- mapCodeM f c.code
  storage' <- mapExprM f c.storage
  origStorage' <- mapExprM f c.origStorage
  balance' <- mapExprM f c.balance
  pure $ c { code = code', storage = storage', origStorage = origStorage', balance = balance' }

mapCodeM :: Monad m => (forall a . Expr a -> m (Expr a)) -> ContractCode -> m (ContractCode)
mapCodeM f = \case
  UnknownCode a -> fmap UnknownCode (f a)
  c@(RuntimeCode (ConcreteRuntimeCode _)) -> pure c
  RuntimeCode (SymbolicRuntimeCode c) -> do
    c' <- mapM (mapExprM f) c
    pure . RuntimeCode $ SymbolicRuntimeCode c'
  InitCode bs buf -> do
    buf' <- mapExprM f buf
    pure $ InitCode bs buf'

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
