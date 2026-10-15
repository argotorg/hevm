{- |
    Module: EVM.Traversals.Children
    Description: One-layer traversal of Expr, shared by EVM.Traversals and EVM.HashCons
-}
module EVM.Traversals.Children
  ( mapChildrenM
  , mapPropChildrenM
  , mapCodeChildrenM
  ) where

import Prelude hiding (LT, GT)

import Data.Map.Strict qualified as Map

import EVM.Types

-- | Applies @g@ to every term directly below a node, left to right, and rebuilds the node
mapChildrenM :: Applicative m => (forall a . Expr a -> m (Expr a)) -> Expr b -> m (Expr b)
mapChildrenM g expr = case expr of
  Lit _ -> pure expr
  LitByte _ -> pure expr
  Var _ -> pure expr
  GVar _ -> pure expr

  C code storage tStorage balance nonce ->
    C <$> mapCodeChildrenM g code <*> g storage <*> g tStorage <*> g balance <*> pure nonce

  LitAddr _ -> pure expr
  SymAddr _ -> pure expr
  WAddr a -> WAddr <$> g a

  IndexWord a b -> IndexWord <$> g a <*> g b
  EqByte a b -> EqByte <$> g a <*> g b
  JoinBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
            b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 ->
    JoinBytes <$> g b0 <*> g b1 <*> g b2 <*> g b3 <*> g b4 <*> g b5 <*> g b6 <*> g b7
              <*> g b8 <*> g b9 <*> g b10 <*> g b11 <*> g b12 <*> g b13 <*> g b14 <*> g b15
              <*> g b16 <*> g b17 <*> g b18 <*> g b19 <*> g b20 <*> g b21 <*> g b22 <*> g b23
              <*> g b24 <*> g b25 <*> g b26 <*> g b27 <*> g b28 <*> g b29 <*> g b30 <*> g b31

  Failure a b c -> (\a' c' -> Failure a' b c') <$> traverse (mapPropChildrenM g) a <*> mapErrorChildrenM g c
  Partial a b c -> (\a' c' -> Partial a' b c') <$> traverse (mapPropChildrenM g) a <*> mapPartialChildrenM g c
  Success a b c d ->
    (\a' c' d' -> Success a' b c' (Map.fromList d'))
      <$> traverse (mapPropChildrenM g) a
      <*> g c
      <*> traverse (\(k, v) -> (,) <$> g k <*> g v) (Map.toList d)

  Add a b -> Add <$> g a <*> g b
  Sub a b -> Sub <$> g a <*> g b
  Mul a b -> Mul <$> g a <*> g b
  Div a b -> Div <$> g a <*> g b
  SDiv a b -> SDiv <$> g a <*> g b
  Mod a b -> Mod <$> g a <*> g b
  SMod a b -> SMod <$> g a <*> g b
  AddMod a b c -> AddMod <$> g a <*> g b <*> g c
  MulMod a b c -> MulMod <$> g a <*> g b <*> g c
  Exp a b -> Exp <$> g a <*> g b
  SEx a b -> SEx <$> g a <*> g b
  Min a b -> Min <$> g a <*> g b
  Max a b -> Max <$> g a <*> g b

  LT a b -> LT <$> g a <*> g b
  GT a b -> GT <$> g a <*> g b
  LEq a b -> LEq <$> g a <*> g b
  GEq a b -> GEq <$> g a <*> g b
  SLT a b -> SLT <$> g a <*> g b
  SGT a b -> SGT <$> g a <*> g b
  Eq a b -> Eq <$> g a <*> g b
  IsZero a -> IsZero <$> g a
  ITE c t e -> ITE <$> g c <*> g t <*> g e

  And a b -> And <$> g a <*> g b
  Or a b -> Or <$> g a <*> g b
  Xor a b -> Xor <$> g a <*> g b
  Not a -> Not <$> g a
  SHL a b -> SHL <$> g a <*> g b
  SHR a b -> SHR <$> g a <*> g b
  SAR a b -> SAR <$> g a <*> g b
  CLZ a -> CLZ <$> g a

  Keccak a -> Keccak <$> g a

  Origin -> pure expr
  Coinbase -> pure expr
  Timestamp -> pure expr
  BlockNumber -> pure expr
  PrevRandao -> pure expr
  GasLimit -> pure expr
  ChainId -> pure expr
  BaseFee -> pure expr
  BlockHash a -> BlockHash <$> g a
  TxValue -> pure expr

  Gas _ _ -> pure expr
  Balance a -> Balance <$> g a
  CodeSize a -> CodeSize <$> g a
  CodeHash a -> CodeHash <$> g a

  LogEntry a b c -> LogEntry <$> g a <*> g b <*> traverse g c

  ConcreteStore _ -> pure expr
  -- the address is not traversed
  AbstractStore _ _ -> pure expr
  SLoad a b -> SLoad <$> g a <*> g b
  SStore a b c -> SStore <$> g a <*> g b <*> g c

  ConcreteBuf _ -> pure expr
  AbstractBuf _ -> pure expr
  ReadWord a b -> ReadWord <$> g a <*> g b
  ReadByte a b -> ReadByte <$> g a <*> g b
  WriteWord a b c -> WriteWord <$> g a <*> g b <*> g c
  WriteByte a b c -> WriteByte <$> g a <*> g b <*> g c
  CopySlice a b c d e -> CopySlice <$> g a <*> g b <*> g c <*> g d <*> g e
  BufLength a -> BufLength <$> g a

-- | Applies @g@ to every term in a prop
mapPropChildrenM :: Applicative m => (forall a . Expr a -> m (Expr a)) -> Prop -> m Prop
mapPropChildrenM g = \case
  PBool b -> pure (PBool b)
  PEq a b -> PEq <$> g a <*> g b
  PLT a b -> PLT <$> g a <*> g b
  PGT a b -> PGT <$> g a <*> g b
  PLEq a b -> PLEq <$> g a <*> g b
  PGEq a b -> PGEq <$> g a <*> g b
  PNeg a -> PNeg <$> mapPropChildrenM g a
  PAnd a b -> PAnd <$> mapPropChildrenM g a <*> mapPropChildrenM g b
  POr a b -> POr <$> mapPropChildrenM g a <*> mapPropChildrenM g b
  PImpl a b -> PImpl <$> mapPropChildrenM g a <*> mapPropChildrenM g b
  PCall i s r w -> PCall <$> mapCallInputsM g i <*> g s <*> g r <*> traverse g w

mapCallInputsM :: Applicative m => (forall a . Expr a -> m (Expr a)) -> CallInputs -> m CallInputs
mapCallInputsM g (CallInputs w k t v d l c s ts b) =
  CallInputs <$> g w <*> g k <*> g t <*> g v <*> g d <*> g l <*> g c <*> g s <*> g ts <*> g b

mapCodeChildrenM :: Applicative m => (forall a . Expr a -> m (Expr a)) -> ContractCode -> m ContractCode
mapCodeChildrenM g = \case
  UnknownCode a -> UnknownCode <$> g a
  c@(RuntimeCode (ConcreteRuntimeCode _)) -> pure c
  RuntimeCode (SymbolicRuntimeCode c) -> RuntimeCode . SymbolicRuntimeCode <$> traverse g c
  InitCode bs buf -> InitCode bs <$> g buf

mapErrorChildrenM :: Applicative m => (forall a . Expr a -> m (Expr a)) -> EvmError -> m EvmError
mapErrorChildrenM g = \case
  BalanceTooLow a b -> BalanceTooLow <$> g a <*> g b
  Revert a -> Revert <$> g a
  MaxInitCodeSizeExceeded a b -> MaxInitCodeSizeExceeded a <$> g b
  e@UnrecognizedOpcode{} -> pure e
  e@SelfDestruction -> pure e
  e@StackUnderrun -> pure e
  e@BadJumpDestination -> pure e
  e@OutOfGas{} -> pure e
  e@StackLimitExceeded -> pure e
  e@IllegalOverflow -> pure e
  e@StateChangeWhileStatic -> pure e
  e@InvalidMemoryAccess -> pure e
  e@CallDepthLimitReached -> pure e
  e@MaxCodeSizeExceeded{} -> pure e
  e@InvalidFormat -> pure e
  e@PrecompileFailure -> pure e
  e@NonexistentPrecompile{} -> pure e
  e@ReturnDataOutOfBounds -> pure e
  e@NonceOverflow -> pure e
  e@BadCheatCode{} -> pure e
  e@NonexistentFork{} -> pure e
  e@AssumeCheatFailed -> pure e

mapPartialChildrenM :: Applicative m => (forall a . Expr a -> m (Expr a)) -> PartialExec -> m PartialExec
mapPartialChildrenM g = \case
  UnexpectedSymbolicArg pc a op msg args ->
    (\a' args' -> UnexpectedSymbolicArg pc a' op msg args') <$> g a <*> traverse (\(SomeExpr e) -> SomeExpr <$> g e) args
  MaxIterationsReached pc a -> MaxIterationsReached pc <$> g a
  JumpIntoSymbolicCode pc a dst -> (\a' -> JumpIntoSymbolicCode pc a' dst) <$> g a
  PrecompileMissing pc a pre -> (\a' -> PrecompileMissing pc a' pre) <$> g a
  CheatCodeMissing pc a sel -> (\a' -> CheatCodeMissing pc a' sel) <$> g a
  BranchTooDeep pc a -> BranchTooDeep pc <$> g a
