{-# LANGUAGE TemplateHaskell #-}

{- |
    Module: EVM.Expr.Probe
    Description: One term per constructor, with a uniquely named leaf in every field
-}
module EVM.Expr.Probe (Probe(..), probes, contract) where

import Control.Monad (forM)
import Data.ByteString (ByteString)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Word (Word8, Word64)
import Language.Haskell.TH

import EVM.Types
import EVM.Types.TH (constructors)

-- | A value whose terms are leaves named after the given marker, and the names used
class Probe a where
  probe :: Text -> (a, [Text])

none :: a -> Text -> (a, [Text])
none x _ = (x, [])

instance Probe Text where probe m = (m, [m])
instance Probe (Expr EWord) where probe m = (Var m, [m])
instance Probe (Expr Buf) where probe m = (AbstractBuf m, [m])
instance Probe (Expr EAddr) where probe m = (SymAddr m, [m])
instance Probe (Expr Storage) where probe m = (AbstractStore (SymAddr m) Nothing, [m])
instance Probe (Expr Byte) where probe m = (IndexWord (Lit 0) (Var m), [m])
instance Probe (Expr EContract) where probe m = (contract (UnknownCode (SymAddr m)), [m])
instance Probe [Expr EWord] where probe m = ([Var m], [m])
instance Probe [SomeExpr] where probe m = ([SomeExpr (Var m)], [m])
instance Probe Prop where probe m = (PEq (Var m) (Lit 0), [m])
instance Probe [Prop] where probe m = ([PEq (Var m) (Lit 0)], [m])
instance Probe (V.Vector (Expr Byte)) where probe m = (V.singleton (IndexWord (Lit 0) (Var m)), [m])
instance Probe EvmError where probe m = (Revert (AbstractBuf m), [m])
instance Probe PartialExec where probe m = (MaxIterationsReached 0 (SymAddr m), [m])
instance Probe ContractCode where probe m = (UnknownCode (SymAddr m), [m])
instance Probe RuntimeCode where probe m = (SymbolicRuntimeCode (V.singleton (IndexWord (Lit 0) (Var m))), [m])
instance Probe (Map (Expr EAddr) (Expr EContract)) where
  probe m = (Map.singleton (SymAddr k) (contract (UnknownCode (SymAddr v))), [k, v])
    where k = m <> "/key"; v = m <> "/value"

instance Probe Bool where probe = none False
instance Probe String where probe = none ""
instance Probe ByteString where probe = none ""
instance Probe W256 where probe = none 0
instance Probe W64 where probe = none 0
instance Probe Word8 where probe = none 0
instance Probe Word64 where probe = none 0
instance Probe Int where probe = none 0
instance Probe Addr where probe = none 0
instance Probe FunctionSelector where probe = none 0
instance Probe TraceContext where probe = none mempty
instance Probe (Maybe W256) where probe = none Nothing
instance Probe (Maybe W64) where probe = none Nothing
instance Probe (Map W256 W256) where probe = none mempty

contract :: ContractCode -> Expr EContract
contract code = C code (ConcreteStore mempty) (ConcreteStore mempty) (Lit 0) Nothing

-- | @[(wrap term, names), ...]@ with one term per constructor of @ty@ except @skip@, its
-- fields probed with markers "Constructor.field". Type variables in field types are
-- instantiated at EWord.
probes :: Q Exp -> [Name] -> Name -> Q Exp
probes wrap skip ty = do
  cons <- constructors ty
  fmap ListE . forM [c | c@(n, _) <- cons, n `notElem` skip] $ \(c, fields) -> do
    rs <- forM fields (const (newName "r"))
    let marker i = litE (stringL (nameBase c <> "." <> show (i :: Int)))
        bind r i t = valD (varP r) (normalB (sigE [| probe (T.pack $(marker i)) |] [t| ($(pure (mono t)), [Text]) |])) []
        term = foldl appE (conE c) [ [| fst $(varE r) |] | r <- rs ]
    letE (zipWith3 bind rs [1 ..] fields)
      [| ($wrap $term, concat $(listE [ [| snd $(varE r) |] | r <- rs ])) |]
  where
    mono = \case
      VarT _ -> PromotedT 'EWord
      AppT a b -> AppT (mono a) (mono b)
      t -> t
