{-# LANGUAGE TemplateHaskell #-}

{- |
    Module: EVM.Expr.Probe
    Description: One term per constructor, with a uniquely named leaf in every field
-}
module EVM.Expr.Probe (Probe(..), Variant(..), probes, variants, contract) where

import Control.Monad (forM)
import Data.ByteString (ByteString)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Vector qualified as V
import Data.Word (Word8, Word64)
import Language.Haskell.TH

import EVM.Types
import EVM.Types.TH (constructors)

-- | A value whose terms are leaves named after the given marker, and the names used
class Probe a where
  probe :: Text -> (a, [Text])

-- | A scalar that differs between markers of different lengths, so 'variants' can vary it
scalar :: (Int -> a) -> Text -> (a, [Text])
scalar f m = (f (T.length m), [])

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
instance Probe (Maybe (Expr EWord)) where probe m = (Just (Var m), [m])
instance Probe (Maybe (Expr EWord, Expr EWord)) where probe m = (Just (Var (m <> ".0"), Var (m <> ".1")), [m <> ".0", m <> ".1"])
instance Probe CallInputs where
  probe m = (CallInputs (Var (f 1)) (Var (f 2)) (Var (f 3)) (Var (f 4)) (AbstractBuf (f 5)) (Var (f 6))
                        (SymAddr (f 7)) (AbstractStore (SymAddr (f 8)) Nothing) (AbstractStore (SymAddr (f 9)) Nothing)
                        (Var (f 10)) (Var (f 11)), map f [1 .. 11])
    where f :: Int -> Text
          f i = m <> "/" <> T.pack (show i)
instance Probe (Map (Expr EAddr) (Expr EContract)) where
  probe m = (Map.singleton (SymAddr k) (contract (UnknownCode (SymAddr v))), [k, v])
    where k = m <> "/key"; v = m <> "/value"

instance Probe Bool where probe = scalar odd
instance Probe String where probe m = (T.unpack m, [])
instance Probe ByteString where probe m = (encodeUtf8 m, [])
instance Probe W256 where probe = scalar fromIntegral
instance Probe W64 where probe = scalar fromIntegral
instance Probe Word8 where probe = scalar fromIntegral
instance Probe Word64 where probe = scalar fromIntegral
instance Probe Int where probe = scalar id
instance Probe Addr where probe = scalar fromIntegral
instance Probe FunctionSelector where probe = scalar fromIntegral
instance Probe TraceContext where probe m = (TraceContext mempty mempty (Map.singleton 0 m), [])
instance Probe (Maybe W256) where probe = scalar (Just . fromIntegral)
instance Probe (Maybe W64) where probe = scalar (Just . fromIntegral)
instance Probe (Map W256 W256) where probe = scalar (\n -> Map.singleton (fromIntegral n) 0)

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
    let bind r i t = valD (varP r) (normalB (probeAt t (marker c i))) []
        term = foldl appE (conE c) [ [| fst $(varE r) |] | r <- rs ]
    letE (zipWith3 bind rs [1 ..] fields)
      [| ($wrap $term, concat $(listE [ [| snd $(varE r) |] | r <- rs ])) |]

-- | Two terms with the same constructor
data Variant = forall a . Variant (Expr a) (Expr a)

-- | @[("Constructor.field", Variant term term'), ...]@ for every field of every constructor of
-- the Expr type @ty@ except @skip@, where @term'@ differs from @term@ only in that field
variants :: [Name] -> Name -> Q Exp
variants skip ty = do
  cons <- constructors ty
  fmap (ListE . concat) . forM [c | c@(n, _) <- cons, n `notElem` skip] $ \(c, fields) ->
    forM [1 .. length fields] $ \j -> do
      let term v = foldl appE (conE c)
            [ [| fst $(probeAt t (marker c i <> if i == v then "'" else "")) |] | (i, t) <- zip [1 ..] fields ]
      [| ($(sigE (litE (stringL (marker c j))) [t| String |]), Variant $(term 0) $(term j)) |]

marker :: Name -> Int -> String
marker c i = nameBase c <> "." <> show i

probeAt :: Type -> String -> Q Exp
probeAt t m = sigE [| probe (T.pack $(litE (stringL m))) |] [t| ($(pure (mono t)), [Text]) |]
  where
    mono = \case
      VarT _ -> PromotedT 'EWord
      AppT a b -> AppT (mono a) (mono b)
      x -> x
