-- | Symbolic calldata for a function signature, with optional concrete arguments
module EVM.SymExec.Calldata where

import Prelude hiding (Foldable(..))

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Foldable (length, foldl')
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Witch (unsafeInto)

import EVM.ABI
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Types hiding (Comp)

-- | Abstract calldata argument generation
symAbiArg :: Int -> Text -> AbiType -> CalldataFragment
symAbiArg maxDynSize name = \case
  AbiUIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then St [] v
    else internalError "bad type"
  AbiIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then St [] v
    else internalError "bad type"
  AbiBoolType -> St [] v
  AbiAddressType -> St [] (WAddr (SymAddr name))
  AbiBytesType n ->
    if n > 0 && n <= 32
    then St [] v
    else internalError "bad type"
  AbiArrayType sz tps -> do
    Comp . V.toList . V.imap (\(T.pack . show -> i) tp -> symAbiArg maxDynSize (name <> "-a-" <> i) tp) $ (V.replicate sz tps)
  AbiTupleType tps ->
    Comp . V.toList . V.imap (\(T.pack . show -> i) tp -> symAbiArg maxDynSize (name <> "-t-" <> i) tp) $ tps
  -- Dynamic bytes/string: a symbolic length bounded by maxDynSize, the contents
  -- are the calldata bytes that follow the length word
  AbiBytesDynamicType -> dyn (name <> "-bytes-length")
  AbiStringType -> dyn (name <> "-string-length")
  t -> internalError $ "TODO: symbolic abi encoding for " <> show t
  where
    v = Var name
    dyn lenName = let len = Var lenName
                  in Dy [PLEq len (Lit (fromIntegral maxDynSize))] len

-- | Whether 'symAbiArg' can make an argument of this type symbolic
symAbiArgSupported :: AbiType -> Bool
symAbiArgSupported = \case
  AbiArrayType _ t -> symAbiArgSupported t
  AbiTupleType ts -> all symAbiArgSupported ts
  AbiArrayDynamicType _ -> False
  AbiFunctionType -> False
  _ -> True

data CalldataFragment
  = St [Prop] (Expr EWord)
  | Dy [Prop] (Expr EWord) -- ^ props, symbolic length
  | DyConc ByteString -- ^ tail encoding of a concrete dynamic argument
  | Comp [CalldataFragment]
  deriving (Show, Eq)

-- | Generates calldata matching given type signature, optionally specialized
-- with concrete arguments.
-- Any argument given as "<symbolic>" or omitted at the tail of the list are
-- kept symbolic.
symCalldata :: App m => Text -> [AbiType] -> [String] -> Expr Buf -> m (Expr Buf, [Prop], [Caveat])
symCalldata = symCalldataNamed "" False

-- | Like 'symCalldata', with the argument variables' names prefixed, so that
-- the calldata of several calls on one path do not share variables, and
-- optionally without trailing bytes after the arguments
symCalldataNamed :: App m => Text -> Bool -> Text -> [AbiType] -> [String] -> Expr Buf -> m (Expr Buf, [Prop], [Caveat])
symCalldataNamed prefix exact sig typesignature concreteArgs base = do
  conf <- readConfig
  let
    args = concreteArgs <> replicate (length typesignature - length concreteArgs) "<symbolic>"
    mkArg :: AbiType -> String -> Int -> CalldataFragment
    mkArg typ "<symbolic>" n = symAbiArg conf.maxDynSize (prefix <> T.pack ("arg" <> show n)) typ
    mkArg typ arg _ =
      let enc = encodeAbiValue (makeAbiValue typ arg)
      in case abiKind typ of
        Static -> Comp [St [] (Lit (word w)) | w <- chunks32 enc]
        Dynamic -> DyConc enc
    chunks32 bs = if BS.null bs then [] else let (h, t) = BS.splitAt 32 bs in h : chunks32 t
    calldatas = zipWith3 mkArg typesignature args [1..]
    -- with an exact, concrete length, calldatasize is concrete too
    base' = case (exact, cdLen calldatas) of
      (True, Lit n) -> ConcreteBuf (BS.replicate (unsafeInto n) 0)
      _ -> base
    (cdBuf, props) = combineFragments calldatas base'
    withSelector = writeSelector cdBuf sig
    sizeConstraints
      | exact = Expr.bufLength withSelector .== cdLen calldatas
      | otherwise = (Expr.bufLength withSelector .>= cdLen calldatas)
          .&& (Expr.bufLength withSelector .< (Lit (2 ^ conf.maxBufSize)))
    -- A dynamic (bytes/string) argument is turned into a 'Dy' fragment with its
    -- length bounded to maxDynSize. That is a restriction of the input domain
    -- (every path is still explored fully), so we record it as a program-wide
    -- 'Caveat' rather than a per-path 'Partial'. Derived from the fragments we
    -- actually built, so a concretely-supplied argument produces no caveat.
    caveats = [DynArgBounded conf.maxDynSize | any isDy calldatas]
  pure (withSelector, sizeConstraints : props, caveats)

cdLen :: [CalldataFragment] -> Expr EWord
cdLen frags = Expr.add (Expr.add (Lit 4) (countHeadBytes frags)) (tailLen frags)
  where
    tailLen = foldl' (\acc f -> case f of
                         Dy _ len -> Expr.add acc (dynTailSize len)
                         DyConc bs -> Expr.add acc (Lit (unsafeInto (BS.length bs)))
                         _ -> acc) (Lit 0)

-- | Bytes a dynamic argument takes in the tail: the length word and the
-- contents, padded to a multiple of 32
dynTailSize :: Expr EWord -> Expr EWord
dynTailSize len = Expr.add (Lit 32) (Expr.mul (Expr.div (Expr.add len (Lit 31)) (Lit 32)) (Lit 32))

-- | Each top-level fragment occupies 32 bytes in the head (value or offset pointer)
countHeadBytes :: [CalldataFragment] -> Expr EWord
countHeadBytes = foldl' countFrag (Lit 0)
  where
    countFrag acc (St _ _)  = Expr.add acc (Lit 32)
    countFrag acc (Dy {})   = Expr.add acc (Lit 32)
    countFrag acc (DyConc _) = Expr.add acc (Lit 32)
    countFrag acc (Comp xs) | all isSt xs = foldl' countFrag acc xs
    countFrag _ s = internalError $ "unsupported cd fragment: " <> show s

writeSelector :: Expr Buf -> Text -> Expr Buf
writeSelector buf sig =
  writeSel (Lit 0) $ writeSel (Lit 1) $ writeSel (Lit 2) $ writeSel (Lit 3) buf
  where
    sel = ConcreteBuf $ selector sig
    writeSel idx = Expr.writeByte idx (Expr.readByte idx sel)

-- | Writes the arguments in the canonical ABI layout. The tail offset of each
-- dynamic argument depends on the symbolic lengths of the ones before it.
combineFragments :: [CalldataFragment] -> Expr Buf -> (Expr Buf, [Prop])
combineFragments fragments base =
  let headBytes = countHeadBytes fragments
  in go headBytes (Lit 4) (Lit 0) fragments (base, [])
  where
    go :: Expr EWord -> Expr EWord -> Expr EWord
       -> [CalldataFragment] -> (Expr Buf, [Prop]) -> (Expr Buf, [Prop])
    go _ _ _ [] acc = acc
    go headSz idx tailAcc (f:rest) (buf, ps) =
      case f of
        St p w -> go headSz (Expr.add idx (Lit 32)) tailAcc rest
                    (Expr.writeWord idx w buf, p <> ps)
        Comp xs | all isSt xs -> go headSz idx tailAcc (xs <> rest) (buf, ps)
        Dy p len ->
          -- ABI offsets are relative to the start of the args (byte 4)
          let offset = Expr.add headSz tailAcc
              buf1 = Expr.writeWord idx offset buf
              buf2 = Expr.writeWord (Expr.add (Lit 4) offset) len buf1
          in go headSz (Expr.add idx (Lit 32)) (Expr.add tailAcc (dynTailSize len)) rest
               (buf2, p <> ps)
        DyConc bs ->
          let offset = Expr.add headSz tailAcc
              sz = Lit (unsafeInto (BS.length bs))
              buf1 = Expr.writeWord idx offset buf
              buf2 = Expr.copySlice (Lit 0) (Expr.add (Lit 4) offset) sz (ConcreteBuf bs) buf1
          in go headSz (Expr.add idx (Lit 32)) (Expr.add tailAcc sz) rest (buf2, ps)
        s -> internalError $ "unsupported cd fragment: " <> show s

isSt :: CalldataFragment -> Bool
isSt (St {}) = True
isSt (Comp fs) = all isSt fs
isSt _ = False

isDy :: CalldataFragment -> Bool
isDy (Dy {}) = True
isDy _ = False

-- | Builds a buffer representing calldata from the provided method description
-- and concrete arguments, together with any program-wide soundness caveats
-- incurred while building it (see 'Caveat').
mkCalldata :: App m => Maybe Sig -> [String] -> m ((Expr Buf, [Prop]), [Caveat])
mkCalldata Nothing _ = do
  conf <- readConfig
  pure ( ( AbstractBuf "txdata"
         -- assert that the length of the calldata is never more than 2^64
         -- this is way larger than would ever be allowed by the gas limit
         -- and avoids spurious counterexamples during abi decoding
         -- TODO: can we encode calldata as an array with a smaller length?
         , [Expr.bufLength (AbstractBuf "txdata") .< (Lit (2 ^ conf.maxBufSize))]
         )
       , []
       )
mkCalldata (Just (Sig name types)) args = do
  (buf, props, caveats) <- symCalldata name types args (AbstractBuf "txdata")
  pure ((buf, props), caveats)
