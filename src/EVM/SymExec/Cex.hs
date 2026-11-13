-- | Substituting a counterexample's model into expressions, and printing it
module EVM.SymExec.Cex where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as T

import EVM.ABI
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Format (formatExpr, showVal, indent, formatBinary)
import EVM.SMT qualified as SMT
import EVM.Traversals (mapExpr, mapExprM, foldTerm)
import EVM.Types

-- | The concrete calldata of a counterexample, if it has one.
cexCalldata :: Expr Buf -> SMTCex -> Maybe ByteString
cexCalldata cd cex = case Expr.concKeccakSimpExpr <$> defaultSymbolicValues (subModel cex cd) of
  Right (ConcreteBuf bs) -> Just bs
  _ -> Nothing

showModel :: Expr Buf -> (Expr End, SMTResult) -> IO ()
showModel cd (expr, res) = do
  case res of
    Qed -> pure () -- ignore unreachable branches
    Error e -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn $ "Error during SMT solving, cannot check branch " <> e
    Unknown reason -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn $ "Unable to produce a model for the following end state due to '" <> reason <> "' :"
      T.putStrLn $ indent 2 $ formatExpr expr
      putStrLn ""
    Cex cex -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn "Inputs:"
      T.putStrLn $ indent 2 $ formatCex cd Nothing cex
      putStrLn "End State:"
      T.putStrLn $ indent 2 $ formatExpr expr

showBuffer :: (Expr Buf) -> SMTCex -> Text
showBuffer buf cex = case Map.lookup buf cex.buffers of
  Nothing -> internalError "buffer missing in the counterexample"
  Just buffer -> case SMT.collapse buffer of
    Nothing -> T.pack $ show buffer
    Just (Flat bs) -> T.pack $ show bs
    Just (EVM.Types.Comp _) -> internalError "CompressedBuf returned from collapse"

formatCex :: Expr Buf -> Maybe Sig -> SMTCex -> Text
formatCex cd sig m@(SMTCex _ addrs _ store blockContext txContext _) = T.unlines $
  [ bold "Calldata:", indent 2 cd' ]
  <> storeCex
  <> txCtx
  <> blockCtx
  <> addrsCex
  where
    -- we attempt to produce a model for calldata by substituting all variables
    -- and buffers provided by the model into the original calldata expression.
    -- If we have a concrete result then we display it, otherwise we display
    -- `Any`. This is a little bit of a hack (and maybe unsound?), but we need
    -- it for branches that do not refer to calldata at all (e.g. the top level
    -- callvalue check inserted by solidity in contracts that don't have any
    -- payable functions).
    cd' = case sig of
      Nothing -> case (defaultSymbolicValues $ subModel m cd) of
        Right k -> prettyBuf $ Expr.concKeccakSimpExpr k
        Left err -> T.pack err
      Just (Sig n ts) -> prettyCalldata m cd n ts

    storeCex :: [Text]
    storeCex
      | Map.null store = []
      | otherwise =
          [ bold "Storage:"
          , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
              ("Addr " <> (T.pack . show $ key)
                <> ": " <> (T.pack $ show (Map.toList val))) : acc
            ) mempty store
          ]

    txCtx :: [Text]
    txCtx
      | Map.null txContext = []
      | otherwise =
        [ bold "Transaction Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
            (showTxCtx key <> ": " <> (T.pack $ show val)) : acc
          ) mempty (filterSubCtx txContext)
        ]

    addrsCex :: [Text]
    addrsCex
      | Map.null addrs = []
      | otherwise =
          [ bold "Addrs:"
          , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
              ((T.pack . show $ key) <> ": " <> (T.pack $ show val)) : acc
            ) mempty addrs
          ]

    bold :: Text -> Text
    bold t = "\x1b[1m" <> t <> "\x1b[0m"

    -- strips the frame arg from frame context vars to make them easier to read
    showTxCtx :: Expr EWord -> Text
    showTxCtx (TxValue) = "TxValue"
    showTxCtx x = T.pack $ show x

    filterSubCtx :: Map (Expr EWord) W256 -> Map (Expr EWord) W256
    filterSubCtx = Map.filterWithKey go
      where
        go :: Expr EWord -> W256 -> Bool
        go (TxValue) _ = True
        go (Balance {}) _ = True
        -- gas readings are produced by the run, not part of its input
        go (Gas {}) _ = False
        go _ _ = False

    blockCtx :: [Text]
    blockCtx
      | Map.null blockContext = []
      | otherwise =
        [ bold "Block Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
            (T.pack $ show key <> ": " <> show val) : acc
          ) mempty blockContext
        ]

prettyBuf :: Expr Buf -> Text
prettyBuf (ConcreteBuf "") = "Empty"
prettyBuf (ConcreteBuf bs) = formatBinary bs
prettyBuf b = internalError $ "Unexpected symbolic buffer:\n" <> T.unpack (formatExpr b)

calldataFromCex :: App m => SMTCex -> Expr Buf -> Sig -> m (Err ByteString)
calldataFromCex cex buf sig = do
  let sigKeccak = BS.take 4 $ keccakBytes $ encodeUtf8 (callSig sig)
  pure $ (sigKeccak <>) <$> body
  where
    cd = defaultSymbolicValues $ subModel cex buf
    argdata = case cd of
      Right cd' -> Right $ Expr.drop 4 (Expr.simplify cd')
      Left e -> Left e
    body = forceConcrete =<< argdata
    forceConcrete :: (Expr Buf) -> Err ByteString
    forceConcrete (ConcreteBuf k) = Right k
    forceConcrete _ = Left "Symbolic buffer in calldata, cannot produce concrete model"

prettyCalldata :: SMTCex -> Expr Buf -> Text -> [AbiType] -> Text
prettyCalldata cex buf sig types = headErr errSig (T.splitOn "(" sig) <> "(" <> body <> ")" <> T.pack finalErr
  where
    cd = defaultSymbolicValues $ subModel cex buf
    argdata :: Err (Expr Buf) = case cd of
      Right cd' -> Right $ Expr.drop 4 (Expr.simplify cd')
      Left e -> Left e
    (body, finalErr) = case argdata of
      Right argdata' -> case decodeBuf types argdata' of
        (CAbi v, "") -> (T.intercalate "," (fmap showVal v), "")
        (CAbi v, err) -> (T.intercalate "," (fmap showVal v), dash <> err)
        (NoVals, err) -> case argdata' of
            ConcreteBuf c -> (T.pack $ "ABI decode failed. hex calldata: 0x" <> (bsToHex c), dash <> err)
            _ -> (T.pack defaultText, dash <> err)
        (SAbi _, err) -> (T.pack defaultText, dash <> err)
      Left err -> (T.pack err, "")
    headErr e l = fromMaybe (T.pack e) $ listToMaybe l
    dash = " -- "
    defaultText = "Error: unable to produce a concrete model for calldata: " <> show buf
    errSig = "Error unable to split sig: " <> show sig

-- | If the expression contains any symbolic values, default them to some
-- concrete value The intuition here is that if we still have symbolic values
-- in our calldata expression after substituting in our cex, then they can have
-- any value and we can safely pick a random value. This is a bit unsatisfying,
-- we should really be doing smth like: https://github.com/argotorg/hevm/issues/334
-- but it's probably good enough for now
defaultSymbolicValues :: Err (Expr a) -> Err (Expr a)
defaultSymbolicValues = \case
    -- addresses last, as balances are keyed by symbolic address
    Right e -> fmap (subAddrs (foldTerm symaddrs mempty e))
               . subBufs (foldTerm symbufs mempty e)
               . subVars (foldTerm symwords mempty e) $ e
    Left err -> Left err
  where
    symaddrs :: Expr a -> Map (Expr EAddr) Addr
    symaddrs = \case
      a@(SymAddr _) -> Map.singleton a (Addr 0x1312)
      _ -> mempty
    symbufs :: Expr a -> Map (Expr Buf) BufModel
    symbufs = \case
      a@(AbstractBuf _) -> Map.singleton a (Flat BS.empty)
      _ -> mempty
    symwords :: Expr a -> Map (Expr EWord) W256
    symwords = \case
      a@(Var _) -> Map.singleton a 0
      a@Origin -> Map.singleton a 0
      a@Coinbase -> Map.singleton a 0
      a@Timestamp -> Map.singleton a 0
      a@BlockNumber -> Map.singleton a 0
      a@PrevRandao -> Map.singleton a 0
      a@GasLimit -> Map.singleton a 0
      a@ChainId -> Map.singleton a 0
      a@BaseFee -> Map.singleton a 0
      a@TxValue -> Map.singleton a 0
      a@(Balance _) -> Map.singleton a 0
      _ -> mempty

-- | Takes an expression and a Cex and replaces all abstract values in the buf with
-- concrete ones from the Cex.
subModel :: SMTCex -> Expr a -> Err (Expr a)
subModel c
  -- addresses last: the model keys balances and stores by symbolic address
  = fmap (subAddrs c.addrs)
  . subBufs c.buffers
  . subStores c.store
  . subVars c.vars
  . subVars c.blockContext
  . subVars c.txContext

subVars :: Map (Expr EWord) W256 -> Expr a -> Expr a
subVars model b = Map.foldlWithKey subVar b model
  where
    subVar :: Expr a -> Expr EWord -> W256 -> Expr a
    subVar a var val = mapExpr go a
      where
        go :: Expr a -> Expr a
        go = \case
          v@(Var _) -> if v == var then Lit val else v
          v@(Balance _) -> if v == var then Lit val else v
          v@TxValue -> if v == var then Lit val else v
          v@Origin -> if v == var then Lit val else v
          v@Coinbase -> if v == var then Lit val else v
          v@Timestamp -> if v == var then Lit val else v
          v@BlockNumber -> if v == var then Lit val else v
          v@PrevRandao -> if v == var then Lit val else v
          v@GasLimit -> if v == var then Lit val else v
          v@ChainId -> if v == var then Lit val else v
          v@BaseFee -> if v == var then Lit val else v
          e -> e

subAddrs :: Map (Expr EAddr) Addr -> Expr a -> Expr a
subAddrs model b = Map.foldlWithKey subAddr b model
  where
    subAddr :: Expr a -> Expr EAddr -> Addr -> Expr a
    subAddr a var val = mapExpr go a
      where
        go :: Expr a -> Expr a
        go = \case
          v@(SymAddr _) -> if v == var
                      then LitAddr val
                      else v
          e -> e

subBufs :: Map (Expr Buf) BufModel -> Expr a -> Err (Expr a)
subBufs model b = Map.foldlWithKey subBuf (Right b) model
  where
    subBuf :: Err (Expr a) -> Expr Buf -> BufModel -> Err (Expr a)
    subBuf x var val = case x of
      -- too long to flatten, but zero past what was written (e.g. calldata whose
      -- length the solver set to 2^64-1): substitute the written prefix, and
      -- the length separately, which is exact as reads past a ConcreteBuf are 0
      Right x' | Left _ <- forceFlattened val, Just (prefix, len) <- zeroTail val ->
        mapExprM (go' (ConcreteBuf prefix)) (mapExpr (subLen len) x')
      Right x' -> mapExprM go x'
      Left err -> Left err
      where
        go' :: Expr Buf -> Expr a -> Err (Expr a)
        go' prefix = \case
          c@(AbstractBuf _) | c == var -> Right prefix
          e -> Right e
        subLen :: W256 -> Expr a -> Expr a
        subLen len = \case
          BufLength c | c == var -> Lit len
          e -> e
        go :: Expr a -> Err (Expr a)
        go = \case
          c@(AbstractBuf _) -> case c == var of
            True -> case forceFlattened val of
              Right bs -> Right $ ConcreteBuf bs
              Left err -> Left $ show c <> " --- cannot flatten buffer: " <> err
            False -> Right c
          e -> Right e
        forceFlattened :: BufModel -> Err ByteString
        forceFlattened (Flat bs) = Right bs
        forceFlattened buf@(EVM.Types.Comp _) =  case SMT.collapse buf of
          Just k -> forceFlattened k
          Nothing -> Left $ show buf

-- | The written prefix and the length of a huge buffer model whose unwritten
-- bytes are zero, if the prefix is small enough to materialise. Only for
-- lengths that the simplifier never materialises (see 'Expr.copySlice').
zeroTail :: BufModel -> Maybe (ByteString, W256)
zeroTail (Flat _) = Nothing
zeroTail (EVM.Types.Comp c) = go c []
  where
    go (Base 0 len) ws
      | len >= 2 ^ (32 :: Int), all ((< len) . fst) ws, end <= 1_000_000 =
          Just (BS.pack [Map.findWithDefault 0 i m | i <- [0 .. end - 1]], len)
      where
        m = Map.fromList ws
        end = maybe 0 ((+ 1) . fst) (Map.lookupMax m)
    go (Write byte idx next) ws = go next ((idx, byte) : ws)
    go _ _ = Nothing

subStores :: Map (Expr EAddr) (Map W256 W256) -> Expr a -> Expr a
subStores model b = Map.foldlWithKey subStore b model
  where
    subStore :: Expr a -> Expr EAddr -> Map W256 W256 -> Expr a
    subStore x var val = mapExpr go x
      where
        go :: Expr a -> Expr a
        go = \case
          v@(AbstractStore a _)
            -> if a == var
               then ConcreteStore val
               else v
          e -> e
