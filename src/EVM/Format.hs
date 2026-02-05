{-# LANGUAGE ImplicitParams #-}

module EVM.Format
  ( formatExpr
  , formatSomeExpr
  , formatPartial
  , formatPartialDetailed
  , formatProp
  , formatState
  , formatError
  , contractNamePart
  , contractPathPart
  , showError
  , showTree
  , showTraceTree
  , showTraceTree'
  , showValues
  , prettyvmresult
  , prettyvmresults
  , showCall
  , showWordExact
  , showWordExplanation
  , parenthesise
  , showValue
  , textValues
  , showAbiValue
  , prettyIfConcreteWord
  , formatBytes
  , formatBinary
  , indent
  , strip0x
  , strip0x'
  , hexByteString
  , hexText
  , showVal
  ) where

import Prelude hiding (LT, GT)

import EVM (traceForest, traceForest', traceContext, cheatCode)
import EVM.ABI (getAbiSeq, parseTypeName, AbiValue(..), AbiType(..), SolError(..), Indexed(..), Event(..))
import EVM.Dapp (DappContext(..), DappInfo(..), findSrc, showTraceLocation)
import EVM.Expr qualified as Expr
import EVM.Solidity (SolcContract(..), Method(..), SrcMap (..), WarningData (..), SourceCache(..))
import EVM.Types
import EVM.Expr (maybeLitWordSimp, maybeLitAddrSimp)

import Control.Arrow ((>>>))
import Optics.Core
import Data.Binary.Get (runGetOrFail)
import Data.Bits (shiftR)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Base16 qualified as BS16
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Lazy (toStrict, fromStrict)
import Data.Char qualified as Char
import Data.DoubleWord (signedWord)
import Data.Foldable (toList)
import Data.List (isPrefixOf, sort)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Data.Text (Text, pack, unpack, intercalate, dropEnd, splitOn)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Tree.View (showTree)
import Data.Vector (Vector)
import Hexdump (prettyHex)
import Numeric (showHex)
import Witch (into, unsafeInto, tryFrom)
import Data.Vector.Storable qualified as VS
import Data.Sequence qualified as Seq

data Signedness = Signed | Unsigned
  deriving (Show)

showDec :: Signedness -> W256 -> Text
showDec signed (W256 w)
  | Right i' <- tryFrom i, LitAddr i' == cheatCode = "<hevm cheat address>"
  | (i :: Integer) == 2 ^ (256 :: Integer) - 1 = "MAX_UINT256"
  | otherwise = T.pack (show (i :: Integer))
  where
    i = case signed of
          Signed   -> into (signedWord w)
          Unsigned -> into w

showWordExact :: Integral i => i -> Text
showWordExact w = humanizeInteger (toInteger w)

showWordExplanation :: W256 -> DappInfo -> Text
showWordExplanation w _ | w > 0xffffffff = showDec Unsigned w
showWordExplanation w dapp =
  case Map.lookup (unsafeInto w) dapp.abiMap of
    Nothing -> showDec Unsigned w
    Just x  -> "keccak(\"" <> x.methodSignature <> "\")"

humanizeInteger :: (Num a, Integral a, Show a) => a -> Text
humanizeInteger =
  T.intercalate ","
  . reverse
  . map T.reverse
  . T.chunksOf 3
  . T.reverse
  . T.pack
  . show

prettyIfConcreteWord :: Expr EWord -> Text
prettyIfConcreteWord = \case
  Lit w -> T.pack $ "0x" <> showHex w ""
  w -> T.pack $ show w

showAbiValue :: (?context :: DappContext) => AbiValue -> Text
showAbiValue (AbiString bs) = formatBytes bs
showAbiValue (AbiBytesDynamic bs) = formatBytes bs
showAbiValue (AbiBytes _ bs) = formatBytes bs
showAbiValue (AbiAddress addr) = ppAddr (LitAddr addr) False
showAbiValue v = pack $ show v

textAbiValues :: (?context :: DappContext) => Vector AbiValue -> [Text]
textAbiValues vs = toList (fmap showAbiValue vs)

textValues :: (?context :: DappContext) => [AbiType] -> Expr Buf -> [Text]
textValues ts (ConcreteBuf bs) =
  case runGetOrFail (getAbiSeq (length ts) ts) (fromStrict bs) of
    Right (_, _, xs) -> textAbiValues xs
    Left (_, _, _)   -> [formatBinary bs]
textValues ts _ = fmap (const "<symbolic>") ts

textValue :: (?context :: DappContext) => AbiType -> Expr Buf -> Text
textValue ts (ConcreteBuf bs) =
  case runGetOrFail (getAbiSeq 1 [ts]) (fromStrict bs) of
    Right (_, _, xs) -> fromMaybe (internalError "impossible empty list") $ listToMaybe $ textAbiValues xs
    Left (_, _, _)   -> formatBinary bs
textValue _ _ = "<symbolic>"

parenthesise :: [Text] -> Text
parenthesise ts = "(" <> intercalate ", " ts <> ")"

showValues :: (?context :: DappContext) => [AbiType] -> Expr Buf -> Text
showValues ts b = parenthesise $ textValues ts b

showValue :: (?context :: DappContext) => AbiType -> Expr Buf -> Text
showValue t b = textValue t b

showCall :: (?context :: DappContext) => [AbiType] -> Expr Buf -> Text
showCall ts (ConcreteBuf bs) = showValues ts $ ConcreteBuf (BS.drop 4 bs)
showCall _ _ = "(<symbolic>)"

showError :: (?context :: DappContext) => Expr Buf -> Text
showError (ConcreteBuf bs) =
  let dappinfo = ?context.info
      bs4 = BS.take 4 bs
  in case Map.lookup (word bs4) dappinfo.errorMap of
      Just (SolError errName ts) -> errName <> " " <> showCall ts (ConcreteBuf bs)
      Nothing -> case bs4 of
                  -- Method ID for Error(string)
                  "\b\195y\160" -> showCall [AbiStringType] (ConcreteBuf bs)
                  -- Method ID for Panic(uint256)
                  "NH{q"        -> "Panic" <> parenthesise [formatBinary bs]
                  _             -> formatBinary bs
showError b = T.pack $ show b

-- the conditions under which bytes will be decoded and rendered as a string
isPrintable :: ByteString -> Bool
isPrintable =
  T.decodeUtf8' >>>
    either
      (const False)
      (T.all (\c-> Char.isPrint c && (not . Char.isControl) c))

formatBytes :: ByteString -> Text
formatBytes b =
  let (s, _) = BS.spanEnd (== 0) b
  in
    if isPrintable s
    then formatBString s
    else formatBinary b

-- a string that came from bytes, displayed with special quotes
formatBString :: ByteString -> Text
formatBString b = mconcat [ "«",  T.dropAround (=='"') (pack $ formatString b), "»" ]

formatBinary :: ByteString -> Text
formatBinary =
  (<>) "0x" . T.decodeUtf8 . toStrict . toLazyByteString . byteStringHex

formatSBinary :: Expr Buf -> Text
formatSBinary e = format $ Expr.concKeccakSimpExpr e
  where
    format (ConcreteBuf bs) = formatBinary bs
    format (AbstractBuf t) = "<" <> t <> " abstract buf>"
    format e2 = T.pack $ "Symbolic expression: " <> show e2

showTraceTree :: DappInfo -> VM t -> Text
showTraceTree dapp vm =
  let ?context = DappContext { info = dapp
                             , contracts = vm.env.contracts
                             , labels = vm.labels }
  in let forest = traceForest vm
         traces = fmap (fmap (unpack . showTrace)) forest
  in pack $ concatMap showTree traces

showTraceTree' :: DappInfo -> Expr End -> Text
showTraceTree' dapp leaf =
  let ?context = DappContext { info = dapp, contracts, labels }
  in let forest = traceForest' leaf
         traces = fmap (fmap (unpack . showTrace)) forest
  in pack $ concatMap showTree traces
  where TraceContext { contracts, labels } = traceContext leaf

showTrace :: (?context :: DappContext) => Trace -> Text
showTrace trace =
  let
    dapp = ?context.info
    pos =
      case showTraceLocation dapp trace of
        Left x -> " \x1b[1m" <> x <> "\x1b[0m"
        Right x -> " \x1b[1m(" <> x <> ")\x1b[0m"
  in case trace.tracedata of
    EventTrace _ bytes topics ->
      case topics of
        [] ->
          logn
        firstTopic:restTopics ->
          case maybeLitWordSimp firstTopic of
            Just topic ->
              case Map.lookup topic dapp.eventMap of
                Just (Event name _ argInfos) ->
                  showEvent name argInfos restTopics
                Nothing ->
                  case topics of
                    [_, t2, _, _] ->
                      -- check for ds-note logs.. possibly catching false positives
                      -- event LogNote(
                      --     bytes4   indexed  sig,
                      --     address  indexed  usr,
                      --     bytes32  indexed  arg1,
                      --     bytes32  indexed  arg2,
                      --     bytes             data
                      -- ) anonymous;
                      let
                        sig = unsafeInto $ shiftR topic 224 :: FunctionSelector
                        usr = case maybeLitWordSimp t2 of
                          Just w ->
                            pack $ show (unsafeInto w :: Addr)
                          Nothing  ->
                            "<symbolic>"
                      in
                        case Map.lookup sig dapp.abiMap of
                          Just m ->
                            lognote m.methodSignature usr
                          Nothing ->
                            logn
                    _ ->
                      logn
            Nothing ->
              logn
      where
        logn = mconcat
          [ "\x1b[36m"
          , "log" <> (pack (show (length topics)))
          , parenthesise ((map (pack . show) topics) ++ [formatSBinary bytes])
          , "\x1b[0m"
          ] <> pos

        showEvent eventName argInfos indexedTopics = mconcat
          [ "emit "
          , "\x1b[36m"
          , eventName
          , "\x1b[0m"
          , parenthesise (snd <$> sort (unindexedArgs <> indexedArgs))
          ] <> pos
          where
          -- We maintain the original position of event arguments since indexed
          -- and not indexed arguments can be interleaved.
          unindexedArgs :: [(Int, Text)]
          unindexedArgs =
            let (positions, names, abiTypes) = unzip3 (filterArgInfos NotIndexed)
            in zip positions (zipWith withName names (textValues abiTypes bytes))

          indexedArgs :: [(Int, Text)]
          indexedArgs =
            let (positions, names, abiTypes) = unzip3 (filterArgInfos Indexed)
            in zip positions (zipWith withName names (zipWith showTopic abiTypes indexedTopics))
            where
            showTopic :: AbiType -> Expr EWord -> Text
            showTopic abiType topic =
              case maybeLitWordSimp (Expr.concKeccakSimpExpr topic) of
                Just w -> textValue abiType (ConcreteBuf (word256Bytes w))
                _ -> "<symbolic>"

          withName :: Text -> Text -> Text
          withName "" value = value
          withName argName value = argName <> "=" <> value

          filterArgInfos :: Indexed -> [(Int, Text, AbiType)]
          filterArgInfos which =
            [ (i, argName, argType) | (i, (argName, argType, indexed)) <- zip [0..] argInfos
                                    , indexed == which
            ]

        lognote sig usr = mconcat
          [ "\x1b[36m"
          , "LogNote"
          , parenthesise [sig, usr, "..."]
          , "\x1b[0m"
          ] <> pos

    ErrorTrace e ->
      case e of
        Revert out ->
          "\x1b[91merror\x1b[0m " <> "Revert " <> showError out <> pos
        _ ->
          "\x1b[91merror\x1b[0m " <> pack (show e) <> pos

    ReturnTrace out (CallContext { abi = Just abi }) ->
      "← " <>
        case Map.lookup (unsafeInto abi) dapp.abiMap of
          Just m  ->
            case unzip m.output of
              ([], []) ->
                formatSBinary out
              (_, ts) ->
                showValues ts out
          Nothing ->
            formatSBinary out
    ReturnTrace out (CallContext {}) ->
      "← " <> formatSBinary out
    ReturnTrace out (CreationContext {}) ->
      let l = Expr.bufLength out
      in "← " <> formatExpr l <> " bytes of code"
    EntryTrace t ->
      t
    FrameTrace (CreationContext { address }) ->
      "create "
      <> ppAddr address True
      <> pos
    FrameTrace (CallContext { target, context, abi, calldata }) ->
      let calltype = if target == context
                     then "call "
                     else "delegatecall "
      in
      calltype
      <> ppAddr target False
      <> "::"
      <> case findSrcFromAddr target of
        Nothing ->
          case Map.lookup (unsafeInto (fromMaybe 0x00 abi)) dapp.abiMap of
            Just m  ->
              "\x1b[1m"
              <> m.name
              <> "\x1b[0m"
              <> showCall (catMaybes (getAbiTypes m.methodSignature)) calldata
            Nothing ->
              formatSBinary calldata
          <> pos

        Just solc ->
          maybe "[fallback function]"
                 (fromMaybe "[unknown method]" . maybeAbiName solc)
                 abi
          <> maybe ("(" <> formatSBinary calldata <> ")")
                   (\x -> showCall (catMaybes x) calldata)
                   (abi >>= fmap getAbiTypes . maybeAbiName solc)
          <> pos
    where
    findSrcFromAddr addr = do
      contract <- Map.lookup addr ?context.contracts
      findSrc contract ?context.info

ppAddr :: (?context :: DappContext) => Expr EAddr -> Bool -> Text
ppAddr addr alwaysShowAddr =
  let
    sourceName = case Map.lookup addr ?context.contracts of
      Nothing ->
        case addr of
          LitAddr 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D -> Just "HEVM"
          _ -> Nothing
      Just contract ->
        case (findSrc contract ?context.info) of
          Just x -> Just (contractNamePart x.contractName)
          Nothing -> Nothing
    label = case do litAddr <- maybeLitAddrSimp addr
                    Map.lookup litAddr ?context.labels of
              Nothing -> ""
              Just l -> "[" <> "\x1b[1m" <> l <> "\x1b[0m" <> "]"
    name = maybe "" (\n -> "\x1b[1m" <> n <> "\x1b[0m") sourceName <> label
  in
    if name == "" then
      formatAddr addr
    else if alwaysShowAddr then
      name <> "@" <> formatAddr addr
    else
      name

formatAddr :: Expr EAddr -> Text
formatAddr = \case
  LitAddr a -> pack (show a)
  SymAddr a -> "symbolic(" <> a <> ")"
  GVar _ -> internalError "Unexpected GVar"

getAbiTypes :: Text -> [Maybe AbiType]
getAbiTypes abi = map (parseTypeName mempty) types
  where
    types =
      filter (/= "") $
        splitOn "," (dropEnd 1 (last (splitOn "(" abi)))

maybeAbiName :: SolcContract -> W256 -> Maybe Text
maybeAbiName solc abi = Map.lookup (unsafeInto abi) solc.abiMap <&> (.methodSignature)

contractNamePart :: Text -> Text
contractNamePart x = T.split (== ':') x !! 1

contractPathPart :: Text -> Text
contractPathPart x = T.split (== ':') x !! 0

prettyError :: EvmError -> String
prettyError = \case
  IllegalOverflow -> "Illegal overflow"
  SelfDestruction -> "Self destruct"
  StackLimitExceeded -> "Stack limit exceeded"
  InvalidMemoryAccess -> "Invalid memory access"
  BadJumpDestination -> "Bad jump destination"
  StackUnderrun -> "Stack underrun"
  BalanceTooLow a b -> "Balance too low. value: " <> show a <> " balance: " <> show b
  UnrecognizedOpcode a -> "Unrecognized opcode: " <> show a
  Revert (ConcreteBuf msg) -> "Revert: " <> (T.unpack $ formatBinary msg)
  Revert _ -> "Revert: <symbolic>"
  OutOfGas a b -> "Out of gas: have: " <> show a <> " need: " <> show b
  StateChangeWhileStatic -> "State change while static"
  CallDepthLimitReached -> "Call depth limit reached"
  MaxCodeSizeExceeded a b -> "Max code size exceeded: max: " <> show a <> " actual: " <> show b
  MaxInitCodeSizeExceeded a b -> "Max init code size exceeded: max: " <> show a <> " actual: " <> show b
  InvalidFormat -> "Invalid Format"
  PrecompileFailure -> "Precompile failure"
  NonexistentPrecompile a -> "Precompile at address " <> show a <> " does not exist"
  ReturnDataOutOfBounds -> "Return data out of bounds"
  NonceOverflow -> "Nonce overflow"
  BadCheatCode reason a -> "Bad cheat code: " <>  reason <> " sig: " <> show a
  NonexistentFork a -> "Fork ID does not exist: " <> show a
  AssumeCheatFailed -> "Assume failed"

prettyvmresult :: Expr End -> String
prettyvmresult (Failure _ _ (Revert (ConcreteBuf ""))) = "Revert"
prettyvmresult (Success _ _ (ConcreteBuf msg) _) =
  if BS.null msg
  then "Stop"
  else "Return: " <> show (ByteStringS msg)
prettyvmresult (Success _ _ _ _) =
  "Return: <symbolic>"
prettyvmresult (Failure _ _ err) = prettyError err
prettyvmresult (Partial _ _ p) = T.unpack $ formatPartial p
prettyvmresult r = internalError $ "Invalid result: " <> show r

prettyvmresults :: [Expr End] -> String
prettyvmresults results =
  T.unpack $ indent 2 $ T.unlines $ zipWith (\i r -> T.pack ("Result " <> show (i :: Integer) <> ": " <> prettyvmresult r)) [0..] results

indent :: Int -> Text -> Text
indent n = rstrip . T.unlines . fmap (T.replicate n (T.pack [' ']) <>) . T.lines

rstrip :: Text -> Text
rstrip = T.reverse . T.dropWhile (=='\n') . T.reverse

formatError :: EvmError -> Text
formatError = \case
  Revert buf -> T.unlines
    [ "(Revert"
    , indent 2 $ formatExpr buf
    , ")"
    ]
  e -> T.pack $ show e

formatPartial :: PartialExec -> Text
formatPartial = \case
  UnexpectedSymbolicArg pc addr opcode msg args -> T.unlines
    [ "Unexpected symbolic arguments to opcode."
    , indent 2 $ T.unlines
      [ "msg: " <> T.pack (show msg)
      , "contract addr: " <> pack (show addr)
      , "program counter: " <> T.pack (show pc)
      , "opcode: " <> T.pack opcode
      , "arguments: "
      , indent 2 $ T.unlines . fmap formatSomeExpr $ args
      ]
    ]
  MaxIterationsReached pc addr -> T.unlines
    ["Max iterations reached."
    , indent 2 $ T.unlines
      [ "contract addr: " <> T.pack (show addr)
      , "program counter: " <> T.pack (show pc)
      ]
    ]
  JumpIntoSymbolicCode pc addr idx -> T.unlines
    ["Encountered a jump into a symbolic code region."
    , indent 2 $ T.unlines
      [ "contract addr: " <> T.pack (show addr)
      , "program counter: " <> T.pack (show pc)
      , "jump dst: " <> pack (show idx)
      ]
    ]
  CheatCodeMissing pc addr selector -> T.unlines
    [ "Cheat code not recognized."
    , indent 2 $ T.unlines
      [ "contract addr: " <> T.pack (show addr)
      , "program counter: " <> T.pack (show pc)
      , "function selector: " <> T.pack (show selector)
      ]
    ]
  BranchTooDeep pc addr -> T.unlines
    ["Branch too deep."
    , indent 2 $ T.unlines
      [ "contract addr: " <> pack (show addr)
      , "program counter: " <> pack (show pc)]
    ]

  PrecompileMissing pc addr preAddr -> T.unlines
    ["Precompile does not exist"
    , indent 2 $ T.unlines
      [ "precompile addr: " <> pack (show preAddr)
      , "contract addr: " <> pack (show addr)
      , "program counter: " <> pack (show pc)]
    ]


formatPartialDetailed :: Maybe (WarningData t) -> PartialExec -> Text
formatPartialDetailed warnData p =
  let toTxt addr pc = pack $ getSrcInfo warnData addr pc
  in case p of
    UnexpectedSymbolicArg {..} -> "Unexpected symbolic arguments to opcode: " <> T.pack opcode <> toTxt addr pc
    MaxIterationsReached {..}  -> "Max iterations reached" <> toTxt addr pc
    JumpIntoSymbolicCode {..}  -> "Encountered a jump into a symbolic code" <> toTxt addr pc
    CheatCodeMissing {..}      -> "Cheat code not recognized: " <> T.pack (show selector) <> toTxt addr pc
    PrecompileMissing {..}     -> "Precompile at address " <> pack (show preAddr) <> " does not exist, called from" <> toTxt addr pc
    BranchTooDeep {..}         -> "Branches too deep" <> toTxt addr pc

getSrcInfo :: Maybe (WarningData t) -> Expr EAddr -> Int -> String
getSrcInfo Nothing addr pc = " at addr: " <> show addr <> " at pc: " <> show pc
getSrcInfo (Just dat) addr pc = fromMaybe (getSrcInfo Nothing addr pc) $ do
  contr <- Map.lookup addr dat.vm.env.contracts
  pcOp <- contr.opIxMap VS.!? pc
  sMap <- Seq.lookup pcOp dat.solcContr.runtimeSrcmap
  (fname, fcontent) <- Map.lookup sMap.file dat.sourceCache.files
  let eols = BS.count 10 $ BS.take sMap.offset fcontent  -- 10 is \n
  let str = " in file \"" <> fname <> "\" on line " <> show (eols+1)
  case (BS.length fcontent > (sMap.offset + sMap.length)) of
    False -> pure str
    True  -> let relevant = BS.take sMap.length $ BS.drop sMap.offset fcontent
      in pure $ str <> " : " <> show relevant

formatSomeExpr :: SomeExpr -> Text
formatSomeExpr (SomeExpr e) = formatExpr $ Expr.simplify e

formatState :: Map.Map (Expr EAddr) (Expr EContract) -> Text
formatState store = indent 2 $ T.unlines (fmap (\(k,v) ->
              T.unlines
                [ formatExpr k <> ":"
                , indent 2 $ formatExpr v
                ]) (Map.toList store))

formatExpr :: Expr a -> Text
formatExpr = go
  where
    go :: Expr a -> Text
    go x = T.stripEnd $ case x of
      Lit w -> T.pack $ show (into w :: Integer)
      (Var v) -> "(Var " <> T.pack (show v) <> ")"
      (GVar v) -> "(GVar " <> T.pack (show v) <> ")"
      LitByte w -> T.pack $ show w

      Success asserts _ buf store -> T.unlines
        [ "(Success"
        , indent 2 $ T.unlines
          [ "Data:" , indent 2 $ formatExpr buf
          , ""
          , "State:", formatState store
          , "Assertions:", indent 2 . T.unlines $ fmap formatProp asserts
          ]
        , ")"
        ]
      Partial asserts _ err -> T.unlines
        [ "(Partial"
        , indent 2 $ T.unlines
          [ "Reason:"
          , indent 2 $ formatPartial err
          , "Assertions:"
          , indent 2 . T.unlines $ fmap formatProp asserts
          ]
        , ")"
        ]
      Failure asserts _ err -> T.unlines
        [ "(Failure"
        , indent 2 $ T.unlines
          [ "Error:"
          , indent 2 $ formatError err
          , "Assertions:"
          , indent 2 . T.unlines $ fmap formatProp asserts
          ]
        , ")"
        ]

      IndexWord idx val -> T.unlines
        [ "(IndexWord"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "val: "
          , indent 2 $ formatExpr val
          ]
        , ")"
        ]
      ReadWord idx buf -> T.unlines
        [ "(ReadWord"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "buf: "
          , indent 2 $ formatExpr buf
          ]
        , ")"
        ]
      ReadByte idx buf -> T.unlines
        [ "(ReadByte"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "buf: "
          , indent 2 $ formatExpr buf
          ]
        , ")"
        ]

      Add a b -> fmt "Add" [a, b]
      Sub a b -> fmt "Sub" [a, b]
      Mul a b -> fmt "Mul" [a, b]
      Div a b -> fmt "Div" [a, b]
      SDiv a b -> fmt "SDiv" [a, b]
      Mod a b -> fmt "Mod" [a, b]
      SMod a b -> fmt "SMod" [a, b]
      AddMod a b c -> fmt "AddMod" [a, b, c]
      MulMod a b c -> fmt "MulMod" [a, b, c]
      Exp a b -> fmt "Exp" [a, b]
      SEx a b -> fmt "SEx" [a, b]
      Min a b -> fmt "Min" [a, b]
      Max a b -> fmt "Max" [a, b]

      LT a b -> fmt "LT" [a, b]
      GT a b -> fmt "GT" [a, b]
      LEq a b -> fmt "LEq" [a, b]
      GEq a b -> fmt "GEq" [a, b]
      SLT a b -> fmt "SLT" [a, b]
      SGT a b -> fmt "SGT" [a, b]
      Eq a b -> fmt "Eq" [a, b]
      EqByte a b -> fmt "EqByte" [a, b]
      IsZero a -> fmt "IsZero" [a]
      ITE c t el -> fmt "ITE" [c, t, el]

      And a b -> fmt "And" [a, b]
      Or a b -> fmt "Or" [a, b]
      Xor a b -> fmt "Xor" [a, b]
      Not a -> fmt "Not" [a]
      SHL a b -> fmt "SHL" [a, b]
      SHR a b -> fmt "SHR" [a, b]
      SAR a b -> fmt "SAR" [a, b]

      e@Origin -> T.pack (show e)
      e@Coinbase -> T.pack (show e)
      e@Timestamp -> T.pack (show e)
      e@BlockNumber -> T.pack (show e)
      e@PrevRandao -> T.pack (show e)
      e@GasLimit -> T.pack (show e)
      e@ChainId -> T.pack (show e)
      e@BaseFee -> T.pack (show e)
      e@TxValue -> T.pack (show e)
      e@(Gas {}) -> "(" <> T.pack (show e) <> ")"

      BlockHash a -> fmt "BlockHash" [a]
      Balance a -> fmt "Balance" [a]
      CodeSize a -> fmt "CodeSize" [a]
      CodeHash a -> fmt "CodeHash" [a]


      JoinBytes zero one two three four five six seven eight nine
        ten eleven twelve thirteen fourteen fifteen sixteen seventeen
        eighteen nineteen twenty twentyone twentytwo twentythree twentyfour
        twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone -> fmt "JoinBytes"
        [ zero
        , one
        , two
        , three
        , four
        , five
        , six
        , seven
        , eight
        , nine
        , ten
        , eleven
        , twelve
        , thirteen
        , fourteen
        , fifteen
        , sixteen
        , seventeen
        , eighteen
        , nineteen
        , twenty
        , twentyone
        , twentytwo
        , twentythree
        , twentyfour
        , twentyfive
        , twentysix
        , twentyseven
        , twentyeight
        , twentynine
        , thirty
        , thirtyone
        ]

      LogEntry addr dat topics -> T.unlines
        [ "(LogEntry"
        , indent 2 $ T.unlines
          [ "addr:"
          , indent 2 $ formatExpr addr
          , "data:"
          , indent 2 $ formatExpr dat
          , "topics:"
          , indent 2 . T.unlines $ fmap formatExpr topics
          ]
        , ")"
        ]

      a@(SymAddr {}) -> "(" <> T.pack (show a) <> ")"
      LitAddr a -> T.pack (show a)
      WAddr a -> fmt "WAddr" [a]

      BufLength b -> fmt "BufLength" [b]

      C code store tStore bal nonce -> T.unlines
        [ "(Contract"
        , indent 2 $ T.unlines
          [ "code:"
          , indent 2 $ formatCode code
          , "storage:"
          , indent 2 $ formatExpr store
          , "tStorage:"
          , indent 2 $ formatExpr tStore
          , "balance:"
          , indent 2 $ formatExpr bal
          , "nonce:"
          , indent 2 $ formatNonce nonce
          ]
        , ")"
        ]

      -- Stores
      SLoad slot storage -> T.unlines
        [ "(SLoad"
        , indent 2 $ T.unlines
          [ "slot:"
          , indent 2 $ formatExpr slot
          , "storage:"
          , indent 2 $ formatExpr storage
          ]
        , ")"
        ]
      SStore slot val prev -> T.unlines
        [ "(SStore"
        , indent 2 $ T.unlines
          [ "slot:"
          , indent 2 $ formatExpr slot
          , "val:"
          , indent 2 $ formatExpr val
          , "store:"
          , indent 2 $ formatExpr prev
          ]
        , ")"
        ]
      AbstractStore a idx ->
        "(AbstractStore " <> formatExpr a <> " " <> T.pack (show idx) <> ")"
      ConcreteStore s -> if null s
        then "(ConcreteStore <empty>)"
        else T.unlines
          [ "(ConcreteStore"
          , indent 2 $ T.unlines
            [ "vals:"
            , indent 2 $ T.unlines $ fmap (T.pack . show) $ Map.toList s
            ]
          , ")"
          ]

      -- Buffers

      CopySlice srcOff dstOff size src dst -> T.unlines
        [ "(CopySlice"
        , indent 2 $ T.unlines
          [ "srcOffset: " <> formatExpr srcOff
          , "dstOffset: " <> formatExpr dstOff
          , "size:      " <> formatExpr size
          , "src:"
          , indent 2 $ formatExpr src
          , "dst:"
          , indent 2 $ formatExpr dst
          ]
        , ")"
        ]
      WriteWord idx val buf -> T.unlines
        [ "(WriteWord"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "val:"
          , indent 2 $ formatExpr val
          , "buf:"
          , indent 2 $ formatExpr buf
          ]
        , ")"
        ]
      WriteByte idx val buf -> T.unlines
        [ "(WriteByte"
        , indent 2 $ T.unlines
          [ "idx: " <> formatExpr idx
          , "val: " <> formatExpr val
          , "buf: " <> formatExpr buf
          ]
        , ")"
        ]
      ConcreteBuf bs -> case bs of
        "" -> "(ConcreteBuf \"\")"
        _ -> T.unlines
          [ "(ConcreteBuf"
          , indent 2 $ T.pack $ prettyHex bs
          , ")"
          ]
      b@(AbstractBuf _) -> "(" <> T.pack (show b) <> ")"

      -- Hashes
      Keccak b -> fmt "Keccak" [b]
      SHA256 b -> fmt "SHA256" [b]
      where
        fmt nm args = T.unlines
          [ "(" <> nm
          , indent 2 $ T.unlines $ fmap formatExpr args
          , ")"
          ]

formatProp :: Prop -> Text
formatProp x = T.stripEnd $ case x of
  PEq a b -> fmt "PEq" [a, b]
  PLT a b -> fmt "PLT" [a, b]
  PGT a b -> fmt "PGT" [a, b]
  PGEq a b -> fmt "PGEq" [a, b]
  PLEq a b -> fmt "PLEq" [a, b]
  PNeg a -> fmt' "PNeg" [a]
  PAnd a b -> fmt' "PAnd" [a, b]
  POr a b -> fmt' "POr" [a, b]
  PImpl a b -> fmt' "PImpl" [a, b]
  PBool a -> T.pack (show a)
  where
    fmt nm args = T.unlines
      [ "(" <> nm
      , indent 2 $ T.unlines $ fmap formatExpr args
      , ")"
      ]
    fmt' nm args = T.unlines
      [ "(" <> nm
      , indent 2 $ T.unlines $ fmap formatProp args
      , ")"
      ]

formatNonce :: Maybe W64 -> Text
formatNonce = \case
  Just w -> T.pack $ show w
  Nothing -> "symbolic"

formatCode :: ContractCode -> Text
formatCode = \case
  UnknownCode _ -> "Unknown"
  InitCode c d -> T.unlines
    [ "(InitCode"
    , indent 2 $ T.unlines
      [ "code: " <> T.pack (bsToHex c)
      , "data: " <> formatExpr d
      ]
    , ")"
    ]
  RuntimeCode (ConcreteRuntimeCode c)
    -> "(RuntimeCode " <> T.pack (bsToHex c) <> ")"
  RuntimeCode (SymbolicRuntimeCode bs)
    -> "(RuntimeCode " <> T.pack (show (fmap formatExpr bs)) <> ")"


strip0x :: ByteString -> ByteString
strip0x bs = if "0x" `Char8.isPrefixOf` bs then Char8.drop 2 bs else bs

strip0x' :: String -> String
strip0x' s = if "0x" `isPrefixOf` s then drop 2 s else s

hexByteString :: ByteString -> Maybe ByteString
hexByteString bs =
  case BS16.decodeBase16Untyped bs of
    Right x -> pure x
    Left _ -> Nothing

hexText :: Text -> ByteString
hexText t =
  case BS16.decodeBase16Untyped (T.encodeUtf8 (T.drop 2 t)) of
    Right x -> x
    _ -> internalError $ "invalid hex bytestring " ++ show t

showVal :: AbiValue -> Text
showVal (AbiBytes _ bs) = formatBytes bs
showVal (AbiAddress addr) = T.pack  . show $ addr
showVal v = T.pack . show $ v
