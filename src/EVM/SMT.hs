{- |
    Module: EVM.SMT
    Description: Utilities for building and executing SMT queries from Expr instances
-}
module EVM.SMT
(
  module EVM.SMT.Types,
  module EVM.SMT.SMTLIB,

  collapse,
  getVar,
  formatSMT2,
  declareIntermediates,
  assertProps,
  assertPropsHelperWith,
  decompose,
  exprToSMT,
  exprToSMTWith,
  encodeConcreteStore,
  zero,
  one,
  sp,
  propToSMT,
  propToSMTWith,
  parseVar,
  parseEAddr,
  parseBlockCtx,
  parseTxCtx,
  getAddrs,
  getVars,
  queryMaxReads,
  getBufs,
  getStore
) where

import Prelude hiding (LT, GT, Foldable(..))

import Control.Monad
import Control.Monad.Trans.Maybe (hoistMaybe)
import Data.Containers.ListUtils (nubOrd, nubInt)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Foldable (Foldable(..))
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromJust, fromMaybe, isJust, listToMaybe)
import Data.Either.Extra (fromRight')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Word (Word8)
import Data.Text.Lazy (Text)
import Data.Text qualified as TS
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.Builder
import qualified Data.Text.Lazy.Builder.Int (decimal)
import Language.SMT2.Parser (getValueRes, parseCommentFreeFileMsg, parseString, specConstant)
import Language.SMT2.Syntax (Symbol, SpecConstant(..), GeneralRes(..), Term(..), QualIdentifier(..), Identifier(..), Sort(..), Index(..), VarBinding(..))
import Numeric (readHex, readBin)
import Witch (into, unsafeInto)
import EVM.Format (formatProp)

import EVM.CSE
import EVM.Expr (writeByte, bufLengthEnv, bufLength, minLength, inRange)
import EVM.Expr qualified as Expr
import EVM.Keccak (keccakAssumptions, concreteKeccaks, findKeccakPropsExprs)
import EVM.Traversals
import EVM.Types
import EVM.Effects
import EVM.SMT.Types
import EVM.SMT.SMTLIB


-- ** Encoding ** ----------------------------------------------------------------------------------


-- | Attempts to collapse a compressed buffer representation down to a flattened one
collapse :: BufModel -> Maybe BufModel
collapse model = case toBuf model of
  Just (ConcreteBuf b) -> Just $ Flat b
  _ -> Nothing
  where
    toBuf (Comp (Base b sz)) | sz <= 120_000_000 = Just . ConcreteBuf $ BS.replicate (unsafeInto sz) b
    toBuf (Comp (Write b idx next)) = fmap (writeByte (Lit idx) (LitByte b)) (toBuf $ Comp next)
    toBuf (Flat b) = Just . ConcreteBuf $ b
    toBuf _ = Nothing

getVar :: SMTCex -> TS.Text -> W256
getVar cex name = fromJust $ Map.lookup (Var name) cex.vars

formatSMT2 :: SMT2 -> Text
formatSMT2 (SMT2 (SMTScript entries) _ ps) = expr <> smt2
 where
 expr = T.concat [T.singleton ';', T.replace "\n" "\n;" $ T.pack . TS.unpack $  TS.unlines (fmap formatProp ps)]
 smt2 = T.unlines (fmap toText entries)

-- | Reads all intermediate variables from the builder state and produces SMT declaring them as constants
declareIntermediates :: BufEnv -> StoreEnv -> Err [SMTEntry]
declareIntermediates = declareIntermediatesWith ConcreteDivision

declareIntermediatesWith :: DivEncoding -> BufEnv -> StoreEnv -> Err [SMTEntry]
declareIntermediatesWith enc bufs stores = do
  let encSs = Map.mapWithKey encodeStore stores
      encBs = Map.mapWithKey encodeBuf bufs
  snippets <- sequence $ Map.elems $ encSs <> encBs
  let decls = concat snippets
  pure $ (SMTComment "intermediate buffers & stores") : decls
  where
    encodeBuf n expr = do
      buf <- exprToSMTWith enc expr
      bufLen <- encodeBufLen n expr
      pure [SMTCommand ("(define-fun buf" <> (Data.Text.Lazy.Builder.Int.decimal n) <> "() Buf " <> buf <> ")\n"), bufLen]
    encodeBufLen n expr = do
      bufLen <- exprToSMTWith enc (bufLengthEnv bufs True expr)
      pure $ SMTCommand ("(define-fun buf" <> (Data.Text.Lazy.Builder.Int.decimal n) <>"_length () (_ BitVec 256) " <> bufLen <> ")")
    encodeStore n expr = do
      storage <- exprToSMTWith enc expr
      pure [SMTCommand ("(define-fun store" <> (Data.Text.Lazy.Builder.Int.decimal n) <> " () Storage " <> storage <> ")")]

-- simplify to rewrite sload/sstore combos
-- notice: it is VERY important not to concretize early, because Keccak assumptions
--         need unconcretized Props
assertProps :: Config -> [Prop] -> Err SMT2
assertProps conf ps =
  if not conf.simp then assertPropsHelper False ps
  else assertPropsHelper True (decompose conf ps)

decompose :: Config -> [Prop] -> [Prop]
decompose conf props = if conf.decomposeStorage && safeExprs && safeProps
                    then fromMaybe props (mapM (mapPropM Expr.decomposeStorage) props)
                    else props
  where
    -- All in these lists must be a `Just ()` or we cannot decompose
    safeExprs = all (isJust . mapPropM_ Expr.safeToDecompose) props
    safeProps = all Expr.safeToDecomposeProp props

-- Note: we need a version that does NOT call simplify,
-- because we make use of it to verify the correctness of our simplification
-- passes through property-based testing.
assertPropsHelper :: Bool -> [Prop]  -> Err SMT2
assertPropsHelper simp = assertPropsHelperWith ConcreteDivision simp []

assertPropsHelperWith :: DivEncoding -> Bool -> [SMTEntry] -> [Prop]  -> Err SMT2
assertPropsHelperWith divEnc simp extraDecls psPreConc = do
 encs <- mapM (propToSMTWith divEnc) psElim
 intermediates <- declareIntermediatesWith divEnc bufs stores
 readAssumes' <- readAssumes
 keccakAssertions' <- keccakAssertions
 frameCtxs <- (declareFrameContext . nubOrd $ foldl' (<>) [] frameCtx)
 blockCtxs <- (declareBlockContext . nubOrd $ foldl' (<>) [] blockCtx)
 pure $ prelude
  <> SMT2 (SMTScript extraDecls) mempty mempty
  <> SMT2 (SMTScript (declareAbstractStores abstractStores)) mempty mempty
  <> declareConstrainAddrs addresses
  <> (declareBufs toDeclarePsElim bufs stores)
  <> (declareVars . nubOrd $ foldl' (<>) [] allVars)
  <> frameCtxs
  <> blockCtxs
  <> SMT2 (SMTScript intermediates) mempty mempty
  <> SMT2 (SMTScript keccakAssertions') mempty mempty
  <> SMT2 (SMTScript readAssumes') mempty mempty
  <> SMT2 (SMTScript gasOrder) mempty mempty
  <> SMT2 (SMTScript (fmap (\p -> SMTCommand("(assert " <> p <> ")")) encs)) (cexInfo storageReads) ps

  where
    ps = if simp then Expr.concKeccakSimpProps psPreConc else Expr.concKeccakProps psPreConc
    (psElim, bufs, stores) = eliminateProps ps

    -- Props storing info that need declaration(s)
    toDeclarePs     = ps <> keccAssump <> keccComp
    toDeclarePsElim = psElim <> keccAssump <> keccComp

    -- vars, frames, and block contexts in need of declaration
    allVars = fmap referencedVars toDeclarePsElim <> fmap referencedVars bufVals <> fmap referencedVars storeVals
    frameCtx = fmap referencedFrameContext toDeclarePsElim <> fmap referencedFrameContext bufVals <> fmap referencedFrameContext storeVals
    blockCtx = fmap referencedBlockContext toDeclarePsElim <> fmap referencedBlockContext bufVals <> fmap referencedBlockContext storeVals
    gasOrder = enforceGasOrder psPreConc

    -- Buf, Storage, etc. declarations needed
    bufVals = Map.elems bufs
    storeVals = Map.elems stores
    storageReads = mconcat $ fmap findStorageReads toDeclarePs
    abstractStores = Set.toList $ Set.unions (fmap referencedAbstractStores toDeclarePs)
    addresses = Set.toList $ Set.unions (fmap referencedAddrs toDeclarePs)

    -- Keccak assertions: concrete values, distance between pairs, injectivity, etc.
    --      This will make sure concrete values of Keccak are asserted, if they can be computed (i.e. can be concretized)
    concreteKecc = concreteKeccaks psPreConc
    allKeccaks = (findKeccakPropsExprs psElim bufVals storeVals) <> Set.map (Keccak . fst) concreteKecc
    keccAssump = keccakAssumptions $ Set.toList allKeccaks
    keccComp = [(PEq (Lit l) (Keccak buf)) | (buf, l) <- Set.toList concreteKecc]
    keccakAssertions = do
      assumps <- mapM (assertSMTWith divEnc) keccAssump
      comps <- mapM (assertSMTWith divEnc) keccComp
      pure $ ((SMTComment "keccak assumptions") : assumps) <> ((SMTComment "keccak computations") : comps)

    -- assert that reads beyond size of buffer & storage is zero
    readAssumes = do
      assumps <- mapM (assertSMTWith divEnc) $ assertReads psElim bufs stores
      pure (SMTComment "read assumptions" : assumps)

    cexInfo :: StorageReads -> CexVars
    cexInfo a = mempty { storeReads = a }


referencedAbstractStores :: TraversableTerm a => a -> Set Builder
referencedAbstractStores term = foldTerm go mempty term
  where
    go = \case
      AbstractStore s idx -> Set.singleton (storeName s idx)
      _ -> mempty

referencedAddrs :: TraversableTerm a => a -> Set Builder
referencedAddrs term = foldTerm go mempty term
  where
    go = \case
      SymAddr a -> Set.singleton (formatEAddr (SymAddr a))
      _ -> mempty

referencedBufs :: TraversableTerm a => a -> [Builder]
referencedBufs expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [Builder]
    go = \case
      AbstractBuf s -> [fromText s]
      _ -> []

referencedVars :: TraversableTerm a => a -> [Builder]
referencedVars expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [Builder]
    go = \case
      Var s -> [fromText s]
      _ -> []

referencedFrameContext :: TraversableTerm a => a -> [(Builder, [Prop])]
referencedFrameContext expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [(Builder, [Prop])]
    go = \case
      o@TxValue -> [(fromRight' $ exprToSMT o, [])]
      o@(Balance _) -> [(fromRight' $ exprToSMT o, [PLT o (Lit $ 2 ^ (96 :: Int))])]
      o@(Gas _ _) -> [(fromRight' $ exprToSMT o, [])]
      o@(CodeHash (LitAddr _)) -> [(fromRight' $ exprToSMT o, [])]
      _ -> []

referencedBlockContext :: TraversableTerm a => a -> [(Builder, [Prop])]
referencedBlockContext expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [(Builder, [Prop])]
    go = \case
      Origin -> [("origin", [inRange 160 Origin])]
      Coinbase -> [("coinbase", [inRange 160 Coinbase])]
      Timestamp -> [("timestamp", [])]
      BlockNumber -> [("blocknumber", [])]
      PrevRandao -> [("prevrandao", [])]
      GasLimit -> [("gaslimit", [])]
      ChainId -> [("chainid", [])]
      BaseFee -> [("basefee", [])]
      _ -> []

-- | This function overapproximates the reads from the abstract
-- storage. Potentially, it can return locations that do not read a
-- slot directly from the abstract store but from subsequent writes on
-- the store (e.g, SLoad addr idx (SStore addr idx val AbstractStore)).
-- However, we expect that most of such reads will have been
-- simplified away.
findStorageReads :: Prop -> StorageReads
findStorageReads p = foldProp go mempty p
  where
    go :: Expr a -> StorageReads
    go = \case
      SLoad slot store | baseIsAbstractStore store -> case Expr.getAddr store of
          Nothing -> internalError $ "could not extract address from: " <> show store
          Just address -> StorageReads $ Map.singleton (address, Expr.getLogicalIdx store) (Set.singleton slot)
      _ -> mempty

    baseIsAbstractStore :: Expr 'Storage -> Bool
    baseIsAbstractStore (AbstractStore _ _) = True
    baseIsAbstractStore (ConcreteStore _) = False
    baseIsAbstractStore (SStore _ _ base) = baseIsAbstractStore base
    baseIsAbstractStore (GVar _) = internalError "Unexpected GVar"

findBufferAccess :: TraversableTerm a => [a] -> [(Expr EWord, Expr EWord, Expr Buf)]
findBufferAccess = foldl' (foldTerm go) mempty
  where
    go :: Expr a -> [(Expr EWord, Expr EWord, Expr Buf)]
    go = \case
      ReadWord idx buf -> [(idx, Lit 32, buf)]
      ReadByte idx buf -> [(idx, Lit 1, buf)]
      CopySlice srcOff _ size src _  -> [(srcOff, size, src)]
      _ -> mempty

-- | Asserts that buffer reads beyond the size of the buffer are equal
-- to zero. Looks for buffer reads in the a list of given predicates
-- and the buffer and storage environments.
assertReads :: [Prop] -> BufEnv -> StoreEnv -> [Prop]
assertReads props benv senv = nubOrd $ concatMap assertRead allReads
  where
    assertRead :: (Expr EWord, Expr EWord, Expr Buf) -> [Prop]
    assertRead (_, Lit 0, _) = []
    assertRead (idx, Lit sz, buf) = [PImpl (PGEq (Expr.add idx $ Lit offset) (bufLength buf)) (PEq (ReadByte (Expr.add idx $ Lit offset) buf) (LitByte 0)) | offset <- [(0::W256).. sz-1]]
    assertRead (_, _, _) = internalError "Cannot generate assertions for accesses of symbolic size"

    allReads = filter keepRead $ nubOrd $ findBufferAccess props <> findBufferAccess (Map.elems benv) <> findBufferAccess (Map.elems senv)

    -- discard constraints if we can statically determine that read is less than the buffer length
    keepRead (Lit idx, Lit size, buf) =
      case minLength benv buf of
        Just l | into (idx + size) <= l -> False
        _ -> True
    keepRead _ = True

-- | Finds the maximum read index for each abstract buffer in the input props
discoverMaxReads :: [Prop] -> BufEnv -> StoreEnv -> Map Text (Expr EWord)
discoverMaxReads props benv senv = bufMap
  where
    allReads = nubOrd $ findBufferAccess props <> findBufferAccess (Map.elems benv) <> findBufferAccess (Map.elems senv)
    -- we can have buffers that are not read from but are still mentioned via BufLength in some branch condition
    -- we assign a default read hint of 4 to start with in these cases (since in most cases we will need at least 4 bytes to produce a counterexample)
    allBufs = Map.fromList . fmap (, Lit 4) . fmap toLazyText . nubOrd . concat $ fmap referencedBufs props <> fmap referencedBufs (Map.elems benv) <> fmap referencedBufs (Map.elems senv)

    bufMap = Map.unionWith Expr.max (foldl' addBound mempty allReads) allBufs

    addBound m (idx, size, buf) =
      case baseBuf buf of
        AbstractBuf b -> Map.insertWith Expr.max (T.fromStrict b) (Expr.add idx size) m
        _ -> m

    baseBuf :: Expr Buf -> Expr Buf
    baseBuf (AbstractBuf b) = AbstractBuf b
    baseBuf (ConcreteBuf b) = ConcreteBuf b
    baseBuf (GVar (BufVar a)) =
      case Map.lookup a benv of
        Just b -> baseBuf b
        Nothing -> internalError "could not find buffer variable"
    baseBuf (WriteByte _ _ b) = baseBuf b
    baseBuf (WriteWord _ _ b) = baseBuf b
    baseBuf (CopySlice _ _ _ _ dst)= baseBuf dst

-- | Returns an SMT2 object with all buffers referenced from the input props declared, and with the appropriate cex extraction metadata attached
declareBufs :: [Prop] -> BufEnv -> StoreEnv -> SMT2
declareBufs props bufEnv storeEnv = SMT2 (SMTScript ((SMTComment "buffers") : fmap declareBuf allBufs <> ((SMTComment "buffer lengths") : fmap declareLength allBufs))) cexvars mempty
  where
    cexvars = (mempty :: CexVars){ buffers = discoverMaxReads props bufEnv storeEnv }
    allBufs = fmap fromLazyText $ Map.keys cexvars.buffers
    declareBuf n = SMTCommand $ "(declare-fun " <> n <> " () (Array (_ BitVec 256) (_ BitVec 8)))"
    declareLength n = SMTCommand $ "(declare-fun " <> n <> "_length" <> " () (_ BitVec 256))"

-- Given a list of variable names, create an SMT2 object with the variables declared
declareVars :: [Builder] -> SMT2
declareVars names = SMT2 (SMTScript ([SMTComment "variables"] <> fmap declare names)) cexvars mempty
  where
    declare n = SMTCommand $ "(declare-fun " <> n <> " () (_ BitVec 256))"
    cexvars = (mempty :: CexVars){ calldata = fmap toLazyText names }

-- Given a list of variable names, create an SMT2 object with the variables declared
declareConstrainAddrs :: [Builder] -> SMT2
declareConstrainAddrs names = SMT2 (SMTScript ([SMTComment "concrete and symbolic addresses"] <> fmap declare names <> fmap assume names)) cexvars mempty
  where
    declare n = SMTCommand $ "(declare-fun " <> n <> " () Addr)"
    -- assume that symbolic addresses do not collide with the zero address or precompiles
    assume n = SMTCommand $ "(assert (bvugt " <> n <> " (_ bv9 160)))"
    cexvars = (mempty :: CexVars){ addrs = fmap toLazyText names }

-- The gas is a tuple of (prefix, index). Within each prefix, the gas is strictly decreasing as the
-- index increases. This function gets a map of Prefix -> [Int], and for each prefix,
-- enforces the order
enforceGasOrder :: [Prop] -> [SMTEntry]
enforceGasOrder ps = [SMTComment "gas ordering"] <> (concatMap (uncurry order) indices)
  where
    order :: TS.Text -> [Int] -> [SMTEntry]
    order prefix n = consecutivePairs (nubInt n) >>= \(x, y)->
      -- The GAS instruction itself costs gas, so it's strictly decreasing
      [SMTCommand $ "(assert (bvugt " <> fromRight' (exprToSMT (Gas prefix x)) <> " " <>
        fromRight' ((exprToSMT (Gas prefix y))) <> "))"]
    consecutivePairs :: [Int] -> [(Int, Int)]
    consecutivePairs [] = []
    consecutivePairs l@(_:t) = zip l t
    indices = Map.toList $ toMapOfLists $ concatMap (foldProp go mempty) ps
    toMapOfLists :: [(TS.Text, Int)] -> Map.Map TS.Text [Int]
    toMapOfLists = foldr (\(k, v) acc -> Map.insertWith (++) k [v] acc) Map.empty
    go :: Expr a -> [(TS.Text, Int)]
    go e = case e of
      Gas prefix v -> [(prefix, v)]
      _ -> []

declareFrameContext :: [(Builder, [Prop])] -> Err SMT2
declareFrameContext names = do
  decls <- concatMapM declare names
  pure $ SMT2 (SMTScript ([SMTComment "frame context"] <> decls)) cexvars mempty
  where
    declare (n,props) = do
      asserts <- mapM assertSMT props
      pure $ (SMTCommand $ "(declare-fun " <> n <> " () (_ BitVec 256))") : asserts
    cexvars = (mempty :: CexVars){ txContext = fmap (toLazyText . fst) names }

declareAbstractStores :: [Builder] -> [SMTEntry]
declareAbstractStores names = [SMTComment "abstract base stores"] <> fmap declare names
  where
    declare n = SMTCommand $ "(declare-fun " <> n <> " () Storage)"

declareBlockContext :: [(Builder, [Prop])] -> Err SMT2
declareBlockContext names = do
  decls <- concatMapM declare names
  pure $ SMT2 (SMTScript ([SMTComment "block context"] <> decls)) cexvars mempty
  where
    declare (n, props) = do
      asserts <- mapM assertSMT props
      pure $ [ SMTCommand $ "(declare-fun " <> n <> " () (_ BitVec 256))" ] <> asserts
    cexvars = (mempty :: CexVars){ blockContext = fmap (toLazyText . fst) names }

assertSMT :: Prop -> Either String SMTEntry
assertSMT = assertSMTWith ConcreteDivision

assertSMTWith :: DivEncoding -> Prop -> Either String SMTEntry
assertSMTWith enc p = do
  p' <- propToSMTWith enc p
  pure $ SMTCommand ("(assert " <> p' <> ")")

wordAsBV :: forall a. Integral a => a -> Builder
wordAsBV w = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal w <> " 256)"

byteAsBV :: Word8 -> Builder
byteAsBV b = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal b <> " 8)"

exprToSMT :: Expr a -> Err Builder
exprToSMT = exprToSMTWith ConcreteDivision

exprToSMTWith :: DivEncoding -> Expr a -> Err Builder
exprToSMTWith enc = \case
  Lit w -> pure $ wordAsBV w
  Var s -> pure $ fromText s
  GVar (BufVar n) -> pure $ fromString $ "buf" <> (show n)
  GVar (StoreVar n) -> pure $ fromString $ "store" <> (show n)
  JoinBytes
    z o two three four five six seven
    eight nine ten eleven twelve thirteen fourteen fifteen
    sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
    twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone
    -> concatBytesWith enc [
        z, o, two, three, four, five, six, seven
        , eight, nine, ten, eleven, twelve, thirteen, fourteen, fifteen
        , sixteen, seventeen, eighteen, nineteen, twenty, twentyone, twentytwo, twentythree
        , twentyfour, twentyfive, twentysix, twentyseven, twentyeight, twentynine, thirty, thirtyone]

  Add a b -> op2 "bvadd" a b
  Sub a b -> op2 "bvsub" a b
  Mul a b -> op2 "bvmul" a b
  Exp a b -> case a of
    Lit 0 -> do
      benc <- toSMT b
      pure $ "(ite (= " <> benc `sp` zero <> " ) " <> one `sp` zero <> ")"
    Lit 1 -> pure one
    Lit 2 -> do
        benc <- toSMT b
        pure $ "(bvshl " <> one `sp` benc <> ")"
    _ -> case b of
      -- b is limited below, otherwise SMT query will be huge, and eventually Haskell stack overflows
      Lit b' | b' < 1000 -> expandExpWith enc a b'
      _ -> Left $ "Cannot encode symbolic exponent into SMT. Offending symbolic value: " <> show b
  Min a b -> do
    aenc <- toSMT a
    benc <- toSMT b
    pure $ "(ite (bvule " <> aenc `sp` benc <> ") " <> aenc `sp` benc <> ")"
  Max a b -> do
    aenc <- toSMT a
    benc <- toSMT b
    pure $ "(max " <> aenc `sp` benc <> ")"
  LT a b -> do
    cond <- op2 "bvult" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  SLT a b -> do
    cond <- op2 "bvslt" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  SGT a b -> do
    cond <- op2 "bvsgt" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  GT a b -> do
    cond <- op2 "bvugt" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  LEq a b -> do
    cond <- op2 "bvule" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  GEq a b -> do
    cond <- op2 "bvuge" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  Eq a b -> do
    cond <- op2 "=" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  IsZero a -> do
    cond <- op2 "=" a (Lit 0)
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  And a b -> op2 "bvand" a b
  Or a b -> op2 "bvor" a b
  Xor a b -> op2 "bvxor" a b
  Not a -> op1 "bvnot" a
  SHL a b -> op2 "bvshl" b a
  SHR a b -> op2 "bvlshr" b a
  SAR a b -> op2 "bvashr" b a
  SEx a b -> op2 "signext" a b
  Div a b -> divOp "bvudiv" "evm_bvudiv" a b
  SDiv a b -> sdivOp "evm_bvsdiv" a b
  Mod a b -> divOp "bvurem" "evm_bvurem" a b
  SMod a b -> smodOp "evm_bvsrem" a b
  -- NOTE: this needs to do the MUL at a higher precision, then MOD, then downcast
  MulMod a b c -> do
    aExp <- toSMT a
    bExp <- toSMT b
    cExp <- toSMT c
    let aLift = "((_ zero_extend 256) " <> aExp <> ")"
        bLift = "((_ zero_extend 256) " <> bExp <> ")"
        cLift = "((_ zero_extend 256) " <> cExp <> ")"
    pure $ "(ite (= " <> cExp <> " (_ bv0 256)) (_ bv0 256) ((_ extract 255 0) (bvurem (bvmul " <> aLift `sp` bLift <> ")" <> cLift <> ")))"
  AddMod a b c -> do
    aExp <- toSMT a
    bExp <- toSMT b
    cExp <- toSMT c
    let aLift = "((_ zero_extend 1) " <> aExp <> ")"
        bLift = "((_ zero_extend 1) " <> bExp <> ")"
        cLift = "((_ zero_extend 1) " <> cExp <> ")"
    pure $ "(ite (= " <> cExp <> " (_ bv0 256)) (_ bv0 256) ((_ extract 255 0) (bvurem (bvadd " <> aLift `sp` bLift <> ")" <> cLift <> ")))"
  EqByte a b -> do
    cond <- op2 "=" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  Keccak a -> do
    e <- toSMT a
    sz  <- toSMT $ Expr.bufLength a
    pure $ "(keccak " <> e <> " " <> sz <> ")"
  SHA256 a -> do
    e <- toSMT a
    sz  <- toSMT $ Expr.bufLength a
    pure $ "(sha256 " <> e <> " " <> sz <> ")"

  TxValue -> pure $ fromString "txvalue"
  Balance a -> pure $ fromString "balance_" <> formatEAddr a

  Origin ->  pure "origin"
  BlockHash a -> do
    e <- toSMT a
    pure $ "(blockhash " <> e <> ")"
  CodeSize a -> do
    e <- toSMT a
    pure $ "(codesize " <> e <> ")"
  Coinbase -> pure "coinbase"
  Timestamp -> pure "timestamp"
  BlockNumber -> pure "blocknumber"
  PrevRandao -> pure "prevrandao"
  GasLimit -> pure "gaslimit"
  ChainId -> pure "chainid"
  BaseFee -> pure "basefee"

  a@(SymAddr _) -> pure $ formatEAddr a
  WAddr(a@(SymAddr _)) -> do
    wa <- toSMT a
    pure $ "((_ zero_extend 96)" `sp` wa `sp` ")"

  LitByte b -> pure $ byteAsBV b
  IndexWord idx w -> case idx of
    Lit n -> if n >= 0 && n < 32
             then do
               e <- toSMT w
               pure $ fromLazyText ("(indexWord" <> T.pack (show (into n :: Integer))) `sp` e <> ")"
             else toSMT (LitByte 0)
    _ -> op2 "indexWord" idx w
  ReadByte idx src -> op2 "select" src idx

  ConcreteBuf "" -> pure "((as const Buf) #b00000000)"
  ConcreteBuf bs -> writeBytesWith enc bs mempty
  AbstractBuf s -> pure $ fromText s
  ReadWord idx prev -> op2 "readWord" idx prev
  BufLength (AbstractBuf b) -> pure $ fromText b <> "_length"
  BufLength (GVar (BufVar n)) -> pure $ fromLazyText $ "buf" <> (T.pack . show $ n) <> "_length"
  BufLength b -> toSMT (bufLength b)
  WriteByte idx val prev -> do
    encIdx  <- toSMT idx
    encVal  <- toSMT val
    encPrev <- toSMT prev
    pure $ "(store " <> encPrev `sp` encIdx `sp` encVal <> ")"
  WriteWord idx val prev -> do
    encIdx  <- toSMT idx
    encVal  <- toSMT val
    encPrev <- toSMT prev
    pure $ "(writeWord " <> encIdx `sp` encVal `sp` encPrev <> ")"
  CopySlice srcIdx dstIdx size src dst -> do
    srcSMT <- toSMT src
    dstSMT <- toSMT dst
    copySliceWith enc srcIdx dstIdx size srcSMT dstSMT

  -- we need to do a bit of processing here.
  ConcreteStore s -> encodeConcreteStore s
  AbstractStore a idx -> pure $ storeName a idx
  SStore idx val prev -> do
    encIdx  <- toSMT idx
    encVal  <- toSMT val
    encPrev <- toSMT prev
    pure $ "(store" `sp` encPrev `sp` encIdx `sp` encVal <> ")"
  SLoad idx store -> op2 "select" store idx
  LitAddr n -> pure $ fromLazyText $ "(_ bv" <> T.pack (show (into n :: Integer)) <> " 160)"
  CodeHash a@(LitAddr _) -> pure $ fromLazyText "codehash_" <> formatEAddr a
  Gas prefix var -> pure $ fromLazyText $ "gas_" <> T.pack (TS.unpack prefix) <> T.pack (show var)

  a -> internalError $ "TODO: implement: " <> show a
  where
    -- Local alias to avoid repeating 'enc' at every recursive call
    toSMT :: Expr x -> Err Builder
    toSMT = exprToSMTWith enc
    op1 :: Builder -> Expr x -> Err Builder
    op1 op a = do
      e <- toSMT a
      pure $ "(" <> op `sp` e <> ")"
    op2 :: Builder -> Expr x -> Expr y -> Err Builder
    op2 op a b = do
       aenc <- toSMT a
       benc <- toSMT b
       pure $ "(" <> op `sp` aenc `sp` benc <> ")"
    op2CheckZero :: Builder -> Expr x -> Expr y -> Err Builder
    op2CheckZero op a b = do
      aenc <- toSMT a
      benc <- toSMT b
      pure $ "(ite (= " <> benc <> " (_ bv0 256)) (_ bv0 256) " <>  "(" <> op `sp` aenc `sp` benc <> "))"
    divOp :: Builder -> Builder -> Expr x -> Expr y -> Err Builder
    divOp concreteOp abstractOp a b = case enc of
      ConcreteDivision -> op2CheckZero concreteOp a b
      AbstractDivision -> op2 abstractOp a b
    -- | Encode SDiv using bvudiv with abs-value decomposition.
    -- bitwuzla cannot solve UNSAT queries with bvsdiv at 256-bit,
    -- but handles bvudiv efficiently.
    sdivOp :: Builder -> Expr x -> Expr y -> Err Builder
    sdivOp abstractOp a b = case enc of
      AbstractDivision -> op2 abstractOp a b
      ConcreteDivision -> do
        aenc <- toSMT a
        benc <- toSMT b
        let absa = "(ite (bvsge " <> aenc `sp` zero <> ")" `sp` aenc `sp` "(bvsub" `sp` zero `sp` aenc <> "))"
            absb = "(ite (bvsge " <> benc `sp` zero <> ")" `sp` benc `sp` "(bvsub" `sp` zero `sp` benc <> "))"
            udiv = "(bvudiv" `sp` absa `sp` absb <> ")"
            sameSign = "(=" `sp` "(bvslt" `sp` aenc `sp` zero <> ")" `sp` "(bvslt" `sp` benc `sp` zero <> "))"
        pure $ "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero `sp`
                "(ite" `sp` sameSign `sp` udiv `sp` "(bvsub" `sp` zero `sp` udiv <> ")))"
    -- | Encode SMod using bvurem with abs-value decomposition.
    -- EVM SMOD: result has the sign of the dividend (a).
    smodOp :: Builder -> Expr x -> Expr y -> Err Builder
    smodOp abstractOp a b = case enc of
      AbstractDivision -> op2 abstractOp a b
      ConcreteDivision -> do
        aenc <- toSMT a
        benc <- toSMT b
        let absa = "(ite (bvsge " <> aenc `sp` zero <> ")" `sp` aenc `sp` "(bvsub" `sp` zero `sp` aenc <> "))"
            absb = "(ite (bvsge " <> benc `sp` zero <> ")" `sp` benc `sp` "(bvsub" `sp` zero `sp` benc <> "))"
            urem = "(bvurem" `sp` absa `sp` absb <> ")"
        pure $ "(ite (=" `sp` benc `sp` zero <> ")" `sp` zero `sp`
                "(ite (bvsge" `sp` aenc `sp` zero <> ")" `sp` urem `sp` "(bvsub" `sp` zero `sp` urem <> ")))"

sp :: Builder -> Builder -> Builder
a `sp` b = a <> (fromText " ") <> b

zero :: Builder
zero = "(_ bv0 256)"

one :: Builder
one = "(_ bv1 256)"

propToSMT :: Prop -> Err Builder
propToSMT = propToSMTWith ConcreteDivision

propToSMTWith :: DivEncoding -> Prop -> Err Builder
propToSMTWith enc = \case
  PEq a b -> op2 "=" a b
  PLT a b -> op2 "bvult" a b
  PGT a b -> op2 "bvugt" a b
  PLEq a b -> op2 "bvule" a b
  PGEq a b -> op2 "bvuge" a b
  PNeg a -> do
    e <- propToSMTWith enc a
    pure $ "(not " <> e <> ")"
  PAnd a b -> do
    aenc <- propToSMTWith enc a
    benc <- propToSMTWith enc b
    pure $ "(and " <> aenc <> " " <> benc <> ")"
  POr a b -> do
    aenc <- propToSMTWith enc a
    benc <- propToSMTWith enc b
    pure $ "(or " <> aenc <> " " <> benc <> ")"
  PImpl a b -> do
    aenc <- propToSMTWith enc a
    benc <- propToSMTWith enc b
    pure $ "(=> " <> aenc <> " " <> benc <> ")"
  PBool b -> pure $ if b then "true" else "false"
  where
    op2 :: Builder -> Expr x -> Expr y -> Err Builder
    op2 op a b = do
      aenc <- exprToSMTWith enc a
      benc <- exprToSMTWith enc b
      pure $ "(" <> op <> " " <> aenc <> " " <> benc <> ")"



-- ** Helpers ** ---------------------------------------------------------------------------------



copySliceWith :: DivEncoding -> Expr EWord -> Expr EWord -> Expr EWord -> Builder -> Builder -> Err Builder
copySliceWith divEnc srcOffset dstOffset (Lit size) src dst = do
  sz <- internal size
  pure $ "(let ((src " <> src <> ")) " <> sz <> ")"
  where
    internal 0 = pure dst
    internal idx = do
      let idx' = idx - 1
      encDstOff <- offset idx' dstOffset
      encSrcOff <- offset idx' srcOffset
      child <- internal idx'
      pure $ "(store " <> child `sp` encDstOff `sp` "(select src " <> encSrcOff <> "))"
    offset :: W256 -> Expr EWord -> Err Builder
    offset o (Lit b) = pure $ wordAsBV $ o + b
    offset o e = exprToSMTWith divEnc $ Expr.add (Lit o) e
copySliceWith _ _ _ _ _ _ = Left "CopySlice with a symbolically sized region not currently implemented, cannot execute SMT solver on this query"


expandExpWith :: DivEncoding -> Expr EWord -> W256 -> Err Builder
expandExpWith divEnc base expnt
  -- in EVM, anything (including 0) to the power of 0 is 1
  | expnt == 0 = pure one
  | expnt == 1 = exprToSMTWith divEnc base
  | otherwise = do
    b <- exprToSMTWith divEnc base
    n <- expandExpWith divEnc base (expnt - 1)
    pure $ "(bvmul " <> b `sp` n <> ")"


concatBytesWith :: DivEncoding -> [Expr Byte] -> Err Builder
concatBytesWith divEnc bytes = do
  case List.uncons $ reverse bytes of
    Nothing -> Left "unexpected empty bytes"
    Just (h, t) -> do
      a2 <- exprToSMTWith divEnc h
      foldM wrap a2 t
  where
    wrap :: Builder -> Expr a -> Err Builder
    wrap inner byte = do
      byteSMT <- exprToSMTWith divEnc byte
      pure $ "(concat " <> byteSMT `sp` inner <> ")"


writeBytesWith :: DivEncoding -> ByteString -> Expr Buf -> Err Builder
writeBytesWith divEnc bytes buf =  do
  smtText <- exprToSMTWith divEnc buf
  let ret = BS.foldl wrap (0, smtText) bytes
  pure $ snd ret
  where
    -- we don't need to store zeros if the base buffer is empty
    skipZeros = buf == mempty
    wrap :: (Int, Builder) -> Word8 -> (Int, Builder)
    wrap (idx, acc) byte =
      if skipZeros && byte == 0
      then (idx', acc)
      else (idx', "(store " <> acc `sp` (wordAsBV idx) `sp` (byteAsBV byte) <> ")")
      where
        !idx' = idx + 1

encodeConcreteStore :: Map W256 W256 -> Err Builder
encodeConcreteStore s = foldM encodeWrite ("((as const Storage) #x0000000000000000000000000000000000000000000000000000000000000000)") (Map.toList s)
  where
    encodeWrite :: Builder -> (W256, W256) -> Err Builder
    encodeWrite prev (key, val) = do
      encKey <- exprToSMT $ Lit key
      encVal <- exprToSMT $ Lit val
      pure $ "(store " <> prev `sp` encKey `sp` encVal <> ")"

storeName :: Expr EAddr -> Maybe W256 -> Builder
storeName a Nothing = fromString ("baseStore_") <> formatEAddr a
storeName a (Just idx) = fromString ("baseStore_") <> formatEAddr a <> "_" <> (fromString $ show idx)

formatEAddr :: Expr EAddr -> Builder
formatEAddr = \case
  LitAddr a -> fromString ("litaddr_" <> show a)
  SymAddr a -> fromText ("symaddr_" <> a)
  GVar _ -> internalError "Unexpected GVar"


-- ** Cex parsing ** --------------------------------------------------------------------------------

parseAddr :: SpecConstant -> Addr
parseAddr = parseSC

parseW256 :: SpecConstant -> W256
parseW256 = parseSC

parseW8 :: SpecConstant -> Word8
parseW8 = parseSC

readOrError :: (Num a, Eq a) => ReadS a -> TS.Text -> a
readOrError reader val = fst . headErr . reader . T.unpack . T.fromStrict $ val
  where
    headErr x = fromMaybe (internalError "error reading empty result") $ listToMaybe x

parseSC :: (Num a, Eq a) => SpecConstant -> a
parseSC (SCHexadecimal a) = readOrError Numeric.readHex a
parseSC (SCBinary a) = readOrError Numeric.readBin a
parseSC sc = internalError $ "cannot parse: " <> show sc

parseVar :: TS.Text -> Expr EWord
parseVar = Var

parseEAddr :: TS.Text -> Expr EAddr
parseEAddr name
  | Just a <- TS.stripPrefix "litaddr_" name = LitAddr (read (TS.unpack a))
  | Just a <- TS.stripPrefix "symaddr_" name = SymAddr a
  | otherwise = internalError $ "cannot parse: " <> show name

parseBlockCtx :: TS.Text -> Expr EWord
parseBlockCtx "origin" = Origin
parseBlockCtx "coinbase" = Coinbase
parseBlockCtx "timestamp" = Timestamp
parseBlockCtx "blocknumber" = BlockNumber
parseBlockCtx "prevrandao" = PrevRandao
parseBlockCtx "gaslimit" = GasLimit
parseBlockCtx "chainid" = ChainId
parseBlockCtx "basefee" = BaseFee
parseBlockCtx val = internalError $ "cannot parse '" <> (TS.unpack val) <> "' into an Expr"

parseTxCtx :: TS.Text -> Expr EWord
parseTxCtx name
  | name == "txvalue" = TxValue
  | Just a <- TS.stripPrefix "balance_" name = Balance (parseEAddr a)
  | Just a <- TS.stripPrefix "codehash_" name = CodeHash (parseEAddr a)
  | otherwise = internalError $ "cannot parse " <> (TS.unpack name) <> " into an Expr"

type ValGetter = Text -> MaybeIO Text

getAddrs :: (TS.Text -> Expr EAddr) -> ValGetter -> [TS.Text] -> MaybeIO (Map (Expr EAddr) Addr)
getAddrs parseName getVal names = do
  m <- foldM (getOne parseAddr getVal) mempty names
  pure $ Map.mapKeys parseName m

getVars :: (TS.Text -> Expr EWord) -> ValGetter -> [TS.Text] -> MaybeIO (Map (Expr EWord) W256)
getVars parseName getVal names = do
  m <- foldM (getOne parseW256 getVal) mempty names
  pure $ Map.mapKeys parseName m

getOne :: (SpecConstant -> a) -> ValGetter -> Map TS.Text a -> TS.Text -> MaybeIO (Map TS.Text a)
getOne parseVal getVal acc name = do
  raw <- getVal (T.fromStrict name)
  val <- hoistMaybe $ do
    Right (ResSpecific (valParsed :| [])) <- pure $ parseCommentFreeFileMsg getValueRes (T.toStrict raw)
    (TermQualIdentifier (Unqualified (IdSymbol symbol)), TermSpecConstant sc) <- pure valParsed
    guard (symbol == name)
    pure $ parseVal sc
  pure $ Map.insert name val acc

-- | Queries the solver for models for each of the expressions representing the
-- max read index for a given buffer
queryMaxReads :: ValGetter -> Map Text (Expr EWord) -> MaybeIO (Map Text W256)
queryMaxReads getVal maxReads = mapM (queryValue getVal) maxReads

-- | Gets the initial model for each buffer, these will often be much too large for our purposes
getBufs :: ValGetter -> [Text] -> MaybeIO (Map (Expr Buf) BufModel)
getBufs getVal bufs = foldM getBuf mempty bufs
  where
    getLength :: Text -> MaybeIO W256
    getLength name = do
      val <- getVal (name <> "_length ")
      hoistMaybe $ do
        Right (ResSpecific (parsed :| [])) <- pure $ parseCommentFreeFileMsg getValueRes (T.toStrict val)
        (TermQualIdentifier (Unqualified (IdSymbol symbol)), TermSpecConstant sc) <- pure parsed
        guard (symbol == T.toStrict (name <> "_length"))
        pure $ parseW256 sc

    getBuf :: Map (Expr Buf) BufModel -> Text -> MaybeIO (Map (Expr Buf) BufModel)
    getBuf acc name = do
      len <- getLength name
      val <- getVal name
      buf <- hoistMaybe $ do
        Right (ResSpecific (valParsed :| [])) <- pure $ parseCommentFreeFileMsg getValueRes (T.toStrict val)
        (TermQualIdentifier (Unqualified (IdSymbol symbol)), term) <- pure valParsed
        guard (T.fromStrict symbol == name)
        parseBuf len term
      pure $ Map.insert (AbstractBuf $ T.toStrict name) buf acc

    parseBuf :: W256 -> Term -> Maybe BufModel
    parseBuf len term = Comp <$> go mempty term
      where
        go env = \case
          -- constant arrays
          (TermApplication (
            Qualified (IdSymbol "const") (
              SortParameter (IdSymbol "Array") (
                SortSymbol (IdIndexed "BitVec" (IxNumeral "256" :| []))
                :| [SortSymbol (IdIndexed "BitVec" (IxNumeral "8" :| []))]
              )
            )) ((TermSpecConstant val :| [])))
            -> Just $ Base (parseW8 val) len

          -- writing a byte over some array
          (TermApplication
            (Unqualified (IdSymbol "store"))
            (base :| [TermSpecConstant idx, TermSpecConstant val])
            ) -> do
              pbase <- go env base
              let pidx = parseW256 idx
                  pval = parseW8 val
              Just $ Write pval pidx pbase

          -- binding a new name
          (TermLet ((VarBinding name' bound) :| []) term') -> do
              pbound <- go env bound
              go (Map.insert name' pbound env) term'

          -- looking up a bound name
          (TermQualIdentifier (Unqualified (IdSymbol name'))) ->
            Map.lookup name' env

          _ -> Nothing

-- | Takes a Map containing all reads from a store with an abstract base, as
-- well as the concrete part of the storage prestate and returns a fully
-- concretized storage
getStore
  :: ValGetter
  -> StorageReads
  -> MaybeIO (Map (Expr EAddr) (Map W256 W256))
getStore getVal (StorageReads innerMap) = do
  results <- forM (Map.toList innerMap) $ \((addr, idx), slots) -> do
    let name = toLazyText (storeName addr idx)
    raw <- getVal name
    fun <- hoistMaybe $ do
      Right (ResSpecific (valParsed :| [])) <- pure $ parseCommentFreeFileMsg getValueRes (T.toStrict raw)
      (TermQualIdentifier (Unqualified (IdSymbol symbol)), term) <- pure valParsed
      guard (symbol == T.toStrict name)
      pure $ interpret1DArray Map.empty term
    -- create a map by adding only the locations that are read by the program
    store <- foldM (\m slot -> do
      slot' <- queryValue getVal slot
      pure $ Map.insert slot' (fun slot') m) Map.empty (Set.toList slots)
    pure (addr, store)
  pure $ Map.fromList results

-- | Ask the solver to give us the concrete value of an arbitrary abstract word
queryValue :: ValGetter -> Expr EWord -> MaybeIO W256
queryValue _ (Lit w) = pure w
queryValue getVal w = do
  -- this exprToSMT should never fail, since we have already ran the solver
  let expr = toLazyText $ fromRight' $ exprToSMT w
  raw <- getVal expr
  hoistMaybe $ do
    valTxt <- extractValue raw
    Right sc <- pure $ parseString specConstant (T.toStrict valTxt)
    pure $ parseW256 sc
  where
    extractValue :: Text -> Maybe Text
    extractValue getValResponse = (T.stripSuffix "))") $ snd $ T.breakOnEnd " " $ T.stripEnd getValResponse

-- | Interpret an N-dimensional array as a value of type a.
-- Parameterized by an interpretation function for array values.
interpretNDArray :: (Map Symbol Term -> Term -> a) -> (Map Symbol Term) -> Term -> (W256 -> a)
interpretNDArray interp env = \case
  -- variable reference
  TermQualIdentifier (Unqualified (IdSymbol s)) ->
    case Map.lookup s env of
      Just t -> interpretNDArray interp env t
      Nothing -> internalError "unknown identifier, cannot parse array"
  -- (let (x t') t)
  TermLet (VarBinding x t' :| []) t -> interpretNDArray interp (Map.insert x t' env) t
  TermLet (VarBinding x t' :| lets) t -> interpretNDArray interp (Map.insert x t' env) (TermLet (NonEmpty.fromList lets) t)
  -- (as const (Array (_ BitVec 256) (_ BitVec 256))) SpecConstant
  TermApplication asconst (val :| []) | isArrConst asconst ->
    \_ -> interp env val
  -- (store arr ind val)
  TermApplication store (arr :| [TermSpecConstant ind, val]) | isStore store ->
    \x -> if x == parseW256 ind then interp env val else interpretNDArray interp env arr x
  t -> internalError $ "cannot parse array value. Unexpected term: " <> (show t)

  where
    isArrConst :: QualIdentifier -> Bool
    isArrConst = \case
      Qualified (IdSymbol "const") (SortParameter (IdSymbol "Array") _) -> True
      _ -> False

    isStore :: QualIdentifier -> Bool
    isStore t = t == Unqualified (IdSymbol "store")


-- | Interpret an 1-dimensional array as a function
interpret1DArray :: (Map Symbol Term) -> Term -> (W256 -> W256)
interpret1DArray = interpretNDArray interpretW256
  where
    interpretW256 :: (Map Symbol Term) -> Term -> W256
    interpretW256 _ (TermSpecConstant val) = parseW256 val
    interpretW256 env (TermQualIdentifier (Unqualified (IdSymbol s))) =
      case Map.lookup s env of
        Just t -> interpretW256 env t
        Nothing -> internalError "unknown identifier, cannot parse array"
    interpretW256 _ t = internalError $ "cannot parse array value. Unexpected term: " <> (show t)
