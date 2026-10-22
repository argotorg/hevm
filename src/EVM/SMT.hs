{- |
    Module: EVM.SMT
    Description: Utilities for building and executing SMT queries from Expr instances
-}
module EVM.SMT
(
  module EVM.SMT.Types,
  module EVM.SMT.SMTLIB,
  module EVM.SMT.ArithEncoding,

  collapse,
  getVar,
  formatSMT2,
  declareIntermediates,
  assertProps,
  assertPropsAbstract,
  AbstractQuery(..),
  encodeConcreteStore,
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
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Bits (shiftR, testBit)
import Data.Char (isDigit)
import Data.Containers.ListUtils (nubOrd)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Data.Vector.Storable.ByteString (vectorToByteString)
import Data.Foldable (Foldable(..))
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromJust, fromMaybe, listToMaybe)
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
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (eqT)
import qualified Data.Text.Lazy.Builder.Int (decimal)
import Language.SMT2.Parser (getValueRes, parseCommentFreeFileMsg, parseString, specConstant)
import Language.SMT2.Syntax (Symbol, SpecConstant(..), GeneralRes(..), Term(..), QualIdentifier(..), Identifier(..), Sort(..), Index(..), VarBinding(..))
import Numeric (readHex, readBin, showHex)
import Witch (into, unsafeInto)
import EVM.Format (formatProp)

import EVM.CSE
import EVM.Expr (bufLengthEnv, bufLength, minLength, inRange)
import EVM.Expr qualified as Expr
import EVM.Keccak (keccakAssumptions, concreteKeccaks, findKeccakPropsExprs)
import EVM.Traversals
import EVM.Types
import EVM.Effects
import EVM.SMT.Types
import EVM.SMT.SMTLIB
import EVM.SMT.ArithEncoding
import EVM.SMT.AbstractBase (DivModKind(..), abstFnName, concFnName, mulSMT, mulModSMT, concreteMulModSMT, shareTerms)


-- ** Encoding ** ----------------------------------------------------------------------------------


-- | Attempts to collapse a compressed buffer representation down to a flattened one
-- | Flattens a buffer model to its length, with the semantics of applying its
-- writes with 'writeByte'. Builds the bytes in one pass: applying the writes
-- one by one copies the whole buffer for every write.
collapse :: BufModel -> Maybe BufModel
collapse (Flat b) = Just (Flat b)
collapse (Comp c) = Flat <$> go c []
  where
    -- collected innermost first, so the outermost write to an index wins in 'Map.fromList'
    go (Write byte idx next) ws = go next ((idx, byte) : ws)
    go (Base byte sz) ws
      | sz <= 120_000_000 = Just $ vectorToByteString $ VS.create $ do
          v <- VSM.replicate base byte
          forM_ (Map.toList writes) $ \(i, b) -> VSM.write v (unsafeInto i) b
          pure v
      | otherwise = Nothing
      where
        base = unsafeInto sz
        -- the length is the solver's, past it a buffer reads as zero; the solver
        -- writes there e.g. to satisfy the assertion that such reads are zero
        writes = Map.filterWithKey (\i _ -> i < sz) (Map.fromList ws)

getVar :: SMTCex -> TS.Text -> W256
getVar cex name = fromJust $ Map.lookup (Var name) cex.vars

formatSMT2 :: SMT2 -> Text
formatSMT2 (SMT2 (SMTScript entries) _ ps) = expr <> smt2
 where
 expr = T.concat [T.singleton ';', T.replace "\n" "\n;" $ T.pack . TS.unpack $  TS.unlines (fmap formatProp ps)]
 smt2 = T.unlines (fmap toText entries)

-- | Reads all intermediate variables from the builder state and produces SMT declaring them as constants
declareIntermediates :: BufEnv -> StoreEnv -> Err [SMTEntry]
declareIntermediates = declareIntermediatesWith ConcreteArith

declareIntermediatesWith :: ArithEncoding -> BufEnv -> StoreEnv -> Err [SMTEntry]
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

decompose :: Config -> [Prop] -> ([Prop], CexVars)
decompose conf props = case Expr.decomposeStorageProps props of
  Just decomposed | conf.decomposeStorage ->
    (decomposed, mempty { logicalStores = Map.fromList [(i, s) | s <- Expr.accessedLogicalStores props, i <- storeIdx s] })
  _ -> (props, mempty)
  where
    storeIdx = \case
      MapStore i -> [i]
      ArrayStore i -> [i]
      SmallSlots -> []

-- simplify to rewrite sload/sstore combos
-- notice: it is VERY important not to concretize early, because Keccak assumptions
--         need unconcretized Props
assertProps :: Config -> [Prop] -> Err SMT2
assertProps conf ps =
  if not conf.simp then assertPropsHelperWith ConcreteArith False [] ps
  else let (decomposed, stores) = decompose conf ps
       in (<> SMT2 mempty stores mempty) <$> assertPropsHelperWith ConcreteArith True [] decomposed

data AbstractQuery = AbstractQuery
  { query :: SMT2
  , refinement :: [SMTEntry]
    -- ^ equates the goal's abstract terms with the native ops, to re-check a
    -- SAT result with; empty if nothing is abstract
  , saturatedTruth :: [SMTEntry]
    -- ^ the same for every term the lemmas mention, see 'saturatedGroundTruth'
  , lemmaFamilies :: [String]
    -- ^ the family of each lemma instance in the query
  }

-- | Assert props with abstract div/mod/mul (uninterpreted functions + lemmas).
assertPropsAbstract :: Config -> [Prop] -> Err AbstractQuery
assertPropsAbstract conf ps = do
  base@(SMT2 _ _ goalPs) <- (<> SMT2 mempty decompStores mempty) <$> assertPropsHelperWith AbstractArith conf.simp divModAbstractDecls psDecomp
  -- Lemmas and ground truth come from the helper's concretized props, the ones
  -- the goal is encoded from: raw props can keep storage reads that simplify
  -- away in the goal, so their terms would not match.
  let (share, terms) = shareTerms goalPs
      enc = exprToSMTWith AbstractArith . share
  termDefs <- mapM defineTerm terms
  shiftBounds <- divModEncoding enc goalPs
  (families, mulLemmas) <- mulEncoding enc goalPs
  divTruth <- divModGroundTruth enc goalPs
  mulTruth <- mulGroundTruth enc goalPs
  mulModTruth <- mulModGroundTruth enc goalPs
  saturated <- saturatedGroundTruth enc goalPs
  pure AbstractQuery
    { query = base <> SMT2 (SMTScript (termDefs <> shiftBounds <> mulLemmas)) mempty mempty
    , refinement = divTruth <> mulTruth <> mulModTruth
    , saturatedTruth = saturated
    , lemmaFamilies = families
    }
  where
    (psDecomp, decompStores) = if conf.simp then decompose conf ps else (ps, mempty)
    defineTerm (name, body) = do
      encoded <- exprToSMTWith AbstractArith body
      pure $ SMTCommand $ "(define-fun " <> fromText name <> " () (_ BitVec 256) " <> encoded <> ")"

-- Note: we need a version that does NOT call simplify,
-- because we make use of it to verify the correctness of our simplification
-- passes through property-based testing.
assertPropsHelperWith :: ArithEncoding -> Bool -> [SMTEntry] -> [Prop]  -> Err SMT2
assertPropsHelperWith arithEnc simp extraDecls psPreConc = do
 encs <- mapM (propToSMTWith arithEnc) psElim
 intermediates <- declareIntermediatesWith arithEnc bufs stores
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
  <> SMT2 (SMTScript (fmap (\p -> SMTCommand("(assert " <> p <> ")")) encs)) (cexInfo storageReads) ps

  where
    ps = if simp then Expr.concKeccakSimpProps psPreConc else Expr.concKeccakProps psPreConc
    (psElim, bufs, stores) = eliminateProps ps

    -- Props storing info that need declaration(s)
    toDeclarePs     = ps <> keccAssump <> keccComp
    toDeclarePsElim = psElim <> keccAssump <> keccComp

    -- vars, frames, and block contexts in need of declaration
    allVars = fmap referencedVars toDeclarePsElim <> fmap referencedVars bufVals <> fmap referencedVars storeVals
    frameCtx = fmap (referencedFrameContext arithEnc) toDeclarePsElim <> fmap (referencedFrameContext arithEnc) bufVals <> fmap (referencedFrameContext arithEnc) storeVals
    blockCtx = fmap referencedBlockContext toDeclarePsElim <> fmap referencedBlockContext bufVals <> fmap referencedBlockContext storeVals

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
      assumps <- mapM (assertSMTWith arithEnc) keccAssump
      comps <- mapM (assertSMTWith arithEnc) keccComp
      pure $ ((SMTComment "keccak assumptions") : assumps) <> ((SMTComment "keccak computations") : comps)

    -- assert that reads beyond size of buffer & storage is zero
    readAssumes = do
      assumps <- mapM (assertSMTWith arithEnc) $ assertReads psElim bufs stores
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

referencedFrameContext :: TraversableTerm a => ArithEncoding -> a -> [(Builder, [Prop])]
referencedFrameContext enc expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [(Builder, [Prop])]
    go = \case
      o@TxValue -> [(fromRight' $ exprToSMT o, [])]
      o@(Balance _) -> [(fromRight' $ exprToSMT o, [PLT o (Lit $ 2 ^ (96 :: Int))])]
      o@(Gas _ _) -> [(fromRight' $ exprToSMT o, [])]
      o@(CodeHash (LitAddr _)) -> [(fromRight' $ exprToSMT o, [])]
      _ -> []
    exprToSMT :: Expr x -> Err Builder
    exprToSMT = exprToSMTWith enc

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
    assume n = SMTCommand $ "(assert (and (bvugt " <> n <> " (_ bv17 160)) (distinct " <> n <> " (_ bv256 160))))"
    cexvars = (mempty :: CexVars){ addrs = fmap toLazyText names }

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
assertSMT = assertSMTWith ConcreteArith

assertSMTWith :: ArithEncoding -> Prop -> Either String SMTEntry
assertSMTWith enc p = do
  p' <- propToSMTWith enc p
  pure $ SMTCommand ("(assert " <> p' <> ")")

byteAsBV :: Word8 -> Builder
byteAsBV b = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal b <> " 8)"

exprToSMTWith :: ArithEncoding -> Expr a -> Err Builder
exprToSMTWith arithEnc = \case
  Lit w -> pure $ wordAsBV w
  Var s -> pure $ fromText s
  GVar (BufVar n) -> pure $ fromString $ "buf" <> (show n)
  GVar (StoreVar n) -> pure $ fromString $ "store" <> (show n)
  JoinBytes
    z o two three four five six seven
    eight nine ten eleven twelve thirteen fourteen fifteen
    sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
    twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone
    -> concatBytesWith arithEnc [
        z, o, two, three, four, five, six, seven
        , eight, nine, ten, eleven, twelve, thirteen, fourteen, fifteen
        , sixteen, seventeen, eighteen, nineteen, twenty, twentyone, twentytwo, twentythree
        , twentyfour, twentyfive, twentysix, twentyseven, twentyeight, twentynine, thirty, thirtyone]

  Add a b -> op2 "bvadd" a b
  Sub a b -> op2 "bvsub" a b
  Mul a b -> case arithEnc of
    ConcreteArith -> op2 "bvmul" a b
    -- 'mulSMT' is the one definition of which products are abstracted; the
    -- lemmas build theirs with it too, so their terms match the goal's
    AbstractArith -> do
      aenc <- exprToSMT a
      benc <- exprToSMT b
      pure $ mulSMT (a, aenc) (b, benc)
  Exp a b -> case a of
    Lit 0 -> do
      benc <- exprToSMT b
      pure $ "(ite (= " <> benc `sp` zero <> " ) " <> one `sp` zero <> ")"
    Lit 1 -> pure one
    Lit 2 -> do
        benc <- exprToSMT b
        pure $ "(bvshl " <> one `sp` benc <> ")"
    _ -> case b of
      Lit b' -> expandExpWith arithEnc a b'
      _ -> Left $ "Cannot encode symbolic exponent into SMT. Offending symbolic value: " <> show b
  Min a b -> do
    aenc <- exprToSMT a
    benc <- exprToSMT b
    pure $ "(ite (bvule " <> aenc `sp` benc <> ") " <> aenc `sp` benc <> ")"
  Max a b -> do
    aenc <- exprToSMT a
    benc <- exprToSMT b
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
  ITE c t f -> do
    condEnc <- exprToSMT c
    thenEnc <- exprToSMT t
    elseEnc <- exprToSMT f
    pure $ "(ite (distinct " <> condEnc `sp` zero <> ") " <> thenEnc `sp` elseEnc <> ")"
  And a b -> op2 "bvand" a b
  Or a b -> op2 "bvor" a b
  Xor a b -> op2 "bvxor" a b
  Not a -> op1 "bvnot" a
  SHL a b -> op2 "bvshl" b a
  SHR a b -> op2 "bvlshr" b a
  SAR a b -> op2 "bvashr" b a
  CLZ a -> op1 "clz256" a
  SEx a b -> op2 "signext" a b
  Div a b -> divModOp IsUDiv a b
  SDiv a b -> divModOp IsSDiv a b
  Mod a b -> divModOp IsUMod a b
  SMod a b -> divModOp IsSMod a b
  MulMod a b c -> do
    aExp <- exprToSMT a
    bExp <- exprToSMT b
    cExp <- exprToSMT c
    pure $ case arithEnc of
      AbstractArith -> mulModSMT aExp bExp cExp
      ConcreteArith -> concreteMulModSMT aExp bExp cExp
  AddMod a b c -> do
    aExp <- exprToSMT a
    bExp <- exprToSMT b
    cExp <- exprToSMT c
    let aLift = "((_ zero_extend 1) " <> aExp <> ")"
        bLift = "((_ zero_extend 1) " <> bExp <> ")"
        cLift = "((_ zero_extend 1) " <> cExp <> ")"
    pure $ "(ite (= " <> cExp <> " (_ bv0 256)) (_ bv0 256) ((_ extract 255 0) (bvurem (bvadd " <> aLift `sp` bLift <> ")" <> cLift <> ")))"
  EqByte a b -> do
    cond <- op2 "=" a b
    pure $ "(ite " <> cond `sp` one `sp` zero <> ")"
  Keccak a -> do
    enc <- exprToSMT a
    sz  <- exprToSMT $ Expr.bufLength a
    pure $ "(keccak " <> enc <> " " <> sz <> ")"

  TxValue -> pure $ fromString "txvalue"
  Balance a -> pure $ fromString "balance_" <> formatEAddr a

  Origin ->  pure "origin"
  BlockHash a -> do
    enc <- exprToSMT a
    pure $ "(blockhash " <> enc <> ")"
  CodeSize a -> do
    enc <- exprToSMT a
    pure $ "(codesize " <> enc <> ")"
  Coinbase -> pure "coinbase"
  Timestamp -> pure "timestamp"
  BlockNumber -> pure "blocknumber"
  PrevRandao -> pure "prevrandao"
  GasLimit -> pure "gaslimit"
  ChainId -> pure "chainid"
  BaseFee -> pure "basefee"

  a@(SymAddr _) -> pure $ formatEAddr a
  WAddr(a@(SymAddr _)) -> do
    wa <- exprToSMT a
    pure $ "((_ zero_extend 96)" `sp` wa `sp` ")"

  LitByte b -> pure $ byteAsBV b
  IndexWord idx w -> case idx of
    Lit n -> if n >= 0 && n < 32
             then do
               enc <- exprToSMT w
               pure $ fromLazyText ("(indexWord" <> T.pack (show (into n :: Integer))) `sp` enc <> ")"
             else exprToSMT (LitByte 0)
    _ -> op2 "indexWord" idx w
  ReadByte idx src -> op2 "select" src idx

  ConcreteBuf "" -> pure "((as const Buf) #b00000000)"
  ConcreteBuf bs -> writeBytesWith arithEnc bs mempty
  AbstractBuf s -> pure $ fromText s
  ReadWord idx prev -> op2 "readWord" idx prev
  BufLength (AbstractBuf b) -> pure $ fromText b <> "_length"
  BufLength (GVar (BufVar n)) -> pure $ fromLazyText $ "buf" <> (T.pack . show $ n) <> "_length"
  BufLength b -> exprToSMT (bufLength b)
  WriteByte idx val prev -> do
    encIdx  <- exprToSMT idx
    encVal  <- exprToSMT val
    encPrev <- exprToSMT prev
    pure $ "(store " <> encPrev `sp` encIdx `sp` encVal <> ")"
  WriteWord idx val prev -> do
    encIdx  <- exprToSMT idx
    encVal  <- exprToSMT val
    encPrev <- exprToSMT prev
    pure $ "(writeWord " <> encIdx `sp` encVal `sp` encPrev <> ")"
  CopySlice srcIdx dstIdx size src dst -> do
    srcSMT <- exprToSMT src
    dstSMT <- exprToSMT dst
    copySliceWith arithEnc srcIdx dstIdx size srcSMT dstSMT

  -- we need to do a bit of processing here.
  ConcreteStore s -> encodeConcreteStore arithEnc s
  AbstractStore a idx -> pure $ storeName a idx
  SStore idx val prev -> do
    encIdx  <- exprToSMT idx
    encVal  <- exprToSMT val
    encPrev <- exprToSMT prev
    pure $ "(store" `sp` encPrev `sp` encIdx `sp` encVal <> ")"
  SLoad idx store -> op2 "select" store idx
  LitAddr n -> pure $ fromLazyText $ "(_ bv" <> T.pack (show (into n :: Integer)) <> " 160)"
  CodeHash a@(LitAddr _) -> pure $ fromLazyText "codehash_" <> formatEAddr a
  Gas prefix var -> pure $ fromLazyText $ "gas_" <> T.pack (TS.unpack prefix) <> T.pack (show var)

  a -> internalError $ "TODO: implement: " <> show a
  where
    exprToSMT :: Expr x -> Err Builder
    exprToSMT = exprToSMTWith arithEnc
    op1 :: Builder -> Expr x -> Err Builder
    op1 op a = do
      enc <- exprToSMT a
      pure $ "(" <> op `sp` enc <> ")"
    op2 :: Builder -> Expr x -> Expr y -> Err Builder
    op2 op a b = do
       aenc <- exprToSMT a
       benc <- exprToSMT b
       pure $ "(" <> op `sp` aenc `sp` benc <> ")"
    op2CheckZero :: Builder -> Expr x -> Expr y -> Err Builder
    op2CheckZero op a b = do
      aenc <- exprToSMT a
      benc <- exprToSMT b
      pure $ "(ite (= " <> benc <> " (_ bv0 256)) (_ bv0 256) " <>  "(" <> op `sp` aenc `sp` benc <> "))"
    -- the abstract function needs no zero guard: 'divModEncoding' asserts the
    -- EVM x/0 = 0 convention on it, and so does the ground truth
    divModOp :: DivModKind -> Expr x -> Expr y -> Err Builder
    divModOp kind a b = case arithEnc of
      ConcreteArith -> op2CheckZero (concFnName kind) a b
      AbstractArith -> op2 (abstFnName kind) a b

propToSMTWith :: ArithEncoding -> Prop -> Err Builder
propToSMTWith arithEnc = \case
  -- array equality alone ignores length: all-zero buffers of different lengths would be equal
  PEq (a :: Expr x) b | Just Refl <- eqT @x @Buf -> do
    arrEq <- op2 "=" a b
    lenEq <- op2 "=" (BufLength a) (BufLength b)
    pure $ "(and " <> arrEq <> " " <> lenEq <> ")"
  PEq a b -> op2 "=" a b
  PLT a b -> op2 "bvult" a b
  PGT a b -> op2 "bvugt" a b
  PLEq a b -> op2 "bvule" a b
  PGEq a b -> op2 "bvuge" a b
  PNeg a -> do
    enc <- propToSMT a
    pure $ "(not " <> enc <> ")"
  PAnd a b -> do
    aenc <- propToSMT a
    benc <- propToSMT b
    pure $ "(and " <> aenc <> " " <> benc <> ")"
  POr a b -> do
    aenc <- propToSMT a
    benc <- propToSMT b
    pure $ "(or " <> aenc <> " " <> benc <> ")"
  PImpl a b -> do
    aenc <- propToSMT a
    benc <- propToSMT b
    pure $ "(=> " <> aenc <> " " <> benc <> ")"
  PBool b -> pure $ if b then "true" else "false"
  PCall i success retdata world -> do
    args <- sequence
      [ encE i.world, encE i.callKind, encE i.target, encE i.callValue, encE i.callData, encE i.callDataLen
      , encE i.caller, encE i.callerStorage, encE i.callerTStorage, encE i.callerBalance, encE i.callGas ]
    let app f = "(" <> f <> " " <> mconcat (List.intersperse " " args) <> ")"
        def v f = "(= " <> v <> " " <> app f <> ")"
    s <- encE success
    r <- encE retdata
    l <- encE (bufLength retdata)
    w <- traverse (\(a, b) -> (,) <$> encE a <*> encE b) world
    pure $ "(and " <> def s "call_success" <> " " <> def r "call_retdata" <> " " <> def l "call_retlen"
      <> maybe "" (\(w', e) -> " " <> def w' "call_world" <> " " <> def e "call_ether") w <> ")"
  where
    encE :: Expr x -> Err Builder
    encE = exprToSMTWith arithEnc
    propToSMT :: Prop -> Err Builder
    propToSMT = propToSMTWith arithEnc
    op2 :: Builder -> Expr x -> Expr y -> Err Builder
    op2 op a b = do
      aenc <- exprToSMTWith arithEnc a
      benc <- exprToSMTWith arithEnc b
      pure $ "(" <> op <> " " <> aenc <> " " <> benc <> ")"

-- ** Helpers ** ---------------------------------------------------------------------------------

-- | Copies are encoded a byte at a time, so a larger one would take gigabytes
maxEncodedCopy :: W256
maxEncodedCopy = 0x100000

copySliceWith :: ArithEncoding -> Expr EWord -> Expr EWord -> Expr EWord -> Builder -> Builder -> Err Builder
copySliceWith arithEnc srcOffset dstOffset (Lit size) src dst = do
  -- a symbolic size, e.g. a keccak, can become this large only once concretized for encoding
  when (size > maxEncodedCopy) $
    Left $ "CopySlice of 0x" <> showHex size "" <> " bytes not currently implemented, encoding it would take too much memory"
  -- a symbolic offset is encoded once, not once per byte
  srcBind <- binding "copy!srcoff" srcOffset
  dstBind <- binding "copy!dstoff" dstOffset
  sz <- internal size
  -- the binders must not be possible buffer names, or they capture that buffer in dst
  pure $ "(let ((copy!src " <> src <> ")" <> srcBind <> dstBind <> ") " <> sz <> ")"
  where
    binding :: Builder -> Expr EWord -> Err Builder
    binding _ (Lit _) = pure ""
    binding name e = do
      enc <- exprToSMTWith arithEnc e
      pure $ " (" <> name <> " " <> enc <> ")"
    internal 0 = pure dst
    internal idx = do
      let idx' = idx - 1
          encDstOff = offset "copy!dstoff" idx' dstOffset
          encSrcOff = offset "copy!srcoff" idx' srcOffset
      child <- internal idx'
      pure $ "(store " <> child `sp` encDstOff `sp` "(select copy!src " <> encSrcOff <> "))"
    offset :: Builder -> W256 -> Expr EWord -> Builder
    offset _ o (Lit b) = wordAsBV $ o + b
    offset name 0 _ = name
    offset name o _ = "(bvadd " <> name <> " (_ bv" <> fromString (show (into o :: Integer)) <> " 256))"
copySliceWith _ _ _ _ _ _ = Left "CopySlice with a symbolically sized region not currently implemented, cannot execute SMT solver on this query"

expandExpWith :: ArithEncoding -> Expr EWord -> W256 -> Err Builder
expandExpWith arithEnc base expnt
  -- in EVM, anything (including 0) to the power of 0 is 1
  | expnt == 0 = pure one
  | expnt == 1 = exprToSMTWith arithEnc base
  | otherwise = do
    -- by squaring, binding the base and each square once: inlining them repeats the base
    -- expnt times, and nested exponentiations multiply that
    b <- exprToSMTWith arithEnc base
    let bits = takeWhile (> 0) (iterate (`shiftR` 1) expnt)
        sq :: Int -> Builder
        sq i = "exp!sq" <> fromString (show i)
        squares = [ "(let ((" <> sq i <> " " <> (if i == 0 then b else "(bvmul " <> sq (i - 1) `sp` sq (i - 1) <> ")") <> ")) "
                  | i <- [0 .. length bits - 1] ]
        used = [sq i | (i, k) <- zip [0 ..] bits, testBit k 0]
        prod = foldr1 (\x acc -> "(bvmul " <> x `sp` acc <> ")") used
    pure $ mconcat squares <> prod <> mconcat (replicate (length bits) ")")

concatBytesWith :: ArithEncoding -> [Expr Byte] -> Err Builder
concatBytesWith arithEnc bytes = do
  case List.uncons $ reverse bytes of
    Nothing -> Left "unexpected empty bytes"
    Just (h, t) -> do
      a2 <- exprToSMTWith arithEnc h
      foldM wrap a2 t
  where
    wrap :: Builder -> Expr a -> Err Builder
    wrap inner byte = do
      byteSMT <- exprToSMTWith arithEnc byte
      pure $ "(concat " <> byteSMT `sp` inner <> ")"

writeBytesWith :: ArithEncoding -> ByteString -> Expr Buf -> Err Builder
writeBytesWith arithEnc bytes buf =  do
  smtText <- exprToSMTWith arithEnc buf
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

encodeConcreteStore :: ArithEncoding -> Map W256 W256 -> Err Builder
encodeConcreteStore enc s = foldM encodeWrite ("((as const Storage) #x0000000000000000000000000000000000000000000000000000000000000000)") (Map.toList s)
  where
    encodeWrite :: Builder -> (W256, W256) -> Err Builder
    encodeWrite prev (key, val) = do
      encKey <- exprToSMTWith enc $ Lit key
      encVal <- exprToSMTWith enc $ Lit val
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
  | Just a <- TS.stripPrefix "gas_" name
  , n <- TS.takeWhileEnd isDigit a
  , not (TS.null n) = Gas (TS.dropWhileEnd isDigit a) (read (TS.unpack n))
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
              -- bytes past the length read as zero, so the solver is free to
              -- put anything at unread ones (even 2^256-1), which can't be flattened
              Just $ if pidx >= len then pbase else Write pval pidx pbase

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
  -> Map W256 LogicalStore
  -> StorageReads
  -> MaybeIO (Map (Expr EAddr) (Map W256 W256))
getStore getVal stores (StorageReads innerMap) = do
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
      real <- hoistMaybe $ realSlot idx slot'
      pure $ Map.insert real (fun slot') m) Map.empty (Set.toList slots)
    pure (addr, store)
  pure $ Map.fromListWith Map.union results
  where
    -- a decomposed store is indexed by the key within its mapping or array
    realSlot Nothing key = Just key
    realSlot (Just idx) key = case Map.lookup idx stores of
      Just (MapStore p) -> Just $ keccak' (word256Bytes key <> word256Bytes p)
      Just (ArrayStore p) -> Just $ keccak' (word256Bytes p) + key
      _ -> Nothing

-- | Ask the solver to give us the concrete value of an arbitrary abstract word
queryValue :: ValGetter -> Expr EWord -> MaybeIO W256
queryValue _ (Lit w) = pure w
queryValue getVal w = do
  -- this exprToSMTWith should never fail, since we have already ran the solver, in refined mode
  let expr = toLazyText $ fromRight' $ exprToSMTWith ConcreteArith w
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


hoistMaybe :: Monad m => Maybe a -> MaybeT m a
hoistMaybe = MaybeT . pure
