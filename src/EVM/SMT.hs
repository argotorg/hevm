{-# LANGUAGE QuasiQuotes #-}

{- |
    Module: EVM.SMT
    Description: Utilities for building and executing SMT queries from Expr instances
-}
module EVM.SMT where

import Prelude hiding (LT, GT)

import Control.Monad
import Data.Containers.ListUtils (nubOrd, nubInt)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Data.String.Here
import Data.Maybe (fromJust, fromMaybe, isJust, listToMaybe)
import Data.Either.Extra (fromRight')
import Data.Foldable (fold)
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
import Data.Text.Read (decimal)
import Language.SMT2.Parser (getValueRes, parseCommentFreeFileMsg)
import Language.SMT2.Syntax (Symbol, SpecConstant(..), GeneralRes(..), Term(..), QualIdentifier(..), Identifier(..), Sort(..), Index(..), VarBinding(..))
import Numeric (readHex, readBin)
import Witch (into, unsafeInto)
import EVM.Format (formatProp)

import EVM.CSE
import EVM.Expr (writeByte, bufLengthEnv, bufLength, minLength, inRange)
import EVM.Expr qualified as Expr
import EVM.Keccak (keccakAssumptions, keccakCompute)
import EVM.Traversals
import EVM.Types
import EVM.Effects


-- ** Encoding ** ----------------------------------------------------------------------------------


-- | Data that we need to construct a nice counterexample
data CexVars = CexVars
  { -- | variable names that we need models for to reconstruct calldata
    calldata     :: [Text]
    -- | symbolic address names
  , addrs        :: [Text]
    -- | buffer names and guesses at their maximum size
  , buffers      :: Map Text (Expr EWord)
    -- | reads from abstract storage
  , storeReads   :: Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
    -- | the names of any block context variables
  , blockContext :: [Text]
    -- | the names of any tx context variables
  , txContext    :: [Text]
  }
  deriving (Eq, Show)

instance Semigroup CexVars where
  (CexVars a b c d e f) <> (CexVars a2 b2 c2 d2 e2 f2) = CexVars (a <> a2) (b <> b2) (c <> c2) (d <> d2) (e <> e2) (f <> f2)

instance Monoid CexVars where
    mempty = CexVars
      { calldata = mempty
      , addrs = mempty
      , buffers = mempty
      , storeReads = mempty
      , blockContext = mempty
      , txContext = mempty
      }


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

-- Props are ONLY for pretty printing the query Props
data SMT2 = SMT2 [Builder] CexVars [Prop]
  deriving (Eq, Show)

instance Semigroup SMT2 where
  (SMT2 a c d) <> (SMT2 a2 c2 d2) = SMT2 (a <> a2) (c <> c2) (d <> d2)

instance Monoid SMT2 where
  mempty = SMT2 mempty mempty mempty

formatSMT2 :: SMT2 -> Text
formatSMT2 (SMT2 ls _ ps) = expr <> smt2
 where
 expr = T.concat [T.singleton ';', T.replace "\n" "\n;" $ T.pack . TS.unpack $  TS.unlines (fmap formatProp ps)]
 smt2 = T.unlines (fmap toLazyText ls)

-- | Reads all intermediate variables from the builder state and produces SMT declaring them as constants
declareIntermediates :: BufEnv -> StoreEnv -> Err SMT2
declareIntermediates bufs stores = do
  let encSs = Map.mapWithKey encodeStore stores
      encBs = Map.mapWithKey encodeBuf bufs
      sorted = List.sortBy compareFst $ Map.toList $ encSs <> encBs
  decls <- mapM snd sorted
  let smt2 = (SMT2 [fromText "; intermediate buffers & stores"] mempty mempty):decls
  pure $ fold smt2
  where
    compareFst (l, _) (r, _) = compare l r
    encodeBuf n expr = do
      buf <- exprToSMT expr
      bufLen <- encodeBufLen n expr
      pure $ SMT2 ["(define-fun buf" <> (fromString . show $ n) <> "() Buf " <> buf <> ")\n"]  mempty mempty <> bufLen
    encodeBufLen n expr = do
      bufLen <- exprToSMT (bufLengthEnv bufs True expr)
      pure $ SMT2 ["(define-fun buf" <> (fromString . show $ n) <>"_length () (_ BitVec 256) " <> bufLen <> ")"] mempty mempty
    encodeStore n expr = do
      storage <- exprToSMT expr
      pure $ SMT2 ["(define-fun store" <> (fromString . show $ n) <> " () Storage " <> storage <> ")"] mempty mempty

smt2Line :: Builder -> SMT2
smt2Line txt = SMT2 [txt] mempty mempty

-- simplify to rewrite sload/sstore combos
-- notice: it is VERY important not to concretize early, because Keccak assumptions
--         need unconcretized Props
assertProps :: Config -> [Prop] -> Err SMT2
assertProps conf ps =
  if not conf.simp then assertPropsHelper False ps
  else assertPropsHelper True (decompose . Expr.simplifyProps $ ps)
  where
    decompose :: [Prop] -> [Prop]
    decompose props = if conf.decomposeStorage && safeExprs && safeProps
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
assertPropsHelper simp psPreConc = do
 encs <- mapM propToSMT psElim
 intermediates <- declareIntermediates bufs stores
 readAssumes' <- readAssumes
 keccakAssertions' <- keccakAssertions
 frameCtxs <- (declareFrameContext . nubOrd $ foldl (<>) [] frameCtx)
 blockCtxs <- (declareBlockContext . nubOrd $ foldl (<>) [] blockCtx)
 pure $ prelude
  <> (declareAbstractStores abstractStores)
  <> smt2Line ""
  <> declareConstrainAddrs addresses
  <> smt2Line ""
  <> (declareBufs toDeclarePsElim bufs stores)
  <> smt2Line ""
  <> (declareVars . nubOrd $ foldl (<>) [] allVars)
  <> smt2Line ""
  <> frameCtxs
  <> smt2Line ""
  <> blockCtxs
  <> smt2Line ""
  <> intermediates
  <> smt2Line ""
  <> keccakAssertions'
  <> readAssumes'
  <> gasOrder
  <> smt2Line ""
  <> SMT2 (fmap (\p -> "(assert " <> p <> ")") encs) (cexInfo storageReads) ps

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
    storageReads = Map.unionsWith (<>) $ fmap findStorageReads toDeclarePs
    abstractStores = Set.toList $ Set.unions (fmap referencedAbstractStores toDeclarePs)
    addresses = Set.toList $ Set.unions (fmap referencedAddrs toDeclarePs)

    -- Keccak assertions: concrete values, distance between pairs, injectivity, etc.
    --      This will make sure concrete values of Keccak are asserted, if they can be computed (i.e. can be concretized)
    keccAssump = keccakAssumptions psPreConc bufVals storeVals
    keccComp = keccakCompute psPreConc bufVals storeVals
    keccakAssertions = do
      assumps <- mapM assertSMT keccAssump
      comps <- mapM assertSMT keccComp
      pure $ smt2Line "; keccak assumptions"
        <> SMT2 assumps mempty mempty
        <> smt2Line "; keccak computations"
        <> SMT2 comps mempty mempty

    -- assert that reads beyond size of buffer & storage is zero
    readAssumes = do
      assumps <- mapM assertSMT $ assertReads psElim bufs stores
      pure $ smt2Line "; read assumptions" <> SMT2 assumps mempty mempty

    cexInfo :: Map (Expr 'EAddr, Maybe W256) (Set (Expr 'EWord)) -> CexVars
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
findStorageReads :: Prop -> Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
findStorageReads p = foldProp go mempty p
  where
    go :: Expr a -> Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
    go = \case
      SLoad slot store | baseIsAbstractStore store -> case Expr.getAddr store of
          Nothing -> internalError $ "could not extract address from: " <> show store
          Just address -> Map.singleton (address, Expr.getLogicalIdx store) (Set.singleton slot)
      _ -> mempty

    baseIsAbstractStore :: Expr 'Storage -> Bool
    baseIsAbstractStore (AbstractStore _ _) = True
    baseIsAbstractStore (ConcreteStore _) = False
    baseIsAbstractStore (SStore _ _ base) = baseIsAbstractStore base
    baseIsAbstractStore (GVar _) = internalError "Unexpected GVar"

findBufferAccess :: TraversableTerm a => [a] -> [(Expr EWord, Expr EWord, Expr Buf)]
findBufferAccess = foldl (foldTerm go) mempty
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

    bufMap = Map.unionWith Expr.max (foldl addBound mempty allReads) allBufs

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
declareBufs props bufEnv storeEnv = SMT2 ("; buffers" : fmap declareBuf allBufs <> ("; buffer lengths" : fmap declareLength allBufs)) cexvars mempty
  where
    cexvars = (mempty :: CexVars){ buffers = discoverMaxReads props bufEnv storeEnv }
    allBufs = fmap fromLazyText $ Map.keys cexvars.buffers
    declareBuf n = "(declare-fun " <> n <> " () (Array (_ BitVec 256) (_ BitVec 8)))"
    declareLength n = "(declare-fun " <> n <> "_length" <> " () (_ BitVec 256))"

-- Given a list of variable names, create an SMT2 object with the variables declared
declareVars :: [Builder] -> SMT2
declareVars names = SMT2 (["; variables"] <> fmap declare names) cexvars mempty
  where
    declare n = "(declare-fun " <> n <> " () (_ BitVec 256))"
    cexvars = (mempty :: CexVars){ calldata = fmap toLazyText names }

-- Given a list of variable names, create an SMT2 object with the variables declared
declareConstrainAddrs :: [Builder] -> SMT2
declareConstrainAddrs names = SMT2 (["; concrete and symbolic addresses"] <> fmap declare names <> fmap assume names) cexvars mempty
  where
    declare n = "(declare-fun " <> n <> " () Addr)"
    -- assume that symbolic addresses do not collide with the zero address or precompiles
    assume n = "(assert (bvugt " <> n <> " (_ bv9 160)))"
    cexvars = (mempty :: CexVars){ addrs = fmap toLazyText names }

-- The gas is a tuple of (prefix, index). Within each prefix, the gas is strictly decreasing as the
-- index increases. This function gets a map of Prefix -> [Int], and for each prefix,
-- enforces the order
enforceGasOrder :: [Prop] -> SMT2
enforceGasOrder ps = SMT2 (["; gas ordering"] <> (concatMap (uncurry order) indices)) mempty mempty
  where
    order :: TS.Text -> [Int] -> [Builder]
    order prefix n = consecutivePairs (nubInt n) >>= \(x, y)->
      -- The GAS instruction itself costs gas, so it's strictly decreasing
      ["(assert (bvugt " <> fromRight' (exprToSMT (Gas prefix x)) <> " " <>
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
  pure $ SMT2 (["; frame context"] <> decls) cexvars mempty
  where
    declare (n,props) = do
      asserts <- mapM assertSMT props
      pure $ [ "(declare-fun " <> n <> " () (_ BitVec 256))" ] <> asserts
    cexvars = (mempty :: CexVars){ txContext = fmap (toLazyText . fst) names }

declareAbstractStores :: [Builder] -> SMT2
declareAbstractStores names = SMT2 (["; abstract base stores"] <> fmap declare names) mempty mempty
  where
    declare n = "(declare-fun " <> n <> " () Storage)"

declareBlockContext :: [(Builder, [Prop])] -> Err SMT2
declareBlockContext names = do
  decls <- concatMapM declare names
  pure $ SMT2 (["; block context"] <> decls) cexvars mempty
  where
    declare (n, props) = do
      asserts <- mapM assertSMT props
      pure $ [ "(declare-fun " <> n <> " () (_ BitVec 256))" ] <> asserts
    cexvars = (mempty :: CexVars){ blockContext = fmap (toLazyText . fst) names }

assertSMT :: Prop -> Either String Builder
assertSMT p = do
  p' <- propToSMT p
  pure $ "(assert " <> p' <> ")"

prelude :: SMT2
prelude =  SMT2 src mempty mempty
  where
  src = fmap (fromLazyText . T.drop 2) . T.lines $ [i|
  ; logic
  (set-info :smt-lib-version 2.6)
  ;(set-logic QF_AUFBV)
  (set-logic ALL)
  (set-info :source |
  Generator: hevm
  Application: hevm symbolic execution system
  |)
  (set-info :category "industrial")

  ; types
  (define-sort Byte () (_ BitVec 8))
  (define-sort Word () (_ BitVec 256))
  (define-sort Addr () (_ BitVec 160))
  (define-sort Buf () (Array Word Byte))

  ; slot -> value
  (define-sort Storage () (Array Word Word))

  ; hash functions. They take buffer and a buffer size, and return a Word
  (declare-fun keccak (Buf Word) Word)
  (declare-fun sha256 (Buf Word) Word)

  ; helper functions
  (define-fun max ((a (_ BitVec 256)) (b (_ BitVec 256))) (_ BitVec 256) (ite (bvult a b) b a))

  ; word indexing
  (define-fun indexWord31 ((w Word)) Byte ((_ extract 7 0) w))
  (define-fun indexWord30 ((w Word)) Byte ((_ extract 15 8) w))
  (define-fun indexWord29 ((w Word)) Byte ((_ extract 23 16) w))
  (define-fun indexWord28 ((w Word)) Byte ((_ extract 31 24) w))
  (define-fun indexWord27 ((w Word)) Byte ((_ extract 39 32) w))
  (define-fun indexWord26 ((w Word)) Byte ((_ extract 47 40) w))
  (define-fun indexWord25 ((w Word)) Byte ((_ extract 55 48) w))
  (define-fun indexWord24 ((w Word)) Byte ((_ extract 63 56) w))
  (define-fun indexWord23 ((w Word)) Byte ((_ extract 71 64) w))
  (define-fun indexWord22 ((w Word)) Byte ((_ extract 79 72) w))
  (define-fun indexWord21 ((w Word)) Byte ((_ extract 87 80) w))
  (define-fun indexWord20 ((w Word)) Byte ((_ extract 95 88) w))
  (define-fun indexWord19 ((w Word)) Byte ((_ extract 103 96) w))
  (define-fun indexWord18 ((w Word)) Byte ((_ extract 111 104) w))
  (define-fun indexWord17 ((w Word)) Byte ((_ extract 119 112) w))
  (define-fun indexWord16 ((w Word)) Byte ((_ extract 127 120) w))
  (define-fun indexWord15 ((w Word)) Byte ((_ extract 135 128) w))
  (define-fun indexWord14 ((w Word)) Byte ((_ extract 143 136) w))
  (define-fun indexWord13 ((w Word)) Byte ((_ extract 151 144) w))
  (define-fun indexWord12 ((w Word)) Byte ((_ extract 159 152) w))
  (define-fun indexWord11 ((w Word)) Byte ((_ extract 167 160) w))
  (define-fun indexWord10 ((w Word)) Byte ((_ extract 175 168) w))
  (define-fun indexWord9 ((w Word)) Byte ((_ extract 183 176) w))
  (define-fun indexWord8 ((w Word)) Byte ((_ extract 191 184) w))
  (define-fun indexWord7 ((w Word)) Byte ((_ extract 199 192) w))
  (define-fun indexWord6 ((w Word)) Byte ((_ extract 207 200) w))
  (define-fun indexWord5 ((w Word)) Byte ((_ extract 215 208) w))
  (define-fun indexWord4 ((w Word)) Byte ((_ extract 223 216) w))
  (define-fun indexWord3 ((w Word)) Byte ((_ extract 231 224) w))
  (define-fun indexWord2 ((w Word)) Byte ((_ extract 239 232) w))
  (define-fun indexWord1 ((w Word)) Byte ((_ extract 247 240) w))
  (define-fun indexWord0 ((w Word)) Byte ((_ extract 255 248) w))

  ; symbolic word indexing
  ; a bitshift based version might be more performant here...
  (define-fun indexWord ((idx Word) (w Word)) Byte
    (ite (bvuge idx (_ bv32 256)) (_ bv0 8)
    (ite (= idx (_ bv31 256)) (indexWord31 w)
    (ite (= idx (_ bv30 256)) (indexWord30 w)
    (ite (= idx (_ bv29 256)) (indexWord29 w)
    (ite (= idx (_ bv28 256)) (indexWord28 w)
    (ite (= idx (_ bv27 256)) (indexWord27 w)
    (ite (= idx (_ bv26 256)) (indexWord26 w)
    (ite (= idx (_ bv25 256)) (indexWord25 w)
    (ite (= idx (_ bv24 256)) (indexWord24 w)
    (ite (= idx (_ bv23 256)) (indexWord23 w)
    (ite (= idx (_ bv22 256)) (indexWord22 w)
    (ite (= idx (_ bv21 256)) (indexWord21 w)
    (ite (= idx (_ bv20 256)) (indexWord20 w)
    (ite (= idx (_ bv19 256)) (indexWord19 w)
    (ite (= idx (_ bv18 256)) (indexWord18 w)
    (ite (= idx (_ bv17 256)) (indexWord17 w)
    (ite (= idx (_ bv16 256)) (indexWord16 w)
    (ite (= idx (_ bv15 256)) (indexWord15 w)
    (ite (= idx (_ bv14 256)) (indexWord14 w)
    (ite (= idx (_ bv13 256)) (indexWord13 w)
    (ite (= idx (_ bv12 256)) (indexWord12 w)
    (ite (= idx (_ bv11 256)) (indexWord11 w)
    (ite (= idx (_ bv10 256)) (indexWord10 w)
    (ite (= idx (_ bv9 256)) (indexWord9 w)
    (ite (= idx (_ bv8 256)) (indexWord8 w)
    (ite (= idx (_ bv7 256)) (indexWord7 w)
    (ite (= idx (_ bv6 256)) (indexWord6 w)
    (ite (= idx (_ bv5 256)) (indexWord5 w)
    (ite (= idx (_ bv4 256)) (indexWord4 w)
    (ite (= idx (_ bv3 256)) (indexWord3 w)
    (ite (= idx (_ bv2 256)) (indexWord2 w)
    (ite (= idx (_ bv1 256)) (indexWord1 w)
    (indexWord0 w)
    ))))))))))))))))))))))))))))))))
  )

  (define-fun readWord ((idx Word) (buf Buf)) Word
    (concat
      (select buf idx)
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f))
      ))))))))))))))))))))))))))))))
    )
  )

  (define-fun writeWord ((idx Word) (val Word) (buf Buf)) Buf
      (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store
      (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store buf
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f) (indexWord31 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e) (indexWord30 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d) (indexWord29 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c) (indexWord28 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b) (indexWord27 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a) (indexWord26 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019) (indexWord25 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018) (indexWord24 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017) (indexWord23 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016) (indexWord22 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015) (indexWord21 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014) (indexWord20 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013) (indexWord19 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012) (indexWord18 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011) (indexWord17 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010) (indexWord16 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f) (indexWord15 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e) (indexWord14 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d) (indexWord13 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c) (indexWord12 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b) (indexWord11 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a) (indexWord10 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009) (indexWord9 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008) (indexWord8 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007) (indexWord7 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006) (indexWord6 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005) (indexWord5 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004) (indexWord4 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003) (indexWord3 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002) (indexWord2 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001) (indexWord1 val))
      idx (indexWord0 val))
  )

  ; block context
  (declare-fun blockhash (Word) Word)
  (declare-fun codesize (Addr) Word)

  ; macros
  (define-fun signext ( (b Word) (val Word)) Word
    (ite (= b (_ bv0  256)) ((_ sign_extend 248) ((_ extract 7    0) val))
    (ite (= b (_ bv1  256)) ((_ sign_extend 240) ((_ extract 15   0) val))
    (ite (= b (_ bv2  256)) ((_ sign_extend 232) ((_ extract 23   0) val))
    (ite (= b (_ bv3  256)) ((_ sign_extend 224) ((_ extract 31   0) val))
    (ite (= b (_ bv4  256)) ((_ sign_extend 216) ((_ extract 39   0) val))
    (ite (= b (_ bv5  256)) ((_ sign_extend 208) ((_ extract 47   0) val))
    (ite (= b (_ bv6  256)) ((_ sign_extend 200) ((_ extract 55   0) val))
    (ite (= b (_ bv7  256)) ((_ sign_extend 192) ((_ extract 63   0) val))
    (ite (= b (_ bv8  256)) ((_ sign_extend 184) ((_ extract 71   0) val))
    (ite (= b (_ bv9  256)) ((_ sign_extend 176) ((_ extract 79   0) val))
    (ite (= b (_ bv10 256)) ((_ sign_extend 168) ((_ extract 87   0) val))
    (ite (= b (_ bv11 256)) ((_ sign_extend 160) ((_ extract 95   0) val))
    (ite (= b (_ bv12 256)) ((_ sign_extend 152) ((_ extract 103  0) val))
    (ite (= b (_ bv13 256)) ((_ sign_extend 144) ((_ extract 111  0) val))
    (ite (= b (_ bv14 256)) ((_ sign_extend 136) ((_ extract 119  0) val))
    (ite (= b (_ bv15 256)) ((_ sign_extend 128) ((_ extract 127  0) val))
    (ite (= b (_ bv16 256)) ((_ sign_extend 120) ((_ extract 135  0) val))
    (ite (= b (_ bv17 256)) ((_ sign_extend 112) ((_ extract 143  0) val))
    (ite (= b (_ bv18 256)) ((_ sign_extend 104) ((_ extract 151  0) val))
    (ite (= b (_ bv19 256)) ((_ sign_extend 96 ) ((_ extract 159  0) val))
    (ite (= b (_ bv20 256)) ((_ sign_extend 88 ) ((_ extract 167  0) val))
    (ite (= b (_ bv21 256)) ((_ sign_extend 80 ) ((_ extract 175  0) val))
    (ite (= b (_ bv22 256)) ((_ sign_extend 72 ) ((_ extract 183  0) val))
    (ite (= b (_ bv23 256)) ((_ sign_extend 64 ) ((_ extract 191  0) val))
    (ite (= b (_ bv24 256)) ((_ sign_extend 56 ) ((_ extract 199  0) val))
    (ite (= b (_ bv25 256)) ((_ sign_extend 48 ) ((_ extract 207  0) val))
    (ite (= b (_ bv26 256)) ((_ sign_extend 40 ) ((_ extract 215  0) val))
    (ite (= b (_ bv27 256)) ((_ sign_extend 32 ) ((_ extract 223  0) val))
    (ite (= b (_ bv28 256)) ((_ sign_extend 24 ) ((_ extract 231  0) val))
    (ite (= b (_ bv29 256)) ((_ sign_extend 16 ) ((_ extract 239  0) val))
    (ite (= b (_ bv30 256)) ((_ sign_extend 8  ) ((_ extract 247  0) val)) val))))))))))))))))))))))))))))))))
  |]

wordAsBV :: forall a. Integral a => a -> Builder
wordAsBV w = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal w <> " 256)"

byteAsBV :: Word8 -> Builder
byteAsBV b = "(_ bv" <> Data.Text.Lazy.Builder.Int.decimal b <> " 8)"

exprToSMT :: Expr a -> Err Builder
exprToSMT = \case
  Lit w -> pure $ wordAsBV w
  Var s -> pure $ fromText s
  GVar (BufVar n) -> pure $ fromString $ "buf" <> (show n)
  GVar (StoreVar n) -> pure $ fromString $ "store" <> (show n)
  JoinBytes
    z o two three four five six seven
    eight nine ten eleven twelve thirteen fourteen fifteen
    sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
    twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone
    -> concatBytes [
        z, o, two, three, four, five, six, seven
        , eight, nine, ten, eleven, twelve, thirteen, fourteen, fifteen
        , sixteen, seventeen, eighteen, nineteen, twenty, twentyone, twentytwo, twentythree
        , twentyfour, twentyfive, twentysix, twentyseven, twentyeight, twentynine, thirty, thirtyone]

  Add a b -> op2 "bvadd" a b
  Sub a b -> op2 "bvsub" a b
  Mul a b -> op2 "bvmul" a b
  Exp a b -> case a of
    -- Lit 1 has already been handled via Expr.simplify
    Lit 0 -> do
      benc <- exprToSMT b
      pure $ "(ite (= " <> benc `sp` zero <> " ) " <> one `sp` zero <> ")"
    _ -> case b of
      Lit b' -> expandExp a b'
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
  And a b -> op2 "bvand" a b
  Or a b -> op2 "bvor" a b
  Xor a b -> op2 "bvxor" a b
  Not a -> op1 "bvnot" a
  SHL a b -> op2 "bvshl" b a
  SHR a b -> op2 "bvlshr" b a
  SAR a b -> op2 "bvashr" b a
  SEx a b -> op2 "signext" a b
  Div a b -> op2CheckZero "bvudiv" a b
  SDiv a b -> op2CheckZero "bvsdiv" a b
  Mod a b -> op2CheckZero "bvurem" a b
  SMod a b -> op2CheckZero "bvsrem" a b
  -- NOTE: this needs to do the MUL at a higher precision, then MOD, then downcast
  MulMod a b c -> do
    aExp <- exprToSMT a
    bExp <- exprToSMT b
    cExp <- exprToSMT c
    let aLift = "((_ zero_extend 256) " <> aExp <> ")"
        bLift = "((_ zero_extend 256) " <> bExp <> ")"
        cLift = "((_ zero_extend 256) " <> cExp <> ")"
    pure $ "(ite (= " <> cExp <> " (_ bv0 256)) (_ bv0 256) ((_ extract 255 0) (bvurem (bvmul " <> aLift `sp` bLift <> ")" <> cLift <> ")))"
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
  SHA256 a -> do
    enc <- exprToSMT a
    sz  <- exprToSMT $ Expr.bufLength a
    pure $ "(sha256 " <> enc <> " " <> sz <> ")"

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
  ConcreteBuf bs -> writeBytes bs mempty
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
    copySlice srcIdx dstIdx size srcSMT dstSMT

  -- we need to do a bit of processing here.
  ConcreteStore s -> encodeConcreteStore s
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
    op1 op a = do
      enc <- exprToSMT a
      pure $ "(" <> op `sp` enc <> ")"
    op2 op a b = do
       aenc <- exprToSMT a
       benc <- exprToSMT b
       pure $ "(" <> op `sp` aenc `sp` benc <> ")"
    op2CheckZero op a b = do
      aenc <- exprToSMT a
      benc <- exprToSMT b
      pure $ "(ite (= " <> benc <> " (_ bv0 256)) (_ bv0 256) " <>  "(" <> op `sp` aenc `sp` benc <> "))"

sp :: Builder -> Builder -> Builder
a `sp` b = a <> (fromText " ") <> b

zero :: Builder
zero = "(_ bv0 256)"

one :: Builder
one = "(_ bv1 256)"

propToSMT :: Prop -> Err Builder
propToSMT = \case
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
  where
    op2 op a b = do
      aenc <- exprToSMT a
      benc <- exprToSMT b
      pure $ "(" <> op <> " " <> aenc <> " " <> benc <> ")"



-- ** Helpers ** ---------------------------------------------------------------------------------


-- | Stores a region of src into dst
copySlice :: Expr EWord -> Expr EWord -> Expr EWord -> Builder -> Builder -> Err Builder
copySlice srcOffset dstOffset size0@(Lit _) src dst = do
  sz <- internal size0
  pure $ "(let ((src " <> src <> ")) " <> sz <> ")"
  where
    internal (Lit 0) = pure dst
    internal size = do
      let size' = (Expr.sub size (Lit 1))
      encDstOff <- exprToSMT (Expr.add dstOffset size')
      encSrcOff <- exprToSMT (Expr.add srcOffset size')
      child <- internal size'
      pure $ "(store " <> child `sp` encDstOff `sp` "(select src " <> encSrcOff <> "))"
copySlice _ _ _ _ _ = Left "CopySlice with a symbolically sized region not currently implemented, cannot execute SMT solver on this query"

-- | Unrolls an exponentiation into a series of multiplications
expandExp :: Expr EWord -> W256 -> Err Builder
expandExp base expnt
  -- in EVM, anything (including 0) to the power of 0 is 1
  | expnt == 0 = pure one
  | expnt == 1 = exprToSMT base
  | otherwise = do
    b <- exprToSMT base
    n <- expandExp base (expnt - 1)
    pure $ "(bvmul " <> b `sp` n <> ")"

-- | Concatenates a list of bytes into a larger bitvector
concatBytes :: [Expr Byte] -> Err Builder
concatBytes bytes = do
  case List.uncons $ reverse bytes of
    Nothing -> Left "unexpected empty bytes"
    Just (h, t) -> do
      a2 <- exprToSMT h
      foldM wrap a2 t
  where
    wrap :: Builder -> Expr a -> Err Builder
    wrap inner byte = do
      byteSMT <- exprToSMT byte
      pure $ "(concat " <> byteSMT `sp` inner <> ")"

-- | Concatenates a list of bytes into a larger bitvector
writeBytes :: ByteString -> Expr Buf -> Err Builder
writeBytes bytes buf =  do
  smtText <- exprToSMT buf
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

parseInteger :: SpecConstant -> Integer
parseInteger = parseSC

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

parseErr :: (Show a) => a -> b
parseErr res = internalError $ "cannot parse solver response: " <> show res

parseVar :: TS.Text -> Expr EWord
parseVar = Var

parseEAddr :: TS.Text -> Expr EAddr
parseEAddr name
  | Just a <- TS.stripPrefix "litaddr_" name = LitAddr (read (TS.unpack a))
  | Just a <- TS.stripPrefix "symaddr_" name = SymAddr a
  | otherwise = internalError $ "cannot parse: " <> show name

textToInt :: TS.Text -> Int
textToInt text = case decimal text of
  Right (value, _) -> value
  Left _ -> internalError $ "cannot parse '" <> (TS.unpack text) <> "' into an Int"

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

getAddrs :: (TS.Text -> Expr EAddr) -> (Text -> IO Text) -> [TS.Text] -> IO (Map (Expr EAddr) Addr)
getAddrs parseName getVal names = Map.mapKeys parseName <$> foldM (getOne parseAddr getVal) mempty names

getVars :: (TS.Text -> Expr EWord) -> (Text -> IO Text) -> [TS.Text] -> IO (Map (Expr EWord) W256)
getVars parseName getVal names = Map.mapKeys parseName <$> foldM (getOne parseW256 getVal) mempty names

getOne :: (SpecConstant -> a) -> (Text -> IO Text) -> Map TS.Text a -> TS.Text -> IO (Map TS.Text a)
getOne parseVal getVal acc name = do
  raw <- getVal (T.fromStrict name)
  let
    parsed = case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
      Right (ResSpecific (valParsed :| [])) -> valParsed
      r -> parseErr r
    val = case parsed of
      (TermQualIdentifier (
        Unqualified (IdSymbol symbol)),
        TermSpecConstant sc)
          -> if symbol == name
             then parseVal sc
             else internalError "solver did not return model for requested value"
      r -> parseErr r
  pure $ Map.insert name val acc

-- | Queries the solver for models for each of the expressions representing the
-- max read index for a given buffer
queryMaxReads :: (Text -> IO Text) -> Map Text (Expr EWord)  -> IO (Map Text W256)
queryMaxReads getVal maxReads = mapM (queryValue getVal) maxReads

-- | Gets the initial model for each buffer, these will often be much too large for our purposes
getBufs :: (Text -> IO Text) -> [Text] -> IO (Map (Expr Buf) BufModel)
getBufs getVal bufs = foldM getBuf mempty bufs
  where
    getLength :: Text -> IO W256
    getLength name = do
      val <- getVal (name <> "_length ")
      pure $ case parseCommentFreeFileMsg getValueRes (T.toStrict val) of
        Right (ResSpecific (parsed :| [])) -> case parsed of
          (TermQualIdentifier (Unqualified (IdSymbol symbol)), (TermSpecConstant sc))
            -> if symbol == (T.toStrict $ name <> "_length")
               then parseW256 sc
               else internalError "solver did not return model for requested value"
          res -> parseErr res
        res -> parseErr res

    getBuf :: Map (Expr Buf) BufModel -> Text -> IO (Map (Expr Buf) BufModel)
    getBuf acc name = do
      len <- getLength name
      val <- getVal name

      buf <- case parseCommentFreeFileMsg getValueRes (T.toStrict val) of
        Right (ResSpecific (valParsed :| [])) -> case valParsed of
          (TermQualIdentifier (Unqualified (IdSymbol symbol)), term)
            -> if (T.fromStrict symbol) == name
               then pure $ parseBuf len term
               else internalError "solver did not return model for requested value"
          res -> internalError $ "cannot parse solver response: " <> show res
        res -> internalError $ "cannot parse solver response: " <> show res
      pure $ Map.insert (AbstractBuf $ T.toStrict name) buf acc

    parseBuf :: W256 -> Term -> BufModel
    parseBuf len = Comp . go mempty
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
            -> Base (parseW8 val) len

          -- writing a byte over some array
          (TermApplication
            (Unqualified (IdSymbol "store"))
            (base :| [TermSpecConstant idx, TermSpecConstant val])
            ) -> let
              pbase = go env base
              pidx = parseW256 idx
              pval = parseW8 val
            in Write pval pidx pbase

          -- binding a new name
          (TermLet ((VarBinding name bound) :| []) term) -> let
              pbound = go env bound
            in go (Map.insert name pbound env) term

          -- looking up a bound name
          (TermQualIdentifier (Unqualified (IdSymbol name))) -> case Map.lookup name env of
            Just t -> t
            Nothing -> internalError $ "could not find "
                            <> (TS.unpack name)
                            <> " in environment mapping"
          p -> parseErr p

-- | Takes a Map containing all reads from a store with an abstract base, as
-- well as the concrete part of the storage prestate and returns a fully
-- concretized storage
getStore
  :: (Text -> IO Text)
  -> Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
  -> IO (Map (Expr EAddr) (Map W256 W256))
getStore getVal abstractReads =
  fmap Map.fromList $ forM (Map.toList abstractReads) $ \((addr, idx), slots) -> do
    let name = toLazyText (storeName addr idx)
    raw <- getVal name
    let parsed = case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
                   Right (ResSpecific (valParsed :| [])) -> valParsed
                   r -> parseErr r
        -- first interpret SMT term as a function
        fun = case parsed of
                (TermQualIdentifier (Unqualified (IdSymbol symbol)), term) ->
                  if symbol == (T.toStrict name)
                  then interpret1DArray Map.empty term
                  else internalError "solver did not return model for requested value"
                r -> parseErr r

    -- then create a map by adding only the locations that are read by the program
    store <- foldM (\m slot -> do
      slot' <- queryValue getVal slot
      pure $ Map.insert slot' (fun slot') m) Map.empty slots
    pure (addr, store)

-- | Ask the solver to give us the concrete value of an arbitrary abstract word
queryValue :: (Text -> IO Text) -> Expr EWord -> IO W256
queryValue _ (Lit w) = pure w
queryValue getVal w = do
  -- this exprToSMT should never fail, since we have already ran the solver
  let expr = toLazyText $ fromRight' $ exprToSMT w
  raw <- getVal expr
  case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
    Right (ResSpecific (valParsed :| [])) ->
      case valParsed of
        (_, TermSpecConstant sc) -> pure $ parseW256 sc
        _ -> internalError $ "cannot parse model for: " <> show w
    r -> parseErr r

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
