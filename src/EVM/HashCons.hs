{- |
    Module: EVM.HashCons
    Description: Construction-time hash-consing (structural sharing) for the Expr AST.

    The symbolic interpreter rebuilds structurally-identical subterms as separate heap objects
    (e.g. a mapping-slot keccak recomputed on every storage access), so a computation that reuses
    an intermediate at k nesting levels materializes a 2^k tree with no sharing. On storage-heavy
    targets this exhausts memory (observed: a 914-node DAG materialized as a 601,664-node tree,
    22 GB peak), and it makes every structural traversal or comparison pay the logical - not the
    shared - size.

    'hashConsExpr' returns a canonical representative for a node: the first structurally-equal node
    ever seen is reused for all later duplicates, so the heap holds the DAG, not the tree. It is
    exact (never merges structurally-different terms) and O(1) amortized per constructed node:

      * a StableName table shortcuts nodes that are ALREADY canonical, so canonical subtrees
        (e.g. operands taken off the stack) are not re-traversed, and
      * the structural tables are keyed by (constructor tag, scalar payload, child ids) - all
        shallow - so a lookup never compares whole subterms.

    Canonicalization also makes physical identity a cheap witness for structural equality, which
    the ptrEq fast paths in Expr's Eq/Ord instances and 'untilFixpoint' exploit: comparisons on
    shared terms drop from O(logical size) to O(size of the differing part).

    hashConsExpr e is always structurally equal to e, so it is semantically the identity; it only
    shares memory. Gated by 'setHashConsEnabled' (off by default): when disabled every call is a
    single IORef read returning the argument unchanged, so ordinary (non-symbolic) use is
    unaffected.

    The tables are module-global state in the style of GHC's FastString table: this module is the
    only code that can touch them, a canonical node never changes meaning (the tables are only
    ever consulted to return an already-constructed, structurally-equal node), and
    'resetHashCons' is called at the start of each symbolic exploration so entries never leak
    between runs.
-}
module EVM.HashCons
  ( Rewrite(..)
  , runRewrite
  , hashConsExpr
  , setHashConsEnabled
  , hashConsEnabled
  , resetHashCons
  , memoFixTraverse
  ) where

import Prelude hiding (LT, GT)
import Data.IORef
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.IntMap.Strict qualified as IM
import Control.Monad (unless)
import Data.Word (Word8)
import Data.Text (Text)
import Data.ByteString (ByteString)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName
import GHC.StaticPtr (StaticPtr, StaticKey, staticKey, deRefStaticPtr)

import EVM.Traversals.Children (mapChildrenM)
import EVM.Types

-- | Scalar data carried by leaf/annotated constructors, folded into the structural key so that
-- e.g. two different literals are never merged.
data Payload
  = P0
  | PW  !W256
  | PT  !Text
  | PB8 !Word8
  | PBS !ByteString
  | PAddr !Addr
  | PMW !(Maybe W256)
  | PStore ![(W256, W256)]
  | PGas !Text !Int
  | PInt !Int
  deriving (Eq, Ord)

-- | Structural key: constructor tag, scalar payload, child ids. All shallow.
type Key = (Int, Payload, [Int])

-- | A type-erased StableName. 'eqStableName' compares heterogeneously, so no coercion is ever
-- needed to look a name up again.
data SomeSN = forall x. SomeSN !(StableName x)

-- | One canonical-node table per expression type, so nodes are recovered at their own type and
-- no unsafe coercion is involved anywhere.
data HCState = HCState
  { hcWords  :: !(Map Key (Expr EWord, Int))
  , hcBytes  :: !(Map Key (Expr Byte, Int))
  , hcBufs   :: !(Map Key (Expr Buf, Int))
  , hcStores :: !(Map Key (Expr Storage, Int))
  , hcAddrs  :: !(Map Key (Expr EAddr, Int))
  , hcSns    :: !(IM.IntMap [(SomeSN, Int)])  -- ^ hashStableName -> [(name, id)]: node -> id
  , hcNext   :: !Int
  }

emptyHC :: HCState
emptyHC = HCState M.empty M.empty M.empty M.empty M.empty IM.empty 0

{-# NOINLINE hcEnabled #-}
hcEnabled :: IORef Bool
hcEnabled = unsafePerformIO (newIORef False)

{-# NOINLINE hcState #-}
hcState :: IORef HCState
hcState = unsafePerformIO (newIORef emptyHC)

setHashConsEnabled :: Bool -> IO ()
setHashConsEnabled = writeIORef hcEnabled

resetHashCons :: IO ()
resetHashCons = do
  -- The id counter survives the reset: ids are never reused, so if another exploration is
  -- still running (parallel test suites), its stale memo entries reference ids that no new
  -- node can be assigned — a mid-run reset can only lose sharing, never correctness.
  atomicModifyIORef' hcState $ \st -> (emptyHC { hcNext = st.hcNext }, ())
  writeIORef passMemos M.empty

-- | Per-pass memo of simplification results, keyed by canonical node id, with one table per
-- expression type. Values are recovered at their own type by dispatching on the node's
-- constructor (which fixes the type via GADT refinement), so no coercion is involved. Cleared
-- together with the hash-consing tables.
data MemoTables = MemoTables
  { mtW  :: !(IM.IntMap (Expr EWord))
  , mtBy :: !(IM.IntMap (Expr Byte))
  , mtBu :: !(IM.IntMap (Expr Buf))
  , mtS  :: !(IM.IntMap (Expr Storage))
  , mtA  :: !(IM.IntMap (Expr EAddr))
  }

emptyMT :: MemoTables
emptyMT = MemoTables IM.empty IM.empty IM.empty IM.empty IM.empty

{-# NOINLINE passMemos #-}
passMemos :: IORef (Map StaticKey MemoTables)
passMemos = unsafePerformIO (newIORef M.empty)

-- | The canonical-node table and the memo table for one expression type
data Table a = Table
  { nodes    :: HCState -> Map Key (Expr a, Int)
  , setNodes :: HCState -> Map Key (Expr a, Int) -> HCState
  , memo     :: MemoTables -> IM.IntMap (Expr a)
  , setMemo  :: MemoTables -> IM.IntMap (Expr a) -> MemoTables
  }

wordT :: Table EWord
wordT = Table (.hcWords) (\s t -> s { hcWords = t }) (.mtW) (\m t -> m { mtW = t })

byteT :: Table Byte
byteT = Table (.hcBytes) (\s t -> s { hcBytes = t }) (.mtBy) (\m t -> m { mtBy = t })

bufT :: Table Buf
bufT = Table (.hcBufs) (\s t -> s { hcBufs = t }) (.mtBu) (\m t -> m { mtBu = t })

storeT :: Table Storage
storeT = Table (.hcStores) (\s t -> s { hcStores = t }) (.mtS) (\m t -> m { mtS = t })

addrT :: Table EAddr
addrT = Table (.hcAddrs) (\s t -> s { hcAddrs = t }) (.mtA) (\m t -> m { mtA = t })

-- | How a node is hash-consed. Matching on the constructor fixes the type, so nodes come back
-- out of the tables at their own type.
data Shape a
  = Keyed (Table a) Payload  -- ^ shared by structure: constructor, payload and child ids
  | Unkeyed (Table a)        -- ^ given an identity, but an equal node built later is not shared
  | Untabled                 -- ^ End, Log and EContract nodes: an identity, and no memo either

-- | No wildcard, so a new constructor does not compile until it is given a shape here. A
-- constructor with a field that is not a term must put that field in the payload, or terms that
-- differ only there are merged.
shape :: Expr a -> Shape a
shape = \case
  Lit x -> ew (PW x); Var t -> ew (PT t); Gas p i -> ew (PGas p i)
  Origin -> ew P0; Coinbase -> ew P0; Timestamp -> ew P0; BlockNumber -> ew P0
  PrevRandao -> ew P0; GasLimit -> ew P0; ChainId -> ew P0; BaseFee -> ew P0
  TxValue -> ew P0
  IsZero{} -> ew P0; Not{} -> ew P0; CLZ{} -> ew P0; BlockHash{} -> ew P0
  Keccak{} -> ew P0; BufLength{} -> ew P0; WAddr{} -> ew P0; Balance{} -> ew P0
  CodeSize{} -> ew P0; CodeHash{} -> ew P0
  Add{} -> ew P0; Sub{} -> ew P0; Mul{} -> ew P0; Div{} -> ew P0; SDiv{} -> ew P0
  Mod{} -> ew P0; SMod{} -> ew P0; Exp{} -> ew P0; SEx{} -> ew P0; Min{} -> ew P0
  Max{} -> ew P0; LT{} -> ew P0; GT{} -> ew P0; LEq{} -> ew P0; GEq{} -> ew P0
  SLT{} -> ew P0; SGT{} -> ew P0; Eq{} -> ew P0; And{} -> ew P0; Or{} -> ew P0
  Xor{} -> ew P0; SHL{} -> ew P0; SHR{} -> ew P0; SAR{} -> ew P0
  EqByte{} -> ew P0; ReadWord{} -> ew P0; SLoad{} -> ew P0
  AddMod{} -> ew P0; MulMod{} -> ew P0; ITE{} -> ew P0
  JoinBytes{} -> Unkeyed wordT
  LitByte w -> Keyed byteT (PB8 w); IndexWord{} -> Keyed byteT P0; ReadByte{} -> Keyed byteT P0
  SymAddr t -> Keyed addrT (PT t); LitAddr a -> Keyed addrT (PAddr a)
  ConcreteBuf bs -> Keyed bufT (PBS bs); AbstractBuf t -> Keyed bufT (PT t)
  WriteWord{} -> Keyed bufT P0; WriteByte{} -> Keyed bufT P0; CopySlice{} -> Keyed bufT P0
  ConcreteStore m -> Keyed storeT (PStore (M.toList m)); AbstractStore _ mw -> Keyed storeT (PMW mw)
  SStore{} -> Keyed storeT P0
  GVar (BufVar n) -> Keyed bufT (PInt n); GVar (StoreVar n) -> Keyed storeT (PInt n)
  Partial{} -> Untabled; Failure{} -> Untabled; Success{} -> Untabled
  LogEntry{} -> Untabled; C{} -> Untabled
  where
    ew = Keyed wordT

-- | Read the enable flag with a data dependency on the argument so the check cannot be floated
-- out and shared across calls (the flag changes between explorations).
hashConsEnabled :: Expr b -> Bool
hashConsEnabled x = unsafePerformIO (x `seq` readIORef hcEnabled)
{-# NOINLINE hashConsEnabled #-}

-- | Map a node (and, as needed, its not-yet-canonical descendants) to its canonical
-- representative. Semantically the identity.
hashConsExpr :: Expr a -> Expr a
hashConsExpr e = unsafePerformIO $ do
  en <- readIORef hcEnabled
  if en then fst <$> go e else pure e
{-# NOINLINE hashConsExpr #-}

-- Look up a node's id by physical identity. A hit means the node is already canonical.
lookupSN :: Expr a -> IO (Maybe Int)
lookupSN e = do
  sn <- makeStableName $! e
  st <- readIORef hcState
  pure $ case IM.lookup (hashStableName sn) st.hcSns of
    Nothing -> Nothing
    Just bucket -> lookupBucket sn bucket
  where
    lookupBucket :: StableName x -> [(SomeSN, Int)] -> Maybe Int
    lookupBucket _ [] = Nothing
    lookupBucket sn ((SomeSN sn', i):rest)
      | eqStableName sn sn' = Just i
      | otherwise = lookupBucket sn rest

-- Record a canonical node's StableName -> id (atomic; interpreters may run concurrently).
recordSN :: Expr a -> Int -> IO ()
recordSN e i = do
  sn <- makeStableName $! e
  atomicModifyIORef' hcState $ \st ->
    (st { hcSns = IM.insertWith (++) (hashStableName sn) [(SomeSN sn, i)] st.hcSns }, ())

-- Canonicalize a rebuilt node (children already canonical) by its structural key. The id counter
-- is bumped atomically so concurrent interpreters can never hand out the same id for different
-- structures.
recanon :: Table a -> Key -> Expr a -> IO (Expr a, Int)
recanon tab key e' = do
  r <- atomicModifyIORef' hcState $ \st ->
    case M.lookup key (tab.nodes st) of
      Just c -> (st, Left c)
      Nothing ->
        let i = st.hcNext
            st' = (tab.setNodes st (M.insert key (e', i) (tab.nodes st))) { hcNext = i + 1 }
        in (st', Right i)
  case r of
    Left c  -> pure c
    Right i -> do recordSN e' i; pure (e', i)

-- Assign a fresh id without structural deduping. Recording the StableName still makes the object
-- canonical-by-identity on later encounters.
freshOpaque :: Expr a -> IO (Expr a, Int)
freshOpaque e = do
  i <- atomicModifyIORef' hcState $ \st -> (st { hcNext = st.hcNext + 1 }, st.hcNext)
  recordSN e i
  pure (e, i)

-- Top-down: shortcut already-canonical nodes, else canonicalize bottom-up.
go :: Expr a -> IO (Expr a, Int)
go e = do
  m <- lookupSN e
  case m of
    Just i  -> pure (e, i)
    Nothing -> goBuild e

goBuild :: Expr a -> IO (Expr a, Int)
goBuild e = case shape e of
  Untabled -> freshOpaque e
  Unkeyed _ -> freshOpaque e
  Keyed tab payload -> case e of
    -- the traversals treat it as a leaf, but its address is a term
    AbstractStore a mw -> do
      (a', ia) <- go a
      recanon tab (exprRank e, payload, [ia]) (AbstractStore a' mw)
    _ -> do
      ids <- newIORef []
      e' <- mapChildrenM (\c -> do (c', i) <- go c; modifyIORef' ids (i :); pure c') e
      childIds <- readIORef ids
      recanon tab (exprRank e, payload, reverse childIds) e'

-- | A simplification pass. Its results are remembered for as long as the tables live, which is
-- only sound for a function that depends on nothing but the node, so 'memoFixTraverse' takes it
-- as a 'StaticPtr': the compiler rejects a @static@ form that captures a local variable.
newtype Rewrite = Rewrite (forall a . Expr a -> Expr a)

runRewrite :: Rewrite -> Expr a -> Expr a
runRewrite (Rewrite f) = f

-- | Memoized structural map for repeatedly-applied simplification passes over hash-consed terms.
-- Matches Traversals.mapExprM's f-application at every node, with three additions:
--
--   * the rewrite's output is deduplicated, so a rewrite that rebuilds a structurally-equal node
--     (e.g. via argument normalization) collapses back to the canonical object;
--   * reconstruction is identity-preserving: when nothing changed, the ORIGINAL node is returned,
--     so convergence is detectable by pointer identity in O(1) (see 'untilFixpoint');
--   * the result for a canonical node is remembered per pass, so later applications skip it in
--     O(1). On a shared DAG this turns each pass from O(logical size) into O(nodes not yet seen).
--
-- All results are forced before use: an unevaluated thunk never has the pointer identity of the
-- node it evaluates to.
memoFixTraverse :: StaticPtr Rewrite -> Expr b -> Expr b
memoFixTraverse pass root = unsafePerformIO (goM root)
  where
    key = staticKey pass

    fi :: Expr x -> Expr x
    fi x = hashConsExpr (runRewrite (deRefStaticPtr pass) x)

    goM :: Expr x -> IO (Expr x)
    goM n = do
      mid <- lookupSN n
      case (mid, memoTable n) of
        (Just i, Just tab) -> do
          memos <- readIORef passMemos
          case IM.lookup i (tab.memo (M.findWithDefault emptyMT key memos)) of
            Just r  -> pure r
            Nothing -> do
              r <- rebuild n
              atomicModifyIORef' passMemos $ \ms ->
                let mt = M.findWithDefault emptyMT key ms
                in (M.insert key (tab.setMemo mt (IM.insert i r (tab.memo mt))) ms, ())
              pure r
        _ -> rebuild n

    memoTable :: Expr x -> Maybe (Table x)
    memoTable n = case shape n of
      Keyed tab _ -> Just tab
      Unkeyed tab -> Just tab
      Untabled -> Nothing

    rebuild :: Expr x -> IO (Expr x)
    rebuild orig = do
      changed <- newIORef False
      new <- mapChildrenM (\c -> do c' <- goM c; unless (ptrEq c' c) (writeIORef changed True); pure c') orig
      isChanged <- readIORef changed
      let e = if isChanged then new else orig
      case orig of
        -- as in mapExprM, the rewrite is not applied to a contract itself
        C {} -> pure $! e
        _ -> pure $! fi e
{-# NOINLINE memoFixTraverse #-}
