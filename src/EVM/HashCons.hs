{- |
    Module: EVM.HashCons
    Description: Construction-time hash-consing (structural sharing) for the Expr AST.

    The interpreter rebuilds equal subterms as separate heap objects, so a reused intermediate
    turns into an exponentially large tree. 'hashConsExpr' maps a node to the first equal node
    seen, keyed by (constructor, scalar payload, child ids), so the heap holds the DAG and
    pointer equality witnesses structural equality. It is semantically the identity.

    The tables and the on/off flag are process-wide. Every 'interpret' sets the flag from
    'hashConsExplore' and resets the tables; the flag stays set afterwards, and concurrent
    explorations see whichever value was set last. That changes sharing, never results.
    The tables pin every node they ever saw, so they are also reset once they grow past
    'setHashConsLimit' nodes.
-}
module EVM.HashCons
  ( Rewrite(..)
  , runRewrite
  , hashConsExpr
  , hashConsExprIO
  , setHashConsEnabled
  , getHashConsEnabled
  , hashConsEnabled
  , resetHashCons
  , setHashConsLimit
  , memoFixTraverse
  ) where

import Prelude hiding (LT, GT)
import Data.IORef
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.IntMap.Strict qualified as IM
import Control.Monad (unless, when)
import Data.Word (Word8)
import Data.Text (Text)
import Data.ByteString (ByteString)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName
import GHC.StaticPtr (StaticPtr, StaticKey, staticKey, deRefStaticPtr)

import EVM.Traversals.Children (mapChildrenM)
import EVM.Types

-- | The non-term fields of a node, part of its key
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

-- | Constructor tag, payload, child ids
type Key = (Int, Payload, [Int])

data SomeSN = forall x. SomeSN !(StableName x)

-- | One table per expression type, so no coercion is needed
data HCState = HCState
  { hcWords  :: !(Map Key (Expr EWord, Int))
  , hcBytes  :: !(Map Key (Expr Byte, Int))
  , hcBufs   :: !(Map Key (Expr Buf, Int))
  , hcStores :: !(Map Key (Expr Storage, Int))
  , hcAddrs  :: !(Map Key (Expr EAddr, Int))
  , hcSns    :: !(IM.IntMap [(SomeSN, Int)])  -- ^ ids of canonical nodes, by StableName
  , hcNext   :: !Int
  , hcBase   :: !Int  -- ^ 'hcNext' at the last reset
  }

emptyHC :: HCState
emptyHC = HCState M.empty M.empty M.empty M.empty M.empty IM.empty 0 0

{-# NOINLINE hcEnabled #-}
hcEnabled :: IORef Bool
hcEnabled = unsafePerformIO (newIORef False)

{-# NOINLINE hcState #-}
hcState :: IORef HCState
hcState = unsafePerformIO (newIORef emptyHC)

setHashConsEnabled :: Bool -> IO ()
setHashConsEnabled = writeIORef hcEnabled

getHashConsEnabled :: IO Bool
getHashConsEnabled = readIORef hcEnabled

resetHashCons :: IO ()
resetHashCons = do
  -- ids are never reused, so memo entries of a concurrent exploration can't hit a new node
  atomicModifyIORef' hcState $ \st -> (emptyHC { hcNext = st.hcNext, hcBase = st.hcNext }, ())
  writeIORef passMemos M.empty

{-# NOINLINE hcLimit #-}
hcLimit :: IORef Int
hcLimit = unsafePerformIO (newIORef 1000000)

-- | How many nodes the tables may take in before they are reset; returns the previous limit
setHashConsLimit :: Int -> IO Int
setHashConsLimit n = atomicModifyIORef' hcLimit (n,)

bounded :: Int -> IO ()
bounded i = do
  lim <- readIORef hcLimit
  st <- readIORef hcState
  when (i - st.hcBase >= lim) resetHashCons

-- | Per-pass results of 'memoFixTraverse', by node id
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

data Shape a
  = Keyed (Table a) Payload  -- ^ shared by structure: constructor, payload and child ids
  | Unkeyed (Table a)        -- ^ given an id, but an equal node built later is not shared
  | Untabled                 -- ^ given an id, not memoized

-- | A field that is not a term must go in the payload, or terms differing only there are merged
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

-- | Depends on the argument so GHC can't float the flag read out and share it across calls
hashConsEnabled :: Expr b -> Bool
hashConsEnabled x = unsafePerformIO (x `seq` readIORef hcEnabled)
{-# NOINLINE hashConsEnabled #-}

-- | The canonical node equal to the argument
hashConsExpr :: Expr a -> Expr a
hashConsExpr e = unsafePerformIO (hashConsExprIO e)
{-# NOINLINE hashConsExpr #-}

hashConsExprIO :: Expr a -> IO (Expr a)
hashConsExprIO e = do
  en <- readIORef hcEnabled
  if en then fst <$> go e else pure e

-- A hit means the node is already canonical
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

recordSN :: Expr a -> Int -> IO ()
recordSN e i = do
  sn <- makeStableName $! e
  atomicModifyIORef' hcState $ \st ->
    (st { hcSns = IM.insertWith (++) (hashStableName sn) [(SomeSN sn, i)] st.hcSns }, ())

-- Expects canonical children
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
    Right i -> do recordSN e' i; bounded i; pure (e', i)

freshOpaque :: Expr a -> IO (Expr a, Int)
freshOpaque e = do
  i <- atomicModifyIORef' hcState $ \st -> (st { hcNext = st.hcNext + 1 }, st.hcNext)
  recordSN e i
  bounded i
  pure (e, i)

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

-- | A simplification pass. Its results are memoized, so it must depend on nothing but the node:
-- 'memoFixTraverse' takes it as a 'StaticPtr', and @static@ rejects captured variables.
newtype Rewrite = Rewrite (forall a . Expr a -> Expr a)

runRewrite :: Rewrite -> Expr a -> Expr a
runRewrite (Rewrite f) = f

-- | 'mapExpr' that hash-conses each result, memoizes it per pass and node, and returns the
-- original object when nothing changed, so 'untilFixpoint' sees convergence by pointer equality.
-- Results are forced: a thunk never has the pointer identity of the node it evaluates to.
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
