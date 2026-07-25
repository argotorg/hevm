{- |
    Module: EVM.HashCons
    Description: Construction-time hash-consing (structural sharing) for the Expr AST.

    The symbolic interpreter rebuilds structurally-identical subterms as separate heap objects
    (e.g. a mapping-slot keccak recomputed on every storage access), so a computation that reuses
    an intermediate at k nesting levels materializes a 2^k tree with no sharing. On storage-heavy
    targets this exhausts memory (observed: a 914-node DAG materialized as a 601,664-node tree,
    22 GB peak), and it makes every structural traversal or comparison pay the logical - not the
    shared - size.

    'internExpr' returns a canonical representative for a node: the first structurally-equal node
    ever seen is reused for all later duplicates, so the heap holds the DAG, not the tree. It is
    exact (never merges structurally-different terms) and O(1) amortized per constructed node:

      * a StableName table shortcuts nodes that are ALREADY canonical, so canonical subtrees
        (e.g. operands taken off the stack) are not re-traversed, and
      * the structural tables are keyed by (constructor tag, scalar payload, child ids) - all
        shallow - so a lookup never compares whole subterms.

    Canonicalization also makes physical identity a cheap witness for structural equality, which
    the ptrEq fast paths in Expr's Eq/Ord instances and 'untilFixpoint' exploit: comparisons on
    shared terms drop from O(logical size) to O(size of the differing part).

    internExpr e is always structurally equal to e, so it is semantically the identity; it only
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
  ( internExpr
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
import Control.Monad (forM)
import Data.Foldable (toList)
import Data.Word (Word8)
import Data.Text (Text)
import Data.ByteString (ByteString)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName

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
  { hcWords  :: !(Map Key (Expr EWord))
  , hcBytes  :: !(Map Key (Expr Byte))
  , hcBufs   :: !(Map Key (Expr Buf))
  , hcStores :: !(Map Key (Expr Storage))
  , hcAddrs  :: !(Map Key (Expr EAddr))
  , hcSns    :: !(IM.IntMap [(SomeSN, Int)])  -- ^ hashStableName -> [(name, id)]: node -> id
  , hcKeyIds :: !(Map Key Int)                -- ^ structural key -> id
  , hcNext   :: !Int
  }

emptyHC :: HCState
emptyHC = HCState M.empty M.empty M.empty M.empty M.empty IM.empty M.empty 0

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
  writeIORef hcState emptyHC
  writeIORef passMemos IM.empty

-- | Per-pass memo of simplification results, keyed by canonical node id, with one table per
-- expression type. Values are recovered at their own type by dispatching on the node's
-- constructor (which fixes the type via GADT refinement), so no coercion is involved. Cleared
-- together with the intern tables.
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
passMemos :: IORef (IM.IntMap MemoTables)
passMemos = unsafePerformIO (newIORef IM.empty)

-- | Which typed memo table a node's results live in, decided by its constructor. GADT matching
-- refines the type, so reads come back at the node's own type. Nodes of types we do not memo
-- (End, Log, EContract) return Nothing and are simply recomputed.
data TableAt a = TableAt
  { readT  :: MemoTables -> IM.IntMap (Expr a)
  , writeT :: MemoTables -> IM.IntMap (Expr a) -> MemoTables
  }

tableFor :: Expr a -> Maybe (TableAt a)
tableFor e = case e of
  Lit{} -> w; Var{} -> w; Origin -> w; Coinbase -> w; Timestamp -> w; BlockNumber -> w
  PrevRandao -> w; GasLimit -> w; ChainId -> w; BaseFee -> w; TxValue -> w; Gas{} -> w
  IsZero{} -> w; Not{} -> w; CLZ{} -> w; BlockHash{} -> w; Keccak{} -> w; BufLength{} -> w
  WAddr{} -> w; Balance{} -> w; CodeSize{} -> w; CodeHash{} -> w
  Add{} -> w; Sub{} -> w; Mul{} -> w; Div{} -> w; SDiv{} -> w; Mod{} -> w; SMod{} -> w
  Exp{} -> w; SEx{} -> w; Min{} -> w; Max{} -> w
  LT{} -> w; GT{} -> w; LEq{} -> w; GEq{} -> w; SLT{} -> w; SGT{} -> w; Eq{} -> w
  And{} -> w; Or{} -> w; Xor{} -> w; SHL{} -> w; SHR{} -> w; SAR{} -> w
  EqByte{} -> w; ReadWord{} -> w; AddMod{} -> w; MulMod{} -> w; ITE{} -> w; SLoad{} -> w
  JoinBytes{} -> w
  LitByte{} -> by; IndexWord{} -> by; ReadByte{} -> by
  ConcreteBuf{} -> bu; AbstractBuf{} -> bu; WriteWord{} -> bu; WriteByte{} -> bu; CopySlice{} -> bu
  ConcreteStore{} -> st; AbstractStore{} -> st; SStore{} -> st
  SymAddr{} -> ad; LitAddr{} -> ad
  _ -> Nothing
  where
    w  = Just (TableAt (.mtW)  (\m t -> m { mtW = t }))
    by = Just (TableAt (.mtBy) (\m t -> m { mtBy = t }))
    bu = Just (TableAt (.mtBu) (\m t -> m { mtBu = t }))
    st = Just (TableAt (.mtS)  (\m t -> m { mtS = t }))
    ad = Just (TableAt (.mtA)  (\m t -> m { mtA = t }))

-- | Read the enable flag with a data dependency on the argument so the check cannot be floated
-- out and shared across calls (the flag changes between explorations).
hashConsEnabled :: Expr b -> Bool
hashConsEnabled x = unsafePerformIO (x `seq` readIORef hcEnabled)
{-# NOINLINE hashConsEnabled #-}

-- | Intern a node (and, as needed, its not-yet-canonical descendants) to a canonical
-- representative. Semantically the identity.
internExpr :: Expr a -> Expr a
internExpr e = unsafePerformIO $ do
  en <- readIORef hcEnabled
  if en then fst <$> go e else pure e
{-# NOINLINE internExpr #-}

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

-- Canonicalize a rebuilt node (children already canonical) by its structural key, in the table
-- selected by the caller (which fixes the type). The id counter is bumped atomically so
-- concurrent interpreters can never hand out the same id for different structures.
recanonIn :: (HCState -> Map Key (Expr a))
          -> (HCState -> Map Key (Expr a) -> HCState)
          -> Key -> Expr a -> IO (Expr a, Int)
recanonIn getT setT key e' = do
  r <- atomicModifyIORef' hcState $ \st ->
    case M.lookup key (getT st) of
      Just c -> (st, Left (c, M.findWithDefault (-1) key st.hcKeyIds))
      Nothing ->
        let i = st.hcNext
            st' = (setT st (M.insert key e' (getT st)))
                    { hcKeyIds = M.insert key i st.hcKeyIds, hcNext = i + 1 }
        in (st', Right i)
  case r of
    Left (c, i) -> pure (c, i)
    Right i     -> do recordSN e' i; pure (e', i)

recanonW :: Key -> Expr EWord -> IO (Expr EWord, Int)
recanonW = recanonIn (.hcWords) (\st t -> st { hcWords = t })

recanonBy :: Key -> Expr Byte -> IO (Expr Byte, Int)
recanonBy = recanonIn (.hcBytes) (\st t -> st { hcBytes = t })

recanonBu :: Key -> Expr Buf -> IO (Expr Buf, Int)
recanonBu = recanonIn (.hcBufs) (\st t -> st { hcBufs = t })

recanonS :: Key -> Expr Storage -> IO (Expr Storage, Int)
recanonS = recanonIn (.hcStores) (\st t -> st { hcStores = t })

recanonA :: Key -> Expr EAddr -> IO (Expr EAddr, Int)
recanonA = recanonIn (.hcAddrs) (\st t -> st { hcAddrs = t })

-- Assign a fresh id without structural deduping (constructors we do not key, e.g. End nodes).
-- Recording the StableName still makes the object canonical-by-identity on later encounters.
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

w1 :: Int -> (Expr EWord -> Expr EWord) -> Expr EWord -> IO (Expr EWord, Int)
w1 t con a = do (a', ia) <- go a; recanonW (t, P0, [ia]) (con a')

w2 :: Int -> (Expr EWord -> Expr EWord -> Expr EWord) -> Expr EWord -> Expr EWord -> IO (Expr EWord, Int)
w2 t con a b = do (a', ia) <- go a; (b', ib) <- go b; recanonW (t, P0, [ia, ib]) (con a' b')

w3 :: Int -> (Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord)
   -> Expr EWord -> Expr EWord -> Expr EWord -> IO (Expr EWord, Int)
w3 t con a b c = do
  (a', ia) <- go a; (b', ib) <- go b; (c', ic) <- go c
  recanonW (t, P0, [ia, ib, ic]) (con a' b' c')

goBuild :: Expr a -> IO (Expr a, Int)
goBuild = \case
  -- EWord leaves / block & tx context
  Lit w            -> recanonW (1, PW w, []) (Lit w)
  Var t            -> recanonW (2, PT t, []) (Var t)
  Origin           -> recanonW (3, P0, []) Origin
  Coinbase         -> recanonW (4, P0, []) Coinbase
  Timestamp        -> recanonW (5, P0, []) Timestamp
  BlockNumber      -> recanonW (6, P0, []) BlockNumber
  PrevRandao       -> recanonW (7, P0, []) PrevRandao
  GasLimit         -> recanonW (8, P0, []) GasLimit
  ChainId          -> recanonW (9, P0, []) ChainId
  BaseFee          -> recanonW (10, P0, []) BaseFee
  TxValue          -> recanonW (11, P0, []) TxValue
  Gas p i          -> recanonW (12, PGas p i, []) (Gas p i)
  -- EWord unary
  IsZero a         -> w1 20 IsZero a
  Not a            -> w1 21 Not a
  CLZ a            -> w1 22 CLZ a
  BlockHash a      -> w1 23 BlockHash a
  Keccak a         -> do (a', ia) <- go a; recanonW (24, P0, [ia]) (Keccak a')
  BufLength a      -> do (a', ia) <- go a; recanonW (25, P0, [ia]) (BufLength a')
  WAddr a          -> do (a', ia) <- go a; recanonW (26, P0, [ia]) (WAddr a')
  Balance a        -> do (a', ia) <- go a; recanonW (27, P0, [ia]) (Balance a')
  CodeSize a       -> do (a', ia) <- go a; recanonW (28, P0, [ia]) (CodeSize a')
  CodeHash a       -> do (a', ia) <- go a; recanonW (29, P0, [ia]) (CodeHash a')
  -- EWord binary
  Add a b          -> w2 40 Add a b
  Sub a b          -> w2 41 Sub a b
  Mul a b          -> w2 42 Mul a b
  Div a b          -> w2 43 Div a b
  SDiv a b         -> w2 44 SDiv a b
  Mod a b          -> w2 45 Mod a b
  SMod a b         -> w2 46 SMod a b
  Exp a b          -> w2 47 Exp a b
  SEx a b          -> w2 48 SEx a b
  Min a b          -> w2 49 Min a b
  Max a b          -> w2 50 Max a b
  LT a b           -> w2 51 LT a b
  GT a b           -> w2 52 GT a b
  LEq a b          -> w2 53 LEq a b
  GEq a b          -> w2 54 GEq a b
  SLT a b          -> w2 55 SLT a b
  SGT a b          -> w2 56 SGT a b
  Eq a b           -> w2 57 Eq a b
  And a b          -> w2 58 And a b
  Or a b           -> w2 59 Or a b
  Xor a b          -> w2 60 Xor a b
  SHL a b          -> w2 61 SHL a b
  SHR a b          -> w2 62 SHR a b
  SAR a b          -> w2 63 SAR a b
  EqByte a b       -> do (a', ia) <- go a; (b', ib) <- go b; recanonW (64, P0, [ia, ib]) (EqByte a' b')
  ReadWord a b     -> do (a', ia) <- go a; (b', ib) <- go b; recanonW (65, P0, [ia, ib]) (ReadWord a' b')
  -- EWord ternary
  AddMod a b c     -> w3 70 AddMod a b c
  MulMod a b c     -> w3 71 MulMod a b c
  ITE a b c        -> w3 72 ITE a b c
  -- Byte
  LitByte w        -> recanonBy (80, PB8 w, []) (LitByte w)
  IndexWord a b    -> do (a', ia) <- go a; (b', ib) <- go b; recanonBy (81, P0, [ia, ib]) (IndexWord a' b')
  ReadByte a b     -> do (a', ia) <- go a; (b', ib) <- go b; recanonBy (82, P0, [ia, ib]) (ReadByte a' b')
  -- EAddr
  SymAddr t        -> recanonA (90, PT t, []) (SymAddr t)
  LitAddr a        -> recanonA (91, PAddr a, []) (LitAddr a)
  -- Buffers
  ConcreteBuf bs   -> recanonBu (100, PBS bs, []) (ConcreteBuf bs)
  AbstractBuf t    -> recanonBu (101, PT t, []) (AbstractBuf t)
  WriteWord a b c  -> do
    (a', ia) <- go a; (b', ib) <- go b; (c', ic) <- go c
    recanonBu (102, P0, [ia, ib, ic]) (WriteWord a' b' c')
  WriteByte a b c  -> do
    (a', ia) <- go a; (b', ib) <- go b; (c', ic) <- go c
    recanonBu (103, P0, [ia, ib, ic]) (WriteByte a' b' c')
  CopySlice a b c d e -> do
    (a', ia) <- go a; (b', ib) <- go b; (c', ic) <- go c; (d', idd) <- go d; (e', ie) <- go e
    recanonBu (104, P0, [ia, ib, ic, idd, ie]) (CopySlice a' b' c' d' e')
  -- Storage
  ConcreteStore m  -> recanonS (110, PStore (M.toList m), []) (ConcreteStore m)
  AbstractStore a mw -> do
    (a', ia) <- go a
    recanonS (111, PMW mw, [ia]) (AbstractStore a' mw)
  SLoad a b        -> do (a', ia) <- go a; (b', ib) <- go b; recanonW (112, P0, [ia, ib]) (SLoad a' b')
  SStore a b c     -> do
    (a', ia) <- go a; (b', ib) <- go b; (c', ic) <- go c
    recanonS (113, P0, [ia, ib, ic]) (SStore a' b' c')
  -- CSE variables (shared refs), keyed by their index
  g@(GVar (BufVar n))   -> recanonBu (120, PInt n, []) g
  g@(GVar (StoreVar n)) -> recanonS (121, PInt n, []) g
  -- Everything else (JoinBytes, End/Log/EContract nodes): not structurally keyed.
  e                -> freshOpaque e

-- | Memoized structural map for repeatedly-applied simplification passes over hash-consed terms.
-- Matches Traversals.mapExprM's f-application at every node, with three additions:
--
--   * the rewrite's output is interned, so a rewrite that rebuilds a structurally-equal node
--     (e.g. via argument normalization) collapses back to the canonical object;
--   * reconstruction is identity-preserving: when nothing changed, the ORIGINAL node is returned,
--     so convergence is detectable by pointer identity in O(1) (see 'untilFixpoint');
--   * canonical nodes that a pass has mapped to themselves are remembered per pass slot (an id
--     set - no values are stored), so later applications skip them in O(1). On a shared DAG this
--     turns each pass from O(logical size) into O(nodes not yet known to be fixpoints).
--
-- Sound for an f that is a pure function of node structure (all simplifier passes are). All
-- results are forced before use: an unevaluated thunk never has the pointer identity of the
-- node it evaluates to.
memoFixTraverse :: Int -> (forall x. Expr x -> Expr x) -> Expr b -> Expr b
memoFixTraverse slot f root = unsafePerformIO (goM root)
  where
    fi :: Expr x -> Expr x
    fi x = internExpr (f x)

    goM :: Expr x -> IO (Expr x)
    goM n = do
      mid <- lookupSN n
      case (mid, tableFor n) of
        (Just i, Just tab) -> do
          memos <- readIORef passMemos
          case IM.lookup i (tab.readT (IM.findWithDefault emptyMT slot memos)) of
            Just r  -> pure r
            Nothing -> do
              r0 <- rb n
              let !r = r0
              atomicModifyIORef' passMemos $ \ms ->
                let mt = IM.findWithDefault emptyMT slot ms
                in (IM.insert slot (tab.writeT mt (IM.insert i r (tab.readT mt))) ms, ())
              pure r
        _ -> do
          r0 <- rb n
          let !r = r0
          pure r

    u0 :: Expr x -> IO (Expr x)
    u0 orig = pure $! fi orig
    u1 :: Expr x -> (Expr y -> Expr x) -> Expr y -> Expr y -> IO (Expr x)
    u1 orig con a a' = pure $! fi (if ptrEq a' a then orig else con a')
    u2 :: Expr x -> (Expr y -> Expr z -> Expr x) -> Expr y -> Expr z -> Expr y -> Expr z -> IO (Expr x)
    u2 orig con a b a' b' = pure $! fi (if ptrEq a' a && ptrEq b' b then orig else con a' b')
    u3 :: Expr x -> (Expr v -> Expr y -> Expr z -> Expr x)
       -> Expr v -> Expr y -> Expr z -> Expr v -> Expr y -> Expr z -> IO (Expr x)
    u3 orig con a b c a' b' c' =
      pure $! fi (if ptrEq a' a && ptrEq b' b && ptrEq c' c then orig else con a' b' c')
    u5 :: Expr x -> (Expr u -> Expr v -> Expr w -> Expr y -> Expr z -> Expr x)
       -> Expr u -> Expr v -> Expr w -> Expr y -> Expr z
       -> Expr u -> Expr v -> Expr w -> Expr y -> Expr z -> IO (Expr x)
    u5 orig con a b c d e a' b' c' d' e' =
      pure $! fi (if ptrEq a' a && ptrEq b' b && ptrEq c' c && ptrEq d' d && ptrEq e' e
                  then orig else con a' b' c' d' e')

    rb :: Expr x -> IO (Expr x)
    rb orig = case orig of
      Lit _ -> u0 orig
      LitByte _ -> u0 orig
      Var _ -> u0 orig
      GVar _ -> u0 orig
      C{} -> goEC orig
      LitAddr _ -> u0 orig
      SymAddr _ -> u0 orig
      WAddr a -> do a' <- goM a; u1 orig WAddr a a'
      IndexWord a b -> do a' <- goM a; b' <- goM b; u2 orig IndexWord a b a' b'
      EqByte a b -> do a' <- goM a; b' <- goM b; u2 orig EqByte a b a' b'
      JoinBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 -> do
        let olds = [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15
                   ,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31]
        news <- mapM goM olds
        case news of
          [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15
           ,y16,y17,y18,y19,y20,y21,y22,y23,y24,y25,y26,y27,y28,y29,y30,y31] ->
            pure $! fi (if and (zipWith ptrEq news olds) then orig
                        else JoinBytes y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
                                       y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          _ -> internalError "memoFixTraverse: JoinBytes arity"
      Failure a b c -> do
        (a', sa) <- goPs a
        pure $! fi (if sa then orig else Failure a' b c)
      Partial a b c -> do
        (a', sa) <- goPs a
        pure $! fi (if sa then orig else Partial a' b c)
      Success a b c d -> do
        (a', sa) <- goPs a
        c' <- goM c
        kvs <- forM (M.toList d) $ \(k, v) -> do
          k' <- goM k
          v' <- goEC v
          pure ((k', v'), ptrEq k' k && ptrEq v' v)
        let sd = all snd kvs
            d' = if sd then d else M.fromList (map fst kvs)
        pure $! fi (if sa && ptrEq c' c && sd then orig else Success a' b c' d')
      Add a b -> do a' <- goM a; b' <- goM b; u2 orig Add a b a' b'
      Sub a b -> do a' <- goM a; b' <- goM b; u2 orig Sub a b a' b'
      Mul a b -> do a' <- goM a; b' <- goM b; u2 orig Mul a b a' b'
      Div a b -> do a' <- goM a; b' <- goM b; u2 orig Div a b a' b'
      SDiv a b -> do a' <- goM a; b' <- goM b; u2 orig SDiv a b a' b'
      Mod a b -> do a' <- goM a; b' <- goM b; u2 orig Mod a b a' b'
      SMod a b -> do a' <- goM a; b' <- goM b; u2 orig SMod a b a' b'
      AddMod a b c -> do a' <- goM a; b' <- goM b; c' <- goM c; u3 orig AddMod a b c a' b' c'
      MulMod a b c -> do a' <- goM a; b' <- goM b; c' <- goM c; u3 orig MulMod a b c a' b' c'
      Exp a b -> do a' <- goM a; b' <- goM b; u2 orig Exp a b a' b'
      SEx a b -> do a' <- goM a; b' <- goM b; u2 orig SEx a b a' b'
      Min a b -> do a' <- goM a; b' <- goM b; u2 orig Min a b a' b'
      Max a b -> do a' <- goM a; b' <- goM b; u2 orig Max a b a' b'
      LT a b -> do a' <- goM a; b' <- goM b; u2 orig LT a b a' b'
      GT a b -> do a' <- goM a; b' <- goM b; u2 orig GT a b a' b'
      LEq a b -> do a' <- goM a; b' <- goM b; u2 orig LEq a b a' b'
      GEq a b -> do a' <- goM a; b' <- goM b; u2 orig GEq a b a' b'
      SLT a b -> do a' <- goM a; b' <- goM b; u2 orig SLT a b a' b'
      SGT a b -> do a' <- goM a; b' <- goM b; u2 orig SGT a b a' b'
      Eq a b -> do a' <- goM a; b' <- goM b; u2 orig Eq a b a' b'
      IsZero a -> do a' <- goM a; u1 orig IsZero a a'
      ITE c t e -> do c' <- goM c; t' <- goM t; e' <- goM e; u3 orig ITE c t e c' t' e'
      And a b -> do a' <- goM a; b' <- goM b; u2 orig And a b a' b'
      Or a b -> do a' <- goM a; b' <- goM b; u2 orig Or a b a' b'
      Xor a b -> do a' <- goM a; b' <- goM b; u2 orig Xor a b a' b'
      Not a -> do a' <- goM a; u1 orig Not a a'
      SHL a b -> do a' <- goM a; b' <- goM b; u2 orig SHL a b a' b'
      SHR a b -> do a' <- goM a; b' <- goM b; u2 orig SHR a b a' b'
      SAR a b -> do a' <- goM a; b' <- goM b; u2 orig SAR a b a' b'
      CLZ a -> do a' <- goM a; u1 orig CLZ a a'
      Keccak a -> do a' <- goM a; u1 orig Keccak a a'
      Origin -> u0 orig
      Coinbase -> u0 orig
      Timestamp -> u0 orig
      BlockNumber -> u0 orig
      PrevRandao -> u0 orig
      GasLimit -> u0 orig
      ChainId -> u0 orig
      BaseFee -> u0 orig
      BlockHash a -> do a' <- goM a; u1 orig BlockHash a a'
      TxValue -> u0 orig
      Gas _ _ -> u0 orig
      Balance a -> do a' <- goM a; u1 orig Balance a a'
      CodeSize a -> do a' <- goM a; u1 orig CodeSize a a'
      CodeHash a -> do a' <- goM a; u1 orig CodeHash a a'
      LogEntry a b c -> do
        a' <- goM a
        b' <- goM b
        c' <- mapM goM c
        pure $! fi (if ptrEq a' a && ptrEq b' b && and (zipWith ptrEq c' c) then orig else LogEntry a' b' c')
      ConcreteStore _ -> u0 orig
      AbstractStore _ _ -> u0 orig
      SLoad a b -> do a' <- goM a; b' <- goM b; u2 orig SLoad a b a' b'
      SStore a b c -> do a' <- goM a; b' <- goM b; c' <- goM c; u3 orig SStore a b c a' b' c'
      ConcreteBuf _ -> u0 orig
      AbstractBuf _ -> u0 orig
      ReadWord a b -> do a' <- goM a; b' <- goM b; u2 orig ReadWord a b a' b'
      ReadByte a b -> do a' <- goM a; b' <- goM b; u2 orig ReadByte a b a' b'
      WriteWord a b c -> do a' <- goM a; b' <- goM b; c' <- goM c; u3 orig WriteWord a b c a' b' c'
      WriteByte a b c -> do a' <- goM a; b' <- goM b; c' <- goM c; u3 orig WriteByte a b c a' b' c'
      CopySlice a b c d e -> do
        a' <- goM a; b' <- goM b; c' <- goM c; d' <- goM d; e' <- goM e
        u5 orig CopySlice a b c d e a' b' c' d' e'
      BufLength a -> do a' <- goM a; u1 orig BufLength a a'

    goPs :: [Prop] -> IO ([Prop], Bool)
    goPs ps = do
      ps' <- mapM goP ps
      let same = and (zipWith ptrEq ps' ps)
      pure (if same then (ps, True) else (ps', False))

    goP :: Prop -> IO Prop
    goP p = case p of
      PBool _ -> pure p
      PEq a b -> do a' <- goM a; b' <- goM b; pure $! (if ptrEq a' a && ptrEq b' b then p else PEq a' b')
      PLT a b -> do a' <- goM a; b' <- goM b; pure $! (if ptrEq a' a && ptrEq b' b then p else PLT a' b')
      PGT a b -> do a' <- goM a; b' <- goM b; pure $! (if ptrEq a' a && ptrEq b' b then p else PGT a' b')
      PLEq a b -> do a' <- goM a; b' <- goM b; pure $! (if ptrEq a' a && ptrEq b' b then p else PLEq a' b')
      PGEq a b -> do a' <- goM a; b' <- goM b; pure $! (if ptrEq a' a && ptrEq b' b then p else PGEq a' b')
      PNeg a -> do a' <- goP a; pure $! (if ptrEq a' a then p else PNeg a')
      PAnd a b -> do a' <- goP a; b' <- goP b; pure $! (if ptrEq a' a && ptrEq b' b then p else PAnd a' b')
      POr a b -> do a' <- goP a; b' <- goP b; pure $! (if ptrEq a' a && ptrEq b' b then p else POr a' b')
      PImpl a b -> do a' <- goP a; b' <- goP b; pure $! (if ptrEq a' a && ptrEq b' b then p else PImpl a' b')

    goEC :: Expr EContract -> IO (Expr EContract)
    goEC g@(GVar _) = pure g
    goEC orig@(C code st tst bal n) = do
      code' <- goCode code
      st' <- goM st
      tst' <- goM tst
      bal' <- goM bal
      pure $! (if ptrEq code' code && ptrEq st' st && ptrEq tst' tst && ptrEq bal' bal
               then orig else C code' st' tst' bal' n)

    goCode :: ContractCode -> IO ContractCode
    goCode orig = case orig of
      UnknownCode a -> do a' <- goM a; pure $! (if ptrEq a' a then orig else UnknownCode a')
      RuntimeCode (ConcreteRuntimeCode _) -> pure orig
      RuntimeCode (SymbolicRuntimeCode cs) -> do
        cs' <- mapM goM cs
        pure $! (if and (zipWith ptrEq (toList cs') (toList cs))
                 then orig else RuntimeCode (SymbolicRuntimeCode cs'))
      InitCode bs buf -> do buf' <- goM buf; pure $! (if ptrEq buf' buf then orig else InitCode bs buf')
{-# NOINLINE memoFixTraverse #-}
