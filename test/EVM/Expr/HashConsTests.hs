module EVM.Expr.HashConsTests (tests) where

import Prelude hiding (LT, GT)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding (Failure, Success)

import Control.Concurrent.MVar
import Control.Exception (evaluate)
import Control.Monad (forM)
import Data.ByteString (ByteString)
import Data.List (sort, tails)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Monoid (Any(..), Sum(..))
import Data.Ord qualified as Ord
import System.Timeout (timeout)

import EVM.Expr qualified as Expr
import EVM.Expr.Generator
import EVM.HashCons
import EVM.Traversals (foldExpr, mapExpr)
import EVM.Types

tests :: TestTree
tests = withResource (newMVar ()) (const (pure ())) $ \getLock ->
  let withHC :: Bool -> IO a -> IO a
      withHC on act = getLock >>= \lock -> withFlag lock on act
  in testGroup "HashCons"
  [ testCase "interning-is-live" $ do
      let e = Add (Var "x") (Mul (Var "x") (Lit 3))
      (c, copied, off) <- withHC False $ do
        c <- clone e
        off <- same <$> internExprIO e <*> internExprIO c
        pure (c, c == e && not (same c e), off)
      on <- withHC True $ same <$> internExprIO e <*> internExprIO c
      assertBool "clone must build a new, equal term" copied
      assertBool "interning must do nothing when disabled" (not off)
      assertBool "equal terms must intern to one object" on
  , testProperty "simplify-differential" $ \(t :: SharedTerms) -> ioProperty $ do
      let jobs = concat
            [ concat [ [ Job "simplify" Expr.simplify w, Job "concKeccakSimpExpr" Expr.concKeccakSimpExpr w
                       , Job "litToKeccak" Expr.litToKeccak w ]
                     | w <- t.words ]
            , [ Job "simplify" Expr.simplify x | x <- t.bufs ]
            , [ Job "simplify" Expr.simplify x | x <- t.stores ]
            , [ Job "simplify" Expr.simplify x | x <- t.bytes ]
            , [ Job "simplify" Expr.simplify x | x <- t.ends ]
            , [ Job "simplifyProp" Expr.simplifyProp x | x <- t.props ]
            , [ Job "simplifyProps" Expr.simplifyProps t.props, Job "concKeccakProps" Expr.concKeccakProps t.props ]
            , [ Job "readStorage" (uncurry Expr.readStorage) (k, s) | (k, s) <- zip t.words (cycle t.stores) ]
            , [ Job "writeStorage" (\(a, b, c) -> Expr.writeStorage a b c) (k, v, s)
              | (k, v, s) <- zip3 t.words (reverse t.words) (cycle t.stores) ]
            ]
      refs <- catMaybes <$> withHC False (mapM reference jobs)
      -- one table generation for everything, twice over, so later jobs run against the memos of earlier ones
      fails <- withHC True $ mapM againstReference (refs <> reverse refs)
      -- only most: without hash-consing the simplifier walks these heavily shared terms as trees,
      -- which can be exponentially larger
      pure $ cover 90 (10 * length refs >= 9 * length jobs) "most jobs terminate" $ noFailures (catMaybes fails)
  , testProperty "intern-invariants" $ \(t :: SharedTerms) -> ioProperty $ do
      let attempt = do
            (cw, cb, cs, cy) <- withHC False $
              (,,,) <$> mapM clone t.words <*> mapM clone t.bufs <*> mapM clone t.stores <*> mapM clone t.bytes
            (f1, (iw, ib, is, iy)) <- withHC True $ do
              (fw, iw) <- internChecks t.words cw
              (fb, ib) <- internChecks t.bufs cb
              (fs, is) <- internChecks t.stores cs
              (fy, iy) <- internChecks t.bytes cy
              pure (fw <> fb <> fs <> fy, (iw, ib, is, iy))
            -- terms that were canonical in tables that are gone by now
            f2 <- withHC True $ do
              (fw, _) <- internChecks iw cw
              (fb, _) <- internChecks ib cb
              (fs, _) <- internChecks is cs
              (fy, _) <- internChecks iy cy
              pure (fw <> fb <> fs <> fy)
            let orderFails = orderChecks (t.words <> cw <> iw) <> orderChecks (t.bufs <> cb <> ib)
                          <> orderChecks (t.stores <> cs <> is) <> orderChecks (t.bytes <> cy <> iy)
            pure (f1 <> fmap ("after reset: " <>) f2 <> orderFails)
          -- the parallel GC can copy an immutable node twice, and the copy is no longer the
          -- canonical object; a real failure shows up on every attempt
          retrying :: Int -> IO [String]
          retrying n = attempt >>= \fails -> if null fails || n <= 1 then pure fails else retrying (n - 1)
          interior = concatMap (foldExpr (\e -> [ show e | not (isLeaf e) ]) []) t.words
      fails <- retrying 5
      pure $ cover 80 (Set.size (Set.fromList interior) < length interior) "an interior subterm recurs" $ noFailures fails
  , testProperty "simplify-closed-agrees" $ \(t :: SharedTerms, c :: Closing, hc :: Bool, picks :: [(Int, Int, Small Int)]) -> ioProperty $
      withHC hc $ do
        let eval :: Expr a -> Expr a
            eval = Expr.concKeccakSimpExpr . close c
        wordFails <- forM t.words $ \w -> do
          r <- inTime 2 (eval w, eval (Expr.simplify w), eval (Expr.concKeccakSimpExpr w))
          pure $ case r of
            Just (Lit a, Lit b, _) | a /= b -> Just $ "simplify changed the value of a closed term\n" <> closedMsg w c a b
            Just (Lit a, _, Lit b) | a /= b -> Just $ "concKeccakSimpExpr changed the value of a closed term\n" <> closedMsg w c a b
            _ -> Nothing
        -- props that hold in the model by construction, so nothing may refute them
        truths <- fmap catMaybes . forM picks $ \(i, kind, Small d) -> do
          let w = t.words !! (i `mod` length t.words)
          r <- inTime 2 (eval w)
          pure $ r >>= \v -> trueProp w v kind (fromIntegral (abs d))
        refuted <- inTime 10 (filter ((== PBool False) . Expr.simplifyProp) truths, Expr.simplifyProps truths)
        let propFails = case refuted of
              Just (singles, together) ->
                [ "simplifyProp refuted a prop that holds under " <> show c <> "\n" <> show p | p <- singles ]
                <> [ "simplifyProps refuted props that all hold under " <> show c <> "\n" <> show truths
                   | together == [PBool False] ]
              Nothing -> []
        pure $ cover 50 (not (null truths)) "has props that hold in the model" $
          noFailures (catMaybes wordFails <> propFails)
  ]

-- | 'ptrEq' does not force its arguments, and a thunk is never the object it evaluates to
same :: a -> a -> Bool
same !a !b = ptrEq a b

noFailures :: [String] -> Property
noFailures fails = counterexample (unlines (take 3 fails)) (null fails)

-- Running under a fixed flag ------------------------------------------------------------------------

-- | Runs with hash-consing forced on or off, starting from empty tables. Every 'interpret' sets
-- the same global flag and wipes the tables, and under -f devel tests run concurrently, so the
-- action is rerun if a sentinel interned at the start is no longer canonical at the end.
withFlag :: MVar () -> Bool -> IO a -> IO a
withFlag lock on act = withMVar lock (const loop)
  where
    loop = do
      setHashConsEnabled on
      resetHashCons
      s <- internExprIO sentinel
      r <- act
      s' <- internExprIO sentinel
      still <- getHashConsEnabled
      if still == on && (not on || same s s') then pure r else loop

sentinel :: Expr EWord
sentinel = Var "hashcons-sentinel"

-- | Forces the whole term: a lazily built result would otherwise be computed later, under another flag
force :: Show a => a -> IO a
force x = evaluate (length (show x)) >> pure x

inTime :: Show a => Int -> a -> IO (Maybe a)
inTime secs x = timeout (secs * 1000000) (force x)

-- | A structurally equal term that shares no interior node with the original. Only a copy when
-- hash-consing is off, as 'mapExpr' interns what it rebuilds.
clone :: Expr a -> IO (Expr a)
clone e = force (mapExpr id e)

-- Differential -----------------------------------------------------------------------------------

data Job = forall a b . (Show a, Show b, Eq b) => Job String (a -> b) a
data Ref = forall a b . (Show a, Show b, Eq b) => Ref String (a -> b) a b

-- | The simplifier does not terminate on every term, hash-consing or not; such jobs are skipped
reference :: Job -> IO (Maybe Ref)
reference (Job name f x) = fmap (Ref name f x) <$> inTime 2 (f x)

-- | derived Show is the notion of structural equality that does not go through the Eq instance
againstReference :: Ref -> IO (Maybe String)
againstReference (Ref name f x expected) = do
  inTime 30 (f x) >>= \case
    Nothing -> pure . Just $ name <> " finishes without hash-consing but not with it\ninput:    " <> show x
    Just got -> pure $ if show got == show expected && got == expected && expected == got
      then Nothing
      else Just $ name <> " differs with hash-consing on\ninput:    " <> show x
                <> "\nwith:     " <> show got <> "\nwithout:  " <> show expected

-- Interning invariants ------------------------------------------------------------------------------

-- | JoinBytes is given an identity but is not keyed by its structure, so neither it nor anything
-- above it is shared
isLeaf :: Expr a -> Bool
isLeaf e = getSum (foldExpr (const (Sum (1 :: Int))) mempty e) == 1

keyed :: Expr a -> Bool
keyed = not . getAny . foldExpr isJoin mempty
  where
    isJoin :: Expr b -> Any
    isJoin = \case { JoinBytes {} -> Any True; _ -> Any False }

data Subterm = forall b . Subterm (Expr b)

internChecks :: [Expr a] -> [Expr a] -> IO ([String], [Expr a])
internChecks xs copies = do
  is <- mapM internExprIO xs
  perTerm <- forM (zip3 xs copies is) $ \(x, c, i) -> do
    twice <- internExprIO i
    fromCopy <- internExprIO c
    stray <- fmap catMaybes . forM (foldExpr (\s -> [Subterm s]) [] i) $ \(Subterm s) -> do
      s' <- internExprIO s
      pure $ if same s' s then Nothing else Just (show s)
    pure $ fmap (<> "\n" <> show x) $ concat
      [ [ "interning changed the term" | show i /= show x || i /= x || compare i x /= EQ ]
      , [ "interning is not idempotent" | not (same twice i) ]
      , [ "an equal copy interned to another object" | keyed x && not (same fromCopy i) ]
      , [ "an equal copy interned to a different term" | show fromCopy /= show x ]
      , [ "a subterm of an interned term is not canonical: " <> s | keyed x, s <- take 1 stray ]
      ]
  let shown = zip (fmap show xs) is
      pairwise = concat
        [ [ "different terms interned to one object\n" <> sa <> "\n" <> sb | same a b && sa /= sb ]
          <> [ "equal terms interned to different objects\n" <> sa | sa == sb && keyed a && not (same a b) ]
        | ((sa, a):rest) <- tails shown, (sb, b) <- rest ]
  pure (concat perTerm <> pairwise, is)

-- | The hand-written Eq and Ord have to agree with structural equality whether or not the two
-- sides share heap objects
orderChecks :: [Expr a] -> [String]
orderChecks xs = concat
  [ [ "== disagrees with structural equality\n" <> sa <> "\n" <> sb | (a == b) /= eq || (b == a) /= eq ]
    <> [ "compare disagrees with structural equality\n" <> sa <> "\n" <> sb | (compare a b == EQ) /= eq ]
    <> [ "compare is not antisymmetric\n" <> sa <> "\n" <> sb | compare a b /= flipOrd (compare b a) ]
  | ((sa, a):rest) <- tails (zip (fmap show xs) xs), (sb, b) <- (sa, a) : rest, let eq = sa == sb ]
  <> [ "compare is not transitive: sorting left\n" <> show a <> "\nbefore\n" <> show b
     | (a:rest) <- tails (sort xs), b <- rest, compare a b == Ord.GT ]
  where
    flipOrd = \case { Ord.LT -> Ord.GT; Ord.GT -> Ord.LT; EQ -> EQ }

-- Closed terms --------------------------------------------------------------------------------------

-- | One concrete value for every symbolic leaf the pool generator emits
data Closing = Closing
  { vars  :: [W256]
  , env   :: [W256]
  , buf   :: ByteString
  , store :: Map.Map W256 W256
  , addr  :: Addr
  }
  deriving (Show)

instance Arbitrary Closing where
  arbitrary = Closing
    <$> vectorOf (length poolVars) genArithValue
    <*> vectorOf 9 (fromIntegral <$> chooseInteger (0, 2 ^ (160 :: Int) - 1))
    <*> resize 70 arbitrary
    <*> (Map.fromList <$> listOf ((,) <$> (fromIntegral <$> chooseInt (0, 20)) <*> genArithValue))
    <*> arbitrary

close :: Closing -> Expr a -> Expr a
close c = mapExpr go
  where
    varVals = Map.fromList (zip poolVars c.vars)
    go :: Expr b -> Expr b
    go = \case
      Var v | Just x <- Map.lookup v varVals -> Lit x
      AbstractBuf _ -> ConcreteBuf c.buf
      AbstractStore _ _ -> ConcreteStore c.store
      SymAddr _ -> LitAddr c.addr
      Origin -> envVal 0
      Coinbase -> envVal 1
      Timestamp -> envVal 2
      BlockNumber -> envVal 3
      PrevRandao -> envVal 4
      GasLimit -> envVal 5
      ChainId -> envVal 6
      BaseFee -> envVal 7
      TxValue -> envVal 8
      e -> e
    envVal i = Lit (c.env !! i)

closedMsg :: Expr EWord -> Closing -> W256 -> W256 -> String
closedMsg w c a b = show w <> "\nunder " <> show c <> "\ndirectly:   " <> show a <> "\nsimplified: " <> show b

-- | A prop about @w@ that is true once the symbolic leaves take their 'Closing' values
trueProp :: Expr EWord -> Expr EWord -> Int -> W256 -> Maybe Prop
trueProp w val kind d = case val of
  Lit v -> case kind `mod` 6 of
    0 -> Just $ PEq w (Lit v)
    1 -> Just $ PEq (Lit v) w
    2 | v <= maxBound - d -> Just $ PLEq w (Lit (v + d))
    3 | v >= d -> Just $ PGEq w (Lit (v - d))
    4 | v > d -> Just $ PLT (Lit (v - d - 1)) w
    5 -> Just $ PNeg (PEq w (Lit (v + 1)))
    _ -> Nothing
  _ -> Nothing
