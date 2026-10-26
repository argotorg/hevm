-- | Equivalence checking of two programs, by comparing every pair of end states
module EVM.Equivalence where

import Prelude hiding (Foldable(..))

import Control.Concurrent.Spawn (parMapIO, pool)
import Control.Exception (evaluate)
import Control.Monad (when, forM, forM_)
import Control.Monad.IO.Unlift (MonadUnliftIO, withRunInIO)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (liftIO)
import Data.Aeson ((.=))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Foldable (length, foldl', foldr)
import Data.List (sortBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Vector qualified as V
import GHC.Conc (getNumProcessors)
import Optics.Core

import EVM.CexReplay (modelUnknownCalls)
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (formatExpr, formatProp, formatState, formatError)
import EVM.Progress qualified as Progress
import EVM.Solvers (SolverGroup, checkSatWithProps)
import EVM.SymExec
import EVM.SymExec.Calldata (mkCalldata)
import EVM.Traversals (mapExpr)
import EVM.Types

data EqIssues = EqIssues
  { res :: [(EquivResult, String)]
    , partials :: [Expr End]
  }
  deriving (Show, Eq)

instance Monoid EqIssues where
  mempty = EqIssues mempty mempty

instance Semigroup EqIssues where
  EqIssues a1 b1 <> EqIssues a2 b2 = EqIssues (a1 <> a2) (b1 <> b2)

-- | Compares two contract runtimes for trace equivalence by running two VMs
-- and comparing the end states.
--
-- We do this by asking the solver to find a common input for each pair of
-- endstates that satisfies the path conditions for both sides and produces a
-- differing output. If we can find such an input, then we have a clear
-- equivalence break, and since we run this check for every pair of end states,
-- the check is exhaustive.
equivalenceCheck
  :: forall m . App m
  => SolverGroup
  -> Maybe Fetch.Session
  -> ByteString
  -> ByteString
  -> VeriOpts
  -> (Expr Buf, [Prop])
  -> Bool
  -> m EqIssues
equivalenceCheck solvers sess bytecodeA bytecodeB opts calldata create = do
  conf <- readConfig
  case bytecodeA == bytecodeB of
    True -> liftIO $ do
      when conf.debug $ putStrLn "bytecodeA and bytecodeB are identical"
      pure mempty
    False -> do
      when conf.debug $ liftIO $ do
        putStrLn "bytecodeA and bytecodeB are different, checking for equivalence"
      branchesAorig <- explorePhase "A" $ getBranches bytecodeA
      branchesBorig <- explorePhase "B" $ getBranches bytecodeB
      when conf.debug $ liftIO $ do
        liftIO $ putStrLn $ "branchesA props: " <> show (map extractProps branchesAorig)
        liftIO $ putStrLn $ "branchesB props: " <> show (map extractProps branchesBorig)
        liftIO $ putStrLn ""
        liftIO $ putStrLn $ "branchesA endstates: " <> show (map extractEndStates branchesAorig)

        liftIO $ putStrLn $ "branchesB endstates: " <> show (map extractEndStates branchesBorig)
      let branchesA = rewriteFresh "A-" branchesAorig
          branchesB = rewriteFresh "B-" branchesBorig
      let partialIssues = EqIssues mempty (filter isPartial branchesA <> filter isPartial branchesB)
      issues <- equivalenceCheck' solvers sess branchesA branchesB create
      pure $ filterQeds (issues <> partialIssues)
  where
    -- decompiles the given bytecode into a list of branches
    getBranches :: App m => ByteString -> m [Expr End]
    getBranches bs = do
      let bytecode = if BS.null bs then BS.pack [0] else bs
      prestate <- liftIO $ stToIO $ abstractVM calldata bytecode Nothing create
      interpret (Fetch.oracle solvers sess Fetch.noRpc) opts.iterConf prestate runExpr noopPathHandler
    filterQeds (EqIssues res partials) = EqIssues (filter (\(r, _) -> not . isQed $ r) res) partials
    explorePhase :: Text -> m [Expr End] -> m [Expr End]
    explorePhase prog = Progress.withPhase ("explore " <> prog) ["program" .= prog] $ \ends ->
      ["paths" .= length ends, "partial" .= length (filter isPartial ends)]

rewriteFresh :: Text -> [Expr a] -> [Expr a]
rewriteFresh prefix exprs = fmap (mapExpr mymap) exprs
  where
    mymap :: Expr a -> Expr a
    mymap = \case
      Gas p x -> Gas (prefix <> p) x
      Var name | ("-fresh-" `T.isInfixOf` name) -> Var $ prefix <> name
      AbstractBuf name | ("-fresh-" `T.isInfixOf` name) -> AbstractBuf $ prefix <> name
      x -> x

equivalenceCheck'
  :: forall m . App m
  => SolverGroup -> Maybe Fetch.Session -> [Expr End] -> [Expr End] -> Bool -> m EqIssues
equivalenceCheck' solvers sess branchesA branchesB create = do
      conf <- readConfig
      when conf.debug $ do
        liftIO $ printPartialIssues branchesA "codeA"
        liftIO $ printPartialIssues branchesB "codeB"

      let allPairs = [(a,b) | a <- branchesA, b <- branchesB]
      when conf.debug $ liftIO $ putStrLn $ "Found " <> show (length allPairs) <> " total pairs of endstates"

      when conf.dumpEndStates $ liftIO $
        putStrLn $ "endstates in bytecodeA: " <> show (length branchesA)
                   <> "\nendstates in bytecodeB: " <> show (length branchesB)

      let numPairs = length allPairs
      ps <- Progress.withPhase "build-pairs" ["pairs" .= numPairs] (\r -> ["toCheck" .= length (mapMaybe (view _1) r)]) $ do
        Progress.phaseTotal numPairs
        forM (zip [(0::Int)..] allPairs) $ \(i, (a, b)) -> do
          when (i `mod` 1000 == 0) $ do
            Progress.setWorker ["phase" .= ("build-pairs" :: Text), "pair" .= i, "of" .= numPairs]
            Progress.phaseAt i
          r <- distinct a b
          -- force the simplification here, or it would be timed as part of the next phase
          _ <- liftIO $ evaluate $ maybe 0 (Set.size . fst) (fst r)
          pure r
      Progress.clearWorker
      let differingEndStates = sortBySize $ mapMaybe (view _1) ps
      let knownIssues = foldr ((<>) . (view _2)) mempty ps
      when conf.debug $ liftIO $ putStrLn $ "Asking the SMT solver for " <> (show $ length differingEndStates) <> " pairs"
      when conf.dumpEndStates $ forM_ (zip differingEndStates [(1::Integer)..]) (\((props, msg), i) ->
        liftIO $ T.writeFile ("prop-checked-" <> show i <> ".prop") (T.pack $ show props <> msg))

      procs <- liftIO getNumProcessors
      newDifferences <- Progress.withPhase "check-pairs" ["pairs" .= length differingEndStates]
        (\r -> [ "sat" .= length (filter (isCex . fst) r), "unsat" .= length (filter (isQed . fst) r)
               , "other" .= length (filter (\(x, _) -> not (isCex x || isQed x)) r) ]) $ do
        Progress.phaseTotal (length differingEndStates)
        checkAll differingEndStates procs
      let additionalIssues = EqIssues newDifferences mempty
      pure $ knownIssues <> additionalIssues

  where
    -- we order the sets by size because this gives us more UNSAT cache hits when
    -- running our queries later on (since we rely on a subset check)
    sortBySize :: [(Set a, b)] -> [(Set a, b)]
    sortBySize = sortBy (\(a, _) (b, _) -> compare (Set.size a) (Set.size b))

    -- Allows us to run the queries in parallel. Note that this (seems to) run it
    -- from left-to-right, and with a max of K threads. This is in contrast to
    -- mapConcurrently which would spawn as many threads as there are jobs, and
    -- run them in a random order. We ordered them correctly, though so that'd be bad
    checkAll :: (App m, MonadUnliftIO m) => [(Set Prop, String)] -> Int -> m [(EquivResult, String)]
    checkAll input numproc = withRunInIO $ \env -> do
       wrap <- pool numproc
       parMapIO (runOne env wrap) (zip [(0::Int)..] input)
       where
         total = length input
         runOne env wrap (i, (props, meaning)) = do
           res <- wrap $ do
             Progress.setWorker ["phase" .= ("check-pairs" :: Text), "pair" .= i, "of" .= total, "props" .= Set.size props]
             r <- env $ checkSatWithProps solvers (Set.toList props)
                    <&> \case
                      Cex c -> Cex c { unknownCalls = modelUnknownCalls c (Set.toList props) }
                      other -> other
             Progress.clearWorker
             Progress.phaseTick
             pure r
           pure (res, meaning)

    -- Takes two branches and returns a set of props that will need to be
    -- satisfied for the two branches to violate the equivalence check. i.e.
    -- for a given pair of branches, equivalence is violated if there exists an
    -- input that satisfies the branch conditions from both sides and produces
    -- a differing result in each branch
    distinct :: App m => Expr End -> Expr End -> m (Maybe (Set Prop, String), EqIssues)
    distinct aEnd bEnd = do
      (requireToDiff, issues) <- resultsDiffer aEnd bEnd
      pure (collectReqs requireToDiff, issues)
      where
        collectReqs (Just (reqToDiff, meaning)) = Just (Set.fromList $ Expr.simplifyProps (reqToDiff : extractProps aEnd <> extractProps bEnd), meaning)
        collectReqs Nothing  = Nothing

    -- Note that the a==b and similar checks are ONLY syntactic checks. If they are true,
    -- then they are surely equivalent. But if not, we need to check via SMT
    resultsDiffer :: App m => Expr End -> Expr End -> m (Maybe (Prop, String), EqIssues)
    resultsDiffer aEnd bEnd = do
      let deployText :: String = if create then "Undeployed contracts. " else "Deployed contracts. "
      case (aEnd, bEnd) of
        (Success aProps _ aOut aState, Success bProps _ bOut bState) ->
          case (aOut == bOut, aState == bState, create) of
            (True, True, _) -> pure (Nothing, mempty)
            (_, _, True) -> do
              -- Either the deployed code doesn't behave the same, or they start with a different
              -- starting state
              deployedContractIssues <- deployedCodeDiffer aOut bOut aProps bProps
              let deployedStateDiffer = (statesDiffer aState bState,
                    deployText <> "Both end in Successful code deployment, but starting states differ. " <>
                    "\nRet of A: " <> T.unpack (formatExpr aOut) <>
                    "\nState of A: " <> T.unpack (formatState aState) <>
                    "\nRet of B: " <> T.unpack (formatExpr bOut) <>
                    "\nState of B: " <> T.unpack (formatState bState))
              pure (Just deployedStateDiffer, deployedContractIssues)
            (_, _, False) -> do
              pure (Just ((aOut ./= bOut) .|| (statesDiffer aState bState),
                deployText <> "Both end in Success, but return values or end state differ. " <>
                "\nRet of A: " <> T.unpack (formatExpr aOut) <>
                "\nState of A: " <> T.unpack (formatState aState) <>
                "\nRet of B: " <> T.unpack (formatExpr bOut) <>
                "\nState of B: " <> T.unpack (formatState bState)), mempty)
        (Failure _ _ a, Failure _ _ b) -> pure (Just (differentError a b,
                  deployText <> "Both end in Failure but different EVM error." <>
                  "\nA err: " <> T.unpack (formatError a) <>
                  "\nB err: " <> T.unpack (formatError b)), mempty)
        ((Failure _ _ a), (Success _ _ b _)) -> pure (Just (PBool True,
          deployText <> "Failure vs Success end states" <>
          "\nA err: " <> T.unpack (formatError a) <>
          "\nB ret: " <> T.unpack (formatExpr b)), mempty)
        ((Success _ _ a _), (Failure _ _ b)) -> pure (Just (PBool True,
          deployText <> "Success vs Failure end states" <>
          "\nA ret: " <> T.unpack (formatExpr a) <>
          "\nB err: " <> T.unpack (formatError b)), mempty)
        -- partial end states can't be compared to actual end states, so we always ignore them
        (Partial {}, _) -> pure (Nothing, mempty)
        (_, Partial {}) -> pure (Nothing, mempty)
        (GVar _, _) -> internalError "GVar in equivalence check"
        (_, GVar _) -> internalError "GVar in equivalence check"

        where
          -- All EVM errors that cannot be syntactically compared are compared semantically: BalanceTooLow, Revert, and MaxInitCodeSizeExceeded
          differentError :: EvmError ->EvmError -> Prop
          differentError a b =  case (a, b) of
            (BalanceTooLow a1Word a2Word, BalanceTooLow b1Word b2Word) -> (a1Word ./= b1Word) .|| (a2Word ./= b2Word)
            (Revert aBuf, Revert bBuf) -> aBuf ./= bBuf
            (MaxInitCodeSizeExceeded l1 aWord, MaxInitCodeSizeExceeded l2 bWord) -> (PBool (l1 /= l2)) .|| (aWord ./= bWord)
            (x, y) | x == y -> PBool False
                   | otherwise -> PBool True

    -- If the original check was for create (i.e. undeployed code), then we must also check that the deployed
    -- code is equivalent. The constraints from the undeployed code (aProps,bProps) influence this check.
    deployedCodeDiffer :: Expr Buf -> Expr Buf -> [Prop] -> [Prop] -> m EqIssues
    deployedCodeDiffer aOut bOut aProps bProps = do
      let simpA = Expr.simplify aOut
          simpB = Expr.simplify bOut
      conf <- readConfig
      case (simpA, simpB) of
        (ConcreteBuf codeA, ConcreteBuf codeB) -> do
          -- TODO: use aProps/bProps to constrain the deployed code
          --       since symbolic code (with constructors taking arguments) is not supported,
          --       this is currently not necessary
          when conf.debug $ liftIO $ do
            liftIO $ putStrLn $ "create deployed code A: " <> bsToHex codeA
              <> " with constraints: " <> (T.unpack . T.unlines $ map formatProp aProps)
            liftIO $ putStrLn $ "create deployed code B: " <> bsToHex codeB
              <> " with constraints: " <> (T.unpack . T.unlines $ map formatProp bProps)
          (calldata, _) <- mkCalldata Nothing []
          equivalenceCheck solvers sess codeA codeB defaultVeriOpts calldata False
        _ -> internalError $ "Symbolic code returned from constructor." <> " A: " <> show simpA <> " B: " <> show simpB

    statesDiffer :: Map (Expr EAddr) (Expr EContract) -> Map (Expr EAddr) (Expr EContract) -> Prop
    statesDiffer aState bState
      | aState == bState = PBool False
      | otherwise = case sequence (Map.merge (Map.mapMissing (\_ c -> (c,) <$> untouched c))
                                             (Map.mapMissing (\_ c -> (,c) <$> untouched c))
                                             (Map.zipWithMatched (\_ x y -> Just (x, y))) aState bState) of
          -- TODO: consider possibility of aliased symbolic addresses
          Nothing -> PBool True
          Just merged -> Map.foldlWithKey' (\a addr (ac, bc) -> a .|| contractsDiffer addr ac bc) (PBool False) merged
      where
        -- a call to unknown code adds its callee to the state of only the program
        -- that made it; the other program sees the callee as it was before
        untouched :: Expr EContract -> Maybe (Expr EContract)
        untouched = \case
          C (UnknownCode k) _ _ _ _ -> Just (C (UnknownCode k) (AbstractStore k Nothing) (ConcreteStore mempty) (Balance k) Nothing)
          _ -> Nothing

    contractsDiffer :: Expr EAddr -> Expr EContract -> Expr EContract -> Prop
    contractsDiffer addr ac bc = let
        balsDiffer = case (ac.balance, bc.balance) of
          (Lit ab, Lit bb) -> PBool $ ab /= bb
          (ab, bb) -> if ab == bb then PBool False else ab ./= bb
        -- TODO: is this sound? do we need a more sophisticated nonce representation?
        noncesDiffer = PBool (ac.nonce /= bc.nonce)
        storesDiffer = case (ac.storage, bc.storage) of
          -- a slot written with 0 is the same as an unwritten one
          (ConcreteStore as, ConcreteStore bs) -> PBool $ Map.filter (/= 0) as /= Map.filter (/= 0) bs
          (as, bs) -> if as == bs then PBool False else as ./= bs
        -- e.g. of created contracts; the entrypoint's code is A or B by construction
        codesDiffer = if addr == SymAddr "entrypoint" || ac.code == bc.code then PBool False else case (ac.code, bc.code) of
          (RuntimeCode a, RuntimeCode b) -> case (bytes a, bytes b) of
            (as, bs) | length as /= length bs -> PBool True
                     | otherwise -> foldl' (.||) (PBool False) [x ./= y | (x, y) <- zip as bs, x /= y]
          _ -> PBool True
        bytes = \case
          ConcreteRuntimeCode bs -> map LitByte (BS.unpack bs)
          SymbolicRuntimeCode v -> V.toList v
      in balsDiffer .|| storesDiffer .|| noncesDiffer .|| codesDiffer
