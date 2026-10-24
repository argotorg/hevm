-- | Checking hevm's runs against geth's
module EVM.Test.Fuzz.Check
  ( Report(..), addCoverage, bucket, checkCase, checkConcrete, concretize, concretizeProps
  , errorKind, hevmErrorKind, modelInputs, printCoverage, test, testEnv, withDir
  ) where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.IO.Unlift
import Control.Monad.Reader (ReaderT)
import Data.ByteString (ByteString)
import Data.Char (isDigit, toLower)
import Data.IORef (IORef, readIORef, atomicModifyIORef')
import Data.List (isInfixOf, isPrefixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Monoid (Any(..))
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (unpack)
import System.Directory (removeDirectoryRecursive)
import System.Environment (lookupEnv)
import System.IO.Temp (getCanonicalTemporaryDirectory, createTempDirectory)
import Test.Tasty (TestTree, TestName)
import Test.Tasty.HUnit (assertFailure, testCase)
import Witch (into)
import EVM.Expr qualified as Expr
import EVM.Fetch.MockNode (Node(..), withMockNode)
import EVM.Op (intToOpName)
import EVM.Progress qualified as Progress
import EVM.SMT qualified as SMT
import EVM.Solvers
import EVM.SymExec
import EVM.Traversals (foldProp, mapExpr, mapProp)
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Tracing (VMTraceStep(..))
import EVM.Test.Fuzz.Program
import EVM.Test.Fuzz.Geth
import EVM.Test.Fuzz.Hevm
import EVM.Test.Fuzz.Case

-- * Checking

data Outcome
  = OSuccess ByteString (Map Addr (Map W256 W256))
  | ORevert ByteString
  | OError String
  deriving (Show, Eq)

gethOutcome :: GethRun -> Outcome
gethOutcome g = case g.error of
  Nothing -> OSuccess g.output g.storage
  Just "execution reverted" -> ORevert g.output
  Just e -> OError (errorKind e)

-- | An error message without its details, e.g. "stack underflow" for geth's "stack underflow (0 <=> 2)"
errorKind :: String -> String
errorKind e = case unwords (takeWhile (not . any isDigit) (words (takeWhile (`notElem` ("(:" :: String)) (map toLower e)))) of
  "attempting to modify state while in static context" -> "write protection"
  k -> k

hevmErrorKind :: EvmError -> String
hevmErrorKind = errorKind . evmErrToString

-- | Symbolic execution does not track gas, so its outcome is unknown when gas ran out anywhere
gasDependent :: GethRun -> Bool
gasDependent g = any isGas (g.error : map (.error) g.trace) || any lowGasPrecompile (zip g.trace (drop 1 g.trace)) || callsModexp g
  where
    isGas = maybe False (\e -> "out of gas" `isInfixOf` e || "gas uint64 overflow" `isInfixOf` e)
    -- geth does not trace precompiles, and one that fails burns its gas whether it ran out or not.
    -- Generated precompile calls get plenty of gas, so a failing one with little may have run out.
    lowGasPrecompile (a, b) = case reverse a.stack of
      gas : target : _ -> a.op `elem` [0xf1, 0xf2, 0xf4, 0xfa] && target >= 1 && target <= 0x11
        && b.depth == a.depth && headMay (reverse b.stack) == Just 0 && min gas a.gas < 0x100000
      _ -> False

callsModexp :: GethRun -> Bool
callsModexp g = any (\t -> t.op `elem` [0xf1, 0xf2, 0xf4, 0xfa] && take 1 (drop 1 (reverse t.stack)) == [5]) g.trace

compareTraces :: [VMTraceStep] -> [EVMToolTrace] -> Either String ()
compareTraces hs gs = go hs (dedup gs)
  where
    -- geth traces a failing step once more, with its error
    dedup (a:b:rest) | isJust b.error, a.pc == b.pc, a.op == b.op, a.depth == b.depth = dedup (a : rest)
    dedup (a:rest) = a : dedup rest
    dedup [] = []
    go [] [] = Right ()
    -- hevm steps into code-less accounts, geth does not
    go (a:ax) bs
      | a.op == 0, a.pc == 0, a.depth > 1
      , maybe True (\b -> b.depth < a.depth) (headMay bs) = go ax bs
    go (a:ax) (b:bx)
      | a.op /= b.op || a.pc /= b.pc =
          Left $ "op/pc mismatch: hevm " <> step a <> ", geth " <> intToOpName b.op <> " pc " <> show b.pc
      | a.stack /= b.stack = mismatch "stack" a.stack b.stack
      | into a.gas /= b.gas = mismatch "gas" a.gas b.gas
      | into a.memSize /= b.memSize = mismatch "memSize" a.memSize b.memSize
      | a.depth /= b.depth = mismatch "depth" a.depth b.depth
      | otherwise = go ax bx
      where
        mismatch :: (Show x, Show y) => String -> x -> y -> Either String ()
        mismatch what x y = Left $ what <> " mismatch at " <> step a
          <> "\nhevm: " <> show x <> "\ngeth: " <> show y
    go a b = Left $ "trace lengths differ, hevm has " <> show (length a)
                 <> " more, geth has " <> show (length b) <> " more"
    step a = intToOpName a.op <> " pc " <> show a.pc

hevmOutcome :: HevmRun -> Outcome
hevmOutcome h = case h.result of
  Right b -> OSuccess b h.storage
  Left (Revert (ConcreteBuf b)) -> ORevert b
  Left e -> OError (hevmErrorKind e)

logsMatch :: [Expr Log] -> [GethLog] -> Bool
logsMatch hs gs = length hs == length gs && and (zipWith same hs gs)
  where
    same :: Expr Log -> GethLog -> Bool
    same (LogEntry (WAddr (LitAddr a)) (ConcreteBuf d) ts) g =
      addrKey a == g.address && d == bssToBs g.logData && map forceLit ts == g.topics
    same _ _ = False

-- | Concrete hevm against geth, howling failures with how hevm ran
checkConcrete :: String -> TestCase -> Inputs -> GethRun -> HevmRun -> IO ()
checkConcrete how c i g h = do
  let fails :: String -> IO a
      fails = failWith c i . ((how <> ": ") <>)
      ops :: [(Int, String)] -> String
      ops xs = unwords (map (\(p, o) -> show p <> ":" <> o) (take 40 xs))
        <> (if length xs > 40 then " ... " <> unwords (map (\(p, o) -> show p <> ":" <> o) (lastN 15 xs)) else "")
      lastN n xs = drop (length xs - n) xs
      traces = "\nhevm trace: " <> ops [(t.pc, intToOpName t.op) | t <- h.trace]
            <> "\ngeth trace: "
            <> ops [(t.pc, intToOpName t.op <> maybe "" withParens t.error) | t <- g.trace]
      withParens e = "(" <> e <> ")"
  -- geth 1.16.1 prices modexp before EIP-7883 was final, so gas and what depends on it differ
  unless (callsModexp g) $ do
    either (fails . (<> traces)) pure (compareTraces h.trace g.trace)
    let ho = hevmOutcome h
        go = gethOutcome g
    unless (ho == go || gasDependent g && failed ho && failed go) $
      fails $ "concrete outcome mismatch\nhevm: " <> show ho <> "\ngeth: " <> show go
    when (succeeded go && not (logsMatch h.logs g.logs)) $
      fails $ "logs mismatch\nhevm: " <> show h.logs <> "\ngeth: " <> show g.logs
    when (h.gasUsed /= g.gasUsed) $
      fails $ "gas used mismatch\nhevm: " <> show h.gasUsed <> "\ngeth: " <> show g.gasUsed
  where
    failed = \case OSuccess {} -> False; _ -> True
    succeeded = \case OSuccess {} -> True; _ -> False

-- | Substitute concrete inputs into a symbolic expression and evaluate it
concretize :: TestCase -> Inputs -> Expr a -> Expr a
concretize c i = untilFixpointN 4 (Expr.concKeccakSimpExpr . mapExpr blockHashes) . mapExpr inputs
  where
    inputs :: Expr b -> Expr b
    inputs = \case
      AbstractBuf "calldata" -> ConcreteBuf i.calldata
      AbstractStore (LitAddr a) Nothing | a == contractAddr -> ConcreteStore i.store
      TxValue -> Lit i.callvalue
      Timestamp -> Lit i.timestamp
      e -> e
    blockHashes :: Expr b -> Expr b
    blockHashes = \case
      BlockHash (Lit n) -> Lit $ if n + 256 < c.number || n >= c.number then 0 else blockHash n
      e -> e
    untilFixpointN :: Int -> (Expr b -> Expr b) -> Expr b -> Expr b
    untilFixpointN 0 _ e = e
    untilFixpointN k f e = let e' = f e in if e' == e then e else untilFixpointN (k - 1) f e'

concretizeProps :: TestCase -> Inputs -> [Prop] -> Maybe Bool
concretizeProps c i ps = case Expr.concKeccakSimpProps (map (mapProp (concretize c i)) ps) of
  [] -> Just True
  [PBool False] -> Just False
  _ -> Nothing

leafOutcome :: TestCase -> Inputs -> Expr End -> Either String (Maybe Outcome)
leafOutcome c i = \case
  Success _ _ buf contracts -> do
    out <- concreteBuf (concretize c i buf)
    stores <- forM [contractAddr, calleeAddr] $ \a -> case Map.lookup (LitAddr a) contracts of
      Just (C { storage = s }) -> case concretize c i s of
        ConcreteStore m -> Right (a, nonZero m)
        s' -> Left $ "storage of " <> show a <> " did not concretize: " <> show s'
      _ -> Left $ "missing contract " <> show a
    Right $ Just $ OSuccess out (Map.fromList stores)
  Failure _ _ (Revert buf) -> Just . ORevert <$> concreteBuf (concretize c i buf)
  Failure _ _ e -> Right $ Just $ OError (hevmErrorKind e)
  Partial {} -> Right Nothing
  e -> Left $ "unexpected leaf: " <> show e
  where
    concreteBuf :: Expr Buf -> Either String ByteString
    concreteBuf (ConcreteBuf b) = Right b
    concreteBuf b = Left $ "buffer did not concretize: " <> show b

-- | Select the leaf that the concrete inputs reach, and check it against geth.
-- Returns a label for coverage.
checkLeaves :: TestCase -> Inputs -> [Expr End] -> Maybe Int -> GethRun -> IO String
checkLeaves c i leaves expected g = do
  let fails :: String -> IO a
      fails msg = failWith c i (msg <> "\nleaves: " <> show leaves)
      evals = map (concretizeProps c i . extractProps) leaves
      concProps = Expr.concKeccakSimpProps . map (mapProp (concretize c i))
      undecided = [n | (n, Nothing) <- zip [0 :: Int ..] evals]
      taken = [n | (n, Just True) <- zip [0 :: Int ..] evals]
  -- past where gas runs out, the symbolic paths can e.g. hash huge buffers
      unknownCall = any (\case PCall {} -> True; _ -> False) . extractProps
  if gasDependent g && not (null undecided) && length taken <= 1 then pure "gas-dependent, undecided path"
  -- a call to a symbolic target gets fresh results, which the inputs cannot decide
  else if not (null undecided) && all (unknownCall . (leaves !!)) undecided && length taken <= 1
    then pure "call to unknown code, undecided path" else do
    unless (null undecided) $ fails $ "path conditions of leaves " <> show undecided <> " did not concretize: "
      <> show [concProps (extractProps (leaves !! n)) | n <- undecided]
    n <- case taken of
      [n] -> pure n
      _ -> fails $ "concrete inputs reach leaves " <> show taken <> " instead of exactly one"
    -- keccak of a symbolic buffer is only bounded, so a model may pick a hash no input has
    let spurious = maybe False (\e -> e /= n && hashesSymbolic (leaves !! e)) expected
        -- decomposition replaces mapping and array slots by their keys, and then
        -- the model's storage must be exact
        hashesSymbolic l = let ps = Expr.simplifyProps (extractProps l)
          in getAny $ foldMap (foldProp symKeccak mempty) (fromMaybe ps (Expr.decomposeStorageProps ps))
        symKeccak :: Expr b -> Any
        symKeccak = \case Keccak (ConcreteBuf _) -> Any False; Keccak _ -> Any True; _ -> Any False
    forM_ expected $ \e -> when (e /= n && not spurious) $ fails $ "model of leaf " <> show e <> " reaches leaf " <> show n
    if spurious then pure "model via symbolic keccak reaches another leaf"
    else if gasDependent g then pure "gas-dependent" else case leafOutcome c i (leaves !! n) of
      Left err -> fails err
      Right Nothing -> pure $ leafKind (leaves !! n)
      Right (Just o)
        | o == gethOutcome g -> pure $ case o of
            OSuccess {} -> "success"
            ORevert _ -> "revert"
            OError e -> "error: " <> e
        | otherwise -> fails $ "symbolic outcome mismatch\nsymbolic: " <> show o
                             <> "\ngeth: " <> show (gethOutcome g)

-- | Inputs from a model of a leaf's path condition
modelInputs :: Inputs -> SMTCex -> Either String Inputs
modelInputs orig cex = do
  cd <- case Map.lookup symCalldataBuf cex.buffers of
    Nothing -> Right orig.calldata
    Just m -> case SMT.collapse m of
      Just (Flat bs) -> Right bs
      _ -> Left $ "cannot flatten calldata model: " <> show m
  pure $ Inputs
    { calldata = cd
    , store = maybe orig.store (Map.filter (/= 0)) (Map.lookup (LitAddr contractAddr) cex.store)
    , callvalue = Map.findWithDefault orig.callvalue TxValue cex.txContext
    , timestamp = Map.findWithDefault orig.timestamp Timestamp cex.blockContext
    }

withDir :: (FilePath -> IO a) -> IO a
withDir f = do
  tmp <- getCanonicalTemporaryDirectory
  dir <- createTempDirectory tmp "evm-trace"
  r <- f dir
  removeDirectoryRecursive dir
  pure r

data Report = Report
  { tables :: [(String, String)] -- ^ (table, label) for 'tabulate'
  , generated :: Set String
  , executed :: Set String       -- ^ by geth, on any of the inputs
  , symbolic :: Set String       -- ^ with a non-literal operand
  }

leafKind :: Expr End -> String
leafKind = \case
  Success {} -> "success"
  Failure _ _ (Revert _) -> "revert"
  Failure _ _ e -> "error: " <> hevmErrorKind e
  Partial _ _ p -> "partial: " <> takeWhile (/= ' ') (show p)
  _ -> "other"

-- | Concrete hevm against geth, then the symbolic leaves against geth on the
-- concrete inputs and on models of up to 'maxReplays' other leaves
checkCase :: App m => Int -> TestCase -> m Report
checkCase maxReplays c = Progress.withProgressLogFromEnv "fuzz-symexec" $
  withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
  let phase name = liftIO $ lookupEnv "HEVM_FUZZ_CASE_FILE" >>= mapM_ (\f -> appendFile (f <> ".random-contract-concrete-call") ("\nphase: " <> name))
      runBoth i = do
        phase "geth"
        g <- liftIO $ withDir $ \dir -> runGeth dir c i
        phase "hevm"
        h <- runHevm solvers Nothing c i
        liftIO $ checkConcrete "hevm" c i g h
        phase "hevm via RPC"
        hr <- withRunInIO $ \run -> withMockNode c.number (preState c i) $ \node ->
          run (runHevm solvers (Just node.url) c i)
        liftIO $ checkConcrete "hevm via RPC" c i g hr
        pure g
      ran g = Set.fromList [intToOpName t.op | t <- g.trace]
      generated = codeOps (assembleItems c.prog.main) <> codeOps (assembleItems c.prog.callee)
  g <- runBoth c.inputs
  let gethTables = [("geth outcome", maybe "success" errorKind g.error)]
  phase "symbolic"
  runSymbolic solvers c >>= \case
    Nothing -> pure $ Report (("symbolic", "timeout") : gethTables) generated (ran g) mempty
    Just SymRun { leaves, symbolicOps = symOps, merges } -> do
      phase $ "leaves: " <> show (length leaves)
      first <- liftIO $ checkLeaves c c.inputs leaves Nothing g
      let candidates = take maxReplays [ (n, l) | (n, l) <- zip [0 ..] leaves
                                                , concretizeProps c c.inputs (extractProps l) /= Just True
                                                , not (isPartial l) ]
      replays <- forM candidates $ \(n, l) -> if mentionsBlockHash l
        -- BLOCKHASH of a symbolic number is uninterpreted, so a model can pick any hash
        then pure ("skipped: symbolic blockhash", Nothing, Nothing)
        else phase ("replay " <> show n) >> checkSatWithProps solvers (extractProps l) >>= \case
          Cex cex -> case modelInputs c.inputs cex of
            Left err -> pure ("model: " <> err, Nothing, Nothing)
            Right i -> do
              g' <- runBoth i
              r <- liftIO (checkLeaves c i leaves (Just n) g')
              phase ("hevm replay " <> show n)
              replayed <- replayModel c l cex
              -- where geth confirms the model reaches the leaf, so must `hevm symbolic`'s replay
              let confirmed = not (any (`isPrefixOf` r) ["gas-dependent", "model via symbolic keccak", "call to unknown code"])
              when (confirmed && replayed == Right False) $ liftIO $ failWith c i $
                "hevm symbolic's replay does not reproduce leaf " <> show n <> " that geth reaches\nleaf: " <> show l
              pure (r, Just g', Just (either (("cannot replay: " <>) . unpack) (\b -> if b then "validated" else "not reproducible") replayed))
          -- outside loops, branches are not checked for feasibility
          Qed -> pure ("unsat leaf", Nothing, Nothing)
          Unknown _ -> pure ("unknown", Nothing, Nothing)
          Error e
            | any (`isInfixOf` e) ["not currently implemented", "Cannot encode"] -> pure ("unsupported by SMT", Nothing, Nothing)
            | otherwise -> liftIO $ assertFailure $ "solver error: " <> show e
      pure $ Report
        { tables = gethTables
            <> [("leaves", bucket (length leaves)), ("concrete inputs reach", first)]
            <> [("forward jumps merged", bucket merges)]
            <> [("replayed model reaches", r) | (r, _, _) <- replays]
            <> [("hevm symbolic replay", h) | (_, _, Just h) <- replays]
            <> [("leaf kinds", leafKind l) | l <- leaves]
        , generated
        , executed = Set.unions (ran g : [ran g' | (_, Just g', _) <- replays])
        , symbolic = symOps
        }
  where
    mentionsBlockHash l = getAny $ foldMap (foldProp isBlockHash mempty) (extractProps l)
    isBlockHash :: Expr a -> Any
    isBlockHash = \case BlockHash _ -> Any True; _ -> Any False

-- | A count, in buckets for the coverage tables
bucket :: Int -> String
bucket n
  | n <= 1 = show n
  | n <= 4 = "2-4"
  | n <= 16 = "5-16"
  | n <= 64 = "17-64"
  | n <= 256 = "65-256"
  | n <= 1024 = "257-1024"
  | otherwise = ">1024"

-- | For each opcode: how many cases generated it, ran it in geth, and ran it
-- symbolically with a non-literal operand
type Coverage = Map String (Int, Int, Int)

addCoverage :: IO (IORef Coverage) -> Report -> IO ()
addCoverage cov r = do
  ref <- cov
  let new = Map.unionsWith add3
        [Map.fromSet (const (1, 0, 0)) r.generated, Map.fromSet (const (0, 1, 0)) r.executed, Map.fromSet (const (0, 0, 1)) r.symbolic]
      add3 (a, b, x) (a', b', x') = (a + a', b + b', x + x')
  atomicModifyIORef' ref (\m -> (Map.unionWith add3 m new, ()))

printCoverage :: IORef Coverage -> IO ()
printCoverage ref = do
  m <- readIORef ref
  let counts o = Map.findWithDefault (0, 0, 0) o m
      missing f = unwords [o | o <- genOps, f (counts o) == 0]
      takesOperands o = Map.findWithDefault 0 o opPops > 0
      fst3 (a, _, _) = a
      snd3 (_, b, _) = b
      thd3 (_, _, x) = x
  unless (Map.null m) $ do
    putStrLn "fuzz-symexec opcode coverage, in cases (generated/ran in geth/ran with a symbolic operand):"
    putStrLn $ "  never generated: " <> missing fst3
    putStrLn $ "  never ran in geth: " <> missing snd3
    putStrLn $ "  never ran with a symbolic operand: "
      <> unwords [o | o <- genOps, takesOperands o, thd3 (counts o) == 0]
    forM_ (chunksOf 6 (Map.toList m)) $ \row ->
      putStrLn $ "  " <> unwords [pad 20 (o <> " " <> show a <> "/" <> show b <> "/" <> show x) | (o, (a, b, x)) <- row]
  where
    pad n t = t <> replicate (n - length t) ' '
    chunksOf _ [] = []
    chunksOf n xs = take n xs : chunksOf n (drop n xs)

testEnv :: Env
testEnv = Env { config = defaultConfig }

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv testEnv b

-- | A hand-written program as a 'TestCase' with the given calldata
