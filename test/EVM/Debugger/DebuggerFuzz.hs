{-# LANGUAGE MultiWayIf #-}

{-|
Module      : DebuggerFuzz
Description : Fuzzing of the interactive debugger and its HTTP server

Random command sequences drive debugging sessions of the random programs of
'EVM.Test.FuzzSymExec'. Every state reached must be the one that plainly stepping
forward reaches, and every symbolic branch offered must be feasible. The HTTP
server gets malformed and concurrent requests, and must keep answering.
-}
module EVM.Debugger.DebuggerFuzz (tests) where

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Exception (bracket, try, SomeException, evaluate)
import Control.Monad (forM, forM_, void)
import Control.Monad.IO.Unlift (MonadUnliftIO, liftIO)
import Control.Monad.ST (stToIO)
import Data.Aeson qualified as JSON
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BC
import Data.ByteString.Lazy qualified as BL
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import System.Timeout (timeout)
import Test.QuickCheck.Instances.ByteString ()
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck

import EVM.Dapp (emptyDapp)
import EVM.Debugger
import EVM.Debugger.Server (serveSession)
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Solvers (withSolvers, defMemLimit, Solver(..), SolverGroup, checkSatWithProps)
import EVM.Stepper qualified as Stepper
import EVM.Test.FuzzSymExec (TestCase, concreteTestVm, symbolicTestVm)
import EVM.Types hiding (Env)

tests :: TestTree
tests = testGroup "debugger-fuzz"
  [ testProperty "concrete-replay" $ mapSize (* 4) $ \(c :: TestCase) ->
      forAll (genCommands False) $ \cmds -> within 120_000_000 $ ioProperty $ runEnv testEnv $ concreteReplay c cmds
  , testProperty "symbolic-branches" $ mapSize (* 4) $ \(c :: TestCase) ->
      forAll (genCommands True) $ \cmds -> forAll (vectorOf 40 genReaction) $ \reactions ->
      within 300_000_000 $ ioProperty $ runEnv testEnv $ symbolicBranches c cmds reactions
  , testProperty "forward-back-concrete" $ mapSize (* 4) $ \(c :: TestCase) ->
      forAll genRoundTrips $ \(start, ks) -> within 120_000_000 $ ioProperty $ runEnv testEnv $ withSession $ \solvers -> do
        s0 <- liftIO $ stToIO (concreteTestVm c) >>= newSession emptyDapp
        roundTrips (Fetch.oracle solvers Nothing Fetch.noRpc) (repeat Nothing) start ks s0
  , testProperty "forward-back-symbolic" $ mapSize (* 4) $ \(c :: TestCase) ->
      forAll genRoundTrips $ \(start, ks) -> forAll (vectorOf 100 genReaction) $ \reactions -> \explorer -> \merging ->
      within 300_000_000 $ ioProperty $ runEnv testEnv $ withSession $ \solvers -> do
        s0 <- liftIO $ stToIO (symbolicTestVm c) >>= newSession emptyDapp
        let mode = if explorer then ExplorerBranches else SolverBranches
        tabulate "branch mode" [show mode <> if merging then ", merging" else ""] <$>
          roundTrips (Fetch.oracle solvers Nothing Fetch.noRpc) reactions start ks (setMerge merging (setBranchMode mode (setStepLimit 3000 s0)))
  , testProperty "http-garbage" $ \(c :: TestCase) ->
      forAll (listOf1 genRequest) $ \reqs -> within 120_000_000 $ ioProperty $ runEnv testEnv $ httpGarbage c reqs
  ]

testEnv :: Env
testEnv = Env { config = defaultConfig }

-- * Commands

genCommands :: Bool -> Gen [Text]
genCommands symbolic = do
  n <- chooseInt (1, 25)
  vectorOf n (genCommand symbolic)

genCommand :: Bool -> Gen Text
genCommand symbolic = frequency $
  [ (8, ("step " <>) . tshow <$> chooseInt (0, 60))
  , (2, pure "step")
  , (5, ("back " <>) . tshow <$> chooseInt (0, 80))
  , (2, pure "back")
  , (2, pure "restart")
  , (if symbolic then 10 else 2, pure "continue")
  , (1, elements ["next", "over", "out", "back-line"])
  , (2, ("break op " <>) <$> elements ["JUMPI", "JUMP", "SSTORE", "MSTORE", "CALL", "JUMPDEST", "SLOAD", "RETURN"])
  , (1, ("break pc " <>) . tshow <$> chooseInt (0, 300))
  , (1, ("break line " <>) . tshow <$> chooseInt (0, 30))
  , (1, elements ["delete all", "delete 0", "delete 1", "delete 7", "breakpoints"])
  , (1, elements ["memory", "memory 0 64", "memory 32", "memory 0x40 0x20", "storage", "calldata", "trace"
                 , "pathconds", "help", "show", "stats", ""])
  , (1, genGarbage)
  , (1, elements ["simplify on", "simplify off"])
  , (1, elements ["merge on", "merge off"])
  ] <> [ (1, elements ["branches solver", "branches explorer"]) | not symbolic ] <> [ (8, elements ["branch true", "branch false", "branch 0", "branch 1", "branch 2", "branch t", "branch f"])
       | symbolic ]

genGarbage :: Gen Text
genGarbage = oneof
  [ T.pack <$> listOf (elements (['a' .. 'z'] <> ['0' .. '9'] <> " -:x\t\n\"{}"))
  , elements [ "step 0x", "step -3", "back -5", "step 99999999999999999999999", "back 0xffffffffffffffffffff"
             , "memory 0xffffffffffffffff 10", "memory 10 0xffffffffffffffffff", "memory -1 -1"
             , "break pc -1", "break line :", "break line foo:", "break line :12", "delete -1"
             , "branch", "branch 99999999999999999999", "branch -1", "STEP 2", "  step   3  ", "step 1 2" ]
  ]

type Fingerprint = [Text]

-- | Everything a session shows. Also forces the JSON and text renderings.
fingerprint :: (App m, Debuggable t) => Fetch.Fetcher t m -> Session t -> m Fingerprint
fingerprint fetcher s0 = do
  -- what is shown depends on this setting, the state does not
  s <- runCommandText fetcher "simplify on" s0
  v <- liftIO $ mkView s
  _ <- liftIO $ evaluate (BL.length (JSON.encode v) + fromIntegral (T.length (renderView v)))
  let memLen = min 4096 (fromIntegral v.memorySize) :: Int
  extra <- forM ["memory 0 " <> tshow memLen, "storage", "calldata", "trace", "pathconds"] $ \cmd -> do
    v' <- runCommandText fetcher cmd s >>= liftIO . mkView
    pure (maybe "" id v'.output)
  pure $ [ tshow v.step, tshow v.pc, v.op, T.intercalate "," v.stack, tshow v.gas, tshow v.depth
         , v.status, tshow v.result, tshow v.memorySize, tshow (fmap (.options) v.branch) ] <> extra

fingerprintKeys :: [Text]
fingerprintKeys = ["step", "pc", "op", "stack", "gas", "depth", "status", "result", "memorySize", "branch"
                  , "memory", "storage", "calldata", "trace", "pathconds"]

describeDiff :: Fingerprint -> Fingerprint -> String
describeDiff a b = unlines
  [ T.unpack k <> ":\n  got:      " <> T.unpack x <> "\n  expected: " <> T.unpack y
  | (k, x, y) <- zip3 fingerprintKeys a b, x /= y ]

-- | Each command counts once, and nothing counted is ever undone
statsProblems :: StatsView -> StatsView -> [String]
statsProblems before after =
  [ "commands went from " <> show b.commands <> " to " <> show a.commands | a.commands /= b.commands + 1 ]
  <> [ name <> " decreased from " <> show (f b) <> " to " <> show (f a) | (name, f) <- ints, f a < f b ]
  <> [ name <> " decreased" | (name, f) <- [("commandSecs", (.commandSecs)), ("querySecs", (.querySecs))], f a < f b ]
  <> [ "replayed " <> show a.replayedOpcodes <> " of " <> show a.opcodes <> " opcodes" | a.replayedOpcodes > a.opcodes ]
  <> [ "took " <> show a.branchesTaken <> " of " <> show a.branchesOffered <> " branches offered" | a.branchesTaken > a.branchesOffered ]
  <> [ "queries " <> show a.queries <> " are not the sum of their kinds" | a.queries /= a.branchQueries + a.solutionQueries + a.fetchQueries + a.otherQueries ]
  <> [ "step " <> show after.step <> " is not the session's" | after.step < 0 ]
  where
    a = after.counters
    b = before.counters
    ints :: [(String, Stats -> Int)]
    ints = [ ("opcodes", (.opcodes)), ("replayedOpcodes", (.replayedOpcodes)), ("queries", (.queries))
           , ("branchQueries", (.branchQueries)), ("solutionQueries", (.solutionQueries)), ("fetchQueries", (.fetchQueries))
           , ("otherQueries", (.otherQueries)), ("branchesOffered", (.branchesOffered)), ("branchesTaken", (.branchesTaken))
           , ("staticDecisions", (.staticDecisions))
           , ("breakpointHits", (.breakpointHits)) ]

withSession :: (MonadUnliftIO m, ReadConfig m, TTY m) => (SolverGroup -> m a) -> m a
withSession = withSolvers Bitwuzla 1 (Just 10) defMemLimit

-- * Concrete

-- | After every command, the state must be the one a fresh session reaches by
-- stepping forward to the same step, and running to the end must agree with exec
concreteReplay :: App m => TestCase -> [Text] -> m Property
concreteReplay c cmds = withSession $ \solvers -> do
  let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
      fresh = liftIO $ stToIO (concreteTestVm c) >>= newSession emptyDapp
      go _ [] _ = pure Nothing
      go s (cmd : rest) done = do
        s' <- runCommandText fetcher cmd s
        ref <- fresh >>= runCommandText fetcher ("step " <> tshow (sessionStep s'))
        a <- fingerprint fetcher s'
        b <- fingerprint fetcher ref
        let hist = reverse (cmd : done)
            refStats = (sessionStats ref).counters
            problems = statsProblems (sessionStats s) (sessionStats s')
              <> [ "a session that only stepped forward executed " <> show refStats.opcodes <> " opcodes to reach step "
                   <> show (sessionStep ref) | refStats.opcodes /= sessionStep ref || refStats.replayedOpcodes /= 0 ]
        if | a /= b -> pure $ Just $ "after commands " <> show hist <> " the state differs from stepping forward:\n" <> describeDiff a b
           | not (null problems) -> pure $ Just $ "after commands " <> show hist <> " the stats are wrong:\n" <> unlines problems
           | otherwise -> go s' rest (cmd : done)
  s0 <- fresh
  mismatch <- go s0 cmds []
  case mismatch of
    Just msg -> pure $ counterexample msg False
    Nothing -> do
      sEnd <- fresh >>= runCommandText fetcher "continue"
      vm0 <- liftIO $ stToIO (concreteTestVm c)
      vm' <- Stepper.interpret fetcher vm0 Stepper.runFully
      let got = (show (sessionVM sEnd).result, (sessionVM sEnd).state.gas)
          expected = (show vm'.result, vm'.state.gas)
      pure $ tabulate "steps to the end" [bucket (sessionStep sEnd)]
           $ counterexample ("run to the end: " <> show got <> "\nexec: " <> show expected) (got == expected)

-- * Symbolic

-- | What to do at a pending branch: pick a side, or go on with the next command
genReaction :: Gen (Maybe Text)
genReaction = frequency [(3, Just <$> elements ["branch true", "branch false"]), (1, pure Nothing)]

-- | States revisited on the same path must not change, and the path
-- conditions after picking a branch must be satisfiable
symbolicBranches :: App m => TestCase -> [Text] -> [Maybe Text] -> m Property
symbolicBranches c cmds0 reactions0 = withSession $ \solvers -> do
  let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
      go s seen cmds done taken reactions
        | isPending s, (Just r : more) <- reactions = step s seen r cmds done taken more
        | otherwise = case cmds of
            [] -> finish s taken
            cmd : rest -> step s seen cmd rest done taken (drop 1 reactions)
      isPending = hasPendingBranch
      finish s taken = do
        v <- liftIO $ mkView s
        pure (Right (taken, v.status, maybe "" (T.take 40) v.result))
      step s seen cmd rest done taken reactions = do
        s' <- runCommandText fetcher cmd s
        v <- liftIO $ mkView s'
        fp <- fingerprint fetcher s'
        let hist = reverse (cmd : done)
            key = (v.choices, v.step, v.status)
        let tookBranch = "Took branch" `T.isPrefixOf` v.message
        infeasible <- if tookBranch
          then isQed <$> checkSatWithProps solvers (sessionVM s').constraints
          else pure False
        let problems = statsProblems (sessionStats s) (sessionStats s')
              <> [ "branchesTaken is " <> show (sessionStats s').counters.branchesTaken <> " after taking " <> show taken'
                 | (sessionStats s').counters.branchesTaken /= taken' ]
            taken' = taken + if tookBranch then 1 else 0
        case Map.lookup key seen of
          _ | not (null problems) -> pure $ Left $ "after commands " <> show hist <> " the stats are wrong:\n" <> unlines problems
          _ | infeasible -> pure $ Left $ "after commands " <> show hist <> " the path is infeasible"
          Just fp0 | fp0 /= fp ->
            pure $ Left $ "after commands " <> show hist <> " a revisited state differs:\n" <> describeDiff fp fp0
          -- with another merge setting, a step number reaches another state
          _ | "merge" `T.isPrefixOf` T.strip cmd -> go s' (Map.singleton key fp) rest (cmd : done) taken' reactions
            | otherwise -> go s' (Map.insert key fp seen) rest (cmd : done) taken' reactions
  s0 <- liftIO $ stToIO (symbolicTestVm c) >>= newSession emptyDapp
  mismatch <- go (setStepLimit 3000 s0) (mempty :: Map ([Text], Int, Text) Fingerprint) cmds0 [] (0 :: Int) reactions0
  pure $ case mismatch of
    Left msg -> counterexample msg False
    Right (taken, status, res) -> tabulate "branches taken" [bucket taken]
                                $ tabulate "final status" [T.unpack status]
                                $ tabulate "result" [T.unpack res] (property True)

-- * Round trips

-- | Where to start, as a fraction of the steps the run has, and the trips
genRoundTrips :: Gen (Double, [Int])
genRoundTrips = (,) <$> choose (0, 1) <*> (listOf1 (frequency [(3, chooseInt (1, 20)), (1, chooseInt (1, 300))]))

-- | Steps n times, picking a side whenever a branch is pending
advance :: (App m, Debuggable t) => Fetch.Fetcher t m -> [Maybe Text] -> Int -> Session t -> m (Session t, [Maybe Text])
advance fetcher reactions n s
  | n <= 0 || isHalted s = pure (s, reactions)
  | hasPendingBranch s = case reactions of
      Just r : more -> runCommandText fetcher r s >>= advance fetcher more n
      _ -> pure (s, drop 1 reactions)
  | otherwise = do
      s' <- runCommandText fetcher "step" s
      if sessionStep s' == sessionStep s then pure (s', reactions) else advance fetcher reactions (n - 1) s'

-- | From step @start@, going forward k steps and back as many as were taken
-- must return to the same state, for each k in turn
roundTrips :: (App m, Debuggable t) => Fetch.Fetcher t m -> [Maybe Text] -> Double -> [Int] -> Session t -> m Property
roundTrips fetcher reactions0 at ks s0 = do
  (sEnd, _) <- advance fetcher reactions0 3000 s0
  let start = floor (at * fromIntegral (sessionStep sEnd))
  (s1, reactions1) <- advance fetcher reactions0 start s0
  fp1 <- fingerprint fetcher s1
  let go _ [] _ trips = pure $ tabulate "trips taken" [bucket trips] (property True)
      go reactions (k : rest) done trips = do
        (s2, reactions') <- advance fetcher reactions k s1
        let d = sessionStep s2 - sessionStep s1
        s3 <- if d > 0 then runCommandText fetcher ("back " <> tshow d) s2 else pure s1
        fp3 <- fingerprint fetcher s3
        if fp3 /= fp1
          then pure $ counterexample ("from step " <> show (sessionStep s1) <> ", after going forward " <> show done
                                      <> " then " <> show d <> " steps and back, the state differs:\n" <> describeDiff fp3 fp1) False
          else go reactions' rest (done <> [k]) (trips + if d > 0 then 1 else 0)
  go reactions1 ks [] (0 :: Int)

-- * HTTP

data Framing = Exact | NoLength | Shorter | Longer | BogusLength ByteString | Truncated | BareNewlines
  deriving (Show)

data Request = Request
  { method  :: ByteString
  , target  :: ByteString
  , body    :: ByteString
  , framing :: Framing
  , raw     :: Maybe ByteString
  } deriving (Show)

genRequest :: Gen Request
genRequest = do
  m <- frequency [(5, pure "GET"), (5, pure "POST"), (1, elements ["OPTIONS", "PUT", "DELETE", "", "get", "POST POST"])]
  t <- frequency
    [ (8, elements [ "/state", "/state?format=text", "/command", "/command?format=text", "/help", "/", "/stats", "/stats?format=text"
                   , "/progress", "/progress?format=text" ])
    , (2, elements [ "/nope", "/state?format", "/command?&&==", "/state?format=text&format=json", "//state"
                   , "/command?format=text?x", "*", "" ])
    , (1, BS.pack <$> listOf (choose (33, 126)))
    ]
  b <- frequency
    [ (6, encodeUtf8 <$> genCommand True)
    , (3, (\cmd -> BL.toStrict (JSON.encode (JSON.object ["command" JSON..= cmd]))) <$> genCommand True)
    , (1, elements [ "{\"command\": 5}", "{\"cmd\": \"step\"}", "{", "[]", "null", "{\"command\": \"step\"" ])
    , (1, arbitrary)
    ]
  f <- frequency
    [ (8, pure Exact), (1, pure NoLength), (1, pure Shorter), (1, pure Longer)
    , (1, BogusLength <$> elements ["-5", "abc", "99999999999999999999", "", "0x10", " 3 "])
    , (1, pure Truncated), (1, pure BareNewlines) ]
  r <- frequency [(12, pure Nothing), (1, Just <$> arbitrary)]
  pure $ Request m t b f r

render :: Request -> ByteString
render r = case r.raw of
  Just bytes -> bytes
  Nothing -> case r.framing of
    Truncated -> BS.take (BS.length full `div` 2) full
    BareNewlines -> BC.filter (/= '\r') full
    _ -> full
  where
    len = BS.length r.body
    lenHeader = case r.framing of
      NoLength -> ""
      Shorter -> header (max 0 (len - 3))
      Longer -> header (len + 10)
      BogusLength v -> "Content-Length: " <> v <> "\r\n"
      _ -> header len
    header n = "Content-Length: " <> BC.pack (show n) <> "\r\n"
    full = r.method <> " " <> r.target <> " HTTP/1.1\r\nHost: localhost\r\n" <> lenHeader <> "\r\n" <> r.body

-- | Sends a request, closing our side so a server waiting for more body sees EOF
exchange :: Int -> ByteString -> IO (Maybe ByteString)
exchange port bytes = timeout 30_000_000 $ do
  addr : _ <- getAddrInfo (Just defaultHints { addrSocketType = Stream }) (Just "127.0.0.1") (Just (show port))
  bracket (openSocket addr) close $ \sock -> do
    connect sock (addrAddress addr)
    sendAll sock bytes
    shutdown sock ShutdownSend
    readAll sock BS.empty
  where
    readAll sock acc = do
      chunk <- try (recv sock 65536)
      case chunk of
        Left (_ :: SomeException) -> pure acc
        Right ch | BS.null ch -> pure acc
                 | otherwise -> readAll sock (acc <> ch)

-- | Every request is answered with a well-formed response, and afterwards the
-- server still serves the session
httpGarbage :: App m => TestCase -> [Request] -> m Property
httpGarbage c reqs = withSession $ \solvers -> do
  sess <- liftIO $ stToIO (concreteTestVm c) >>= newSession emptyDapp
  portVar <- liftIO newEmptyMVar
  done <- liftIO newEmptyMVar
  conf <- readConfig
  let serve = serveSession (Fetch.oracle solvers Nothing Fetch.noRpc) 0 (putMVar portVar) (setStepLimit 20000 sess)
  liftIO $ bracket (forkIO (runEnv (Env { config = conf }) serve >> putMVar done ())) killThread $ \_ -> do
    port <- takeMVar portVar
    -- a few at a time, concurrently
    results <- fmap concat $ forM (chunksOf 4 reqs) $ \batch -> do
      vars <- forM batch $ \r -> do
        var <- newEmptyMVar
        void $ forkIO $ exchange port (render r) >>= putMVar var . (r,)
        pure var
      mapM takeMVar vars
    let bad = [ (r, resp) | (r, resp) <- results, not (wellFormed r resp) ]
    final <- exchange port "GET /state HTTP/1.1\r\n\r\n"
    let finalOk = case final of
          Just resp | Just o <- JSON.decodeStrict (bodyOf resp) -> KM.member "step" (o :: JSON.Object)
          _ -> False
    _ <- exchange port "POST /quit HTTP/1.1\r\n\r\n"
    _ <- timeout 10_000_000 (takeMVar done)
    forM_ bad $ \(r, resp) -> putStrLn $ "bad response to " <> show r <> ":\n" <> show resp
    pure $ tabulate "status" [ BC.unpack (BC.takeWhile (/= '\r') resp) | (_, Just resp) <- results ]
         $ counterexample ("bad responses: " <> show (length bad) <> ", final state ok: " <> show finalOk)
                          (null bad && finalOk)
  where
    bodyOf = BS.drop 4 . snd . BS.breakSubstring "\r\n\r\n"
    wellFormed r = \case
      Nothing -> False
      Just resp ->
        let statusLine = BC.takeWhile (/= '\r') resp
            okStatus = case BC.words statusLine of
              ("HTTP/1.1" : code : _) -> maybe False ((`elem` [200, 204, 400, 404, 500]) . fst) (BC.readInt code)
              _ -> False
            isCommand = r.raw == Nothing && r.method == "POST" && BC.takeWhile (/= '?') r.target == "/command"
                        && case r.framing of { Exact -> True; _ -> False }
            jsonOk = r.target /= "/command" || maybe False (KM.member "step") (JSON.decodeStrict (bodyOf resp) :: Maybe JSON.Object)
            isStats = r.raw == Nothing && r.method == "GET" && r.target == "/stats"
                      && case r.framing of { Exact -> True; _ -> False }
            statsOk = maybe False (KM.member "counters") (JSON.decodeStrict (bodyOf resp) :: Maybe JSON.Object)
            isProgress = r.raw == Nothing && r.method == "GET" && r.target == "/progress"
                         && case r.framing of { Exact -> True; _ -> False }
            progressOk = maybe False (KM.member "running") (JSON.decodeStrict (bodyOf resp) :: Maybe JSON.Object)
        in okStatus && (not isCommand || (" 200 " `BS.isInfixOf` statusLine && jsonOk))
                    && (not isStats || (" 200 " `BS.isInfixOf` statusLine && statsOk))
                    && (not isProgress || (" 200 " `BS.isInfixOf` statusLine && progressOk))

bucket :: Int -> String
bucket n
  | n == 0 = "0"
  | n < 10 = "1-9"
  | n < 100 = "10-99"
  | n < 1000 = "100-999"
  | otherwise = ">=1000"

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

tshow :: Show a => a -> Text
tshow = T.pack . show
