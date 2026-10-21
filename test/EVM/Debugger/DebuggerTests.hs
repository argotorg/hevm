module EVM.Debugger.DebuggerTests (tests, http, httpJSON, branchCode) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Exception (bracket)
import Control.Monad.IO.Unlift (MonadUnliftIO, liftIO)
import Control.Monad.ST (stToIO)
import Data.Aeson qualified as JSON
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BC
import Data.Text (Text)
import Data.Text qualified as T
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)

import EVM (makeVm, defaultVMOpts, initialContract)
import EVM.Dapp (emptyDapp)
import EVM.Debugger
import EVM.Debugger.Server (serveSession)
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.Stepper qualified as Stepper
import EVM.SymExec (abstractVM)
import EVM.Transaction (initTx)
import EVM.Types hiding (Env)

tests :: TestTree
tests = testGroup "Debugger"
  [ testCase "back-equals-forward" $ runEnv testEnv $ withConcrete loopCode $ \run s0 -> do
      s300 <- run "step 300" s0
      v300 <- snap s300
      sEnd <- run "continue" s300
      sBack <- run ("back " <> tshow (sessionStep sEnd - 300)) sEnd
      liftIO . assertEqual "state after going back" v300 =<< snap sBack
      s163 <- run "step 163" s0
      sBack2 <- run "back 137" s300
      v163 <- snap s163
      liftIO . assertEqual "back 137 from 300 is step 163" v163 =<< snap sBack2
      sFwd <- run "step 137" sBack2
      liftIO . assertEqual "forward again" v300 =<< snap sFwd
  , testCase "run-to-end-matches-exec" $ runEnv testEnv $ withConcrete loopCode $ \run s0 -> do
      sEnd <- run "continue" s0
      vm <- liftIO $ concreteVM loopCode
      vm' <- withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers ->
        Stepper.interpret (Fetch.oracle solvers Nothing Fetch.noRpc) vm Stepper.runFully
      liftIO $ do
        assertBool "halted" (isHalted sEnd)
        assertEqual "result" (show vm'.result) (show (sessionVM sEnd).result)
        assertEqual "gas" vm'.state.gas (sessionVM sEnd).state.gas
  , testCase "restart-after-memory-writes" $ runEnv testEnv $ withConcrete loopCode $ \run s0 -> do
      v0 <- snap s0
      s <- run "step 120" s0 >>= run "restart"
      liftIO . assertEqual "initial state restored" v0 =<< snap s
  , testCase "breakpoint" $ runEnv testEnv $ withConcrete loopCode $ \run s0 -> do
      s <- run "break op MSTORE" s0 >>= run "continue" >>= run "continue"
      v <- liftIO $ mkView s
      liftIO $ assertEqual "stopped at MSTORE" "MSTORE" v.op
      liftIO $ assertEqual "second iteration" ["0x1", "0x1", "0x1"] (take 3 v.stack)
  , testCase "symbolic-branch-choice" $ runEnv testEnv $ withSymbolic branchCode $ \run s0 -> do
      s1 <- run "continue" s0
      v1 <- liftIO $ mkView s1
      liftIO $ do
        assertEqual "branch pending" "branch" v1.status
        assertEqual "two options" (Just ["true", "false"]) ((.options) <$> v1.branch)
      -- x == 5 is implied on this side, so the second branch is decided by the solver
      sT <- run "branch true" s1 >>= run "continue"
      vT <- liftIO $ mkView sT
      liftIO $ do
        assertEqual "halted" "halted" vT.status
        assertEqual "stopped at the end" 0x16 vT.pc
        assertEqual "one choice made" 1 (length vT.choices)
      sF <- run "back" sT >>= run "restart" >>= run "continue" >>= run "branch false" >>= run "continue"
      vF <- liftIO $ mkView sF
      liftIO $ do
        assertEqual "other side" 0x0b vF.pc
        assertEqual "halted" "halted" vF.status
  , testCase "back-to-branch-offers-it-again" $ runEnv testEnv $ withSymbolic branchCode $ \run s0 -> do
      s1 <- run "continue" s0
      v1 <- liftIO $ mkView s1
      v2 <- run "branch true" s1 >>= run "step" >>= run "back" >>= liftIO . mkView
      liftIO $ do
        assertEqual "same step" v1.step v2.step
        assertEqual "branch pending again" "branch" v2.status
        assertEqual "same pc" v1.pc v2.pc
        assertEqual "choice undone" [] v2.choices
        assertEqual "same path conditions" v1.pathConditions v2.pathConditions
      v3 <- run "branch true" s1 >>= run "step" >>= run "back" >>= run "branch false" >>= run "continue" >>= liftIO . mkView
      liftIO $ assertEqual "the other side can be taken" 0x0b v3.pc
  , testCase "stats-concrete" $ runEnv testEnv $ withConcrete loopCode $ \run s0 -> do
      s1 <- run "step 300" s0
      let c1 = (sessionStats s1).counters
      liftIO $ do
        assertEqual "opcodes" 300 c1.opcodes
        assertEqual "nothing replayed" 0 c1.replayedOpcodes
        assertEqual "no queries" 0 c1.queries
        assertEqual "one command" 1 c1.commands
      -- the nearest snapshot to step 290 is at 250
      s2 <- run "back 10" s1
      let c2 = (sessionStats s2).counters
      liftIO $ do
        assertEqual "replayed from the snapshot" 40 c2.replayedOpcodes
        assertEqual "opcodes include the replay" 340 c2.opcodes
      s3 <- run "break op MSTORE" s2 >>= run "restart" >>= run "continue" >>= run "continue"
      let v3 = sessionStats s3
      liftIO $ do
        assertEqual "two breakpoint hits" 2 v3.counters.breakpointHits
        assertEqual "commands" 6 v3.counters.commands
        assertBool "snapshots kept" (v3.snapshotCount >= 1)
  , testCase "stats-symbolic" $ runEnv testEnv $ withSymbolic branchCode $ \run s0 -> do
      s1 <- run "continue" s0
      let c1 = (sessionStats s1).counters
      liftIO $ do
        assertEqual "one branch query" 1 c1.branchQueries
        assertEqual "one branch offered" 1 c1.branchesOffered
        assertEqual "none taken" 0 c1.branchesTaken
      s2 <- run "branch true" s1 >>= run "continue"
      let c2 = (sessionStats s2).counters
      liftIO $ do
        assertEqual "the second branch was queried too" 2 c2.branchQueries
        assertEqual "but decided by the solver" 1 c2.branchesOffered
        assertEqual "one taken" 1 c2.branchesTaken
        assertBool "query time" (c2.querySecs > 0)
      v <- run "stats" s2 >>= liftIO . mkView
      liftIO $ assertBool "stats command" (maybe False ("2 branch" `T.isInfixOf`) v.output)
  , testCase "http" $ runEnv testEnv $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> do
      vm <- liftIO $ concreteVM loopCode
      sess <- liftIO $ newSession emptyDapp vm
      portVar <- liftIO newEmptyMVar
      done <- liftIO newEmptyMVar
      let serve = serveSession (Fetch.oracle solvers Nothing Fetch.noRpc) 0 (putMVar portVar) sess
      env <- readConfig
      liftIO $ bracket (forkIO (runEnv (Env { config = env }) serve >> putMVar done ())) killThread $ \_ -> do
        port <- takeMVar portVar
        st <- httpJSON port "GET" "/state" ""
        assertEqual "starts at step 0" (Just (JSON.Number 0)) (KM.lookup "step" st)
        st' <- httpJSON port "POST" "/command" "{\"command\": \"step 5\"}"
        assertEqual "stepped" (Just (JSON.Number 5)) (KM.lookup "step" st')
        st'' <- httpJSON port "POST" "/command" "back 2"
        assertEqual "stepped back" (Just (JSON.Number 3)) (KM.lookup "step" st'')
        txt <- http port "GET" "/state?format=text" ""
        assertBool "text view" ("== step 3" `BS.isInfixOf` txt)
        stats <- httpJSON port "GET" "/stats" ""
        let counter k = KM.lookup "counters" stats >>= \case
              JSON.Object o -> KM.lookup k o
              _ -> Nothing
        assertEqual "stats step" (Just (JSON.Number 3)) (KM.lookup "step" stats)
        assertEqual "stats commands" (Just (JSON.Number 2)) (counter "commands")
        -- 5 forward, then 3 replayed from step 0 to go back to step 3
        assertEqual "stats opcodes" (Just (JSON.Number 8)) (counter "opcodes")
        statsTxt <- http port "GET" "/stats?format=text" ""
        assertBool "text stats" ("opcodes:" `BS.isInfixOf` statsTxt)
        _ <- http port "POST" "/quit" ""
        takeMVar done
  ]
  where
    snap s = liftIO $ do
      v <- mkView s
      pure (v.pc, v.stack, v.memory, v.gas, v.depth, v.status)

-- mstore(i, i) for i in 0..99
loopCode :: ByteString
loopCode = BS.pack [0x60, 0x00, 0x5b, 0x80, 0x80, 0x52, 0x60, 0x01, 0x01, 0x80, 0x60, 0x64, 0x11, 0x60, 0x02, 0x57, 0x00]

-- if (x == 5) { if (x == 5) stop at 0x16 else invalid } else stop at 0x0b
branchCode :: ByteString
branchCode = BS.pack
  [ 0x60, 0x00, 0x35, 0x80, 0x60, 0x05, 0x14, 0x60, 0x0c, 0x57, 0x50, 0x00
  , 0x5b, 0x60, 0x05, 0x14, 0x60, 0x15, 0x57, 0xfe, 0x00, 0x5b, 0x00 ]

concreteVM :: ByteString -> IO (VM Concrete)
concreteVM code = do
  vm <- stToIO $ makeVm $ (defaultVMOpts @Concrete)
    { contract = initialContract (RuntimeCode (ConcreteRuntimeCode code))
    , gas = 1000000
    , gaslimit = 1000000
    , blockGaslimit = 1000000
    }
  pure (initTx vm)

type Run t m = Text -> Session t -> m (Session t)

withConcrete :: (MonadUnliftIO m, ReadConfig m, TTY m) => ByteString -> (Run Concrete m -> Session Concrete -> m a) -> m a
withConcrete code k = withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> do
  vm <- liftIO $ concreteVM code
  s0 <- liftIO $ newSession emptyDapp vm
  k (runCommandText (Fetch.oracle solvers Nothing Fetch.noRpc)) s0

withSymbolic :: (MonadUnliftIO m, ReadConfig m, TTY m) => ByteString -> (Run Symbolic m -> Session Symbolic -> m a) -> m a
withSymbolic code k = withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> do
  vm <- liftIO $ stToIO $ abstractVM (AbstractBuf "txdata", []) code Nothing False
  s0 <- liftIO $ newSession emptyDapp vm
  k (runCommandText (Fetch.oracle solvers Nothing Fetch.noRpc)) s0

http :: Int -> ByteString -> ByteString -> ByteString -> IO ByteString
http port method path body = do
  addr : _ <- getAddrInfo (Just defaultHints { addrSocketType = Stream }) (Just "127.0.0.1") (Just (show port))
  bracket (openSocket addr) close $ \sock -> do
    connect sock (addrAddress addr)
    sendAll sock $ BS.concat [method, " ", path, " HTTP/1.1\r\nHost: localhost\r\nContent-Length: "
                             , BC.pack (show (BS.length body)), "\r\n\r\n", body]
    resp <- readAll sock BS.empty
    pure $ snd (BS.breakSubstring "\r\n\r\n" resp) & BS.drop 4
  where
    readAll sock acc = do
      chunk <- recv sock 4096
      if BS.null chunk then pure acc else readAll sock (acc <> chunk)
    x & f = f x

httpJSON :: Int -> ByteString -> ByteString -> ByteString -> IO JSON.Object
httpJSON port method path body = do
  r <- http port method path body
  case JSON.decodeStrict r of
    Just o -> pure o
    Nothing -> assertFailure ("not a JSON object: " <> BC.unpack r)

tshow :: Int -> Text
tshow = T.pack . show

testEnv :: Env
testEnv = Env { config = defaultConfig }
