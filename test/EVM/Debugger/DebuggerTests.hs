module EVM.Debugger.DebuggerTests (tests) where

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
