{-|
Module      : ApiFixtures
Description : The JSON clients of the debugger are written against

The fixtures in test/debugger-api are answers of the debugger server. These
tests check that it still answers with the same fields and types; clients, such
as hevm-web-ui, test against copies of them. After changing the API on purpose,
rewrite them with HEVM_WRITE_API_FIXTURES=1.
-}
module EVM.Debugger.ApiFixtures (tests, checkFixture) where

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Exception (bracket)
import Control.Monad.IO.Unlift (liftIO)
import Control.Monad.ST (stToIO)
import Data.Aeson qualified as JSON
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KM
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.List (isSuffixOf, sort)
import Data.Vector qualified as V
import System.Environment (lookupEnv)
import Test.Tasty
import Test.Tasty.HUnit

import EVM.Dapp (emptyDapp)
import EVM.Debugger (newSession)
import EVM.Debugger.DebuggerTests (http, httpJSON, branchCode, loopCode, concreteVM)
import EVM.Debugger.Server (serveSession)
import EVM.Effects
import EVM.Fetch qualified as Fetch
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.SymExec (abstractVM)
import EVM.Types (Expr(AbstractBuf))

tests :: TestTree
tests = testGroup "api-fixtures"
  [ testCase "concrete" $ withServer False $ \port -> do
      _ <- httpJSON port "POST" "/command" "step 5"
      fixture "state-concrete" =<< get port "/state"
      fixture "stats" =<< get port "/stats"
      fixture "help" =<< get port "/help"
  , testCase "describes-the-api" $ withServer False $ \port -> do
      apiText <- http port "GET" "/api" ""
      assertBool "the API help" ("POST /command" `BS.isInfixOf` apiText)
      root <- http port "GET" "/" ""
      assertEqual "the same at /" apiText root
  , testCase "symbolic" $ withServer True $ \port -> do
      fixture "state-branch" . JSON.Object =<< httpJSON port "POST" "/command" "continue"
      _ <- httpJSON port "POST" "/command" "break op STOP"
      fixture "state-breakpoint" . JSON.Object =<< httpJSON port "POST" "/command" "branch true"
      _ <- httpJSON port "POST" "/command" "delete all"
      fixture "state-halted" . JSON.Object =<< httpJSON port "POST" "/command" "continue"
      fixture "trace" =<< get port "/trace"
  ]
  where
    get port path = JSON.Object <$> httpJSON port "GET" path ""
    fixture = checkFixture

-- | Serves a session of loopCode, or of branchCode symbolically
withServer :: Bool -> (Int -> IO ()) -> IO ()
withServer symbolic act = runEnv (Env defaultConfig) $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> liftIO $ do
  portVar <- newEmptyMVar
  done <- newEmptyMVar
  let serve :: IO ()
      serve = if symbolic
        then do
          vm <- stToIO $ abstractVM (AbstractBuf "txdata", []) branchCode Nothing False
          s <- newSession emptyDapp vm
          runEnv (Env defaultConfig) $ serveSession (Fetch.oracle solvers Nothing Fetch.noRpc) 0 (putMVar portVar) s
        else do
          vm <- concreteVM loopCode
          s <- newSession emptyDapp vm
          runEnv (Env defaultConfig) $ serveSession (Fetch.oracle solvers Nothing Fetch.noRpc) 0 (putMVar portVar) s
  bracket (forkIO (serve >> putMVar done ())) killThread $ \_ -> do
    port <- takeMVar portVar
    act port
    _ <- http port "POST" "/quit" ""
    takeMVar done

-- | Writes the fixture with HEVM_WRITE_API_FIXTURES set, else checks the server
-- still answers in its shape
checkFixture :: String -> JSON.Value -> IO ()
checkFixture name value = do
  let path = "test/debugger-api/" <> name <> ".json"
  lookupEnv "HEVM_WRITE_API_FIXTURES" >>= \case
    Just _ -> BL.writeFile path (encodePretty (withoutNoise value) <> "\n")
    Nothing -> JSON.eitherDecodeFileStrict path >>= \case
      Left err -> assertFailure $ "cannot read " <> path <> ": " <> err
      Right expected -> case difference "" expected value of
        Nothing -> pure ()
        Just diff -> assertFailure $ "the server's answer no longer matches " <> path <> ", which clients are written against: "
          <> diff <> "\nIf the change is meant, rewrite the fixtures with HEVM_WRITE_API_FIXTURES=1, and tell the clients."

-- | Durations and thread ids replaced by fixed values, so that rewriting the
-- fixtures only changes what changed
withoutNoise :: JSON.Value -> JSON.Value
withoutNoise = \case
  JSON.Object o -> JSON.Object (KM.mapWithKey fixed o)
  JSON.Array a -> JSON.Array (V.map withoutNoise a)
  v -> v
  where
    fixed k v = case (Key.toString k, v) of
      (n, JSON.Number _) | n == "secs" || "Secs" `isSuffixOf` n -> JSON.Number 0
      ("thread", JSON.String _) -> JSON.String "ThreadId 0"
      _ -> withoutNoise v

-- | Where two values differ in their fields or the types of their values
difference :: String -> JSON.Value -> JSON.Value -> Maybe String
difference path expected actual = case (expected, actual) of
  (JSON.Object e, JSON.Object a)
    | keys e /= keys a -> Just $ at <> "fields " <> show (keys e) <> " became " <> show (keys a)
    | otherwise -> firstJust [ difference (path <> "." <> Key.toString k) v av | (k, v) <- KM.toList e, Just av <- [KM.lookup k a] ]
  (JSON.Array e, JSON.Array a) -> case (V.toList e, V.toList a) of
    (x : _, y : _) -> difference (path <> "[0]") x y
    _ -> Nothing
  _ | kind expected /= kind actual -> Just $ at <> kind expected <> " became " <> kind actual
    | otherwise -> Nothing
  where
    at = (if null path then "the answer" else path) <> ": "
    keys = sort . map Key.toString . KM.keys
    firstJust = foldr (\x acc -> maybe acc Just x) Nothing
    kind = \case
      JSON.Object _ -> "an object"
      JSON.Array _ -> "an array"
      JSON.String _ -> "a string"
      JSON.Number _ -> "a number"
      JSON.Bool _ -> "a boolean"
      JSON.Null -> "null"
