{-|
Module      : WebFixtures
Description : The JSON the web frontend is written against

The fixtures in web/test/fixtures are answers of the debugger server, which the
frontend's TypeScript tests parse and render. These tests check that the
server still answers with the same fields and types. After changing the API on
purpose, rewrite the fixtures with HEVM_WRITE_WEB_FIXTURES=1 and run the
TypeScript tests (web/build.sh test).
-}
module EVM.Debugger.WebFixtures (tests, checkFixture) where

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
tests = testGroup "web-fixtures"
  [ testCase "concrete" $ withServer False $ \port -> do
      _ <- httpJSON port "POST" "/command" "step 5"
      fixture "state-concrete" =<< get port "/state"
      fixture "stats" =<< get port "/stats"
      fixture "help" =<< get port "/help"
  , testCase "serves-the-page" $ withServer False $ \port -> do
      page <- http port "GET" "/" ""
      assertBool "the page loads the bundle" ("<script type=\"module\" src=\"debugger.js\">" `BS.isInfixOf` page)
      served <- http port "GET" "/debugger.js" ""
      bundle <- BS.readFile "web/dist/debugger.js"
      assertBool "hevm embeds the current bundle: rebuild hevm after web/build.sh" (served == bundle)
      apiText <- http port "GET" "/api" ""
      assertBool "the API help" ("POST /command" `BS.isInfixOf` apiText)
  , testCase "symbolic" $ withServer True $ \port -> do
      fixture "state-branch" . JSON.Object =<< httpJSON port "POST" "/command" "continue"
      _ <- httpJSON port "POST" "/command" "break op STOP"
      fixture "state-breakpoint" . JSON.Object =<< httpJSON port "POST" "/command" "branch true"
      _ <- httpJSON port "POST" "/command" "delete all"
      fixture "state-halted" . JSON.Object =<< httpJSON port "POST" "/command" "continue"
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

-- | Writes the fixture with HEVM_WRITE_WEB_FIXTURES set, else checks the server
-- still answers in its shape
checkFixture :: String -> JSON.Value -> IO ()
checkFixture name value = do
  let path = "web/test/fixtures/" <> name <> ".json"
  lookupEnv "HEVM_WRITE_WEB_FIXTURES" >>= \case
    Just _ -> BL.writeFile path (encodePretty (withoutTimes value) <> "\n")
    Nothing -> JSON.eitherDecodeFileStrict path >>= \case
      Left err -> assertFailure $ "cannot read " <> path <> ": " <> err
      Right expected -> case difference "" expected value of
        Nothing -> pure ()
        Just diff -> assertFailure $ "the server's answer no longer matches " <> path <> ", which the web frontend is tested against: "
          <> diff <> "\nIf the change is meant, rewrite the fixtures with HEVM_WRITE_WEB_FIXTURES=1 and update web/src/api.ts."

-- | Durations zeroed, so that rewriting the fixtures only changes what changed
withoutTimes :: JSON.Value -> JSON.Value
withoutTimes = \case
  JSON.Object o -> JSON.Object (KM.mapWithKey (\k v -> if isTime k then zeroed v else withoutTimes v) o)
  JSON.Array a -> JSON.Array (V.map withoutTimes a)
  v -> v
  where
    isTime k = let n = Key.toString k in n == "secs" || "Secs" `isSuffixOf` n
    zeroed = \case
      JSON.Number _ -> JSON.Number 0
      v -> v

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
