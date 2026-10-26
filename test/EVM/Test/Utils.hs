{-|
Module      : EVM.Test.Utils
Description : Compiling Solidity with forge and running hevm test on it
-}
module EVM.Test.Utils where

import Data.List (isInfixOf)
import GHC.IO.Exception (IOErrorType(..))
import GHC.Natural
import Paths_hevm qualified as Paths
import System.Directory
import System.FilePath ((</>))
import System.IO.Temp
import System.Process
import System.Exit
import System.IO.Error (mkIOError)

import EVM.Dapp (dappInfo, emptyDapp, TestMethodFilter)
import EVM.Solidity
import EVM.Solvers
import EVM.UnitTest
import EVM.SymExec qualified as SymExec
import Control.Monad.IO.Unlift
import Control.Monad.Catch (MonadMask)
import EVM.Effects
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.IORef
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Stack (HasCallStack)
import Test.Tasty.HUnit (assertFailure)
import EVM.Types (internalError)
import System.Environment (lookupEnv)
import EVM.Fetch (RpcInfo, noRpc)
import EVM.Fetch qualified as Fetch

-- | A run's result, with what hevm printed during it
type WithOutput a = (a, Text)

-- | Fails with the run's output, which is otherwise not shown
assertRun :: (MonadIO m, Eq a, Show a, HasCallStack) => String -> a -> WithOutput a -> m ()
assertRun msg expected (actual, out) = liftIO $ unless (actual == expected) $
  assertFailure $ msg <> "\nexpected: " <> show expected <> "\n but got: " <> show actual
    <> "\n\nhevm output:\n" <> T.unpack out

-- Returns tuple of (No cex, No warnings)
runForgeTestCustom
  :: (MonadMask m, App m)
  => FilePath -> TestMethodFilter -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo -> m (WithOutput (Bool, Bool))
runForgeTestCustom testFile methodFilter timeout maxIter ffiAllowed rpcinfo = do
  (results, out) <- runForgeTestResultsCustom testFile methodFilter timeout maxIter ffiAllowed rpcinfo
  let (firsts, seconds) = unzip results
  pure ((and firsts, and seconds), out)

runForgeTestResultsCustom
  :: (MonadMask m, App m)
  => FilePath -> TestMethodFilter -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo -> m (WithOutput [(Bool, Bool)])
runForgeTestResultsCustom testFile methodFilter timeout maxIter ffiAllowed rpcinfo =
  first (map snd) <$> runForgeTestResultsWith id testFile methodFilter timeout maxIter ffiAllowed rpcinfo

-- | Like 'runForgeTestResultsCustom', with the options changed by the given
-- function, each result with its contract and test name
runForgeTestResultsWith
  :: (MonadMask m, App m)
  => (UnitTestOptions -> UnitTestOptions) -> FilePath -> TestMethodFilter -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo
  -> m (WithOutput [((Text, Text), (Bool, Bool))])
runForgeTestResultsWith modOpts testFile methodFilter timeout maxIter ffiAllowed rpcinfo = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    compileWithForge root testFile >>= \case
      Left e -> liftIO $ do
        putStrLn e
        internalError $ "Error compiling test file " <> show testFile <> " in directory "
          <> show root
      Right buildOut -> do
        outRef <- liftIO $ newIORef []
        let printOut t = atomicModifyIORef' outRef (\ts -> (t:ts, ()))
        results <- withSolvers Bitwuzla 3 timeout defMemLimit $ \solvers -> do
          opts <- testOpts solvers root (Just buildOut) methodFilter maxIter ffiAllowed rpcinfo printOut
          unitTestResultsNamed (modOpts opts) buildOut
        out <- liftIO $ readIORef outRef
        pure (results, T.concat (reverse out))

-- Returns tuple of (No cex, No warnings)
runForgeTest
  :: (MonadMask m, App m)
  => FilePath -> TestMethodFilter -> m (WithOutput (Bool, Bool))
runForgeTest testFile methodFilter = runForgeTestCustom testFile methodFilter Nothing Nothing False noRpc

runForgeTestResults
  :: (MonadMask m, App m)
  => FilePath -> TestMethodFilter -> m (WithOutput [(Bool, Bool)])
runForgeTestResults testFile methodFilter = runForgeTestResultsCustom testFile methodFilter Nothing Nothing False noRpc

testOpts :: forall m . App m => SolverGroup -> FilePath -> Maybe BuildOutput -> TestMethodFilter -> Maybe Integer -> Bool -> RpcInfo -> (Text -> IO ()) -> m (UnitTestOptions)
testOpts solvers root buildOutput methodFilter maxIter allowFFI rpcinfo printOut = do
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput
  sess <- Fetch.mkSessionWithoutCache
  params <- paramsFromRpc rpcinfo sess

  pure UnitTestOptions
    { solvers = solvers
    , sess = sess
    , rpcInfo = rpcinfo
    , maxIter = maxIter
    , maxConcreteIter = Just 10000
    , askSmtIters = 1
    , smtTimeout = Nothing
    , methodFilter = methodFilter
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = allowFFI
    , checkFailBit = True
    , loopHeuristic = SymExec.StackBased
    , printOut = printOut
    , invariantDepth = 2
    }

processFailedException :: String -> String -> [String] -> Int -> IO a
processFailedException fun cmd args exit_code =
      ioError (mkIOError OtherError (fun ++ ": " ++ cmd ++
                                     concatMap ((' ':) . show) args ++
                                     " (exit " ++ show exit_code ++ ")")
                                 Nothing Nothing)

callProcessCwd :: FilePath -> [String] -> FilePath -> IO ()
callProcessCwd cmd args cwd = do
    exit_code <- withCreateProcess (proc cmd args) { cwd = Just cwd, delegate_ctlc = True } $ \_ _ _ p ->
                 waitForProcess p
    case exit_code of
      ExitSuccess   -> pure ()
      ExitFailure r -> processFailedException "callProcess" cmd args r

compileWithForge :: App m => FilePath -> FilePath -> m (Either String BuildOutput)
compileWithForge root src = do
  (res, out, err) <- liftIO $ do
    createDirectory (root </> "src")
    writeFile (root </> "foundry.toml") "[profile.default]\nevm_version = \"Osaka\"\nast = true\n"
    writeFile (root </> "src" </> "unit-tests.t.sol") =<< readFile =<< Paths.getDataFileName src
    initLib (root </> "lib" </> "tokens") ("test" </> "contracts" </> "lib" </> "erc20.sol") "erc20.sol"
    initStdForgeDir (root </> "lib" </> "forge-std")
    readProcessWithExitCode "forge" ["build", "--root", root] ""
  case res of
    ExitFailure _ -> pure . Left $ "compilation failed: " <> "exit code: " <> show res <> "\n\nstdout:\n" <> out <> "\n\nstderr:\n" <> err
    ExitSuccess -> readFilteredBuildOutput root (\path -> "unit-tests.t.sol" `Data.List.isInfixOf` path) Foundry
  where
    initStdForgeDir :: FilePath -> IO ()
    initStdForgeDir tld = do
      createDirectoryIfMissing True tld
      forgeStdRepo <- liftIO $ fromMaybe (internalError "cannot find forge-std repo") <$> (lookupEnv "HEVM_FORGE_STD_REPO")
      callProcess "mkdir" ["-p", tld]
      callProcess "cp" ["-r", forgeStdRepo </> "src", tld </> "src"]
    initLib :: FilePath -> FilePath -> FilePath -> IO ()
    initLib tld srcFile dstFile = do
      createDirectoryIfMissing True (tld </> "src")
      writeFile (tld </> "src" </> dstFile) =<< readFile =<< Paths.getDataFileName srcFile
      pure ()
