module EVM.Test.Utils where

import Data.Text (Text)
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

import EVM.Dapp (dappInfo, emptyDapp)
import EVM.Solidity
import EVM.Solvers
import EVM.UnitTest
import EVM.SymExec qualified as SymExec
import Control.Monad.IO.Unlift
import Control.Monad.Catch (MonadMask)
import EVM.Effects
import Data.Maybe (fromMaybe)
import EVM.Types (internalError)
import System.Environment (lookupEnv)
import EVM.Fetch (RpcInfo, noRpc)
import EVM.Fetch qualified as Fetch
import EVM.SMT.Types

-- Returns tuple of (No cex, No warnings)
runForgeTestCustom
  :: (MonadMask m, App m)
  => FilePath -> Text -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo -> m (Bool, Bool)
runForgeTestCustom testFile match timeout maxIter ffiAllowed rpcinfo = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    compileWithForge root testFile >>= \case
      Left e -> liftIO $ do
        putStrLn e
        internalError $ "Error compiling test file " <> show testFile <> " in directory "
          <> show root
      Right buildOut -> do
        withSolvers Bitwuzla 3 1 timeout $ \solvers -> do
          opts <- testOpts solvers root (Just buildOut) match maxIter ffiAllowed rpcinfo
          unitTest opts buildOut

-- Returns tuple of (No cex, No warnings)
runForgeTest
  :: (MonadMask m, App m)
  => FilePath -> Text -> m (Bool, Bool)
runForgeTest testFile match = runForgeTestCustom testFile match Nothing Nothing True noRpc

testOpts :: forall m . App m => SolverGroup -> FilePath -> Maybe BuildOutput -> Text -> Maybe Integer -> Bool -> RpcInfo -> m (UnitTestOptions)
testOpts solvers root buildOutput match maxIter allowFFI rpcinfo = do
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput
  sess <- Fetch.mkSessionWithoutCache
  params <- paramsFromRpc rpcinfo sess

  pure UnitTestOptions
    { solvers = solvers
    , sess = sess
    , rpcInfo = rpcinfo
    , maxIter = maxIter
    , askSmtIters = 1
    , smtTimeout = Nothing
    , match = match
    , prefix = "prove"
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = allowFFI
    , checkFailBit = False
    , loopHeuristic = SymExec.StackBased
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
  liftIO $ createDirectory (root </> "src")
  liftIO $ writeFile (root </> "src" </> "unit-tests.t.sol") =<< readFile =<< Paths.getDataFileName src
  liftIO $ initLib (root </> "lib" </> "tokens") ("test" </> "contracts" </> "lib" </> "erc20.sol") "erc20.sol"
  liftIO $ initStdForgeDir (root </> "lib" </> "forge-std")
  (res,out,err) <- liftIO $ readProcessWithExitCode "forge" ["build", "--ast", "--root", root] ""
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
