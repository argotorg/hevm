-- Main file of the hevm CLI program

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (when, forM_, unless)
import Control.Monad.State.Strict (runStateT)
import Control.Monad.ST (stToIO)
import Control.Monad.IO.Unlift
import Control.Exception (try, IOException)
import Data.ByteString (ByteString)
import Control.Concurrent.MVar (readMVar)
import qualified Data.ByteString.Lazy as BS
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Char8 as BC
import Data.DoubleWord (Word256)
import Data.List (intersperse, intercalate)
import Data.Maybe (fromMaybe, mapMaybe, fromJust, isNothing, isJust)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Version (showVersion)
import Data.Word (Word64)
import GHC.Conc (getNumProcessors)
import GitHash
import Numeric.Natural (Natural)
import Optics.Core ((&), set)
import Witch (unsafeInto)
import Options.Generic as OptionsGeneric
import Options.Applicative as Options
import Paths_hevm qualified as Paths
import System.Directory (withCurrentDirectory, getCurrentDirectory, doesDirectoryExist, makeAbsolute)
import System.FilePath ((</>))
import System.Exit (exitFailure, exitWith, ExitCode(..))
import Data.List.Split (splitOn)
import Text.Read (readMaybe)
import JSONL (jsonlBuilder, jsonLine)

import EVM (initialContract, abstractContract, makeVm)
import EVM.ABI (Sig(..))
import EVM.Dapp (dappInfo, DappInfo, emptyDapp)
import EVM.Expr qualified as Expr
import EVM.Concrete qualified as Concrete
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified as Fetch
import EVM.Format (hexByteString, strip0x, formatExpr, indent)
import EVM.Solidity
import EVM.Solvers
import EVM.Stepper qualified
import EVM.SymExec
import EVM.Transaction qualified
import EVM.Types hiding (word, Env, Symbolic)
import EVM.Types qualified
import EVM.UnitTest
import EVM.Effects
import EVM.Expr (maybeLitWordSimp, maybeLitAddrSimp)
import EVM.Tracing (interpretWithTrace, VMTraceStepResult(..))

data AssertionType = DSTest | Forge
  deriving (Eq, Show, Read)

projectTypeParser :: Parser ProjectType
projectTypeParser = option auto (long "project-type" <> showDefault <> value Foundry <> help "Is this a CombinedJSON or Foundry project")

sigParser :: Parser (Maybe Text)
sigParser = (optional $ strOption $ long "sig" <> help "Signature of types to decode/encode")

argParser :: Parser [String]
argParser = (many $ strOption $ long "arg" <> help "Value(s) to encode. Can be given multiple times, once for each argument")

createParser :: Parser Bool
createParser = switch $ long "create" <> help "Tx: creation"

rpcParser :: Parser (Maybe URL)
rpcParser = (optional $ strOption $ long "rpc" <> help "Fetch state from a remote node")

data CommonOptions = CommonOptions
  { askSmtIterations ::Integer
  , loopDetectionHeuristic ::LoopHeuristic
  , noDecompose   ::Bool
  , solver        ::Text
  , debug         ::Bool
  , calldata      ::Maybe ByteString
  , trace         ::Bool
  , verb          ::Int
  , root          ::Maybe String
  , assertionType ::AssertionType
  , smtTimeout    ::Natural
  , smtMemory     ::Natural
  , smtDebug      ::Bool
  , dumpUnsolved  ::Maybe String
  , numSolvers    ::Maybe Natural
  , maxIterations ::Integer
  , promiseNoReent::Bool
  , maxBufSize    ::Int
  , maxWidth      ::Int
  , maxDepth      ::Maybe Int
  , noSimplify    ::Bool
  , onlyDeployed  ::Bool
  , cacheDir      ::Maybe String
  , earlyAbort    ::Bool
  , abstractArith ::Bool
  }

commonOptions :: Parser CommonOptions
commonOptions = CommonOptions
  <$> option auto ( long "ask-smt-iterations" <> value 1 <>
    help "Number of times we may revisit a particular branching point before we consult the smt solver to check reachability")
  <*> option auto (long "loop-detection-heuristic" <> showDefault <> value StackBased <>
    help "Which heuristic should be used to determine if we are in a loop: StackBased or Naive")
  <*> (switch $ long "no-decompose"         <> help "Don't decompose storage slots into separate arrays")
  <*> (strOption $ long "solver"            <> value "z3" <> help "Used SMT solver: z3, cvc5, or bitwuzla")
  <*> (switch $ long "debug"                <> help "Debug printing of internal behaviour, and dump internal expressions")
  <*> (optional $ strOption $ long "calldata" <> help "Tx: calldata")
  <*> (switch $ long "trace"                <> help "Dump trace")
  <*> (option auto $ long "verb"            <> showDefault <> value 1 <> help "Append call trace: {1} failures {2} all")
  <*> (optional $ strOption $ long "root"   <> help "Path to  project root directory")
  <*> (option auto $ long "assertion-type"  <> showDefault <> value Forge <> help "Assertions as per Forge or DSTest")
  <*> (option auto $ long "smt-timeout"     <> value 300 <> help "Timeout given to SMT solver in seconds. Not available on Windows")
  <*> (option auto $ long "smt-memory"      <> value defMemLimit <> help "Maximum memory limit for SMT solver in MB. Only available on Linux")
  <*> (switch $ long "smt-debug"            <> help "Print smt queries sent to the solver")
  <*> (optional $ strOption $ long "dump-unsolved" <> help "Dump unsolved SMT queries to this (relative) path")
  <*> (optional $ option auto $ long "num-solvers" <> help "Number of solver instances to use (default: number of cpu cores)")
  <*> (option auto $ long "max-iterations"  <> showDefault <> value 5 <> help "Number of times we may revisit a particular branching point. For no bound, set -1")
  <*> (switch $ long "promise-no-reent"     <> help "Promise no reentrancy is possible into the contract(s) being examined")
  <*> (option auto $ long "max-buf-size"    <> value 64 <> help "Maximum size of buffers such as calldata and returndata in exponents of 2 (default: 64, i.e. 2^64 bytes)")
  <*> (option auto $ long "max-width"      <> showDefault <> value 100 <> help "Max number of concrete values to explore when encountering a symbolic value. This is a form of branch width limitation per symbolic value")
  <*> (optional $ option auto $ long "max-depth" <> help "Limit maximum depth of branching during exploration (default: unlimited)")
  <*> (switch $ long "no-simplify" <> help "Don't perform simplification of expressions")
  <*> (switch $ long "only-deployed" <> help "When trying to resolve unknown addresses, only use addresses of deployed contracts")
  <*> (optional $ strOption $ long "cache-dir" <> help "Directory to save and load RPC cache")
  <*> (switch $  long "early-abort" <> help "Stop exploration immediately upon finding the first counterexample")
  <*> (switch $  long "abstract-arith" <> help "Use uninterpreted functions for div/mod in SMT queries (Halmos-style two-phase solving)")

data CommonExecOptions = CommonExecOptions
  { address       ::Maybe Addr
  , caller        ::Maybe Addr
  , origin        ::Maybe Addr
  , coinbase      ::Maybe Addr
  , value         ::Maybe W256
  , nonce         ::Maybe Word64
  , gas           ::Maybe Word64
  , number        ::Maybe W256
  , timestamp     ::Maybe W256
  , basefee       ::Maybe W256
  , priorityFee   ::Maybe W256
  , gaslimit      ::Maybe Word64
  , gasprice      ::Maybe W256
  , maxcodesize   ::Maybe W256
  , prevRandao    ::Maybe W256
  , chainid       ::Maybe W256
  , rpc           ::Maybe URL
  , block         ::Maybe W256
}

commonExecOptions :: Parser CommonExecOptions
commonExecOptions = CommonExecOptions
  <$> (optional $ option auto $ long "address"       <> help "Tx: address")
  <*> (optional $ option auto $ long "caller"        <> help "Tx: caller")
  <*> (optional $ option auto $ long "origin"        <> help "Tx: origin")
  <*> (optional $ option auto $ long "coinbase"      <> help "Block: coinbase")
  <*> (optional $ option auto $ long "value"         <> help "Tx: Eth amount")
  <*> (optional $ option auto $ long "nonce"         <> help "Nonce of origin")
  <*> (optional $ option auto $ long "gas"           <> help "Tx: gas amount")
  <*> (optional $ option auto $ long "number"        <> help "Block: number")
  <*> (optional $ option auto $ long "timestamp"     <> help "Block: timestamp")
  <*> (optional $ option auto $ long "basefee"       <> help "Block: base fee")
  <*> (optional $ option auto $ long "priority-fee"  <> help "Tx: priority fee")
  <*> (optional $ option auto $ long "gaslimit"      <> help "Tx: gas limit")
  <*> (optional $ option auto $ long "gasprice"      <> help "Tx: gas price")
  <*> (optional $ option auto $ long "maxcodesize"   <> help "Block: max code size")
  <*> (optional $ option auto $ long "prev-randao"   <> help "Block: prevRandao")
  <*> (optional $ option auto $ long "chainid"       <> help "Env: chainId")
  <*> rpcParser
  <*> (optional $ option auto $ long "block"         <> help "Block state is be fetched from")

data CommonFileOptions = CommonFileOptions
 { code        ::Maybe ByteString
 , codeFile    ::Maybe String
 }

commonFileOptions :: Parser CommonFileOptions
commonFileOptions = CommonFileOptions
  <$> (optional $ strOption $ long "code" <> help "Program bytecode")
  <*> (optional $ strOption $ long "code-file" <> help "Program bytecode in a file")

data TestOptions = TestOptions
  { projectType   ::ProjectType
  , rpc           ::Maybe URL
  , number        ::Maybe W256
  , coverage      ::Bool
  , match         ::Maybe String
  , prefix        ::String
  , ffi           ::Bool
  }

testOptions :: Parser TestOptions
testOptions = TestOptions
  <$> projectTypeParser
  <*> rpcParser
  <*> (optional $ option auto $ long "number" <> help "Block: number")
  <*> (switch $ long "coverage" <> help "Coverage analysis")
  <*> (optional $ strOption $ long "match" <> help "Test case filter - only run methods matching regex")
  <*> (strOption $ long "prefix"  <> showDefault <> value "prove" <> help "Prefix for test cases to prove")
  <*> (switch $ long "ffi" <> help "Allow the usage of the hevm.ffi() cheatcode (WARNING: this allows test authors to execute arbitrary code on your machine)")

data EqOptions = EqOptions
  { codeA         ::Maybe ByteString
  , codeB         ::Maybe ByteString
  , codeAFile     ::Maybe String
  , codeBFile     ::Maybe String
  , sig           ::Maybe Text
  , arg           ::[String]
  , create        ::Bool
  }

eqOptions :: Parser EqOptions
eqOptions = EqOptions
  <$> (optional $ strOption $ long "code-a"      <> help "Bytecode of the first program")
  <*> (optional $ strOption $ long "code-b"      <> help "Bytecode of the second program")
  <*> (optional $ strOption $ long "code-a-file" <> help "First program's bytecode in a file")
  <*> (optional $ strOption $ long "code-b-file" <> help "Second program's bytecode in a file")
  <*> sigParser
  <*> argParser
  <*> createParser

data SymbolicOptions = SymbolicOptions
  { projectType       ::ProjectType
  , initialStorage    ::Maybe InitialStorage
  , getModels         ::Bool
  , showTree          ::Bool
  , showReachableTree ::Bool
  , assertions        ::Maybe String
  , sig               ::Maybe Text
  , arg               ::[String]
  , create            ::Bool
  }

symbolicOptions :: Parser SymbolicOptions
symbolicOptions = SymbolicOptions
  <$> projectTypeParser
  <*> (optional $ option auto $ long "initial-storage" <> help "Starting state for storage: Empty, Abstract (default Abstract)")
  <*> (switch $ long "get-models" <> help "Print example testcase for each execution path")
  <*> (switch $ long "show-tree" <> help "Print branches explored in tree view")
  <*> (switch $ long "show-reachable-tree" <> showDefault <> help "Print only reachable branches explored in tree view")
  <*> (optional $ strOption $ long "assertions" <> help "Comma separated list of solc panic codes to check for (default: user defined assertion violations only)")
  <*> sigParser
  <*> argParser
  <*> createParser

data ExecOptions = ExecOptions
  { projectType :: ProjectType
  , create :: Bool
  , jsonTrace :: Bool
  }
execOptions :: Parser ExecOptions
execOptions = ExecOptions
  <$> projectTypeParser
  <*> createParser
  <*> (switch $ long "json-trace" <> help "Output a geth compatible json trace")

-- Combined options data type
data Command
  = Symbolic   CommonFileOptions SymbolicOptions CommonExecOptions CommonOptions
  | Equal      EqOptions CommonOptions
  | Test       TestOptions  CommonOptions
  | Exec       CommonFileOptions ExecOptions CommonExecOptions CommonOptions
  | Version

-- Parser for the subcommands
commandParser :: Parser Command
commandParser = subparser
  ( command "test"
      (info (Test <$> testOptions <*> commonOptions <**> helper)
        (progDesc "Prove Foundry unit tests prefixed with `prove` by default"
        <> footer "For more help: https://hevm.dev/std-test-tutorial.html" ))
  <> command "equivalence"
      (info (Equal <$> eqOptions <*> commonOptions <**> helper)
        (progDesc "Prove equivalence between two programs"
        <> footer "For more help: https://hevm.dev/equivalence-checking-tutorial.html" ))
  <> command "symbolic"
      (info (Symbolic <$> commonFileOptions <*> symbolicOptions <*> commonExecOptions <*> commonOptions <**> helper)
        (progDesc "Symbolically explore an abstract program"
        <> footer "For more help, see: https://hevm.dev/symbolic-execution-tutorial.html" ))
  <> command "exec"
      (info (Exec <$> commonFileOptions <*> execOptions <*> commonExecOptions <*> commonOptions <**> helper)
        (progDesc "Concretely execute a given program"
        <> footer "For more help, see https://hevm.dev/exec.html" ))
  <> command "version"
      (info (pure Version)
        (progDesc "Show the version of the tool"))
  )

type URL = Text

deriving instance OptionsGeneric.ParseField Word256
deriving instance OptionsGeneric.ParseField [Word256]

data InitialStorage
  = Empty
  | Abstract
  deriving (Show, Read, OptionsGeneric.ParseField)

getFullVersion :: [Char]
getFullVersion = showVersion Paths.version <> " [" <> gitVersion <> "]"
  where
    gitInfo = $$tGitInfoCwdTry
    gitVersion = case gitInfo of
      Right val -> "git rev " <> giBranch val <>  "@" <> giHash val
      Left _ -> "no git revision present"

main :: IO ()
main = do
  cmd <- execParser $ info (commandParser <**> helper)
    ( Options.fullDesc
    <> progDesc "hevm, a symbolic and concrete EVM bytecode execution framework"
    <> footer "See https://hevm.dev for more information"
    )

  case cmd of
    Symbolic cFileOpts symbOpts cExecOpts cOpts -> do
      env <- makeEnv cOpts
      root <- getRoot cOpts
      withCurrentDirectory root $ runEnv env $ symbCheck cFileOpts symbOpts cExecOpts cOpts
    Equal eqOpts cOpts -> do
      env <- makeEnv cOpts
      runEnv env $ equivalence eqOpts cOpts
    Test testOpts cOpts -> do
      env <- makeEnv cOpts
      root <- getRoot cOpts
      solver <- getSolver cOpts.solver
      cores <- liftIO $ unsafeInto <$> getNumProcessors
      let solverCount = fromMaybe cores cOpts.numSolvers
      runEnv env $ withSolvers solver solverCount (Just cOpts.smtTimeout) cOpts.smtMemory $ \solvers -> do
        buildOut <- readBuildOutput root testOpts.projectType
        case buildOut of
          Left e -> liftIO $ do
            putStrLn $ "Error: " <> e
            exitFailure
          Right out -> do
            -- TODO: which functions here actually require a BuildOutput, and which can take it as a Maybe?
            unitTestOpts <- unitTestOptions testOpts cOpts solvers (Just out)
            res <- unitTest unitTestOpts out
            liftIO $ forM_ ((,) <$> cOpts.cacheDir <*> testOpts.number) $ \(dir, fetchedBlock) -> do
              cache <- readMVar (unitTestOpts.sess.sharedCache)
              Fetch.saveCache dir fetchedBlock cache
            liftIO $ unless (uncurry (&&) res) exitFailure
    Exec cFileOpts execOpts cExecOpts cOpts-> do
      env <- makeEnv cOpts
      runEnv env $ launchExec cFileOpts execOpts cExecOpts cOpts
    Version {} ->putStrLn getFullVersion
  where
    makeEnv :: CommonOptions -> IO Env
    makeEnv cOpts = do
      when (cOpts.maxBufSize > 64) $ do
        putStrLn "Error: maxBufSize must be less than or equal to 64. That limits buffers to a size of 2^64, which is more than enough for practical purposes"
        exitFailure
      when (cOpts.maxBufSize < 0) $ do
        putStrLn "Error: maxBufSize must be at least 0. Negative values do not make sense. A value of zero means at most 1 byte long buffers"
        exitFailure
      pure Env { config = defaultConfig
        { dumpQueries = cOpts.smtDebug
        , dumpUnsolved = cOpts.dumpUnsolved
        , debug = cOpts.debug
        , dumpEndStates = cOpts.debug
        , dumpExprs = cOpts.debug
        , dumpTrace = cOpts.trace
        , decomposeStorage = Prelude.not cOpts.noDecompose
        , promiseNoReent = cOpts.promiseNoReent
        , maxBufSize = cOpts.maxBufSize
        , maxWidth = cOpts.maxWidth
        , maxDepth = cOpts.maxDepth
        , verb = cOpts.verb
        , simp = Prelude.not cOpts.noSimplify
        , onlyDeployed = cOpts.onlyDeployed
        , earlyAbort = cOpts.earlyAbort
        , abstractArith = cOpts.abstractArith
        } }


getCode :: App m => Maybe String -> Maybe ByteString -> m (Maybe ByteString)
getCode fname code = liftIO $ do
  when (isJust fname && isJust code) $ do
    putStrLn "Error: Cannot provide both a file and code"
    exitFailure
  case fname of
    Nothing -> pure $ fmap strip code
    Just f -> do
      result <- try (BS.readFile f) :: IO (Either IOException BS.ByteString)
      case result of
        Left e -> do
          putStrLn $ "Error reading file: " <> show e
          exitFailure
        Right content -> do
          pure $ Just $ strip (BS.toStrict content)
  where
    strip = BC.filter (\c -> c /= ' ' && c /= '\n' && c /= '\r' && c /= '\t' && c /= '"')

equivalence :: App m => EqOptions -> CommonOptions -> m ()
equivalence eqOpts cOpts = do
  bytecodeA' <- getCode eqOpts.codeAFile eqOpts.codeA
  bytecodeB' <- getCode eqOpts.codeBFile eqOpts.codeB
  let bytecodeA = decipher bytecodeA'
  let bytecodeB = decipher bytecodeB'
  when (isNothing bytecodeA) $ liftIO $ do
    putStrLn "Error: invalid or no bytecode for program A. Provide a valid one with --code-a or --code-a-file"
    exitFailure
  when (isNothing bytecodeB) $ liftIO $ do
    putStrLn "Error: invalid or no bytecode for program B. Provide a valid one with --code-b or --code-b-file"
    exitFailure
  let veriOpts = (defaultVeriOpts :: VeriOpts) { iterConf = IterConfig {
                            maxIter = parseMaxIters cOpts.maxIterations
                            , askSmtIters = cOpts.askSmtIterations
                            , loopHeuristic = cOpts.loopDetectionHeuristic
                            }
                          }
  calldata <- buildCalldata cOpts eqOpts.sig eqOpts.arg
  solver <- liftIO $ getSolver cOpts.solver
  cores <- liftIO $ unsafeInto <$> getNumProcessors
  let solverCount = fromMaybe cores cOpts.numSolvers
  withSolvers solver solverCount (Just cOpts.smtTimeout) cOpts.smtMemory $ \s -> do
    sess <- Fetch.mkSession cOpts.cacheDir Nothing
    eq <- equivalenceCheck s (Just sess) (fromJust bytecodeA) (fromJust bytecodeB) veriOpts calldata eqOpts.create
    let anyIssues =  not (null eq.partials) || any (isUnknown . fst) eq.res  || any (isError . fst) eq.res
    liftIO $ case (any (isCex . fst) eq.res, anyIssues) of
      (False, False) -> putStrLn "   \x1b[32m[PASS]\x1b[0m Contracts behave equivalently"
      (True, _)      -> putStrLn "   \x1b[31m[FAIL]\x1b[0m Contracts do not behave equivalently"
      (_, True)      -> putStrLn "   \x1b[31m[FAIL]\x1b[0m Contracts may not behave equivalently"
    liftIO $ printWarnings Nothing eq.partials (map fst eq.res) "the contracts under test"
    case any (isCex . fst) eq.res of
      False -> liftIO $ do
        when anyIssues exitFailure
        putStrLn "No discrepancies found"
      True -> liftIO $ do
        let cexes = mapMaybe getCexP eq.res
        T.putStrLn . T.unlines $
          [ "Not equivalent. The following inputs result in differing behaviours:"
          , "" , "-----", ""
          ] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap formatCexes cexes)
        exitFailure
  where
    decipher = maybe Nothing (hexByteString . strip0x)
    getCexP :: (ProofResult a b, String) -> Maybe (a, String)
    getCexP (Cex c, reason) = Just (c, reason)
    getCexP _ = Nothing
    formatCexes (cex, reason) = formatCex (AbstractBuf "txdata") Nothing cex <> "Difference: " <> T.pack reason

getSolver :: Text -> IO Solver
getSolver s = case T.unpack s of
  "z3" -> pure Z3
  "cvc5" -> pure CVC5
  "bitwuzla" -> pure Bitwuzla
  "empty" -> pure EmptySolver
  input -> do
    putStrLn $ "unrecognised solver: " <> input
    exitFailure

getSrcInfo :: App m => ExecOptions -> CommonOptions -> m DappInfo
getSrcInfo execOpts cOpts = do
  root <- liftIO $ getRoot cOpts
  conf <- readConfig
  liftIO $ withCurrentDirectory root $ do
    outExists <- doesDirectoryExist (root System.FilePath.</> "out")
    if outExists
    then do
      buildOutput <- runEnv Env {config = conf} $ readBuildOutput root execOpts.projectType
      case buildOutput of
        Left _ -> pure emptyDapp
        Right o -> pure $ dappInfo root o
    else pure emptyDapp

getRoot :: CommonOptions -> IO FilePath
getRoot cmd = maybe getCurrentDirectory makeAbsolute cmd.root

parseMaxIters :: Integer -> Maybe Integer
parseMaxIters num = if num < 0 then Nothing else Just num

-- | Builds a buffer representing calldata based on the given cli arguments
buildCalldata :: App m => CommonOptions -> Maybe Text -> [String] -> m (Expr Buf, [Prop])
buildCalldata cOpts sig arg = case (cOpts.calldata, sig) of
  -- fully abstract calldata
  (Nothing, Nothing) -> mkCalldata Nothing []
  -- fully concrete calldata
  (Just c, Nothing) -> do
    let val = hexByteString $ strip0x c
    if (isNothing val) then liftIO $ do
      putStrLn $ "Error, invalid calldata: " <>  show c
      exitFailure
    else pure (ConcreteBuf (fromJust val), [])
  -- calldata according to given abi with possible specializations from the `arg` list
  (Nothing, Just sig') -> do
    method' <- liftIO $ functionAbi sig'
    mkCalldata (Just (Sig method'.methodSignature (snd <$> method'.inputs))) arg
  -- both args provided
  (_, _) -> liftIO $ do
    putStrLn "incompatible options provided: --calldata and --sig"
    exitFailure


-- If function signatures are known, they should always be given for best results.
symbCheck :: App m => CommonFileOptions -> SymbolicOptions -> CommonExecOptions -> CommonOptions -> m ()
symbCheck cFileOpts sOpts cExecOpts cOpts = do
  let block' = maybe Fetch.Latest Fetch.BlockNumber cExecOpts.block
      blockUrlInfo = (,) block' <$> cExecOpts.rpc
  sess <- Fetch.mkSession cOpts.cacheDir cExecOpts.block
  calldata <- buildCalldata cOpts sOpts.sig sOpts.arg
  preState <- symvmFromCommand cExecOpts sOpts cFileOpts sess calldata
  errCodes <- case sOpts.assertions of
    Nothing -> pure defaultPanicCodes
    Just s -> case (mapM readMaybe $ splitOn "," s) of
      Nothing -> liftIO $ do
        putStrLn $ "Error: invalid assertion codes: " <> s
        exitFailure
      Just codes -> pure codes
  when (cOpts.verb > 0) $ liftIO $ putStrLn $ "Using assertion code(s): " <> intercalate "," (map show errCodes)
  cores <- liftIO $ unsafeInto <$> getNumProcessors
  let solverCount = fromMaybe cores cOpts.numSolvers
  solver <- liftIO $ getSolver cOpts.solver
  withSolvers solver solverCount (Just cOpts.smtTimeout) cOpts.smtMemory $ \solvers -> do
    let veriOpts = VeriOpts { iterConf = IterConfig {
                              maxIter = parseMaxIters cOpts.maxIterations
                              , askSmtIters = cOpts.askSmtIterations
                              , loopHeuristic = cOpts.loopDetectionHeuristic
                              }
                            , rpcInfo = Fetch.RpcInfo blockUrlInfo
                            }
    let fetcher = Fetch.oracle solvers (Just sess) veriOpts.rpcInfo
    (expr, res) <- verify solvers fetcher veriOpts preState (checkAssertions errCodes) Nothing
    liftIO $ forM_ ((,) <$> cOpts.cacheDir <*> cExecOpts.block) $ \(dir, block) -> do
      cache <- readMVar sess.sharedCache
      Fetch.saveCache dir block cache
    case res of
      [] -> do
        liftIO $ putStrLn "\nQED: No reachable property violations discovered\n"
        showExtras solvers sOpts calldata expr
      _ -> do
        let cexs = snd <$> mapMaybe getCex res
            counterexamples
              | null cexs = []
              | otherwise =
                 [ ""
                 , ("Discovered the following " <> (T.pack $ show (length cexs)) <> " counterexample(s):")
                 , ""
                 ] <> fmap (formatCex (fst calldata) Nothing) cexs
        liftIO $ T.putStrLn $ T.unlines counterexamples
        liftIO $ printWarnings Nothing expr res "symbolically"
        showExtras solvers sOpts calldata expr
        liftIO exitFailure

showExtras :: App m => SolverGroup ->SymbolicOptions -> (Expr Buf, [Prop]) -> [Expr End] -> m ()
showExtras solvers sOpts calldata expr = do
  when sOpts.showTree $ liftIO $ do
    putStrLn "=== Leafs ===\n"
    printLeafs $ map (formatExpr . Expr.simplify) expr
    putStrLn ""
  when sOpts.showReachableTree $ do
    reached <- reachable solvers expr
    liftIO $ do
      putStrLn "=== Potentially Reachable Leafs ===\n"
      printLeafs $ map (formatExpr . Expr.simplify) reached
      putStrLn ""
  when sOpts.getModels $ do
    liftIO $ putStrLn $ "=== Models for " <> show (length expr) <> " branches ==="
    ms <- produceModels solvers expr
    liftIO $ forM_ ms (showModel (fst calldata))
  where
    printLeafs leafs =
      T.putStrLn $ indent 2 $ T.unlines $ zipWith (\i r -> "Leaf " <> T.pack (show (i :: Integer)) <> ":\n" <> r) [0..] leafs

isTestOrLib :: Text -> Bool
isTestOrLib file = T.isSuffixOf ".t.sol" file || areAnyPrefixOf ["src/test/", "src/tests/", "lib/"] file

areAnyPrefixOf :: [Text] -> Text -> Bool
areAnyPrefixOf prefixes t = any (flip T.isPrefixOf t) prefixes

launchExec :: App m => CommonFileOptions -> ExecOptions -> CommonExecOptions -> CommonOptions -> m ()
launchExec cFileOpts execOpts cExecOpts cOpts = do
  dapp <- getSrcInfo execOpts cOpts
  sess <- Fetch.mkSession cOpts.cacheDir cExecOpts.block
  vm <- vmFromCommand cOpts cExecOpts cFileOpts execOpts sess
  let
    block = maybe Fetch.Latest Fetch.BlockNumber cExecOpts.block
    blockUrlInfo = (,) block <$> cExecOpts.rpc
    rpcDat :: Fetch.RpcInfo = Fetch.RpcInfo blockUrlInfo

  -- TODO: we shouldn't need solvers to execute this code
  withSolvers Z3 0 Nothing cOpts.smtMemory $ \solvers -> do
    let fetcher = Fetch.oracle solvers (Just sess) rpcDat
    vm' <- if execOpts.jsonTrace
           then do
             (vm', (_, traces)) <- runStateT (interpretWithTrace fetcher EVM.Stepper.runFully) (vm, [])
             liftIO $ do
               let ret = case vm'.result of
                           Just (VMSuccess (ConcreteBuf r)) -> ByteStringS r
                           Just (VMFailure (Revert (ConcreteBuf r))) -> ByteStringS r
                           _ -> ByteStringS ""
               let res = VMTraceStepResult ret (vm.state.gas - vm'.state.gas)
               let jsonl = toLazyByteString $ jsonlBuilder traces <> jsonLine res
               let file = "hevm-trace.jsonl"
               BS.writeFile file jsonl
               putStrLn $ "Wrote json trace to " <> show file
             pure vm'
           else EVM.Stepper.interpret fetcher vm EVM.Stepper.runFully
    writeTraceDapp dapp vm'
    liftIO $ forM_ ((,) <$> cOpts.cacheDir <*> cExecOpts.block) $ \(dir, fetchedBlock) -> do
      cache <- readMVar sess.sharedCache
      Fetch.saveCache dir fetchedBlock cache
    case vm'.result of
      Just (VMFailure (Revert msg)) -> liftIO $ do
        let res = case msg of
                    ConcreteBuf bs -> bs
                    _ -> "<symbolic>"
        putStrLn $ "Revert: " <> (show $ ByteStringS res)
        exitWith (ExitFailure 2)
      Just (VMFailure err) -> liftIO $ do
        putStrLn $ "Error: " <> show err
        exitWith (ExitFailure 2)
      Just (VMSuccess buf) -> liftIO $ do
        let msg = case buf of
              ConcreteBuf msg' -> msg'
              _ -> "<symbolic>"
        print $ "Return: " <> (show $ ByteStringS msg)
      _ ->
        internalError "no EVM result"

-- | Creates a (concrete) VM from command line options
vmFromCommand :: App m => CommonOptions -> CommonExecOptions -> CommonFileOptions -> ExecOptions -> Fetch.Session -> m (VM Concrete)
vmFromCommand cOpts cExecOpts cFileOpts execOpts sess = do
  conf <- readConfig
  (miner,ts,baseFee,blockNum,prevRan) <- case cExecOpts.rpc of
    Nothing -> pure (LitAddr 0,Lit 0,0,Lit 0,0)
    Just url -> liftIO $ Fetch.fetchBlockWithSession conf sess block url >>= \case
      Nothing -> do
        putStrLn $ "Error, Could not fetch block" <> show block <> " from URL: " <> show url
        exitFailure
      Just Block{..} -> pure ( coinbase
                             , timestamp
                             , baseFee
                             , number
                             , prevRandao
                             )

  codeWrapped <- getCode cFileOpts.codeFile cFileOpts.code
  contract <- case (cExecOpts.rpc, cExecOpts.address, codeWrapped) of
    (Just url, Just addr', Just c) -> liftIO $ do
      let code = hexByteString $ strip0x c
      if isNothing code then do
        putStrLn $ "Error, invalid code: " <> show c
        exitFailure
      else
        Fetch.fetchContractWithSession conf sess block url addr' >>= \case
          Fetch.FetchFailure _ -> do
            putStrLn $ "Error: contract not found: " <> show address
            exitFailure
          Fetch.FetchError e -> do
            putStrLn $ "Error: RPC failure: " <> show e
            exitFailure
          Fetch.FetchSuccess rpcContract _ ->
            -- if both code and url is given,
            -- fetch the contract and overwrite the code
              pure $ initialContract (mkCode $ fromJust code)
                & set #balance  (Lit rpcContract.balance)
                & set #nonce    (Just rpcContract.nonce)

    (Just url, Just addr', Nothing) ->
      liftIO $ Fetch.fetchContractWithSession conf sess block url addr' >>= \case
        Fetch.FetchFailure _ -> do
          putStrLn $ "Error, contract not found: " <> show address
          exitFailure
        Fetch.FetchError e -> do
          putStrLn $ "Error: RPC failure: " <> show e
          exitFailure
        Fetch.FetchSuccess rpcContract _ -> pure $ Fetch.makeContractFromRPC rpcContract

    (_, _, Just c)  -> do
      let code = hexByteString $ strip0x c
      if (isNothing code) then liftIO $ do
        putStrLn $ "Error, invalid code: " <> show c
        exitFailure
      else pure $ initialContract (mkCode $ fromJust code)

    (_, _, Nothing) -> liftIO $ do
      putStrLn "Error, must provide at least (rpc + address) or code"
      exitFailure

  let ts' = case maybeLitWordSimp ts of
        Just t -> t
        Nothing -> internalError "unexpected symbolic timestamp when executing vm test"

  if (isNothing bsCallData) then liftIO $ do
    putStrLn $ "Error, invalid calldata: " <> show calldata
    exitFailure
  else liftIO $ do
    vm <- stToIO $ vm0 baseFee miner ts' blockNum prevRan contract
    pure $ EVM.Transaction.initTx vm
  where
        bsCallData = bytes (.calldata) (pure "")
        block   = maybe Fetch.Latest Fetch.BlockNumber cExecOpts.block
        val     = word (.value) 0
        caller  = addr (.caller) (LitAddr 0)
        origin  = addr (.origin) (LitAddr 0)
        calldata = ConcreteBuf $ fromJust bsCallData
        decipher = hexByteString . strip0x
        mkCode bs = if execOpts.create
                    then InitCode bs mempty
                    else RuntimeCode (ConcreteRuntimeCode bs)
        address = if execOpts.create
                  then addr (.address) (Concrete.createAddress (fromJust $ maybeLitAddrSimp origin) (W64 $ word64 (.nonce) 0))
                  else addr (.address) (LitAddr 0xacab)

        vm0 baseFee miner ts blockNum prevRan c = makeVm $ VMOpts
          { contract       = c
          , otherContracts = []
          , calldata       = (calldata, [])
          , value          = Lit val
          , address        = address
          , caller         = caller
          , origin         = origin
          , gas            = word64 (.gas) 0xffffffffffffffff
          , baseFee        = baseFee
          , priorityFee    = word (.priorityFee) 0
          , gaslimit       = word64 (.gaslimit) 0xffffffffffffffff
          , coinbase       = addr (.coinbase) miner
          , number         = maybe blockNum Lit cExecOpts.number
          , timestamp      = Lit $ word (.timestamp) ts
          , blockGaslimit  = word64 (.gaslimit) 0xffffffffffffffff
          , gasprice       = word (.gasprice) 0
          , maxCodeSize    = word (.maxcodesize) 0xffffffff
          , prevRandao     = word (.prevRandao) prevRan
          , schedule       = feeSchedule
          , chainId        = word (.chainid) 1
          , create         = (.create) execOpts
          , baseState      = EmptyBase
          , txAccessList   = mempty -- TODO: support me soon
          , allowFFI       = False
          , freshAddresses = 0
          , beaconRoot     = 0
          }
        word f def = fromMaybe def (f cExecOpts)
        word64 f def = fromMaybe def (f cExecOpts)
        addr f def = maybe def LitAddr (f cExecOpts)
        bytes f def = maybe def decipher (f cOpts)

symvmFromCommand :: App m =>
  CommonExecOptions -> SymbolicOptions -> CommonFileOptions -> Fetch.Session ->
  (Expr Buf, [Prop]) -> m (VM EVM.Types.Symbolic)
symvmFromCommand cExecOpts sOpts cFileOpts sess calldata = do
  conf <- readConfig
  (miner,blockNum,baseFee,prevRan) <- case cExecOpts.rpc of
    Nothing -> pure (SymAddr "miner",Lit 0,0,0)
    Just url -> liftIO $ Fetch.fetchBlockWithSession conf sess block url >>= \case
      Nothing -> do
        putStrLn $ "Error, Could not fetch block" <> show block <> " from URL: " <> show url
        exitFailure
      Just Block{..} -> pure ( coinbase
                             , number
                             , baseFee
                             , prevRandao
                             )

  let
    caller = maybe (SymAddr "caller") LitAddr cExecOpts.caller
    ts = maybe Timestamp Lit cExecOpts.timestamp
    callvalue = maybe TxValue Lit cExecOpts.value
    storageBase = maybe AbstractBase parseInitialStorage (sOpts.initialStorage)

  codeWrapped <- getCode cFileOpts.codeFile cFileOpts.code
  contract <- case (cExecOpts.rpc, cExecOpts.address, codeWrapped) of
    (Just url, Just addr', _) ->
      liftIO $ Fetch.fetchContractWithSession conf sess block url addr' >>= \case
        Fetch.FetchFailure _ -> do
          putStrLn "Error, contract not found."
          exitFailure
        Fetch.FetchError e -> do
          putStrLn $ "Error: RPC failure: " <> show e
          exitFailure
        Fetch.FetchSuccess rpcContract' _ -> case codeWrapped of
              Nothing -> pure $ Fetch.makeContractFromRPC rpcContract'
              -- if both code and url is given,
              -- fetch the contract and overwrite the code
              Just c -> do
                let c' = decipher c
                if isNothing c' then do
                  putStrLn $ "Error, invalid code: " <> show c
                  exitFailure
                else pure $ do
                  initialContract (mkCode $ fromJust c')
                        & set #balance (Lit rpcContract'.balance)
                        & set #nonce (Just rpcContract'.nonce)

    (_, _, Just c) -> liftIO $ do
      let c' = decipher c
      if isNothing c' then do
        putStrLn $ "Error, invalid code: " <> show c
        exitFailure
      else case storageBase of
        EmptyBase -> pure (initialContract . mkCode $ fromJust c')
        AbstractBase -> pure ((`abstractContract` address) . mkCode $ fromJust c')

    (_, _, Nothing) -> liftIO $ do
      putStrLn "Error, must provide at least (rpc + address) or code"
      exitFailure

  vm <- liftIO $ stToIO $ vm0 baseFee miner ts blockNum prevRan calldata callvalue caller contract storageBase
  pure $ EVM.Transaction.initTx vm

  where
    decipher = hexByteString . strip0x
    block = maybe Fetch.Latest Fetch.BlockNumber cExecOpts.block
    origin = eaddr (.origin) (SymAddr "origin")
    mkCode bs = if sOpts.create
                   then InitCode bs mempty
                   else RuntimeCode (ConcreteRuntimeCode bs)
    address = eaddr (.address) (SymAddr "entrypoint")
    originAddr = eaddr (.origin) (SymAddr "origin")
    originContr = abstractContract (RuntimeCode (SymbolicRuntimeCode mempty)) originAddr
    vm0 baseFee miner ts blockNum prevRan cd callvalue caller c baseState = makeVm $ VMOpts
      { contract       = c
      , otherContracts = [(originAddr, originContr)]
      , calldata       = cd
      , value          = callvalue
      , address        = address
      , caller         = caller
      , origin         = origin
      , gas            = ()
      , gaslimit       = word64 (.gaslimit) 0xffffffffffffffff
      , baseFee        = baseFee
      , priorityFee    = word (.priorityFee) 0
      , coinbase       = eaddr (.coinbase) miner
      , number         = maybe blockNum Lit cExecOpts.number
      , timestamp      = ts
      , blockGaslimit  = word64 (.gaslimit) 0xffffffffffffffff
      , gasprice       = word (.gasprice) 0
      , maxCodeSize    = word (.maxcodesize) 0xffffffff
      , prevRandao     = word (.prevRandao) prevRan
      , schedule       = feeSchedule
      , chainId        = word (.chainid) 1
      , create         = (.create) sOpts
      , baseState      = baseState
      , txAccessList   = mempty
      , allowFFI       = False
      , freshAddresses = 0
      , beaconRoot     = 0
      }
    word f def = fromMaybe def (f cExecOpts)
    word64 f def = fromMaybe def (f cExecOpts)
    eaddr f def = maybe def LitAddr (f cExecOpts)

unitTestOptions :: App m => TestOptions -> CommonOptions -> SolverGroup -> Maybe BuildOutput -> m (UnitTestOptions)
unitTestOptions testOpts cOpts solvers buildOutput = do
  root <- liftIO $ getRoot cOpts

  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput
  let blockUrlInfo = case (testOpts.number, testOpts.rpc) of
          (Just block, Just url) -> Just (Fetch.BlockNumber block, url)
          (Nothing, Just url) -> Just (Fetch.Latest, url)
          _ -> Nothing
      rpcDat = Fetch.RpcInfo blockUrlInfo
  sess <- Fetch.mkSession cOpts.cacheDir testOpts.number
  params <- paramsFromRpc rpcDat sess
  let testn = params.number
      block' = if 0 == testn
       then Fetch.Latest
       else Fetch.BlockNumber testn
  pure UnitTestOptions
    { solvers = solvers
    , sess = sess
    , rpcInfo = let i = case testOpts.rpc of
                     Just url -> Just (block', url)
                     Nothing  -> Nothing
                in rpcDat { Fetch.blockNumURL = i }
    , maxIter = parseMaxIters cOpts.maxIterations
    , askSmtIters = cOpts.askSmtIterations
    , smtTimeout = Just cOpts.smtTimeout
    , match = T.pack $ fromMaybe ".*" testOpts.match
    , prefix = T.pack testOpts.prefix
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = testOpts.ffi
    , checkFailBit = cOpts.assertionType == DSTest
    , loopHeuristic = cOpts.loopDetectionHeuristic
    }
parseInitialStorage :: InitialStorage -> BaseState
parseInitialStorage Empty = EmptyBase
parseInitialStorage Abstract = AbstractBase
