-- Main file of the hevm CLI program

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad (when, forM_, unless)
import Control.Monad.ST (RealWorld, stToIO)
import Control.Monad.IO.Unlift
import Control.Exception (try, IOException)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Char8 as BC
import Data.DoubleWord (Word256)
import Data.List (intersperse)
import Data.Maybe (fromMaybe, mapMaybe, fromJust, isNothing, isJust)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Version (showVersion)
import Data.Word (Word64)
import GHC.Conc (getNumProcessors)
import Numeric.Natural (Natural)
import Optics.Core ((&), set)
import Witch (unsafeInto)
import Options.Generic as Options
import Paths_hevm qualified as Paths
import System.Directory (withCurrentDirectory, getCurrentDirectory, doesDirectoryExist, makeAbsolute)
import System.FilePath ((</>))
import System.Exit (exitFailure, exitWith, ExitCode(..))
import Main.Utf8 (withUtf8)
import Options.Applicative

import EVM (initialContract, abstractContract, makeVm)
import EVM.ABI (Sig(..))
import EVM.Dapp (dappInfo, DappInfo, emptyDapp)
import EVM.Expr qualified as Expr
import EVM.Concrete qualified as Concrete
import GitHash
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified as Fetch
import EVM.Format (hexByteString, strip0x, formatExpr)
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

data AssertionType = DSTest | Forge
  deriving (Eq, Show, Read, ParseField)

data CommonOptions w = CommonOptions
  { numCexFuzz           :: w ::: Integer
  , askSmtIterations     :: w ::: Integer
  , maxBranch            :: w ::: Int
  , maxBufSize           :: w ::: Int
  , promiseNoReent       :: w ::: Bool
  , loopDetectionHeuristic :: w ::: LoopHeuristic
  , noDecompose          :: w ::: Bool
  , numSolvers           :: w ::: Maybe Natural
  , solverThreads        :: w ::: Maybe Natural
  , smttimeout           :: w ::: Maybe Natural
  , maxIterations        :: w ::: Maybe Integer
  , solver               :: w ::: Maybe Text
  , smtdebug             :: w ::: Bool
  , debug                :: w ::: Bool
  , trace                :: w ::: Bool
  }

data CommonOptions2 w = CommonOptions2
  { calldata    :: w ::: Maybe ByteString  <?> "Tx: calldata"
    , address     :: w ::: Maybe Addr        <?> "Tx: address"
    , caller      :: w ::: Maybe Addr        <?> "Tx: caller"
    , origin      :: w ::: Maybe Addr        <?> "Tx: origin"
    , coinbase    :: w ::: Maybe Addr        <?> "Block: coinbase"
    , value       :: w ::: Maybe W256        <?> "Tx: Eth amount"
    , nonce       :: w ::: Maybe Word64      <?> "Nonce of origin"
    , gas         :: w ::: Maybe Word64      <?> "Tx: gas amount"
    , number      :: w ::: Maybe W256        <?> "Block: number"
    , timestamp   :: w ::: Maybe W256        <?> "Block: timestamp"
    , basefee     :: w ::: Maybe W256        <?> "Block: base fee"
    , priorityFee :: w ::: Maybe W256        <?> "Tx: priority fee"
    , gaslimit    :: w ::: Maybe Word64      <?> "Tx: gas limit"
    , gasprice    :: w ::: Maybe W256        <?> "Tx: gas price"
    , create      :: w ::: Bool              <?> "Tx: creation"
    , maxcodesize :: w ::: Maybe W256        <?> "Block: max code size"
    , prevRandao  :: w ::: Maybe W256        <?> "Block: prevRandao"
    , chainid     :: w ::: Maybe W256        <?> "Env: chainId"
    , rpc         :: w ::: Maybe URL         <?> "Fetch state from a remote node"
    , block       :: w ::: Maybe W256        <?> "Block state is be fetched from"
    , root        :: w ::: Maybe String      <?> "Path to  project root directory (default: . )"
    , projectType :: w ::: Maybe ProjectType <?> "Is this a CombinedJSON or Foundry project (default: Foundry)"
    , assertionType :: w ::: Maybe AssertionType <?> "Assertions as per Forge or DSTest (default: Forge)"
  }

-- This record defines the program's command-line options
-- automatically via the `optparse-generic` package.
data Command w
  = Symbolic -- Symbolically explore an abstract program, or specialized with specified env & calldata
  -- vm opts
      { code          :: w ::: Maybe ByteString <?> "Program bytecode"
      , codeFile    :: w ::: Maybe String       <?> "Program bytecode in a file"
      , initialStorage :: w ::: Maybe (InitialStorage) <?> "Starting state for storage: Empty, Abstract (default Abstract)"
      , sig           :: w ::: Maybe Text         <?> "Signature of types to decode / encode"
      , arg           :: w ::: [String]           <?> "Values to encode"
      , getModels     :: w ::: Bool               <?> "Print example testcase for each execution path"
      , showTree      :: w ::: Bool               <?> "Print branches explored in tree view"
      , showReachableTree :: w ::: Bool           <?> "Print only reachable branches explored in tree view"
      , assertions    :: w ::: Maybe [Word256]    <?> "Comma separated list of solc panic codes to check for (default: user defined assertion violations only)"
      , commonOptions :: CommonOptions w
      -- , commonOptions2 :: CommonOptions2 w
      }
  | Equivalence -- prove equivalence between two programs
      { codeA         :: w ::: Maybe ByteString   <?> "Bytecode of the first program"
      , codeB         :: w ::: Maybe ByteString   <?> "Bytecode of the second program"
      , codeAFile     :: w ::: Maybe String     <?> "First program's bytecode in a file"
      , codeBFile     :: w ::: Maybe String     <?> "Second program's bytecode in a file"
      , sig           :: w ::: Maybe Text       <?> "Signature of types to decode / encode"
      , arg           :: w ::: [String]         <?> "Values to encode"
      , calldata      :: w ::: Maybe ByteString <?> "Tx: calldata"
      , smtoutput     :: w ::: Bool             <?> "Print verbose smt output"
      , numCexFuzz    :: w ::: Integer          <!> "3" <?> "Number of fuzzing tries to do to generate a counterexample (default: 3)"
      , commonOptions :: CommonOptions w
      }
  | Exec -- Execute a given program with specified env & calldata
      { code        :: w ::: Maybe ByteString  <?> "Program bytecode"
      , codeFile    :: w ::: Maybe String      <?> "Program bytecode in a file"
      , commonOptions :: CommonOptions w
      -- , commonOptions2 :: CommonOptions2 w
      }
  | Test -- Run Foundry unit tests
      { root        :: w ::: Maybe String               <?> "Path to  project root directory (default: . )"
      , projectType   :: w ::: Maybe ProjectType        <?> "Is this a CombinedJSON or Foundry project (default: Foundry)"
      , assertionType :: w ::: Maybe AssertionType <?> "Assertions as per Forge or DSTest (default: Forge)"
      , rpc           :: w ::: Maybe URL                <?> "Fetch state from a remote node"
      , number        :: w ::: Maybe W256               <?> "Block: number"
      , verbose       :: w ::: Maybe Int                <?> "Append call trace: {1} failures {2} all"
      , coverage      :: w ::: Bool                     <?> "Coverage analysis"
      , match         :: w ::: Maybe String             <?> "Test case filter - only run methods matching regex"
      , debug         :: w ::: Bool                     <?> "Debug printing of internal behaviour, and dump internal expressions"
      , trace         :: w ::: Bool                     <?> "Dump trace"
      , ffi           :: w ::: Bool                     <?> "Allow the usage of the hevm.ffi() cheatcode (WARNING: this allows test authors to execute arbitrary code on your machine)"
      , numCexFuzz    :: w ::: Integer                  <!> "3" <?> "Number of fuzzing tries to do to generate a counterexample (default: 3)"
      , commonOptions :: CommonOptions w
      }
  | Version

  deriving (Options.Generic)

type URL = Text


-- For some reason haskell can't derive a
-- parseField instance for (Text, ByteString)
instance Options.ParseField (Text, ByteString)

deriving instance Options.ParseField Word256
deriving instance Options.ParseField [Word256]

-- Import necessary modules

-- Define the ParseRecord instance for CommonOptions
instance Options.ParseRecord (CommonOptions Options.Wrapped) where
  parseRecord = Options.parseRecordWithModifiers Options.lispCaseModifiers

instance Options.ParseRecord (Command Options.Wrapped) where
  parseRecord =
    Options.parseRecordWithModifiers Options.lispCaseModifiers

data InitialStorage
  = Empty
  | Abstract
  deriving (Show, Read, Options.ParseField)

getFullVersion :: [Char]
getFullVersion = showVersion Paths.version <> " [" <> gitVersion <> "]"
  where
    gitInfo = $$tGitInfoCwdTry
    gitVersion = case gitInfo of
      Right val -> "git rev " <> giBranch val <>  "@" <> giHash val
      Left _ -> "no git revision present"

main :: IO ()
main = withUtf8 $ do
  cmd <- Options.unwrapRecord "hevm -- Ethereum evaluator"
  when (cmd.maxBufSize > 64) $ do
    putStrLn "Error: maxBufSize must be less than or equal to 64. That limits buffers to a size of 2^64, which is more than enough for practical purposes"
    exitFailure
  when (cmd.maxBufSize < 0) $ do
    putStrLn "Error: maxBufSize must be at least 0. Negative values do not make sense. A value of zero means at most 1 byte long buffers"
    exitFailure
  let env = Env { config = defaultConfig
    { dumpQueries = cmd.smtdebug
    , debug = cmd.debug
    , dumpEndStates = cmd.debug
    , dumpExprs = cmd.debug
    , numCexFuzz = cmd.numCexFuzz
    , dumpTrace = cmd.trace
    , decomposeStorage = Prelude.not cmd.noDecompose
    , maxBranch = cmd.maxBranch
    , promiseNoReent = cmd.promiseNoReent
    , maxBufSize = cmd.maxBufSize
    } }
  case cmd of
    Version {} ->putStrLn getFullVersion
    Symbolic {} -> do
      root <- getRoot cmd
      withCurrentDirectory root $ runEnv env $ assert cmd
    Equivalence {} -> runEnv env $ equivalence cmd
    Exec {} -> runEnv env $ launchExec cmd
    Test {} -> do
      root <- getRoot cmd
      solver <- getSolver cmd
      cores <- liftIO $ unsafeInto <$> getNumProcessors
      let solverCount = fromMaybe cores cmd.numSolvers
      runEnv env $ withSolvers solver solverCount (fromMaybe 1 cmd.solverThreads) cmd.smttimeout $ \solvers -> do
        buildOut <- readBuildOutput root (getProjectType cmd)
        case buildOut of
          Left e -> liftIO $ do
            putStrLn $ "Error: " <> e
            exitFailure
          Right out -> do
            -- TODO: which functions here actually require a BuildOutput, and which can take it as a Maybe?
            testOpts <- liftIO $ unitTestOptions cmd solvers (Just out)
            res <- unitTest testOpts out.contracts
            liftIO $ unless (uncurry (&&) res) exitFailure

getCode :: Maybe String -> Maybe ByteString -> IO (Maybe ByteString)
getCode fname code = do
  when (isJust fname && isJust code) $ do
    putStrLn "Error: Cannot provide both a file and code"
    exitFailure
  case fname of
    Nothing -> pure $ fmap strip code
    Just f -> do
      result <- try (BS.readFile f) :: IO (Either IOException BS.ByteString)
      case result of
        Left e -> do
          putStrLn $ "Error reading file: " <> (show e)
          exitFailure
        Right content -> do
          pure $ Just $ strip (BS.toStrict content)
  where
    strip = BC.filter (\c -> c /= ' ' && c /= '\n' && c /= '\r' && c /= '\t' && c /= '"')

equivalence :: App m => Command Options.Unwrapped -> m ()
equivalence cmd = do
  bytecodeA' <- liftIO $ getCode cmd.codeAFile cmd.codeA
  bytecodeB' <- liftIO $ getCode cmd.codeBFile cmd.codeB
  let bytecodeA = decipher bytecodeA'
  let bytecodeB = decipher bytecodeB'
  when (isNothing bytecodeA) $ liftIO $ do
    putStrLn "Error: invalid or no bytecode for program A. Provide a valid one with --code-a or --code-a-file"
    exitFailure
  when (isNothing bytecodeB) $ liftIO $ do
    putStrLn "Error: invalid or no bytecode for program B. Provide a valid one with --code-b or --code-b-file"
    exitFailure
  let veriOpts = VeriOpts { simp = True
                          , maxIter = parseMaxIters cmd.maxIterations
                          , askSmtIters = cmd.askSmtIterations
                          , loopHeuristic = cmd.loopDetectionHeuristic
                          , rpcInfo = Nothing
                          }
  calldata <- buildCalldata cmd
  solver <- liftIO $ getSolver cmd
  cores <- liftIO $ unsafeInto <$> getNumProcessors
  let solverCount = fromMaybe cores cmd.numSolvers
  withSolvers solver solverCount (fromMaybe 1 cmd.solverThreads) cmd.smttimeout $ \s -> do
    (res, e) <- equivalenceCheck s (fromJust bytecodeA) (fromJust bytecodeB) veriOpts calldata
    liftIO $ case (any isCex res, any Expr.isPartial e || any isUnknown res) of
      (False, False) -> putStrLn "   \x1b[32m[PASS]\x1b[0m Contracts behave equivalently"
      (True, _)      -> putStrLn "   \x1b[31m[FAIL]\x1b[0m Contracts do not behave equivalently"
      (_, True)      -> putStrLn "   \x1b[31m[FAIL]\x1b[0m Contracts may not behave equivalently"
    liftIO $ printWarnings e res "the contracts under test"
    case any isCex res of
      False -> liftIO $ do
        when (any isUnknown res || any isError res || any isPartial e) exitFailure
        putStrLn "No discrepancies found"
      True -> liftIO $ do
        let cexs = mapMaybe getCex res
        T.putStrLn . T.unlines $
          [ "Not equivalent. The following inputs result in differing behaviours:"
          , "" , "-----", ""
          ] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (formatCex (AbstractBuf "txdata") Nothing) cexs)
        exitFailure
  where
    decipher = maybe Nothing (hexByteString . strip0x)

getSolver :: Command Options.Unwrapped -> IO Solver
getSolver cmd = case cmd.solver of
                  Nothing -> pure Z3
                  Just s -> case T.unpack s of
                              "z3" -> pure Z3
                              "cvc5" -> pure CVC5
                              "bitwuzla" -> pure Bitwuzla
                              input -> do
                                putStrLn $ "unrecognised solver: " <> input
                                exitFailure

getSrcInfo :: App m => Command Options.Unwrapped -> m DappInfo
getSrcInfo cmd = do
  root <- liftIO $ getRoot cmd
  conf <- readConfig
  liftIO $ withCurrentDirectory root $ do
    outExists <- doesDirectoryExist (root </> "out")
    if outExists
    then do
      buildOutput <- runEnv Env {config = conf} $ readBuildOutput root (getProjectType cmd)
      case buildOutput of
        Left _ -> pure emptyDapp
        Right o -> pure $ dappInfo root o
    else pure emptyDapp

getProjectType :: Command Options.Unwrapped -> ProjectType
getProjectType cmd = fromMaybe Foundry cmd.projectType

getRoot :: Command Options.Unwrapped -> IO FilePath
getRoot cmd = maybe getCurrentDirectory makeAbsolute (cmd.root)

parseMaxIters :: Maybe Integer -> Maybe Integer
parseMaxIters i = if num < 0 then Nothing else Just num
  where
    num = fromMaybe (5::Integer) i

-- | Builds a buffer representing calldata based on the given cli arguments
buildCalldata :: App m => Command Options.Unwrapped -> m (Expr Buf, [Prop])
buildCalldata cmd = case (cmd.calldata, cmd.sig) of
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
    mkCalldata (Just (Sig method'.methodSignature (snd <$> method'.inputs))) cmd.arg
  -- both args provided
  (_, _) -> liftIO $ do
    putStrLn "incompatible options provided: --calldata and --sig"
    exitFailure


-- If function signatures are known, they should always be given for best results.
assert :: App m => Command Options.Unwrapped -> m ()
assert cmd = do
  let block'  = maybe Fetch.Latest Fetch.BlockNumber cmd.block
      rpcinfo = (,) block' <$> cmd.rpc
  calldata <- buildCalldata cmd
  preState <- liftIO $ symvmFromCommand cmd calldata
  let errCodes = fromMaybe defaultPanicCodes cmd.assertions
  cores <- liftIO $ unsafeInto <$> getNumProcessors
  let solverCount = fromMaybe cores cmd.numSolvers
  solver <- liftIO $ getSolver cmd
  withSolvers solver solverCount (fromMaybe 1 cmd.solverThreads) cmd.smttimeout $ \solvers -> do
    let veriOpts = VeriOpts { simp = True
                        , maxIter = parseMaxIters cmd.maxIterations
                        , askSmtIters = cmd.askSmtIterations
                        , loopHeuristic = cmd.loopDetectionHeuristic
                        , rpcInfo = rpcinfo
    }
    (expr, res) <- verify solvers veriOpts preState (Just $ checkAssertions errCodes)
    case res of
      [Qed _] -> do
        liftIO $ putStrLn "\nQED: No reachable property violations discovered\n"
        showExtras solvers cmd calldata expr
      _ -> do
        let cexs = snd <$> mapMaybe getCex res
            smtUnknowns = mapMaybe getUnknown res
            counterexamples
              | null cexs = []
              | otherwise =
                 [ ""
                 , ("Discovered the following " <> (T.pack $ show (length cexs)) <> " counterexample(s):")
                 , ""
                 ] <> fmap (formatCex (fst calldata) Nothing) cexs
            unknowns
              | null smtUnknowns = []
              | otherwise =
                 [ ""
                 , "Could not determine reachability of the following end state(s):"
                 , ""
                 ] <> fmap (formatExpr) smtUnknowns
        liftIO $ T.putStrLn $ T.unlines (counterexamples <> unknowns)
        showExtras solvers cmd calldata expr
        liftIO exitFailure

showExtras :: App m => SolverGroup -> Command Options.Unwrapped -> (Expr Buf, [Prop]) -> Expr End -> m ()
showExtras solvers cmd calldata expr = do
  when cmd.showTree $ liftIO $ do
    putStrLn "=== Expression ===\n"
    T.putStrLn $ formatExpr expr
    putStrLn ""
  when cmd.showReachableTree $ do
    reached <- reachable solvers expr
    liftIO $ do
      putStrLn "=== Reachable Expression ===\n"
      T.putStrLn (formatExpr . snd $ reached)
      putStrLn ""
  when cmd.getModels $ do
    liftIO $ putStrLn $ "=== Models for " <> show (Expr.numBranches expr) <> " branches ==="
    ms <- produceModels solvers expr
    liftIO $ forM_ ms (showModel (fst calldata))

isTestOrLib :: Text -> Bool
isTestOrLib file = T.isSuffixOf ".t.sol" file || areAnyPrefixOf ["src/test/", "src/tests/", "lib/"] file

areAnyPrefixOf :: [Text] -> Text -> Bool
areAnyPrefixOf prefixes t = any (flip T.isPrefixOf t) prefixes

launchExec :: App m => Command Options.Unwrapped -> m ()
launchExec cmd = do
  dapp <- getSrcInfo cmd
  vm <- liftIO $ vmFromCommand cmd
  let
    block = maybe Fetch.Latest Fetch.BlockNumber cmd.block
    rpcinfo = (,) block <$> cmd.rpc

  -- TODO: we shouldn't need solvers to execute this code
  withSolvers Z3 0 1 Nothing $ \solvers -> do
    vm' <- EVM.Stepper.interpret (Fetch.oracle solvers rpcinfo) vm EVM.Stepper.runFully
    writeTraceDapp dapp vm'
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
vmFromCommand :: Command Options.Unwrapped -> IO (VM Concrete RealWorld)
vmFromCommand cmd = do
  (miner,ts,baseFee,blockNum,prevRan) <- case cmd.rpc of
    Nothing -> pure (LitAddr 0,Lit 0,0,0,0)
    Just url -> Fetch.fetchBlockFrom block url >>= \case
      Nothing -> do
        putStrLn $ "Error, Could not fetch block" <> show block <> " from URL: " <> show url
        exitFailure
      Just Block{..} -> pure ( coinbase
                             , timestamp
                             , baseFee
                             , number
                             , prevRandao
                             )

  codeWrapped <- getCode cmd.codeFile cmd.code
  contract <- case (cmd.rpc, cmd.address, codeWrapped) of
    (Just url, Just addr', Just c) -> do
      let code = hexByteString $ strip0x c
      if (isNothing code) then do
        putStrLn $ "Error, invalid code: " <> show c
        exitFailure
      else
        Fetch.fetchContractFrom block url addr' >>= \case
          Nothing -> do
            putStrLn $ "Error: contract not found: " <> show address
            exitFailure
          Just contract ->
            -- if both code and url is given,
            -- fetch the contract and overwrite the code
            pure $
              initialContract  (mkCode $ fromJust code)
                & set #balance  (contract.balance)
                & set #nonce    (contract.nonce)
                & set #external (contract.external)

    (Just url, Just addr', Nothing) ->
      Fetch.fetchContractFrom block url addr' >>= \case
        Nothing -> do
          putStrLn $ "Error, contract not found: " <> show address
          exitFailure
        Just contract -> pure contract

    (_, _, Just c)  -> do
      let code = hexByteString $ strip0x c
      if (isNothing code) then do
        putStrLn $ "Error, invalid code: " <> show c
        exitFailure
      else pure $ initialContract (mkCode $ fromJust code)

    (_, _, Nothing) -> do
      putStrLn "Error, must provide at least (rpc + address) or code"
      exitFailure

  let ts' = case maybeLitWordSimp ts of
        Just t -> t
        Nothing -> internalError "unexpected symbolic timestamp when executing vm test"

  if (isNothing bsCallData) then do
    putStrLn $ "Error, invalid calldata: " <> show calldata
    exitFailure
  else do
    vm <- stToIO $ vm0 baseFee miner ts' blockNum prevRan contract
    pure $ EVM.Transaction.initTx vm
  where
        bsCallData = bytes (.calldata) (pure "")
        block   = maybe Fetch.Latest Fetch.BlockNumber cmd.block
        value   = word (.value) 0
        caller  = addr (.caller) (LitAddr 0)
        origin  = addr (.origin) (LitAddr 0)
        calldata = ConcreteBuf $ fromJust bsCallData
        decipher = hexByteString . strip0x
        mkCode bs = if cmd.create
                    then InitCode bs mempty
                    else RuntimeCode (ConcreteRuntimeCode bs)
        address = if cmd.create
                  then addr (.address) (Concrete.createAddress (fromJust $ maybeLitAddrSimp origin) (W64 $ word64 (.nonce) 0))
                  else addr (.address) (LitAddr 0xacab)

        vm0 baseFee miner ts blockNum prevRan c = makeVm $ VMOpts
          { contract       = c
          , otherContracts = []
          , calldata       = (calldata, [])
          , value          = Lit value
          , address        = address
          , caller         = caller
          , origin         = origin
          , gas            = word64 (.gas) 0xffffffffffffffff
          , baseFee        = baseFee
          , priorityFee    = word (.priorityFee) 0
          , gaslimit       = word64 (.gaslimit) 0xffffffffffffffff
          , coinbase       = addr (.coinbase) miner
          , number         = word (.number) blockNum
          , timestamp      = Lit $ word (.timestamp) ts
          , blockGaslimit  = word64 (.gaslimit) 0xffffffffffffffff
          , gasprice       = word (.gasprice) 0
          , maxCodeSize    = word (.maxcodesize) 0xffffffff
          , prevRandao     = word (.prevRandao) prevRan
          , schedule       = feeSchedule
          , chainId        = word (.chainid) 1
          , create         = (.create) cmd
          , baseState      = EmptyBase
          , txAccessList   = mempty -- TODO: support me soon
          , allowFFI       = False
          , freshAddresses = 0
          , beaconRoot     = 0
          }
        word f def = fromMaybe def (f cmd)
        word64 f def = fromMaybe def (f cmd)
        addr f def = maybe def LitAddr (f cmd)
        bytes f def = maybe def decipher (f cmd)

symvmFromCommand :: Command Options.Unwrapped -> (Expr Buf, [Prop]) -> IO (VM EVM.Types.Symbolic RealWorld)
symvmFromCommand cmd calldata = do
  (miner,blockNum,baseFee,prevRan) <- case cmd.rpc of
    Nothing -> pure (SymAddr "miner",0,0,0)
    Just url -> Fetch.fetchBlockFrom block url >>= \case
      Nothing -> do
        putStrLn $ "Error, Could not fetch block" <> show block <> " from URL: " <> show url
        exitFailure
      Just Block{..} -> pure ( coinbase
                             , number
                             , baseFee
                             , prevRandao
                             )

  let
    caller = maybe (SymAddr "caller") LitAddr cmd.caller
    ts = maybe Timestamp Lit cmd.timestamp
    callvalue = maybe TxValue Lit cmd.value
    storageBase = maybe AbstractBase parseInitialStorage (cmd.initialStorage)

  codeWrapped <- getCode cmd.codeFile cmd.code
  contract <- case (cmd.rpc, cmd.address, codeWrapped) of
    (Just url, Just addr', _) ->
      Fetch.fetchContractFrom block url addr' >>= \case
        Nothing -> do
          putStrLn "Error, contract not found."
          exitFailure
        Just contract' -> case codeWrapped of
              Nothing -> pure contract'
              -- if both code and url is given,
              -- fetch the contract and overwrite the code
              Just c -> do
                let c' = decipher c
                if isNothing c' then do
                  putStrLn $ "Error, invalid code: " <> show c
                  exitFailure
                else pure $ do
                  initialContract (mkCode $ fromJust c')
                        & set #origStorage (contract'.origStorage)
                        & set #balance     (contract'.balance)
                        & set #nonce       (contract'.nonce)
                        & set #external    (contract'.external)

    (_, _, Just c)  -> do
      let c' = decipher c
      if isNothing c' then do
        putStrLn $ "Error, invalid code: " <> show c
        exitFailure
      else case storageBase of
        EmptyBase -> pure (initialContract . mkCode $ fromJust c')
        AbstractBase -> pure ((`abstractContract` address) . mkCode $ fromJust c')

    (_, _, Nothing) -> do
      putStrLn "Error, must provide at least (rpc + address) or code"
      exitFailure

  vm <- stToIO $ vm0 baseFee miner ts blockNum prevRan calldata callvalue caller contract storageBase
  pure $ EVM.Transaction.initTx vm

  where
    decipher = hexByteString . strip0x
    block = maybe Fetch.Latest Fetch.BlockNumber cmd.block
    origin = eaddr (.origin) (SymAddr "origin")
    mkCode bs = if cmd.create
                   then InitCode bs mempty
                   else RuntimeCode (ConcreteRuntimeCode bs)
    address = eaddr (.address) (SymAddr "entrypoint")
    vm0 baseFee miner ts blockNum prevRan cd callvalue caller c baseState = makeVm $ VMOpts
      { contract       = c
      , otherContracts = []
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
      , number         = word (.number) blockNum
      , timestamp      = ts
      , blockGaslimit  = word64 (.gaslimit) 0xffffffffffffffff
      , gasprice       = word (.gasprice) 0
      , maxCodeSize    = word (.maxcodesize) 0xffffffff
      , prevRandao     = word (.prevRandao) prevRan
      , schedule       = feeSchedule
      , chainId        = word (.chainid) 1
      , create         = (.create) cmd
      , baseState      = baseState
      , txAccessList   = mempty
      , allowFFI       = False
      , freshAddresses = 0
      , beaconRoot     = 0
      }
    word f def = fromMaybe def (f cmd)
    word64 f def = fromMaybe def (f cmd)
    eaddr f def = maybe def LitAddr (f cmd)

unitTestOptions :: Command Options.Unwrapped -> SolverGroup -> Maybe BuildOutput -> IO (UnitTestOptions RealWorld)
unitTestOptions cmd solvers buildOutput = do
  root <- getRoot cmd
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput

  let rpcinfo = case (cmd.number, cmd.rpc) of
          (Just block, Just url) -> Just (Fetch.BlockNumber block, url)
          (Nothing, Just url) -> Just (Fetch.Latest, url)
          _ -> Nothing
  params <- paramsFromRpc rpcinfo

  let
    testn = params.number
    block' = if 0 == testn
       then Fetch.Latest
       else Fetch.BlockNumber testn

  pure UnitTestOptions
    { solvers = solvers
    , rpcInfo = case cmd.rpc of
         Just url -> Just (block', url)
         Nothing  -> Nothing
    , maxIter = parseMaxIters cmd.maxIterations
    , askSmtIters = cmd.askSmtIterations
    , smtTimeout = cmd.smttimeout
    , solver = cmd.solver
    , verbose = cmd.verbose
    , match = T.pack $ fromMaybe ".*" cmd.match
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = cmd.ffi
    , checkFailBit = (fromMaybe Forge cmd.assertionType) == DSTest
    }
parseInitialStorage :: InitialStorage -> BaseState
parseInitialStorage Empty = EmptyBase
parseInitialStorage Abstract = AbstractBase
