{-# LANGUAGE ImplicitParams #-}

module EVM.UnitTest where

import Prelude hiding (Foldable(..))

import EVM
import EVM.ABI
import EVM.Solvers
import EVM.Dapp
import EVM.Effects
import EVM.Exec
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format
import EVM.Solidity
import EVM.SymExec (Postcondition, defaultVeriOpts, verify, verifyResult, extractCex, panicMsg, VeriOpts(..), groupIssues, groupPartials, IterConfig(..), LoopHeuristic, defaultIterConf)
import EVM.SymExec.Calldata (symAbiArgSupported, symCalldata)
import EVM.SymExec.Cex (prettyCalldata, calldataFromCex)
import EVM.Types
import EVM.Transaction (initTx)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.Tracing qualified as Tracing
import EVM.Expr (maybeLitWordSimp)
import EVM.Progress qualified as Progress
import EVM.Invariant

import Control.Monad (void, when, unless, forM, forM_, foldM, mfilter)
import Control.Monad.ST (RealWorld, ST, stToIO)
import Control.Monad.State.Strict (execState, execStateT, get, put, liftIO, runStateT)
import Optics.Core
import Optics.State
import Optics.State.Operators
import Data.Aeson qualified as JSON
import Data.Binary.Get (runGet)
import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.ByteString.Internal (c2w)
import Data.ByteString.Lazy qualified as BSLazy
import Data.Decimal (DecimalRaw(..))
import Data.Foldable (Foldable(..), toList)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Maybe
import Data.Text (isPrefixOf, stripSuffix, intercalate, Text, pack, unpack)
import Data.Text qualified as Text
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as Text
import Data.Word (Word64)
import GHC.Natural
import System.IO (hFlush, stdout)
import Witch (unsafeInto, into)
import Data.Vector qualified as V
import Data.Vector.Storable qualified as VS
import Data.Sequence qualified as Seq
import Data.Char (ord)

data UnitTestOptions = UnitTestOptions
  { rpcInfo       :: Fetch.RpcInfo
  , solvers       :: SolverGroup
  , sess          :: Fetch.Session
  , maxIter       :: Maybe Integer
  , maxConcreteIter :: Maybe Integer
  , askSmtIters   :: Integer
  , smtTimeout    :: Maybe Natural
  , methodFilter  :: TestMethodFilter
  , dapp          :: DappInfo
  , testParams    :: TestVMParams
  , ffiAllowed    :: Bool
  , checkFailBit  :: Bool
  , loopHeuristic :: LoopHeuristic
  , printOut      :: Text -> IO ()
  , invariantDepth :: Int
  }

data TestVMParams = TestVMParams
  { address       :: Expr EAddr
  , caller        :: Expr EAddr
  , origin        :: Expr EAddr
  , gasCreate     :: Word64
  , gasCall       :: Word64
  , baseFee       :: W256
  , priorityFee   :: W256
  , balanceCreate :: W256
  , coinbase      :: Expr EAddr
  , number        :: W256
  , timestamp     :: W256
  , gaslimit      :: Word64
  , gasprice      :: W256
  , maxCodeSize   :: W256
  , prevrandao    :: W256
  , chainId       :: W256
  }

defaultGasForCreating :: Word64
defaultGasForCreating = 0xffffffffffff

defaultGasForInvoking :: Word64
defaultGasForInvoking = 0xffffffffffff

defaultBalanceForTestContract :: W256
defaultBalanceForTestContract = 0xffffffffffffffffffffffff

defaultMaxCodeSize :: W256
defaultMaxCodeSize = 0xffffffff

type ABIMethod = Text

-- | Used in various places for dumping traces
writeTraceDapp :: App m => DappInfo -> VM t -> m ()
writeTraceDapp dapp vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ Text.writeFile "VM.trace" (showTraceTree dapp vm)

writeTrace :: App m => VM t -> m ()
writeTrace vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ writeFile "VM.trace" (show $ traceForest vm)

-- | Generate VeriOpts from UnitTestOptions
makeVeriOpts :: UnitTestOptions -> VeriOpts
makeVeriOpts opts =
   defaultVeriOpts { iterConf = defaultIterConf {maxIter = opts.maxIter, maxConcreteIter = opts.maxConcreteIter, askSmtIters = opts.askSmtIters, loopHeuristic = opts.loopHeuristic}
                   , rpcInfo = opts.rpcInfo
                   }

-- | Top level CLI endpoint for hevm test
-- | Returns tuple of (No Cex, No warnings)
unitTest :: App m => UnitTestOptions -> BuildOutput -> m (Bool, Bool)
unitTest opts bo = do
  results <- unitTestResults opts bo
  let (firsts, seconds) = unzip results
  pure (and firsts, and seconds)

unitTestResults :: App m => UnitTestOptions -> BuildOutput -> m [(Bool, Bool)]
unitTestResults opts bo = map snd <$> unitTestResultsNamed opts bo

-- | Like 'unitTestResults', each result with its contract and test name
unitTestResultsNamed :: App m => UnitTestOptions -> BuildOutput -> m [((Text, Text), (Bool, Bool))]
unitTestResultsNamed opts bo@(BuildOutput (Contracts cs) _) = do
  let unitTestContrs = [(c, methods) | c <- Map.elems cs, let methods = findUnitTests opts.methodFilter c, not (null methods)]
  conf <- readConfig
  when conf.debug $ liftIO $ do
    putStrLn $ "Found " ++ show (length unitTestContrs) ++ " unit test contract(s) to test:"
    let x = map (\(a,b) -> "  --> " <> a.contractName <> "  ---  functions: " <> (Text.pack $ show b)) unitTestContrs
    putStrLn $ unlines $ map Text.unpack x
  results <- mapM (runUnitTestContract opts bo) unitTestContrs
  pure $ concat results

-- | Assuming a constructor is loaded, this stepper will run the constructor
-- to create the test contract, give it an initial balance, and run `setUp()'.
initializeUnitTest :: UnitTestOptions -> SolcContract -> Stepper Concrete ()
initializeUnitTest opts theContract = do
  let addr = opts.testParams.address

  Stepper.evm $ do
    -- Make a trace entry for running the constructor
    pushTrace (EntryTrace "constructor")

  -- Constructor is loaded; run until it returns code
  void Stepper.execFully

  Stepper.evm $ do
    -- Give a balance to the test target
    #env % #contracts % ix addr % #balance %= (`Expr.add` (Lit opts.testParams.balanceCreate))

    -- call setUp(), if it exists, to initialize the test contract
    let theAbi = theContract.abiMap
        setUp  = abiKeccak (encodeUtf8 "setUp()")
    when (isJust (Map.lookup setUp theAbi)) $ do
      abiCall opts.testParams (Left ("setUp()", emptyAbi))
      popTrace
      pushTrace (EntryTrace "setUp()")

  -- Let `setUp()' run to completion
  res <- Stepper.execFully
  Stepper.evm $ case res of
    Left e -> pushTrace (ErrorTrace e)
    _ -> popTrace

validateCex :: forall m . App m
  => UnitTestOptions
  -> Fetch.Fetcher Concrete m
  -> VM Concrete
  -> Map (Expr EAddr) Addr
  -> ReproducibleCex
  -> m (Bool, Either EvmError (Expr Buf))
validateCex uTestOpts fetcher vm0 cexAddrs repCex = do
  let concAddr dflt a = case a of
        SymAddr _ -> LitAddr $ Map.findWithDefault dflt a cexAddrs
        _ -> a
      params = uTestOpts.testParams
      utoConc = uTestOpts { testParams = params { caller = concAddr 0xdeadbeef params.caller
                                                , origin = concAddr 0xdeadbeef params.origin }}
      vm = vm0 & set (#tx % #origin) utoConc.testParams.origin
               & over (#block % #coinbase) (concAddr 0)
  conf <- readConfig
  when conf.debug $ liftIO $ putStrLn $ "Repro running function: " <> show utoConc.testParams.address <>
    " with caller: " <> show utoConc.testParams.caller <> ", gas: " <> show utoConc.testParams.gasCall <>
    ", and calldata: " <> show (bsToHex repCex.callData)

  -- Note, we should not need solvers to execute this code
  vm2 <- Stepper.interpret fetcher vm $ do
    Stepper.evm $ do
      pushTrace (EntryTrace $ "checking cex for function " <> repCex.testName <> " with calldata: " <> (Text.pack $ bsToHex repCex.callData))
      makeTxCall utoConc.testParams (ConcreteBuf repCex.callData, [])
    Stepper.evm get

  (res, (vm3, vmtrace)) <- runStateT (Tracing.interpretWithTrace fetcher Stepper.execFully) (vm2, [])
  when (conf.debug && (conf.verb > 2)) $ liftIO $ do
    putStrLn $ "vm step trace: " <> unlines (map show vmtrace)
    putStrLn $ "vm res: " <> show res
    putStrLn $ "vm res: " <> show vm3.result
  let shouldFail = "proveFail" `isPrefixOf` repCex.testName
  pure (assertionFailedConc utoConc.checkFailBit res vm3.env.contracts /= shouldFail, res)

-- | Whether a concrete run failed an assertion
assertionFailedConc :: Bool -> Either EvmError (Expr Buf) -> Map (Expr EAddr) Contract -> Bool
assertionFailedConc checkFailBit res contracts = case res of
  Left (UnrecognizedOpcode 0xfe) -> True
  Left (Revert (ConcreteBuf msg)) ->
    msg == panicMsg 0x01 ||
      let sel = selector "Error(string)"
      in (sel `BS.isPrefixOf` msg) && ("assertion failed" `BS.isPrefixOf` (BS.drop (4+32+32) msg))
  Left _ -> False
  Right _ -> checkFailBit && dsTestFailedConc contracts

-- Returns tuple of (No Cex, No warnings)
runUnitTestContract
  :: App m
  => UnitTestOptions
  -> BuildOutput
  -> (SolcContract, [Sig])
  -> m [((Text, Text), (Bool, Bool))]
runUnitTestContract
  opts@(UnitTestOptions {..}) buildOut (contract, testSigs) = do
  unless (Map.member contract.contractName (getContractsMap buildOut.contracts)) $ internalError $ "Contract " ++ unpack contract.contractName ++ " not found"
  liftIO $ printOut $ "Checking " <> Text.pack (show (length testSigs)) <> " function(s) in contract " <> contract.contractName <> "\n"
  -- Construct the initial VM and begin the contract's constructor
  vm0 :: VM Concrete <- liftIO $ stToIO $ initialUnitTestVm opts contract
  vm1 <- Stepper.interpret (Fetch.oracle solvers (Just sess) rpcInfo) vm0 $ do
    Stepper.enter contract.contractName
    initializeUnitTest opts contract
    Stepper.evm get

  writeTraceDapp dapp vm1
  failOut <- failOutput vm1 opts "setUp()"
  case vm1.result of
    Just (VMFailure _) -> do
      liftIO $ printOut $ "   \x1b[31m[BAIL]\x1b[0m setUp() \n" <> indentLines 3 failOut
      pure [(named "setUp", (True, False))]
    Just (VMSuccess _) -> do
      inv <- if any isInvariant testSigs then Just <$> invariantContext opts vm1 contract buildOut.sources else pure Nothing
      forM (zip [1..] testSigs) $ \(i, s@(Sig name _)) -> fmap (named name,) $ case inv of
        Just ctx | isInvariant s -> invariantRun opts ctx (i, length testSigs) s
        _ -> symRun opts vm1 (i, length testSigs) s buildOut.sources
    _ -> internalError "setUp() did not end with a result"
  where
    named name = (Text.takeWhileEnd (/= ':') contract.contractName, name)

-- | The VM of the single test matching the filter, after setUp(), about to
-- call the test with symbolic arguments
debugTestVm :: App m => UnitTestOptions -> BuildOutput -> m (Either Text (VM Symbolic))
debugTestVm opts buildOut@(BuildOutput (Contracts cs) _) =
  case [ (c, s) | c <- Map.elems cs, s <- findUnitTests opts.methodFilter c ] of
    [(contract, sig@(Sig testName types))] -> do
      vm0 :: VM Concrete <- liftIO $ stToIO $ initialUnitTestVm opts contract
      vm1 <- Stepper.interpret (Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo) vm0 $ do
        Stepper.enter contract.contractName
        initializeUnitTest opts contract
        Stepper.evm get
      case vm1.result of
        Just (VMSuccess _) -> do
          (cdBuf, cdProps, _) <- symCalldata (callSig sig) types [] (AbstractBuf "txdata")
          vm2 <- Stepper.interpret (Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo) vm1 $
            Stepper.evm $ do
              pushTrace (EntryTrace testName)
              makeTxCall opts.testParams (cdBuf, cdProps)
              get
          pure $ Right $ symbolify vm2 & set #srcLookup (Just $ makeSrcLookup opts.dapp buildOut.sources)
        _ -> Left . ("setUp() failed:\n" <>) <$> failOutput vm1 opts "setUp()"
    [] -> pure $ Left "No test matches; use --match to select exactly one test to debug"
    many -> pure $ Left $ "Several tests match, use --match to select exactly one to debug:\n"
      <> Text.unlines [ "  " <> c.contractName <> "." <> n | (c, Sig n _) <- many ]

-- | forge-std's and ds-test's fail() set the "failed" slot of the cheat code
-- address, so without that account nothing failed
dsTestFailedSym :: Map (Expr 'EAddr) (Expr EContract) -> Prop
dsTestFailedSym store = case Map.lookup cheatCode store of
  Just cheatContract -> Expr.readStorage' (Lit 0x6661696c65640000000000000000000000000000000000000000000000000000) cheatContract.storage .== Lit 1
  Nothing -> PBool False

dsTestFailedConc :: Map (Expr 'EAddr) Contract -> Bool
dsTestFailedConc store = case Map.lookup cheatCode store of
  Just cheatContract -> Expr.readStorage' (Lit 0x6661696c65640000000000000000000000000000000000000000000000000000) cheatContract.storage == Lit 1
  Nothing -> False

-- Define the thread spawner for symbolic tests
-- Returns tuple of (No Cex, No warnings)
symRun :: forall m . App m => UnitTestOptions -> VM Concrete -> (Int, Int) -> Sig -> SourceCache -> m (Bool, Bool)
symRun opts@UnitTestOptions{..} vm (nth, numTests) sig@(Sig testName types) sourceCache = do
    let cs = callSig sig
    liftIO $ printOut $ "\x1b[96m[RUNNING]\x1b[0m " <> cs <> "\n"
    (cdBuf, cdProps, caveats) <- symCalldata cs types [] (AbstractBuf "txdata")
    let cd = (cdBuf, cdProps)
    let shouldFail = "proveFail" `isPrefixOf` cs
        postcondition = testPostcondition opts.checkFailBit shouldFail

    let fetcherConc = Fetch.oracle solvers (Just sess) rpcInfo
    vm' <- Stepper.interpret fetcherConc vm $
      Stepper.evm $ do
        pushTrace (EntryTrace testName)
        makeTxCall testParams cd
        get
    writeTraceDapp dapp vm'

    -- check postconditions against vm
    let fetcherSym = Fetch.oracle solvers (Just sess) rpcInfo
    let symVm = symbolify vm' & set #srcLookup (Just $ makeSrcLookup dapp sourceCache)
    let summary (ends, results) =
          ("paths" JSON..= length ends) : [k JSON..= n | (k, n) <-
            [ ("partial", length (filter Expr.isPartial ends)), ("cex", length (filter isCex results))
            , ("unknown", length (filter isUnknown results)), ("error", length (filter isError results)) ], n > 0]
    (ends, results) <- Progress.withPhase "test" ["test" JSON..= cs] summary $ do
      Progress.phaseTotal numTests
      Progress.phaseAt nth
      verify solvers fetcherSym (makeVeriOpts opts) symVm postcondition (Just $ cexHandler cd fetcherConc)
    conf <- readConfig
    when (conf.debug) $ liftIO $ do
      putStrLn $ "   \x1b[94m[EXPLORATION COMPLETE]\x1b[0m " <> Text.unpack testName <> " -- explored " <> show (length ends) <> " paths."
      when (conf.verb >= 2) $ do
        forM_ (filter Expr.isFailure ends) $ \case
          (Failure _ _ a) ->  putStrLn $ "   -> debug of func: " <> Text.unpack testName <> " Failure at the end of expr: " <> show a;
          _ -> internalError "cannot be, filtered for failure"

    -- display results
    when (conf.debug && conf.verb >=2) $ liftIO $ do
      putStrLn $ "Collected END-s:\n" <> prettyvmresults ends
      putStrLn $ "Collected verification results: " <> show results
    -- Caveats (e.g. dynamic args bounded to maxDynSize) restrict the input
    -- domain rather than leaving a path unexplored, so they are not Partials;
    -- they still count as a warning so a bounded run is not reported as a clean
    -- pass (avoids a false sense of security).
    let warnings = any Expr.isPartial ends || any isUnknown results || any isError results || not (null caveats)
    -- early abort discards unexplored paths, so the surviving ends say nothing about reverts
    let allReverts = not (any Expr.isSuccess ends) && not (conf.earlyAbort && any isCex results)
    let unexpectedAllRevert = allReverts && not shouldFail
    when conf.debug $ liftIO $ putStrLn $ "   symRun -- (cex,warnings,unexpectedAllRevert): " <> show (any isCex results, warnings, unexpectedAllRevert)
    txtResult <- case (any isCex results, warnings, unexpectedAllRevert) of
      (False, False, False) -> do
        -- happy case
        pure $ "   \x1b[32m[PASS]\x1b[0m " <> Text.unpack testName <> "\n"
      (True, _, _) -> do
        pure $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n"
          <> (if conf.earlyAbort then "   Stopped at the first counterexample, --no-early-abort finds all of them\n" else "")
      (_, True, _) -> do
        -- There are errors/unknowns/partials, we fail them
        pure $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n"
      (_, _, True) -> do
        -- No cexes/errors/unknowns/partials, but all branches reverted
        pure $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n"
          <> "   No reachable assertion violations, but all branches reverted\n"
    liftIO $ printOut $ Text.pack txtResult
    when (unexpectedAllRevert && (warnings || (any isCex results))) $ do
      -- if we display a FAILED due to Cex/warnings, we should also mention everything reverted
      liftIO $ printOut $ "   \x1b[33m[WARNING]\x1b[0m " <> testName <> " all branches reverted\n\n"
    let sl = Just $ makeSrcLookup dapp sourceCache
    liftIO $ printWarnings printOut sl vm'.env.contracts ends results $ "the test " <> Text.unpack testName
    liftIO $ printCaveats printOut caveats
    pure (not (any isCex results), not (warnings || unexpectedAllRevert))
    where
      cexHandler :: (Expr 'Buf, [Prop])
        -> Fetch.Fetcher Concrete m
        -> VM 'Symbolic
        -> SMTResult
        -> Expr 'End
        -> m ()
      cexHandler cd fetcherConc preState smtRes end = do
          let verifRes = snd $ verifyResult preState (smtRes, end)
          case extractCex verifRes of
            Nothing -> internalError "cexHandler: expected a cex"
            Just (cexEnd, smtCex) -> do
              failsToRepro <- getReproFailure (Sig testName types) (fst cd) smtCex
              validation <- traverse (validateCex opts fetcherConc vm smtCex.addrs) failsToRepro
              txtFail <- symFailure opts testName (Just (fst cd, types)) [] (cexEnd, smtCex, validation)
              liftIO $ printOut txtFail

-- | What a test must satisfy at the end of each path: no failed assertion,
-- or, with @shouldFail@, a failed one
testPostcondition :: Bool -> Bool -> Postcondition
testPostcondition checkFailBit shouldFail = curry $ case shouldFail of
  True -> \(_, post) -> case post of
    Success _ _ _ store -> if checkFailBit then dsTestFailedSym store else PBool False
    _ -> PBool True
  False -> \(_, post) -> case post of
    Success _ _ _ store -> if checkFailBit then PNeg (dsTestFailedSym store) else PBool True
    Failure _ _ (UnrecognizedOpcode 0xfe) -> PBool False
    Failure _ _ (Revert msg) -> case msg of
      ConcreteBuf b ->
        -- NOTE: assertTrue/assertFalse does not have the double colon after "assertion failed"
        let assertFail = (selector "Error(string)" `BS.isPrefixOf` b) &&
              ("assertion failed" `BS.isPrefixOf` (BS.drop txtOffset b))
        in if assertFail || b == panicMsg 0x01 then PBool False
        else PBool True
      _ -> symbolicFail msg
    Failure _ _ _ -> PBool True
    Partial _ _ _ -> PBool True
    _ -> internalError "Invalid leaf node"
  where
    -- The offset of the text is: the selector (4B), the offset value (aligned to 32B), and the length of the string (aligned to 32B)
    txtOffset = 4+32+32
    symbolicFail :: Expr Buf -> Prop
    symbolicFail e =
      let origTxt = "assertion failed"
          txtLen = length origTxt
          w8Txt = V.fromList $ map (fromIntegral . ord) origTxt
          panic = e == ConcreteBuf (panicMsg 0x01)
          concretePrefix = Expr.concretePrefix e
          assertFail =
            if (length concretePrefix < txtOffset+txtLen)
            then PAnd (symBytesEq 0 e (BS.unpack $ selector "Error(string)")) (symBytesEq txtOffset e origTxt)
            else PBool (V.drop txtOffset (V.take (txtLen+txtOffset) concretePrefix) == w8Txt)
      in PBool (not panic) .&& PNeg assertFail
    symBytesEq :: Int -> Expr Buf -> String -> Prop
    symBytesEq off buf str = let acc = go str buf off []
      in foldl' PAnd (PBool True) acc
      where
        go :: String -> Expr Buf -> Int -> [Prop] -> [Prop]
        go "" _ _ acc = acc
        go (a:ax) b n acc = go ax b (n+1) (PEq lhs rhs:acc)
          where
            lhs = LitByte (c2w a)
            rhs = Expr.readByte (Lit (fromIntegral n)) b
--
printWarnings :: (Text -> IO ()) -> Maybe SrcLookup -> Map (Expr EAddr) Contract -> GetUnknownStr b => [Expr 'End] -> [ProofResult a b] -> String -> IO ()
printWarnings printOut srcLookupM contracts e results testName = do
  when (any isUnknown results || any isError results || any Expr.isPartial e) $ do
    out $ "   \x1b[33m[WARNING]\x1b[0m hevm was only able to partially explore " <> testName <> " due to: "
    forM_ (groupIssues (filter isError results)) $ \(num, str) -> out $ "      " <> show num <> "x -> " <> str
    forM_ (groupIssues (filter isUnknown results)) $ \(num, str) -> out $ "      " <> show num <> "x -> " <> str
    forM_ (groupPartials srcLookupM contracts e) $ \(num, str) -> out $ "      " <> show num <> "x -> " <> str
  out ""
  where out l = printOut (Text.pack l <> "\n")

-- | Print any program-wide soundness caveats (see 'Caveat'). Unlike
-- 'printWarnings' this is not about unexplored paths: it tells the user the
-- input domain was restricted, so a "no counterexample" result is only valid
-- within that restriction.
printCaveats :: (Text -> IO ()) -> [Caveat] -> IO ()
printCaveats printOut caveats =
  forM_ caveats $ \c ->
    printOut $ "   \x1b[33m[CAVEAT]\x1b[0m " <> formatCaveat c <> "\n"

getReproFailure :: App m => Sig -> Expr Buf -> SMTCex -> m (Err ReproducibleCex)
getReproFailure sig@(Sig testName _) cd cex = do
  bs <- calldataFromCex cex cd sig
  pure $ (\case
    Left err -> Left err
    Right fullCD -> Right $ ReproducibleCex { testName = testName, callData = fullCD}) bs

-- | Without calldata, the failure is in the last of the calls shown before
symFailure :: App m =>
  UnitTestOptions -> Text -> Maybe (Expr Buf, [AbiType]) -> [Text] ->
  (Expr End, SMTCex, Err (Bool, Either EvmError (Expr Buf))) ->
  m Text
symFailure UnitTestOptions {..} testName calldata before failure = do
  conf <- readConfig
  pure $ mconcat [ indentLines 3 $ mkMsg conf failure ]
  where
      showRes = \case
        Success _ _ _ _ -> if "proveFail" `isPrefixOf` testName
                           then "Successful execution"
                           else "Failed: Test Assertion Violation"
        res ->
          let ?context = dappContext (traceContext res)
          in Text.pack $ prettyvmresult res
      mkMsg conf (leaf, cex, repro) = intercalate "\n" $
        ([maybe "Assertion failure in a call:   " (const "Counterexample:   ") calldata <> reproToText repro] <> before <>
        ["  calldata: " <> let ?context = dappContext (traceContext leaf)
                           in prettyCalldata cex cd testName types | Just (cd, types) <- [calldata]] <>
        ["  result:   " <> showRes (replayed leaf repro)
        ]) <> verbText conf leaf
      -- symbolic assertions render their operands as expressions, the replay has the values
      replayed leaf = \case
        Right (True, Left e) -> Failure [] (traceContext leaf) e
        Right (True, Right out) -> Success [] (traceContext leaf) out mempty
        _ -> leaf
      verbText conf leaf = if conf.verb <= 1 then mempty
                           else [Text.unlines [ indentLines 2 (showTraceTree' dapp leaf)]]
      dappContext TraceContext { contracts, labels } =
        DappContext { info = dapp, contracts, labels }

      reproToText :: Err (Bool, a) -> Text
      reproToText (Left err) = "\x1b[33m[error attempting to reproduce: " <> pack err <> "]\x1b[0m"
      reproToText (Right (repro, _)) = if repro then "\x1b[90m[validated]\x1b[0m" else "\x1b[31m[not reproducible]\x1b[0m"

indentLines :: Int -> Text -> Text
indentLines n s =
  let p = Text.replicate n " "
  in Text.unlines (map (p <>) (Text.lines s))

failOutput :: App m => VM t -> UnitTestOptions -> Text -> m Text
failOutput vm UnitTestOptions { .. } testName = do
  conf <- readConfig
  let ?context = DappContext { info = dapp
                             , contracts = vm.env.contracts
                             , labels = vm.labels }
  pure $ mconcat
    [ "Failure: "
    , fromMaybe "" (stripSuffix "()" testName)
    , "\n"
    , if conf.verb <= 1 then ""
      else indentLines 2 (showTraceTree dapp vm)
    , indentLines 2 (formatTestLogs dapp.eventMap vm.logs)
    ]

formatTestLogs :: (?context :: DappContext) => Map W256 Event -> [Expr Log] -> Text
formatTestLogs events xs =
  case catMaybes (toList (fmap (formatTestLog events) xs)) of
    [] -> "\n"
    ys -> "\n" <> intercalate "\n" ys <> "\n\n"

-- Here we catch and render some special logs emitted by ds-test,
-- with the intent to then present them in a separate view to the
-- regular trace output.
formatTestLog :: (?context :: DappContext) => Map W256 Event -> Expr Log -> Maybe Text
formatTestLog _ (LogEntry _ _ []) = Nothing
formatTestLog _ (GVar _) = internalError "unexpected global variable"
formatTestLog events (LogEntry _ args (topic:_)) =
  case maybeLitWordSimp topic >>= \t1 -> (Map.lookup t1 events) of
    Nothing -> Nothing
    Just (Event name _ argInfos) ->
      case (name <> parenthesise (abiTypeSolidity <$> argTypes)) of
        "log(string)" -> Just $ unquote $ showValue AbiStringType args

        -- log_named_x(string, x)
        "log_named_bytes32(string, bytes32)" -> log_named
        "log_named_address(string, address)" -> log_named
        "log_named_int(string, int256)"      -> log_named
        "log_named_uint(string, uint256)"    -> log_named
        "log_named_bytes(string, bytes)"     -> log_named
        "log_named_string(string, string)"   -> log_named

        -- log_named_decimal_x(string, uint, x)
        "log_named_decimal_int(string, int256, uint256)"   -> log_named_decimal
        "log_named_decimal_uint(string, uint256, uint256)" -> log_named_decimal

        -- log_x(x)
        "log_bytes32(bytes32)" -> log_unnamed
        "log_address(address)" -> log_unnamed
        "log_int(int256)"      -> log_unnamed
        "log_uint(uint256)"    -> log_unnamed
        "log_bytes(bytes)"     -> log_unnamed
        "log_string(string)"   -> log_unnamed

        -- log_named_x(bytes32, x), as used in older versions of ds-test.
        -- bytes32 are opportunistically represented as strings in Format.hs
        "log_named_bytes32(bytes32, bytes32)" -> log_named
        "log_named_address(bytes32, address)" -> log_named
        "log_named_int(bytes32, int256)"      -> log_named
        "log_named_uint(bytes32, uint256)"    -> log_named

        _ -> Nothing

        where
          headErr l = fromMaybe (internalError "shouldn't happen") $ listToMaybe l
          argTypes = [argType | (_, argType, NotIndexed) <- argInfos]
          unquote = Text.dropAround (\c -> c == '"' || c == '«' || c == '»')
          log_unnamed =
            Just $ showValue (headErr argTypes) args
          log_named =
            let (key, val) = case take 2 (textValues argTypes args) of
                  [k, v] -> (k, v)
                  _ -> internalError "shouldn't happen"
            in Just $ unquote key <> ": " <> val
          showDecimal dec val =
            pack $ show $ Decimal (unsafeInto dec) val
          log_named_decimal =
            case args of
              (ConcreteBuf b) ->
                case toList $ runGet (getAbiSeq (length argTypes) argTypes) (BSLazy.fromStrict b) of
                  [key, (AbiUInt 256 val), (AbiUInt 256 dec)] ->
                    Just $ (unquote (showAbiValue key)) <> ": " <> showDecimal dec val
                  [key, (AbiInt 256 val), (AbiUInt 256 dec)] ->
                    Just $ (unquote (showAbiValue key)) <> ": " <> showDecimal dec val
                  _ -> Nothing
              _ -> Just "<symbolic decimal>"

abiCall :: VMOps t => TestVMParams -> Either (Text, AbiValue) ByteString -> EVM t ()
abiCall params args =
  let cd = case args of
        Left (sig, args') -> abiMethod sig args'
        Right b -> b
  in makeTxCall params (ConcreteBuf cd, [])

makeTxCall :: VMOps t => TestVMParams -> (Expr Buf, [Prop]) -> EVM t ()
makeTxCall params (cd, cdProps) = do
  resetState
  assign (#tx % #isCreate) False
  execState (loadContract params.address) <$> get >>= put
  assign (#state % #calldata) cd
  #constraints %= (<> cdProps)
  assign (#state % #caller) params.caller
  assign (#state % #gas) (toGas params.gasCall)
  origin <- fromMaybe (initialContract (RuntimeCode (ConcreteRuntimeCode ""))) <$> use (#env % #contracts % at params.origin)
  let insufficientBal = maybe False (\b -> b < params.gasprice * (into params.gasCall)) (maybeLitWordSimp origin.balance)
  when insufficientBal $ internalError "insufficient balance for gas cost"
  vm <- get
  put $ initTx vm

initialUnitTestVm :: forall t. VMOps t => UnitTestOptions -> SolcContract -> ST RealWorld (VM t)
initialUnitTestVm (UnitTestOptions {..}) theContract = do
  vm <- makeVm $ (defaultVMOpts @t)
           { contract = initialContract (InitCode theContract.creationCode mempty)
           , address = testParams.address
           , caller = testParams.caller
           , origin = testParams.origin
           , gas = toGas testParams.gasCreate
           , gaslimit = testParams.gasCreate
           , coinbase = testParams.coinbase
           , number = Lit testParams.number
           , timestamp = Lit testParams.timestamp
           , blockGaslimit = testParams.gaslimit
           , gasprice = testParams.gasprice
           , baseFee = Lit testParams.baseFee
           , priorityFee = testParams.priorityFee
           , maxCodeSize = testParams.maxCodeSize
           , prevRandao = Lit testParams.prevrandao
           , chainId = testParams.chainId
           , create = True
           , allowFFI = ffiAllowed
           }
  let creator =
        initialContract (RuntimeCode (ConcreteRuntimeCode ""))
          & set #nonce (Just 1)
          & set #balance (Lit testParams.balanceCreate)
  pure $ vm & set (#env % #contracts % at (LitAddr ethrunAddress)) (Just creator)

-- | Build a SrcLookup callback that resolves (address, pc) to source location info
makeSrcLookup :: DappInfo -> SourceCache -> SrcLookup
makeSrcLookup dapp srcCache = SrcLookup $ \contracts addr pc ->
  let fallback = " at addr: " <> show addr <> " at pc: " <> show pc
  in fromMaybe fallback $ do
    contr <- Map.lookup addr contracts
    pcOp <- contr.opIxMap VS.!? pc
    sol <- findSrc contr dapp
    sMap <- case contr.code of
      RuntimeCode _ -> Seq.lookup pcOp sol.runtimeSrcmap
      InitCode _ _ -> Seq.lookup pcOp sol.creationSrcmap
      UnknownCode _ -> Nothing
    (fname, fcontent) <- Map.lookup sMap.file srcCache.files
    let eols = BS.count '\n' $ BS.take sMap.offset fcontent
    let str = " in file \"" <> fname <> "\" on line " <> show (eols+1)
    case (BS.length fcontent > (sMap.offset + sMap.length)) of
      False -> pure str
      True  -> let relevant = BS.take sMap.length $ BS.drop sMap.offset fcontent
        in pure $ str <> " : " <> show relevant

paramsFromRpc :: forall m . App m => Fetch.RpcInfo -> Fetch.Session -> m TestVMParams
paramsFromRpc rpcInfo sess = do
  (miner,ts,blockNum,ran,limit,base) <- case rpcInfo.blockNumURL of
    Nothing -> pure (SymAddr "miner", Lit 0, Lit 0, Lit 0, 0, Lit 0)
    Just (Fetch.Latest, url) -> fetch Fetch.Latest url
    Just (Fetch.BlockNumber block, url) -> fetch (Fetch.BlockNumber block) url
  let ts' = fromMaybe (internalError "received unexpected symbolic timestamp via rpc") (maybeLitWordSimp ts)
  pure $ TestVMParams
    -- TODO: make this symbolic! It needs some tweaking to the way that our
    -- symbolic interpreters work to allow us to symbolically exec constructor initialization
    { address = LitAddr 0xacab
    , caller = SymAddr "caller"
    , origin = SymAddr "origin"
    , gasCreate = defaultGasForCreating
    , gasCall = defaultGasForInvoking
    , baseFee = forceLit base
    , priorityFee = 0
    , balanceCreate = defaultBalanceForTestContract
    , coinbase = miner
    , number = forceLit blockNum
    , timestamp = ts'
    , gaslimit = limit
    , gasprice = 0
    , maxCodeSize = defaultMaxCodeSize
    , prevrandao = forceLit ran
    , chainId = 99
    }
  where
    fetch block url = do
      conf <- readConfig
      liftIO $ Fetch.fetchBlockWithSession conf sess block url >>= \case
        Nothing -> internalError "Could not fetch block"
        Just Block{..} -> pure ( coinbase
                               , timestamp
                               , number
                               , prevRandao
                               , gaslimit
                               , baseFee
                               )


tick :: Text -> IO ()
tick x = Text.putStr x >> hFlush stdout

isInvariant :: Sig -> Bool
isInvariant (Sig name _) = "invariant_" `isPrefixOf` name

-- | What the invariants of a test contract share: the functions to call, and
-- the states reached so far, by the number of calls
data InvariantContext = InvariantContext
  { setupVm :: VM Concrete
  , targets :: Either Text [Target]
  -- | target functions whose arguments cannot be symbolic
  , skipped :: [Text]
  , senders :: Senders
  , levels :: IORef [[InvState]]
  -- | the states reached so far, a state reached again is not explored again
  , visited :: IORef (Set StateKey)
  , partials :: IORef [Expr End]
  -- | the first call found to fail an assertion, of each target function
  , probes :: IORef [Probe]
  }

invariantContext :: App m => UnitTestOptions -> VM Concrete -> SolcContract -> SourceCache -> m InvariantContext
invariantContext opts vm testContract sourceCache = do
  targeted <- addrs <$> getter "targetContracts()" (AbiArrayDynamicType AbiAddressType)
  excluded <- addrs <$> getter "excludeContracts()" (AbiArrayDynamicType AbiAddressType)
  selected <- selectors <$> getter "targetSelectors()" selectorsType
  unselected <- selectors <$> getter "excludeSelectors()" selectorsType
  targetSenders <- addrs <$> getter "targetSenders()" (AbiArrayDynamicType AbiAddressType)
  excludedSenders <- addrs <$> getter "excludeSenders()" (AbiArrayDynamicType AbiAddressType)
  let senders = case filter (`notElem` excludedSenders) targetSenders of
        [] | null excludedSenders -> AnySender
           | otherwise -> NoneOf excludedSenders
        as -> OneOf as
  let testAddr = opts.testParams.address
      deployed = [a | (LitAddr a, c) <- Map.toList vm.env.contracts, LitAddr a /= testAddr, isJust (sourceOf c)]
      picked = filter (`notElem` excluded) (if null targeted then deployed else targeted)
      targetAddrs = List.nub (picked <> map fst selected)
      targetsOf a = case Map.lookup (LitAddr a) vm.env.contracts >>= sourceOf of
        Nothing -> Left $ "no source for target contract " <> Text.pack (show a)
        Just (c, name) -> Right
          [ (Target { addr = LitAddr a, contractName = name, sig = mkSig m }
            , all (symAbiArgSupported . snd) m.inputs)
          | m <- Map.elems c.abiMap
          -- as in Foundry, excludeSelector is ignored for a contract with targetSelector
          , case lookup a selected of
              Just sels -> selector m.methodSignature `elem` sels
              Nothing -> m.mutability `notElem` [Pure, View] && not (LitAddr a == testAddr && reserved m.name)
                && selector m.methodSignature `notElem` concat [sels | (a', sels) <- unselected, a' == a]
          ]
      candidates = concat <$> mapM targetsOf targetAddrs
      skipped = [t.contractName <> "." <> callSig t.sig | (t, False) <- either (const []) id candidates]
      targets = case map fst . filter snd <$> candidates of
        Right [] -> Left "no target functions to call"
        r -> r
  conf <- readConfig
  when conf.debug $ liftIO $ putStrLn $ "Invariant targets: " <> either Text.unpack
    (unwords . map (\t -> show t.addr <> ":" <> Text.unpack (t.contractName <> "." <> callSig t.sig))) targets
  let start = InvState { vm = symbolify vm & set #srcLookup (Just $ makeSrcLookup opts.dapp sourceCache), calls = [] }
  levels <- liftIO $ newIORef [[start]]
  visited <- liftIO $ newIORef (Set.singleton (stateKey start.vm))
  partials <- liftIO $ newIORef []
  probes <- liftIO $ newIORef []
  pure InvariantContext { setupVm = vm, targets, skipped, senders, levels, visited, partials, probes }
  where
    getter sig ty
      | Map.notMember (abiKeccak (encodeUtf8 sig)) testContract.abiMap = pure Nothing
      | otherwise = do
          res <- Stepper.interpret (Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo) vm $ do
            Stepper.evm $ abiCall opts.testParams (Left (sig, emptyAbi))
            Stepper.execFully
          pure $ case res of
            Right (ConcreteBuf bs) -> case decodeAbiValue (AbiTupleType (V.singleton ty)) (BSLazy.fromStrict bs) of
              AbiTuple v | [x] <- V.toList v -> Just x
              _ -> Nothing
            _ -> Nothing
    addrs = \case
      Just (AbiArrayDynamic _ v) -> [a | AbiAddress a <- V.toList v]
      _ -> []
    selectors = \case
      Just (AbiArrayDynamic _ v) -> Map.toList $ Map.fromListWith (flip (<>))
        [ (a, [bs | AbiBytes _ bs <- V.toList sels])
        | AbiTuple t <- V.toList v, [AbiAddress a, AbiArrayDynamic _ sels] <- [V.toList t] ]
      _ -> []
    selectorsType = AbiArrayDynamicType (AbiTupleType (V.fromList [AbiAddressType, AbiArrayDynamicType (AbiBytesType 4)]))
    -- an account without code has the code hash of every interface
    sourceOf c = case cloneOf c of
      Just impl -> do
        (src, name) <- Map.lookup (LitAddr impl) vm.env.contracts >>= sourceOf
        pure (src, name <> "(clone)")
      Nothing -> (\src -> (src, Text.takeWhileEnd (/= ':') src.contractName))
        <$> mfilter (not . BS.null . (.runtimeCode)) (findSrc c opts.dapp)
    -- an EIP-1167 minimal proxy, which has the functions of the contract it delegates to
    cloneOf c = case c.code of
      RuntimeCode (ConcreteRuntimeCode bs)
        | BS.length bs == 45
        , BS.take 10 bs == BS.pack "\x36\x3d\x3d\x37\x3d\x3d\x3d\x36\x3d\x73"
        , BS.drop 30 bs == BS.pack "\x5a\xf4\x3d\x82\x80\x3e\x90\x3d\x91\x60\x2b\x57\xfd\x5b\xf3"
        -> Just $ truncateToAddr (word (BS.take 20 (BS.drop 10 bs)))
      _ -> Nothing
    reserved name = any (`isPrefixOf` name) ["test", "prove", "check", "invariant_", "setUp", "afterInvariant"]

-- | The states reached by exactly @d@ calls, computed once per test contract
invariantLevel :: App m => UnitTestOptions -> InvariantContext -> [Target] -> Int -> m [InvState]
invariantLevel opts ctx targets d = do
  known <- liftIO $ readIORef ctx.levels
  case drop d known of
    (states:_) -> pure states
    [] -> do
      prev <- invariantLevel opts ctx targets (d - 1)
      let fetcher = Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo
      results <- mapM (nextStates opts.solvers (testPostcondition opts.checkFailBit False) fetcher
        (makeVeriOpts opts).iterConf opts.testParams.gasCall ctx.senders targets ctx.visited) prev
      let states = concatMap (\(a, _, _) -> a) results
      conf <- readConfig
      when conf.debug $ liftIO $ putStrLn $ "Invariant states after " <> show d <> " calls: "
        <> show (length states) <> " new"
      liftIO $ do
        modifyIORef ctx.levels (<> [states])
        modifyIORef ctx.partials (<> concatMap (\(_, b, _) -> b) results)
        modifyIORef ctx.probes $ \found -> foldl' (\ps p -> if any (sameFunction p) ps then ps else ps <> [p]) found
          (concatMap (\(_, _, c) -> c) results)
      pure states

sameFunction :: Probe -> Probe -> Bool
sameFunction a b = case (lastCall a, lastCall b) of
  (Just x, Just y) -> x.target.addr == y.target.addr && callSig x.target.sig == callSig y.target.sig
  _ -> False
  where lastCall p = listToMaybe (reverse p.state.calls)

-- | Checks an invariant in every state reached by at most 'invariantDepth' calls
-- Returns tuple of (No Cex, No warnings)
invariantRun :: forall m . App m => UnitTestOptions -> InvariantContext -> (Int, Int) -> Sig -> m (Bool, Bool)
invariantRun opts ctx (nth, numTests) sig@(Sig testName types) = do
  let cs = callSig sig
  liftIO $ opts.printOut $ "\x1b[96m[RUNNING]\x1b[0m " <> cs <> "\n"
  case ctx.targets of
    Left err -> do
      liftIO $ opts.printOut $ "   \x1b[31m[FAIL]\x1b[0m " <> testName <> ": " <> err <> "\n"
      pure (True, False)
    Right targets -> do
      (cdBuf, cdProps, caveats) <- symCalldata cs types [] (AbstractBuf "txdata")
      let check :: InvState -> m ([Text], Maybe (InvState, Expr End, SMTCex))
          check st = do
            vm <- liftIO $ stToIO $ execStateT (startCall opts.testParams.address opts.testParams.caller opts.testParams.gasCall testName (cdBuf, cdProps)) st.vm
            let fetcher = Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo
            (ends, results) <- verify opts.solvers fetcher (makeVeriOpts opts) vm (testPostcondition opts.checkFailBit False) Nothing
            let issues = [Text.pack str | (_, str) <- groupPartials vm.srcLookup vm.env.contracts ends]
                  <> [Text.pack (getUnknownStr u) | Unknown u <- results] <> [Text.pack e | Error e <- results]
            pure (issues, (\(leaf, cex) -> (st, leaf, cex)) <$> listToMaybe (mapMaybe extractCex results))
          go d issues
            | d > opts.invariantDepth = pure (Nothing, issues)
            | otherwise = do
                states <- invariantLevel opts ctx targets d
                let firstCex is [] = go (d + 1) is
                    firstCex is (st:rest) = check st >>= \case
                      (is', Just c) -> pure (Just c, is <> is')
                      (is', Nothing) -> firstCex (is <> is') rest
                firstCex issues states
      (found, issues) <- Progress.withPhase "test" ["test" JSON..= cs] (const []) $ do
        Progress.phaseTotal numTests
        Progress.phaseAt nth
        go 0 []
      framePartials <- liftIO $ readIORef ctx.partials
      probes <- filter (\p -> length p.state.calls <= opts.invariantDepth) <$> liftIO (readIORef ctx.probes)
      forM_ probes $ \p -> do
        validation <- validateProbe opts ctx p
        txt <- symFailure opts testName Nothing (callLines p.cex p.state.calls) (p.leaf, p.cex, validation)
        liftIO $ opts.printOut txt
      numStates <- liftIO $ sum . map length . take (opts.invariantDepth + 1) <$> readIORef ctx.levels
      let incomplete = not (null issues) || not (null framePartials) || not (null ctx.skipped)
      case found of
        Nothing | not (null probes) -> liftIO $ opts.printOut $ "   \x1b[31m[FAIL]\x1b[0m " <> testName <> "\n"
        Just (st, leaf, cex) -> do
          validation <- validateInvariantCex opts ctx st cex sig cdBuf
          txt <- symFailure opts testName (Just (cdBuf, types)) (callLines cex st.calls) (leaf, cex, validation)
          liftIO $ opts.printOut $ txt <> "   \x1b[31m[FAIL]\x1b[0m " <> testName <> "\n"
        Nothing -> liftIO $ opts.printOut $
          (if incomplete then "   \x1b[31m[FAIL]\x1b[0m " else "   \x1b[32m[PASS]\x1b[0m ")
          <> testName <> " (" <> Text.pack (show numStates) <> " states, up to "
          <> Text.pack (show opts.invariantDepth) <> " calls deep)\n"
      liftIO $ do
        unless (null issues) $ opts.printOut $
          indentLines 3 "\x1b[33m[WARNING]\x1b[0m some checks of the invariant were inconclusive:"
          <> Text.unlines (List.nub [indentLines 5 ("- " <> i) | i <- issues])
        unless (null framePartials) $ opts.printOut $
          indentLines 3 "\x1b[33m[WARNING]\x1b[0m the calls before the invariant were only partially explored:"
          <> Text.unlines [indentLines 5 ("- " <> Text.pack (show num) <> "x -> " <> Text.pack str)
                          | (num, str) <- groupPartials ctx.setupVm.srcLookup ctx.setupVm.env.contracts framePartials]
        unless (null ctx.skipped) $ opts.printOut $
          indentLines 3 "\x1b[33m[WARNING]\x1b[0m these functions were not called, their arguments cannot be symbolic:"
          <> Text.unlines [indentLines 5 ("- " <> f) | f <- ctx.skipped]
        printCaveats opts.printOut caveats
      pure (isNothing found && null probes, not (incomplete || not (null caveats)))

-- | Shows the calls of a counterexample, with their callers when they matter
callLines :: SMTCex -> [Call] -> [Text]
callLines cex calls = zipWith (<>) ("  calls:    " : repeat "            ") $ flip map calls $ \call ->
  let Sig _ argTypes = call.target.sig
      from = maybe "" (\a -> " from " <> Text.pack (show a)) (Map.lookup call.caller cex.addrs)
  in call.target.contractName <> "." <> prettyCalldata cex call.calldata (callSig call.target.sig) argTypes <> from

-- | Runs one call of a counterexample concretely
replayCall :: App m => UnitTestOptions -> SMTCex -> VM Concrete -> Call -> m (Err (VM Concrete, Either EvmError (Expr Buf)))
replayCall opts cex vm call = calldataFromCex cex call.calldata call.target.sig >>= \case
  Left e -> pure $ Left e
  Right bs -> do
    let fetcher = Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo
        time = maybe vm.block.timestamp Lit $ case call.timestamp of
          v@(Var _) -> Map.lookup v cex.vars
          _ -> Nothing
    (res, vm') <- Stepper.interpret fetcher (vm & set (#block % #timestamp) time) $ do
      Stepper.evm $ startCall call.target.addr (concreteAddr cex call.caller) opts.testParams.gasCall
        (callSig call.target.sig) (ConcreteBuf bs, [])
      res <- Stepper.execFully
      (res,) <$> Stepper.evm get
    pure $ Right (vm', res)

concreteAddr :: SMTCex -> Expr EAddr -> Expr EAddr
concreteAddr cex = \case
  a@(SymAddr _) -> LitAddr $ Map.findWithDefault 0xdeadbeef a cex.addrs
  a -> a

-- | The state after the given calls of a counterexample, run concretely after setUp()
replayCalls :: App m => UnitTestOptions -> InvariantContext -> SMTCex -> [Call] -> m (Err (VM Concrete))
replayCalls opts ctx cex calls = foldM replay (Right vm0) (zip [1 :: Int ..] calls)
  where
    vm0 = ctx.setupVm & set (#tx % #origin) (concreteAddr cex opts.testParams.origin)
    replay (Left e) _ = pure (Left e)
    replay (Right vm) (i, call) = replayCall opts cex vm call <&> \case
      Right (vm', Right _) -> Right vm'
      Right _ -> Left $ "call " <> show i <> " failed in the concrete replay"
      Left e -> Left e

-- | Replays the calls of a counterexample concretely, then checks the invariant
validateInvariantCex :: App m
  => UnitTestOptions -> InvariantContext -> InvState -> SMTCex -> Sig -> Expr Buf
  -> m (Err (Bool, Either EvmError (Expr Buf)))
validateInvariantCex opts ctx st cex sig cd = replayCalls opts ctx cex st.calls >>= \case
  Left e -> pure $ Left e
  Right vm -> do
    let fetcher = Fetch.oracle opts.solvers (Just opts.sess) opts.rpcInfo
    repro <- getReproFailure sig cd cex
    traverse (validateCex opts fetcher vm cex.addrs) repro

-- | Replays the calls of a probe concretely, the last one must fail an assertion
validateProbe :: App m => UnitTestOptions -> InvariantContext -> Probe -> m (Err (Bool, Either EvmError (Expr Buf)))
validateProbe opts ctx p = case reverse p.state.calls of
  [] -> pure $ Left "no calls"
  (lastCall:before) -> replayCalls opts ctx p.cex (reverse before) >>= \case
    Left e -> pure $ Left e
    Right vm -> replayCall opts p.cex vm lastCall <&> fmap (\(vm', res) ->
      (assertionFailedConc opts.checkFailBit res vm'.env.contracts, res))
