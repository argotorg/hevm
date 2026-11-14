-- | Replaying counterexamples on concrete VMs
module EVM.CexReplay where

import Prelude hiding (Foldable(..))

import Control.Monad (when, forM)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (liftIO, get)
import Data.Aeson ((.=))
import Data.Aeson qualified as JSON
import Data.Bits (shiftR)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Either (fromRight, rights)
import Data.Foldable (length, toList)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (Text)
import Data.Text qualified as T
import Optics.Core
import Witch (unsafeInto)

import EVM (makeVm, initialContract, defaultVMOpts, exec1, isPrecompileAddr, isPrecompileAddr')
import EVM.ABI
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Progress qualified as Progress
import EVM.Solvers (SolverGroup)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.SymExec (Postcondition, extractProps)
import EVM.SymExec.Cex (cexCalldata, defaultSymbolicValues, subModel, zeroTail)
import EVM.Types

data CexReplay
  = Validated !Text !Text        -- ^ the concrete outcomes of A and B differ
  | NotReproducible !Text !Text  -- ^ the concrete outcomes are the same
  | CannotReplay !Text
  deriving (Show, Eq)

replayTag :: CexReplay -> Text
replayTag = \case
  Validated {} -> "validated"
  NotReproducible {} -> "not reproducible"
  CannotReplay why -> "cannot replay: " <> why

-- | Replays an equivalence counterexample on concrete VMs running A and B, set
-- up like 'loadSymVM' with the model's values, and compares what they do:
-- return data or error, and the final storage of the called contract.
replayEqCex :: App m => SolverGroup -> Bool -> ByteString -> ByteString -> Expr Buf -> SMTCex -> m CexReplay
replayEqCex solvers create codeA codeB cd cex
  | create = pure $ CannotReplay "contract creation is not replayed"
  | Just (_, len) <- Map.lookup cd cex.buffers >>= zeroTail = pure $ CannotReplay $ "calldata of " <> T.pack (show len) <> " bytes"
  | Left why <- stubs = pure $ CannotReplay why
  | isPrecompileAddr entry = pure $ CannotReplay "the model puts the contract at a precompile address"
  | otherwise = case cexCalldata cd cex of
      Nothing -> pure $ CannotReplay "calldata is not concrete"
      Just calldata -> do
        Progress.emit "replay-stubs" [ "calls" .= map logCall (rights cex.unknownCalls) ]
        a <- run "A" codeA calldata
        b <- run "B" codeB calldata
        -- forced, or the replay keeps both final VMs alive
        pure $! case (a, b) of
          (Left e, _) -> CannotReplay e
          (_, Left e) -> CannotReplay e
          (Right ra, Right rb) -> (if ra == rb then NotReproducible else Validated) (outcome rb ra) (outcome ra rb)
  where
    entry = eqCexEntry cex
    stubs = stubAccounts entry cex.unknownCalls
    logCall m = JSON.object
      [ "callee" .= T.pack (show m.callee), "calldata" .= showBytes (BS.take 256 m.calldata)
      , "success" .= m.success, "returndata" .= showBytes (BS.take 256 m.returndata), "returndataLength" .= m.returndataLength ]
    run :: App m => Text -> ByteString -> ByteString -> m (Either Text (Either EvmError (Expr Buf), Either Text (Map W256 W256), Map (Expr EAddr) W256, Map (Expr EAddr) ReplayAccount))
    run label code calldata = do
      vm <- liftIO $ stToIO $ makeVm $ eqReplayVmOpts cex (fromRight [] stubs) code calldata
      conf <- readConfig
      (steps, lastSteps, end) <- Stepper.interpret (Fetch.oracle solvers Nothing Fetch.noRpc) vm (runTraced conf 32)
      Progress.emit "replay-run"
        [ "program" .= label, "result" .= T.pack (show end.result), "steps" .= steps
        , "trail" .= [(showAddr a, pc) | (a, pc) <- toList lastSteps] ]
      let finalStore = case (.storage) <$> Map.lookup entry end.env.contracts of
            Just (ConcreteStore m) -> Right (Map.filter (/= 0) m)
            s -> Left (T.pack (show s))
          balances = Map.mapMaybe (\c -> case c.balance of Lit v -> Just v; _ -> Nothing) end.env.contracts
          -- the symbolic check compares these too; the entrypoint's code is A or B by construction
          accounts = Map.mapWithKey (\a c -> ReplayAccount
            { code = if a == entry then Nothing else case c.code of
                RuntimeCode (ConcreteRuntimeCode bs) -> Just bs
                _ -> Nothing
            , store = if a == entry then Nothing else case c.storage of
                ConcreteStore m -> Just (Map.filter (/= 0) m)
                _ -> Nothing
            , nonce = c.nonce }) end.env.contracts
      pure $ case end.result of
        Just (VMSuccess out) -> Right (Right out, finalStore, balances, accounts)
        Just (VMFailure e) -> Right (Left e, finalStore, balances, accounts)
        r -> Left $ "concrete run did not finish: " <> T.pack (show r)
    -- the balances are shown where they differ from the other program's
    outcome (_, _, otherBals, otherAccts) (res, st, bals, accts) = T.intercalate ", " $ (case res of
        Right (ConcreteBuf bs) -> ["Return " <> showBytes bs] <> storage
        Right _ -> ["Return (symbolic data)"] <> storage
        Left (Revert (ConcreteBuf bs)) -> ["Revert " <> showRevertData bs]
        Left e -> [T.pack (show e)])
      <> ["balance " <> showAddr a <> "=" <> showW v | (a, v) <- Map.toList bals, Map.lookup a otherBals /= Just v]
      <> [showAccount a acct | (a, acct) <- Map.toList accts, Map.lookup a otherAccts /= Just acct]
      where
        showAccount a acct = "account " <> showAddr a <> T.concat
          [ maybe "" ((" code " <>) . showBytes) acct.code
          , maybe "" (\m -> if Map.null m then "" else " storage " <> T.unwords [showW k <> "=" <> showW v | (k, v) <- take 8 (Map.toList m)]) acct.store
          , maybe "" ((" nonce " <>) . T.pack . show) acct.nonce ]
        storage = case st of
          Right m | Map.null m -> []
                  | otherwise -> ["storage " <> T.intercalate " " [showW k <> "=" <> showW v | (k, v) <- take 8 (Map.toList m)]
                                  <> (if Map.size m > 8 then " ..." else "")]
          Left _ -> ["storage symbolic"]
        showW :: W256 -> Text
        showW = T.pack . show

    -- the derived Show of an Expr EAddr would print "LitAddr 0x..."
    showAddr = \case
      LitAddr a -> T.pack (show a)
      a -> T.pack (show a)

data ReplayAccount = ReplayAccount { code :: Maybe ByteString, store :: Maybe (Map W256 W256), nonce :: Maybe W64 }
  deriving (Eq)

eqCexEntry :: SMTCex -> Expr EAddr
eqCexEntry cex = maybe (LitAddr 0xacab) LitAddr (Map.lookup (SymAddr "entrypoint") cex.addrs)

-- | The concrete VM 'replayEqCex' runs @code@ in, set up like 'loadSymVM' with the model's values
eqReplayVmOpts :: SMTCex -> [(Expr EAddr, Contract)] -> ByteString -> ByteString -> VMOpts Concrete
eqReplayVmOpts cex others code calldata = (defaultVMOpts @Concrete)
  { contract = set #balance (Lit (ctx (Balance (SymAddr "entrypoint")) cex.txContext))
      (initialContract (RuntimeCode (ConcreteRuntimeCode code))) { storage = store, origStorage = store }
  , otherContracts = others
  , calldata = (ConcreteBuf calldata, [])
  , value = Lit (ctx TxValue cex.txContext)
  , address = eqCexEntry cex
  , caller = addr "caller" (LitAddr 0xcafe0001)
  , origin = addr "origin" (LitAddr 0xcafe0002)
  , coinbase = addr "coinbase" (LitAddr 0)
  , timestamp = Lit (ctx Timestamp cex.blockContext)
  , number = Lit (ctx BlockNumber cex.blockContext)
  , gas = 0xffffffffffffffff
  , gaslimit = 0xffffffffffffffff
  , prevRandao = Lit (ctx PrevRandao cex.blockContext)
  , baseFee = Lit (ctx BaseFee cex.blockContext)
  }
  where
    addr name def = maybe def LitAddr (Map.lookup (SymAddr name) cex.addrs)
    ctx k m = Map.findWithDefault 0 k m
    store = ConcreteStore $ Map.findWithDefault mempty (SymAddr "entrypoint") cex.store

-- | Replays a counterexample of @leaf@ on a concrete VM set up like @vm0@ with
-- the model's values. Right True if the concrete run violates @post@ as well.
replaySymCex :: App m => Fetch.Fetcher Concrete m -> Postcondition -> VM Symbolic -> Expr End -> SMTCex -> m (Either Text Bool)
replaySymCex fetcher post vm0 leaf cex' = case setup of
  Left why -> pure (Left why)
  Right opts -> do
    vm <- liftIO $ stToIO $ makeVm opts
    conf <- readConfig
    (_, _, end) <- Stepper.interpret fetcher vm (runTraced conf 32)
    let ctx = TraceContext mempty mempty mempty
    pure $ case end.result of
      Just (VMFailure e) -> violated (Failure [] ctx e)
      Just (VMSuccess out) -> violated (Success [] ctx out mempty)
      r -> Left $ "concrete run did not finish: " <> T.pack (show r)
  where
    cex = cex' { unknownCalls = modelUnknownCalls cex' (extractProps leaf) }
    violated end = case Expr.simplifyProp (post vm0 end) of
      PBool b -> Right (not b)
      p -> Left $ "postcondition is not concrete on the replay: " <> T.pack (show p)
    concrete :: Expr a -> Err (Expr a)
    concrete = fmap Expr.simplify . defaultSymbolicValues . subModel cex
    concWord :: Text -> Expr EWord -> Either Text W256
    concWord what e = case concrete e of
      Right (Lit w) -> Right w
      r -> Left $ "the model leaves the " <> what <> " symbolic: " <> T.pack (show r)
    concStore :: Expr Storage -> Either Text (Expr Storage)
    concStore st = case concrete st of
      Right (ConcreteStore m) -> Right (ConcreteStore m)
      -- the model has no store for storage that is never read
      Right (AbstractStore {}) -> Right (ConcreteStore mempty)
      _ -> Left "the model leaves the storage symbolic"
    addr :: Text -> Expr EAddr -> Either Text (Expr EAddr)
    addr what e = case concrete e of
      Right (LitAddr a) -> Right (LitAddr a)
      _ -> Left $ "the model leaves the " <> what <> " address symbolic"
    setup = do
      let entry = vm0.state.contract
      c <- maybe (Left "no contract at the entry address") Right (Map.lookup entry vm0.env.contracts)
      code <- case c.code of
        RuntimeCode (ConcreteRuntimeCode bs) -> Right bs
        InitCode {} -> Left "contract creation is not replayed"
        _ -> Left "the code is symbolic"
      calldata <- maybe (Left "calldata is not concrete") Right (cexCalldata vm0.state.calldata cex)
      store <- concStore c.storage
      balance <- concWord "balance" c.balance
      address <- addr "contract" entry
      stubs <- stubAccounts address cex.unknownCalls
      others <- fmap catMaybes . forM (Map.toList (Map.delete entry vm0.env.contracts)) $ \(a, oc) ->
        case oc.code of
          RuntimeCode (ConcreteRuntimeCode bs) -> do
            a' <- addr "account" a
            st <- concStore oc.storage
            bal <- concWord "account balance" oc.balance
            pure $ Just (a', (initialContract (RuntimeCode (ConcreteRuntimeCode bs)))
              { storage = st, origStorage = st, balance = Lit bal, nonce = oc.nonce
              , external = oc.external, chainStorage = oc.chainStorage })
          -- e.g. the abstract origin account
          _ -> pure Nothing
      when (isPrecompileAddr address) $ Left "the model puts the contract at a precompile address"
      caller <- addr "caller" vm0.state.caller
      origin <- addr "origin" vm0.tx.origin
      coinbase <- addr "coinbase" vm0.block.coinbase
      value <- concWord "callvalue" vm0.state.callvalue
      timestamp <- concWord "timestamp" vm0.block.timestamp
      number <- concWord "block number" vm0.block.number
      prevRandao <- concWord "prevrandao" vm0.block.prevRandao
      baseFee <- concWord "basefee" vm0.block.baseFee
      pure $ (defaultVMOpts @Concrete)
        { contract = (initialContract (RuntimeCode (ConcreteRuntimeCode code)))
            -- fetched accounts hold only the slots read so far, the replay fetches the rest
            { storage = store, origStorage = store, balance = Lit balance, nonce = c.nonce
            , external = c.external, chainStorage = c.chainStorage }
        , otherContracts = stubs <> filter ((`notElem` map fst stubs) . fst) others
        , calldata = (ConcreteBuf calldata, [])
        , value = Lit value
        , address
        , caller
        , origin
        , coinbase
        , timestamp = Lit timestamp
        , number = Lit number
        , gas = 0xffffffffffffffff
        , gaslimit = vm0.tx.gaslimit
        , blockGaslimit = vm0.block.gaslimit
        , gasprice = vm0.tx.gasprice
        , priorityFee = vm0.tx.priorityFee
        , chainId = vm0.env.chainId
        , maxCodeSize = vm0.block.maxCodeSize
        , schedule = vm0.block.schedule
        , prevRandao = Lit prevRandao
        , baseFee = Lit baseFee
        }

-- | 'Stepper.runFully' that also counts the steps and keeps the code address and
-- pc of the last @n@ of them
runTraced :: Config -> Int -> Stepper Concrete (Int, Seq (Expr EAddr, Int), VM Concrete)
runTraced conf n = go 0 mempty
  where
    go steps lastSteps = do
      (steps', lastSteps', vm) <- Stepper.evm (stepAll steps lastSteps)
      case vm.result of
        Just (HandleEffect (Query q)) -> Stepper.wait q >> go steps' lastSteps'
        _ -> pure (steps', lastSteps', vm)
    stepAll !steps !lastSteps = do
      vm <- get
      case vm.result of
        Nothing -> do
          exec1 conf
          stepAll (steps + 1) (Seq.drop (Seq.length lastSteps + 1 - n) (lastSteps Seq.|> (vm.state.codeContract, vm.state.pc)))
        Just _ -> pure (steps, lastSteps, vm)

-- | The calls to unknown code in @props@, with the values the model gives them
modelUnknownCalls :: SMTCex -> [Prop] -> [Either Text UnknownCall]
modelUnknownCalls cex = concatMap pcalls
  where
    pcalls = \case
      PAnd a b -> pcalls a <> pcalls b
      PCall i ok out _ -> [modelCall i ok out]
      _ -> []
    modelCall i ok out = do
      callee <- concreteWord "target" i.target
      inLen <- concreteWord "calldata length" i.callDataLen
      calldata <- concreteBytes "calldata" inLen i.callData
      okWord <- concreteWord "success flag" ok
      outLen <- concreteWord "returndata length" (Expr.bufLength out)
      returndata <- compactBytes "returndata" outLen out
      pure UnknownCall { callee = truncateToAddr callee, calldata, success = okWord /= 0, returndata, returndataLength = unsafeInto outLen }
    inModel :: Expr a -> Err (Expr a)
    inModel e = Expr.concKeccakSimpExpr <$> defaultSymbolicValues (subModel cex e)
    concreteWord :: Text -> Expr EWord -> Either Text W256
    concreteWord what e = case inModel e of
      Right (Lit w) -> Right w
      _ -> noModel what
    concreteBytes :: Text -> W256 -> Expr Buf -> Either Text ByteString
    concreteBytes what len e = case inModel e of
      -- a model can pick lengths like 2^255; don't allocate them
      Right (ConcreteBuf bs) | len <= 2 ^ (24 :: Int) ->
        -- a ConcreteBuf reads zero past its end
        let n = unsafeInto len in Right $ BS.take n (bs <> BS.replicate (n - BS.length bs) 0)
      _ -> noModel what
    noModel what = Left $ "the " <> what <> " of a call to unknown code has no concrete model"
    -- the solver often makes return data 16 MB long, too much to keep for every
    -- call, so only what the model writes over a zero base is kept
    compactBytes :: Text -> W256 -> Expr Buf -> Either Text ByteString
    compactBytes what len = \case
      b@(AbstractBuf _) | len <= 2 ^ (24 :: Int), Just (EVM.Types.Comp c) <- Map.lookup b cex.buffers, Just ws <- written mempty c ->
        Right $ BS.dropWhileEnd (== 0) $ BS.pack [Map.findWithDefault 0 i ws | i <- takeWhile (< len) [0 .. maybe 0 fst (Map.lookupMax ws)]]
      e -> BS.dropWhileEnd (== 0) <$> concreteBytes what len e
    -- the outermost write to an index is the last one
    written ws = \case
      Write byte idx next -> written (Map.insertWith (\_ old -> old) idx byte ws) next
      Base 0 _ -> Just ws
      _ -> Nothing

-- | Accounts at the callees of the unknown calls, whose code gives each call the
-- answer the model gives it
stubAccounts :: Expr EAddr -> [Either Text UnknownCall] -> Either Text [(Expr EAddr, Contract)]
stubAccounts entry calls = do
  models <- sequence calls
  let byCallee = Map.fromListWith (flip (<>)) [(m.callee, [(m.calldata, (m.success, m.returndata, m.returndataLength))]) | m <- models]
  forM (Map.toList byCallee) $ \(a, answers) -> do
    when (isPrecompileAddr' a) $ Left $ "a call to unknown code goes to precompile " <> T.pack (show a)
    when (LitAddr a == entry) $ Left "a call to unknown code goes to the called contract itself"
    -- a state-changing call in between can give equal calls different results
    answerByCalldata <- forM (Map.toList (Map.fromListWith (flip (<>)) [(i, [r]) | (i, r) <- answers])) $ \case
      (i, r : rest) | all (== r) rest -> Right (i, r)
      _ -> Left $ "the model answers the same call to " <> T.pack (show a) <> " differently"
    pure (LitAddr a, initialContract (RuntimeCode (ConcreteRuntimeCode (stubCode answerByCalldata))))

-- | Code that answers each calldata with its returndata, by RETURN if the call
-- succeeds and REVERT if not, and reverts on any other calldata. A returndata is
-- given up to its last nonzero byte, and its length. Calldata is matched by its
-- hash, which fits in one PUSH32 whatever its length. All jump targets and
-- offsets are PUSH4s, so every piece has a fixed size and they can be computed
-- before the code is assembled.
stubCode :: [(ByteString, (Bool, ByteString, Int))] -> ByteString
stubCode answers = mconcat $ [hashCalldata] <> zipWith dispatch answers answerPCs <> [noMatch]
  <> zipWith answer answers returndataOffsets <> [out | (_, (_, out, _)) <- answers]
  where
    -- CALLDATACOPY(0, 0, CALLDATASIZE), KECCAK256(0, CALLDATASIZE)
    hashCalldata = BS.pack [0x36, 0x60, 0, 0x60, 0, 0x37, 0x36, 0x60, 0, 0x20]
    -- DUP1 PUSH32 hash EQ PUSH4 dest JUMPI: 41 bytes
    dispatch (i, _) dest = BS.pack [0x80, 0x7f] <> keccakBytes i <> BS.pack [0x14, 0x63] <> be32 dest <> BS.pack [0x57]
    noMatch = BS.pack [0x60, 0, 0x60, 0, 0xfd]
    -- JUMPDEST, CODECOPY(CALLDATASIZE, off, size), RETURN(CALLDATASIZE, len) or
    -- REVERT(CALLDATASIZE, len): 20 bytes. Past the copy of the calldata, memory is zero.
    answer (_, (ok, out, len)) off = BS.pack [0x5b, 0x63] <> be32 (BS.length out) <> BS.pack [0x63] <> be32 off
      <> BS.pack [0x36, 0x39, 0x63] <> be32 len <> BS.pack [0x36, if ok then 0xf3 else 0xfd]
    n = length answers
    answersStart = BS.length hashCalldata + 41 * n + BS.length noMatch
    answerPCs = [answersStart + 20 * k | k <- [0 .. n - 1]]
    returndataOffsets = scanl (+) (answersStart + 20 * n) [BS.length out | (_, (_, out, _)) <- answers]
    be32 :: Int -> ByteString
    be32 x = BS.pack [fromIntegral (x `shiftR` k) | k <- [24, 16, 8, 0]]

-- | Replays every counterexample, as a phase of its own in the progress log.
replayEqCexes :: App m => SolverGroup -> Bool -> ByteString -> ByteString -> Expr Buf -> [(SMTCex, String)] -> m [(SMTCex, String, CexReplay)]
replayEqCexes solvers create codeA codeB cd cexes =
  Progress.withPhase "replay" ["cexes" .= length cexes] summary $ do
    Progress.phaseTotal (length cexes)
    forM (zip [(0 :: Int) ..] cexes) $ \(i, (c, d)) -> do
      r <- replayEqCex solvers create codeA codeB cd c
      Progress.emit "replay"
        [ "cex" .= i, "kind" .= takeWhile (/= '\n') d, "result" .= replayTag r
        , "selector" .= fmap (\bs -> "0x" <> T.pack (bsToHex (BS.take 4 bs))) (cexCalldata cd c) ]
      Progress.phaseTick
      pure (c, d, r)
  where
    summary rs =
      [ "validated" .= length [() | (_, _, Validated {}) <- rs]
      , "notReproducible" .= length [() | (_, _, NotReproducible {}) <- rs]
      , "cannotReplay" .= length [() | (_, _, CannotReplay _) <- rs] ]

showBytes :: ByteString -> Text
showBytes bs = if BS.null bs then "(empty)" else "0x" <> T.pack (bsToHex bs)

-- | Revert data in hex, decoded if it is an Error(string) or a Panic(uint256).
showRevertData :: ByteString -> Text
showRevertData bs = showBytes bs <> case BS.splitAt 4 bs of
  ("\x08\xc3\x79\xa0", rest) | (CAbi [AbiString str], "") <- decodeBuf [AbiStringType] (ConcreteBuf rest) ->
    " = Error(" <> T.pack (show str) <> ")"
  ("\x4e\x48\x7b\x71", rest) | (CAbi [AbiUInt _ code], "") <- decodeBuf [AbiUIntType 256] (ConcreteBuf rest) ->
    " = Panic(" <> T.pack (show code) <> ")"
  _ -> ""
