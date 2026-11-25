module EVM.Invariant.DriverTests (tests) where

import Control.Monad (forM_)
import Data.Map qualified as Map
import Data.Maybe (isNothing)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Optics.Core

import EVM (initialContract, symbolify)
import EVM.ABI (AbiType(..), AbiValue(..), Sig(..), selector)
import EVM.Effects (App)
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Invariant
import EVM.Invariant.Driver
import EVM.Solidity (solidity)
import EVM.SymExec (Postcondition, VeriOpts(..), checkAssertions, defaultVeriOpts)
import EVM.Test.Helpers (assertBoolM, assertEqualM, loadVM, test, withDefaultSolver)
import EVM.Types

tests :: TestTree
tests = testGroup "framework-independent driver"
  [ test "native property, cached depths and concrete replay" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          target = Target initial.state.contract "Native" (Sig "advance" [AbiUIntType 256])
          options = ExplorationConfig [target] (OneOf [0x10000, 0x20000])
            ((defaultCallConfig maxBound) { maxTimeDelay = Just 3, maxBlockDelay = Just 2, callerIsOrigin = True }) (\_ _ -> PBool True) False
          check = property initial "valid"
          search cache depth = searchInvariant solvers fetcher defaultVeriOpts cache (0, depth) check
      cache <- newExploration options (symbolify initial)
      one <- search cache 1
      assertBoolM "one call is insufficient" (isNothing one.counterexample)
      assertEqualM "complete at depth one" ([], 0) (one.issues, length one.partials)
      two <- search cache 2
      assertEqualM "complete at depth two" ([], 0) (two.issues, length two.partials)
      cex <- maybe (internalError "expected a two-call counterexample") pure two.counterexample
      calls <- concretizeCalls initial.block cex.model cex.state.calls >>= either internalError pure
      assertEqualM "two solved arguments" [[AbiUInt 256 1], [AbiUInt 256 2]] (map (.arguments) calls)
      forM_ calls $ \call -> do
        assertEqualM "origin follows each sender" call.caller call.origin
        assertBoolM "configured sender" (call.caller `elem` [0x10000, 0x20000])
        assertBoolM "bounded per-call delays" (fst call.delay <= 3 && snd call.delay <= 2)
      replayed <- replayCalls Fetch.noRpcConcreteFetcher maxBound initial cex.model cex.state.calls
        >>= either internalError pure
      replayedCheck <- checkInvariant solvers fetcher defaultVeriOpts check (InvState (symbolify replayed) [])
      assertBoolM "the replay still fails" (not $ isNothing replayedCheck.counterexample)
      (before, diagnostics) <- explorationStatus cache
      assertEqualM "no transition issues" [] diagnostics.issues
      assertEqualM "no partial transitions" 0 (length diagnostics.partials)
      context <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) (property initial "context")
      assertBoolM "check caller and origin are independent of the sequence" (isNothing context.counterexample)
      let invariant = (property initial "invariant_valid" :: Check) { postcondition = checkAssertions [0x01] }
      asserted <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) invariant
      assertionCex <- maybe (internalError "expected an assertion-style invariant failure") pure asserted.counterexample
      assertEqualM "assertion invariant uses the same two-call frontier" 2 (length assertionCex.state.calls)
      assertBoolM "assertion check reverts" (case assertionCex.leaf of Failure _ _ (Revert _) -> True; _ -> False)
      let expectedRevert = (property initial "reverting_check" :: Check)
            { postcondition = \_ -> \case Failure _ _ (Revert _) -> PBool True; _ -> PBool False }
      reverts <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 1) expectedRevert
      assertBoolM "expected-revert property holds at the first depth" (isNothing reverts.counterexample)
      returns <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) expectedRevert
      returned <- maybe (internalError "expected a non-reverting counterexample") pure returns.counterexample
      assertEqualM "expected-revert property uses the same two-call frontier" 2 (length returned.state.calls)
      assertBoolM "successful return violates the expected-revert property" (case returned.leaf of Success {} -> True; _ -> False)
      isolated <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) (property initial "mutating_check")
      assertBoolM "mutating check passes" (isNothing isolated.counterexample)
      unchanged <- search cache 2
      unchangedCex <- maybe (internalError "property counterexample disappeared") pure unchanged.counterexample
      assertEqualM "check writes cannot corrupt the shared frontier" 2 (length unchangedCex.state.calls)
      (after, _) <- explorationStatus cache
      assertEqualM "frontiers are reused" before after
  , test "successful transaction postconditions and isolated properties share a frontier" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          target = Target initial.state.contract "Native" (Sig "advanceAndReport" [AbiUIntType 256])
          post :: Postcondition
          post vm leaf = case leaf of
            Failure {} -> PBool True
            _ -> returnsTrue vm leaf
          options = ExplorationConfig [target] (OneOf [0x10000]) (defaultCallConfig maxBound) post False
      cache <- newExploration options (symbolify initial)
      one <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 1) (property initial "valid")
      assertBoolM "property holds after one call" (isNothing one.counterexample)
      (_, first) <- explorationStatus cache
      assertEqualM "transaction postcondition holds after one call" 0 (length first.probes)
      two <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) (property initial "valid")
      assertBoolM "isolated property fails after two calls" (not $ isNothing two.counterexample)
      (_, transitions) <- explorationStatus cache
      assertEqualM "complete exploration and checks" ([], 0)
        (one.issues <> two.issues <> transitions.issues, length one.partials + length two.partials + length transitions.partials)
      probe <- case transitions.probes of [p] -> pure p; _ -> internalError "expected a successful-call violation"
      assertBoolM "violation is a successful EVM call" (case probe.leaf of Success {} -> True; _ -> False)
      concrete <- concretizeCalls initial.block probe.cex probe.state.calls >>= either internalError pure
      assertEqualM "counterexample includes both calls" [[AbiUInt 256 1], [AbiUInt 256 2]] (map (.arguments) concrete)
      replayed <- replayCalls Fetch.noRpcConcreteFetcher maxBound initial probe.cex probe.state.calls >>= either internalError pure
      case replayed.result of
        Just (VMSuccess buf) -> assertEqualM "last call returned false" (Lit 0) (Expr.simplify $ Expr.readWord (Lit 0) buf)
        _ -> internalError "expected successful concrete replay"
  , test "parameterized view assertions follow mixed transaction sequences" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          targets = [Target initial.state.contract "Native" (Sig name [AbiUIntType 256]) | name <- ["advance", "assertBelow"]]
          options = ExplorationConfig targets (OneOf [0x10000])
            ((defaultCallConfig maxBound) { callerIsOrigin = True }) (checkAssertions [0x01]) False
      cache <- newExploration options (symbolify initial)
      _ <- exploreLevel solvers fetcher defaultVeriOpts.iterConf cache 2
      (_, two) <- explorationStatus cache
      assertEqualM "two transactions cannot reach the assertion" 0 (length two.probes)
      _ <- exploreLevel solvers fetcher defaultVeriOpts.iterConf cache 3
      (_, three) <- explorationStatus cache
      assertEqualM "complete mixed-method search" ([], 0) (three.issues, length three.partials)
      probe <- case three.probes of [p] -> pure p; _ -> internalError "expected a three-call assertion failure"
      concrete <- concretizeCalls initial.block probe.cex probe.state.calls >>= either internalError pure
      assertEqualM "mixed-method counterexample"
        [Sig "advance" [AbiUIntType 256], Sig "advance" [AbiUIntType 256], Sig "assertBelow" [AbiUIntType 256]]
        (map (.sig) concrete)
      assertEqualM "independent symbolic arguments" [[AbiUInt 256 1], [AbiUInt 256 2], [AbiUInt 256 42]] (map (.arguments) concrete)
      setup <- replayCalls Fetch.noRpcConcreteFetcher maxBound initial probe.cex (take 2 probe.state.calls) >>= either internalError pure
      case concrete of
        [_, _, finalCall] -> do
          (_, outcome) <- replayCall Fetch.noRpcConcreteFetcher maxBound setup finalCall
          assertBoolM "assertion failure replays" (case outcome of Left (Revert _) -> True; _ -> False)
        _ -> internalError "expected three concrete transactions"
  , test "context-only steps preserve accounts and support optional property checks" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          calls = (defaultCallConfig maxBound)
            { maxTimeDelay = Just 1, maxBlockDelay = Just 1, allowNoCalls = True }
          -- Waiting requires neither a target nor a sender. Pruning must not
          -- discard it just because storage and balances are unchanged.
          options = ExplorationConfig [] (OneOf []) calls (\_ _ -> PBool False) True
          check = property initial "beforeDeadline"
      cache <- newExploration options (symbolify initial)
      one <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 1) check
      assertBoolM "one bounded wait is insufficient" (isNothing one.counterexample)
      skipped <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2)
        ((check :: Check) { checkAfterNoCall = False })
      assertBoolM "clients may check only after contract calls" (isNothing skipped.counterexample)
      two <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) check
      cex <- maybe (internalError "expected two waits") pure two.counterexample
      concrete <- concretizeCalls initial.block cex.model cex.state.calls >>= either internalError pure
      assertEqualM "two independent bounded delays" [(1, 1), (1, 1)] (map (.delay) concrete)
      assertBoolM "no ABI calls were invented" (all (\case ConcreteNoCall{} -> True; _ -> False) concrete)
      replayed <- replayCalls Fetch.noRpcConcreteFetcher maxBound initial cex.model cex.state.calls >>= either internalError pure
      assertEqualM "accounts, balances and nonces are unchanged" initial.env.contracts replayed.env.contracts
      assertEqualM "origin is unchanged" initial.tx.origin replayed.tx.origin
      assertEqualM "no gas was consumed" initial.burned replayed.burned
      assertEqualM "replayed timestamp and block number" (Lit 2, Lit 2) (replayed.block.timestamp, replayed.block.number)
      (sizes, transitions) <- explorationStatus cache
      assertEqualM "wait contexts are retained even with pruning requested" [1, 1, 1] sizes
      assertEqualM "no transition postcondition was run for a wait" 0 (length transitions.probes)
      assertEqualM "complete wait exploration" ([], 0) (transitions.issues <> two.issues, length transitions.partials + length two.partials)
      forM_ [calls { allowNoCalls = False }, calls { maxTimeDelay = Just 0, maxBlockDelay = Just 0 }] $ \config -> do
        stopped <- newExploration ((options :: ExplorationConfig) { callConfig = config }) (symbolify initial)
        result <- searchInvariant solvers fetcher defaultVeriOpts stopped (0, 2) check
        assertBoolM "disabled or zero-delay waits cannot reach the deadline" (isNothing result.counterexample)
        (levels, _) <- explorationStatus stopped
        assertEqualM "no useless wait successors" [1, 0] levels
  , test "a bounded wait reaches an assertion beyond the per-call delay" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          target = Target initial.state.contract "Native" (Sig "timedAssert" [])
          calls = (defaultCallConfig maxBound)
            { maxTimeDelay = Just 1, maxBlockDelay = Just 1, allowNoCalls = True, callerIsOrigin = True }
          options = ExplorationConfig [target] (OneOf [0x10000]) calls (checkAssertions [0x01]) True
      cache <- newExploration options (symbolify initial)
      _ <- exploreLevel solvers fetcher defaultVeriOpts.iterConf cache 1
      (_, one) <- explorationStatus cache
      assertEqualM "the initial call can only revert its precondition" 0 (length one.probes)
      _ <- exploreLevel solvers fetcher defaultVeriOpts.iterConf cache 2
      (_, two) <- explorationStatus cache
      assertEqualM "complete assertion search" ([], 0) (two.issues, length two.partials)
      probe <- case two.probes of [p] -> pure p; _ -> internalError "expected wait then assertion"
      concrete <- concretizeCalls initial.block probe.cex probe.state.calls >>= either internalError pure
      case concrete of
        [wait@ConcreteNoCall{}, call@ConcreteCall{}] -> do
          assertEqualM "both steps respect the configured bounds" [(1, 1), (1, 1)] (map (.delay) concrete)
          assertEqualM "no-argument assertion" (Sig "timedAssert" []) call.sig
          (waited, _) <- replayCall Fetch.noRpcConcreteFetcher maxBound initial wait
          (_, outcome) <- replayCall Fetch.noRpcConcreteFetcher maxBound waited call
          assertBoolM "assertion replays after waiting" (case outcome of Left (Revert _) -> True; _ -> False)
        _ -> internalError "expected one wait and one contract call"
      forM_ [calls { allowNoCalls = False }, calls { maxTimeDelay = Just 0 }, calls { maxBlockDelay = Just 0 }] $ \config -> do
        limited <- newExploration ((options :: ExplorationConfig) { callConfig = config }) (symbolify initial)
        _ <- exploreLevel solvers fetcher defaultVeriOpts.iterConf limited 2
        (_, result) <- explorationStatus limited
        assertEqualM "both time and block increments are needed" 0 (length result.probes)
  , test "empty sender list has no successors" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let target = Target initial.state.contract "Native" (Sig "advance" [AbiUIntType 256])
          options = ExplorationConfig [target] (OneOf []) (defaultCallConfig maxBound) (\_ _ -> PBool True) False
      cache <- newExploration options (symbolify initial)
      result <- searchInvariant solvers (Fetch.oracle solvers Nothing Fetch.noRpc) defaultVeriOpts
        cache (1, 100) (property initial "valid")
      assertBoolM "no counterexample" (isNothing result.counterexample)
      (sizes, _) <- explorationStatus cache
      assertEqualM "stops at an empty frontier" [1, 0] sizes
  , test "context-only changes survive without storage pruning" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let target = Target initial.state.contract "Native" (Sig "noop" [])
          options = ExplorationConfig [target] (OneOf [0x10000])
            ((defaultCallConfig maxBound) { maxTimeDelay = Just 1, maxBlockDelay = Just 1, callerIsOrigin = True }) (\_ _ -> PBool True) False
      cache <- newExploration options (symbolify initial)
      result <- searchInvariant solvers (Fetch.oracle solvers Nothing Fetch.noRpc) defaultVeriOpts
        cache (1, 1) (property initial "clock")
      assertBoolM "time or number can falsify the property without a storage write" (not $ isNothing result.counterexample)
  , test "delays account for preceding warp and roll cheatcodes" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let target = Target initial.state.contract "Native" (Sig "jump" [])
          options = ExplorationConfig [target] (OneOf [0x10000])
            ((defaultCallConfig maxBound) { maxTimeDelay = Just 0, maxBlockDelay = Just 0, callerIsOrigin = True }) (\_ _ -> PBool True) False
          fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
      cache <- newExploration options (symbolify initial)
      result <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) (property initial "valid")
      cex <- maybe (internalError "expected a two-call counterexample") pure result.counterexample
      calls <- concretizeCalls initial.block cex.model (cex.state.calls <> [cex.call]) >>= either internalError pure
      assertEqualM "cheatcode changes do not become additional delays" [(0, 0), (0, 0), (0, 0)] (map (.delay) calls)
      assertEqualM "timestamps include preceding warp calls" [0, 7, 14] (map (.timestamp) calls)
      assertEqualM "block numbers include preceding roll calls" [0, 3, 6] (map (.blockNumber) calls)
  , test "symbolic values and block context replay with balance accounting" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let funded amount = initial & over (#env % #contracts)
            (Map.insert (LitAddr 0x10000) (initialContract (RuntimeCode (ConcreteRuntimeCode "")) & set #balance (Lit amount)))
          target = Target initial.state.contract "Native" (Sig "pay" [AbiUIntType 256])
          calls = (defaultCallConfig maxBound)
            { maxTimeDelay = Just 2, maxBlockDelay = Just 1, callerIsOrigin = True, maxValue = 6 }
          fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          search config vm = do
            cache <- newExploration (ExplorationConfig [target] (OneOf [0x10000]) config (\_ _ -> PBool True) False) (symbolify vm)
            result <- searchInvariant solvers fetcher defaultVeriOpts cache (0, 2) (property initial "valid")
            (_, transitions) <- explorationStatus cache
            assertEqualM "complete value search" ([], 0) (result.issues <> transitions.issues, length result.partials + length transitions.partials)
            pure result
      forM_ [(TransferValue, 9), (MintValue, 0)] $ \(transfer, balance) -> do
        let vm = funded balance
        result <- search ((calls :: CallConfig) { valueTransfer = transfer }) vm
        cex <- maybe (internalError "expected value-dependent counterexample") pure result.counterexample
        concrete <- concretizeCalls vm.block cex.model cex.state.calls >>= either internalError pure
        assertEqualM "fresh values at each depth" [3, 6] (map (.value) concrete)
        assertEqualM "timestamps" [2, 4] (map (.timestamp) concrete)
        assertEqualM "block numbers" [1, 2] (map (.blockNumber) concrete)
        assertEqualM "per-call delays" [(2, 1), (2, 1)] (map (.delay) concrete)
        replayed <- replayCalls Fetch.noRpcConcreteFetcher maxBound vm cex.model cex.state.calls >>= either internalError pure
        assertEqualM "recipient was credited" (Lit 9) (balanceAt replayed initial.state.contract)
        assertEqualM "sender matches the funding policy" (Lit 0) (balanceAt replayed $ LitAddr 0x10000)
        checked <- checkInvariant solvers fetcher defaultVeriOpts (property initial "valid") (InvState (symbolify replayed) [])
        assertBoolM "paid counterexample replays" (not $ isNothing checked.counterexample)
      forM_ [(calls { maxValue = 5 }, 9), (calls { maxTimeDelay = Just 1 }, 9),
             (calls { maxBlockDelay = Just 0 }, 9), (calls, 8), (defaultCallConfig maxBound, 9)] $ \(config, balance) -> do
        result <- search config (funded balance)
        assertBoolM "bounds, affordability and zero-value default exclude the counterexample" (isNothing result.counterexample)
  , test "reverted minted value restores both balances" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let target = Target initial.state.contract "Native" (Sig "reject" [])
          calls = (defaultCallConfig maxBound)
            { maxTimeDelay = Just 0, maxBlockDelay = Just 0, callerIsOrigin = True, maxValue = 7, valueTransfer = MintValue }
          options = ExplorationConfig [target] (OneOf [0x10000]) calls (checkAssertions [0x01]) False
      cache <- newExploration options (symbolify initial)
      _ <- exploreLevel solvers (Fetch.oracle solvers Nothing Fetch.noRpc) defaultVeriOpts.iterConf cache 1
      (_, transitions) <- explorationStatus cache
      assertEqualM "no transition issues" [] transitions.issues
      probe <- case transitions.probes of [p] -> pure p; _ -> internalError "expected an assertion probe"
      concrete <- concretizeCalls initial.block probe.cex probe.state.calls >>= either internalError pure
      call <- case concrete of [c] -> pure c; _ -> internalError "expected one paid call"
      assertEqualM "solved value" 7 call.value
      (replayed, outcome) <- replayCall Fetch.noRpcConcreteFetcher maxBound initial call
      assertBoolM "call reverted" (case outcome of Left (Revert _) -> True; _ -> False)
      assertEqualM "recipient balance rolled back" (balanceAt initial initial.state.contract) (balanceAt replayed initial.state.contract)
      assertEqualM "origin was not credited on revert" (balanceAt initial $ LitAddr call.origin) (balanceAt replayed $ LitAddr call.origin)
  ]

balanceAt :: VM Concrete -> Expr EAddr -> Expr EWord
balanceAt vm addr = maybe (Lit 0) (.balance) (Map.lookup addr vm.env.contracts)

property :: VM Concrete -> T.Text -> Check
property vm name = Check (Target vm.state.contract "Native" (Sig name [])) (LitAddr 0xcafe)
  (Just $ LitAddr 0xcafe) maxBound (ConcreteBuf (selector $ name <> "()"), []) returnsTrue True

returnsTrue :: Postcondition
returnsTrue _ = \case
  Success _ _ buf _ -> PAnd (PEq (Expr.bufLength buf) (Lit 32)) (PEq (Expr.readWord (Lit 0) buf) (Lit 1))
  Failure {} -> PBool False
  _ -> PBool True

fixture :: App m => m (VM Concrete)
fixture = do
  compiled <- solidity "Native" $ T.unlines
    [ "interface Vm { function warp(uint256) external; function roll(uint256) external; }"
    , "contract Native {"
    , "  uint256 count;"
    , "  function advance(uint256 n) public {"
    , "    require(n == count + 1); require(tx.origin == msg.sender); count = n;"
    , "  }"
    , "  function valid() public view returns (bool) { return count < 2; }"
    , "  function invariant_valid() public view { assert(count < 2); }"
    , "  function reverting_check() public view { if (count < 2) revert(); }"
    , "  function assertBelow(uint256 n) public view { require(n == 42); assert(count < 2); }"
    , "  function mutating_check() public returns (bool) { count = 100; return true; }"
    , "  function advanceAndReport(uint256 n) public returns (bool) {"
    , "    require(n == count + 1); count = n; return count < 2;"
    , "  }"
    , "  function context() public view returns (bool) { return msg.sender == address(0xcafe) && tx.origin == msg.sender; }"
    , "  function noop() public {}"
    , "  function beforeDeadline() public view returns (bool) { return block.timestamp < 2 || block.number < 2; }"
    , "  function timedAssert() public view { require(block.timestamp >= 2 && block.number >= 2); assert(false); }"
    , "  function jump() public {"
    , "    Vm vm = Vm(address(uint160(uint256(keccak256('hevm cheat code')))));"
    , "    vm.warp(block.timestamp + 7); vm.roll(block.number + 3); count++;"
    , "  }"
    , "  function pay(uint256 n) public payable {"
    , "    require(n == count + 1 && n <= 2); require(msg.value == 3 * n);"
    , "    require(block.timestamp == 2 * n && block.number == n);"
    , "    require(address(this).balance == (n == 1 ? 3 : 9)); count = n;"
    , "  }"
    , "  function reject() public payable { require(msg.value == 7); assert(false); }"
    , "  function clock() public view returns (bool) { return block.number == 0 && block.timestamp == 0; }"
    , "}"
    ]
  code <- maybe (internalError "could not compile native invariant fixture") pure compiled
  loadVM code >>= maybe (internalError "could not deploy native invariant fixture") pure
