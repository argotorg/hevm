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
      (after, _) <- explorationStatus cache
      assertEqualM "frontiers are reused" before after
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
        result <- search calls { valueTransfer = transfer } vm
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
  (Just $ LitAddr 0xcafe) maxBound (ConcreteBuf (selector $ name <> "()"), []) returnsTrue

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
    , "  function context() public view returns (bool) { return msg.sender == address(0xcafe) && tx.origin == msg.sender; }"
    , "  function noop() public {}"
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
