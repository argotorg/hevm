module EVM.Invariant.DriverTests (tests) where

import Control.Monad (forM_)
import Data.Maybe (isNothing)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)

import EVM (symbolify)
import EVM.ABI (AbiType(..), AbiValue(..), Sig(..), selector)
import EVM.Effects (App)
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Invariant
import EVM.Invariant.Driver
import EVM.Solidity (solidity)
import EVM.SymExec (Postcondition, defaultVeriOpts)
import EVM.Test.Helpers (assertBoolM, assertEqualM, loadVM, test, withDefaultSolver)
import EVM.Types

tests :: TestTree
tests = testGroup "framework-independent driver"
  [ test "native property, cached depths and concrete replay" $ withDefaultSolver $ \solvers -> do
      initial <- fixture
      let fetcher = Fetch.oracle solvers Nothing Fetch.noRpc
          target = Target initial.state.contract "Native" (Sig "advance" [AbiUIntType 256])
          options = ExplorationConfig [target] (OneOf [0x10000, 0x20000])
            (CallConfig maxBound (Just 3) (Just 2) True) (\_ _ -> PBool True) False
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
            (CallConfig maxBound (Just 1) (Just 1) True) (\_ _ -> PBool True) False
      cache <- newExploration options (symbolify initial)
      result <- searchInvariant solvers (Fetch.oracle solvers Nothing Fetch.noRpc) defaultVeriOpts
        cache (1, 1) (property initial "clock")
      assertBoolM "time or number can falsify the property without a storage write" (not $ isNothing result.counterexample)
  ]

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
  Just code <- solidity "Native" $ T.unlines
    [ "contract Native {"
    , "  uint256 count;"
    , "  function advance(uint256 n) public {"
    , "    require(n == count + 1); require(tx.origin == msg.sender); count = n;"
    , "  }"
    , "  function valid() public view returns (bool) { return count < 2; }"
    , "  function context() public view returns (bool) { return msg.sender == address(0xcafe) && tx.origin == msg.sender; }"
    , "  function noop() public {}"
    , "  function clock() public view returns (bool) { return block.number == 0 && block.timestamp == 0; }"
    , "}"
    ]
  Just vm <- loadVM code
  pure vm
