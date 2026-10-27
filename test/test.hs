module Main where

import Data.Proxy (Proxy(..))
import System.Environment (getArgs)
import Test.Tasty
import Test.Tasty.QuickCheck (QuickCheckTests(..))
import Test.Tasty.Ingredients (composeReporters)
import Test.Tasty.Options (OptionDescription(..))
import Test.Tasty.Runners

import EVM.Test.RunLog (runLogReporter)

import EVM.Test.FuzzSymExec qualified as FuzzSymExec
import EVM.Expr.ExprTests qualified as ExprTests
import EVM.Expr.RewriteFuzz qualified as RewriteFuzz
import EVM.Expr.KeccakFuzz qualified as KeccakFuzz
import EVM.Expr.HashConsTests qualified as HashConsTests
import EVM.ConcreteExecution.ConcreteExecutionTests qualified as ConcreteExecutionTests
import EVM.Equivalence.EquivalenceTests qualified as EquivalenceTests
import EVM.Equivalence.EquivalenceTests (YulVerbosity)
import EVM.Equivalence.EquivFuzz qualified as EquivFuzz
import EVM.Fetch.RpcFuzz qualified as RpcFuzz
import EVM.SymExec.SymExecTests qualified as SymExecTests
import EVM.Debugger.DebuggerTests qualified as DebuggerTests
import EVM.Debugger.DebuggerFuzz qualified as DebuggerFuzz
import EVM.Debugger.ProgressTests qualified as ProgressTests
import EVM.Test.FoundryTests qualified as FoundryTests
import EVM.Invariant.InvariantTests qualified as InvariantTests
import EVM.Encoding.EncodingTests qualified as EncodingTests
import EVM.Solidity.SolidityTests qualified as SolidityTests
import EVM.SymExec.ArithTests qualified as ArithTests
import EVM.SymExec.LoopTests qualified as LoopTests
import EVM.SymExec.CallTests qualified as CallTests
import EVM.SymExec.OpcodeTests qualified as OpcodeTests
import EVM.Solvers.SolverTests qualified as SolverTests
import EVM.Solvers.SolverTests (hangingSolverFlag, hangingSolverMain, randomSolverFlag, randomSolverMain)

main :: IO ()
main = getArgs >>= \args -> case args of
  _ | hangingSolverFlag `elem` args -> hangingSolverMain
  _ | (_ : dir : maxDelay : _) <- dropWhile (/= randomSolverFlag) args -> randomSolverMain dir (read maxDelay)
  _ -> defaultMainWithIngredients
    [ listingTests
    , includingOptions [Option (Proxy :: Proxy YulVerbosity)]
    , runLogReporter `composeReporters` consoleTestReporter
    ] (withDefaultTimeout tests)

-- | 10 minutes per test, more for more QuickCheck tests, unless --timeout says otherwise
withDefaultTimeout :: TestTree -> TestTree
withDefaultTimeout t = askOption $ \(QuickCheckTests n) -> flip adjustOption t $ \case
  NoTimeout -> Timeout (600 * 1000000 * max 1 (toInteger n `div` 100)) "default"
  given -> given

-- | run a subset of tests in the repl. p is a tasty pattern:
-- https://github.com/UnkindPartition/tasty/tree/ee6fe7136fbcc6312da51d7f1b396e1a2d16b98a#patterns
runSubSet :: String -> IO ()
runSubSet p = defaultMain . applyPattern p $ tests

tests :: TestTree
tests = testGroup "hevm" $
  [ FuzzSymExec.tests
  , FuzzSymExec.lockstepTests
  , ExprTests.tests
  , RewriteFuzz.tests
  , KeccakFuzz.tests
  , HashConsTests.tests
  , ConcreteExecutionTests.tests
  , SymExecTests.tests
  , DebuggerTests.tests
  , DebuggerFuzz.tests
  , ProgressTests.tests
  , EquivalenceTests.tests
  , EquivFuzz.tests
  , RpcFuzz.tests
  , FoundryTests.tests
  , InvariantTests.tests
  ]
  ++ EncodingTests.tests
  ++ SolidityTests.tests
  ++ ArithTests.tests
  ++ LoopTests.tests
  ++ CallTests.tests
  ++ OpcodeTests.tests
  ++ SolverTests.tests

applyPattern :: String -> TestTree  -> TestTree
applyPattern p = localOption (TestPattern (parseExpr p))
