{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : FuzzSymExec
Description : Differential fuzzing of concrete and symbolic execution against geth's evm

Random programs are run in geth's evm, and in hevm both concretely (comparing
traces step by step) and symbolically, with calldata, storage, callvalue and
timestamp left abstract. Substituting the concrete inputs into the symbolic
leaves must select exactly one leaf, whose outcome must match geth's. For other
leaves, the solver's model of their path condition is replayed in geth, and
must reach that leaf.
-}
module EVM.Test.FuzzSymExec (tests, lockstepTests) where

import Control.Monad (forM_, unless, void)
import Control.Monad.IO.Unlift
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.IORef (newIORef)
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Set qualified as Set
import GHC.Clock (getMonotonicTime)
import System.Environment (lookupEnv)
import Test.Tasty (testGroup, after, withResource, TestTree, DependencyType(..))
import Test.Tasty.HUnit (assertFailure)
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Witch (into)
import EVM.Format (hexByteString)
import EVM.Solvers
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Debugger (BranchMode(..))
import EVM.Test.Fuzz.Program
import EVM.Test.Fuzz.Gen
import EVM.Test.Fuzz.Hevm
import EVM.Test.Fuzz.Case
import EVM.Test.Fuzz.Check
import EVM.Test.Fuzz.Lockstep

fixedCase :: [Item] -> ByteString -> TestCase
fixedCase items cd = TestCase (Prog items []) (Inputs cd mempty 0 1000) 40000 0

pushOps :: [W256] -> [Item]
pushOps = map (\v -> IPush 32 v)

tests :: TestTree
tests = testGroup "contract-quickcheck-run"
    [ withResource (newIORef mempty) printCoverage $ \cov ->
      testProperty "random-contract-concrete-call" $ \(c :: TestCase, hashCons :: Bool) ->
      -- the flag is process-wide, so concurrent tests may flip it mid-run; results must not change either way
      within 120_000_000 $ ioProperty $ runEnv (Env { config = defaultConfig { hashConsExplore = hashCons } }) $ do
        -- to find a case that crashes or runs out of memory
        liftIO $ writeCaseFile "random-contract-concrete-call" $ show c
          <> "\nmain: " <> bsToHex (assembleItems c.prog.main) <> "\ncallee: " <> bsToHex (assembleItems c.prog.callee)
        t0 <- liftIO getMonotonicTime
        report <- checkCase 3 c
        t1 <- liftIO getMonotonicTime
        liftIO $ addCoverage cov report
        let secs = t1 - t0
            time | secs < 1 = "<1s" | secs < 5 = "1-5s" | secs < 20 = "5-20s" | otherwise = ">20s"
            tables = Map.fromListWith (flip (<>)) [(t, [l]) | (t, l) <- ("case time", time) : report.tables]
        pure $ foldr (uncurry tabulate) (property True) (Map.toList tables)
      -- runs only the symbolic phase on the bytecode in HEVM_FUZZ_MAIN and HEVM_FUZZ_CALLEE, to minimize crashes
      , test "symbolic-from-env" $ liftIO (lookupEnv "HEVM_FUZZ_MAIN") >>= mapM_ (\m -> do
          cl <- fromMaybe "" <$> liftIO (lookupEnv "HEVM_FUZZ_CALLEE")
          let hex = fromJust . hexByteString . Char8.pack
              c = TestCase (Prog [IRaw (hex m)] [IRaw (hex cl)]) (Inputs mempty mempty 0 1) 300000 1
          r <- withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> runSymbolic solvers c
          liftIO $ putStrLn $ "symbolic leaves: " <> show ((\(ls, _, _) -> length ls) <$> r))
      , after AllFinish "random-contract-concrete-call" $ test "symbolic-jump-calldata-length" $ do
        _ <- checkCase 0 (fixedCase [IOp OpCalldatasize, IOp OpJump] (BS.replicate 5 0))
        pure ()
      , after AllFinish "random-contract-concrete-call" $ test "calldata-wraparound-1" $ do
        let items = concat
              [ pushOps [0xff, 31] <> [IOp OpMstore8] -- value, offs
              , pushOps [0x3, maxBound, 0x0] <> [IOp OpCalldatacopy] -- size, offs, destOffs
              , pushOps [0x20, 0] <> [IOp OpReturn] -- datasize, offs
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5]))
        pure ()
      , after AllFinish "calldata-wraparound-1" $ test "calldata-wraparound-2" $ do
        let items = concat
              [ pushOps [0xff, 0] <> [IOp OpMstore8]
              , pushOps [0x10, maxBound, 0x0] <> [IOp OpCalldatacopy]
              , pushOps [0x20, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5]))
        pure ()
      , after AllFinish "calldata-wraparound-2" $ test "codecopy-symbolic-offset-wraparound" $ do
        let items = concat
              [ pushOps [4] <> [IOp OpCallvalue, IOp OpNot] <> pushOps [6] <> [IOp OpCodecopy] -- size, ~callvalue, destOffs
              , pushOps [0x60, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items mempty)
        pure ()
      , after AllFinish "codecopy-symbolic-offset-wraparound" $ test "calldata-overwrite-with-0-if-oversized" $ do
        -- supposed to copy 1...6 and then 0s, overwriting the 0xff with 0
        let items = concat
              [ pushOps [0xff, 1] <> [IOp OpMstore8]
              , pushOps [10, 0, 0] <> [IOp OpCalldatacopy]
              , pushOps [10, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5, 6]))
        pure ()
      , after AllFinish "calldata-overwrite-with-0-if-oversized" $ test "calldata-overwrite-correct-size" $ do
        let items = concat
              [ pushOps [0xff, 8] <> [IOp OpMstore8]
              , pushOps [10, 0, 0] <> [IOp OpCalldatacopy]
              , pushOps [10, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5, 6]))
        pure ()
      , after AllFinish "calldata-overwrite-correct-size" $ test "reverted-call-drops-logs" $ do
        let callee = pushOps [0, 0] <> [IOp (OpLog 0)] <> pushOps [0, 0] <> [IOp OpRevert]
            items = pushOps [0, 0, 0, 0, 0, into calleeAddr, 0xffffff] <> [IOp OpCall]
              <> pushOps [0, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items mempty) { prog = Prog items callee }
        pure ()
      , after AllFinish "reverted-call-drops-logs" $ test "precompile-copies-only-its-output" $ do
        -- ripemd160 returns 32 bytes, so the second word of the return buffer is kept
        let items = pushOps [maxBound, 0x20] <> [IOp OpMstore]
              <> pushOps [0x40, 0, 0x20, 0, 0, 3, 0xffffff] <> [IOp OpCall]
              <> pushOps [0x40, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items mempty)
        pure ()
      , after AllFinish "precompile-copies-only-its-output" $ test "failed-precompile-clears-returndata" $ do
        let callee = pushOps [0x40, 0] <> [IOp OpRevert]
            items = pushOps [0, 0, 0, 0, 0, into calleeAddr, 0xffffff] <> [IOp OpCall]
              -- ecPairing fails on input that is not a multiple of 192 bytes
              <> pushOps [0, 0, 0x80, 0, 0, 8, 0xffffff] <> [IOp OpCall]
              <> [IOp OpReturndatasize] <> pushOps [0] <> [IOp OpMstore]
              <> pushOps [0x20, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items mempty) { prog = Prog items callee }
        pure ()
      , after AllFinish "failed-precompile-clears-returndata" $ test "msize-after-symbolic-access" $ do
        -- the LOG0 expands memory at an offset from calldata
        let items = pushOps [1, 4] <> [IOp OpCalldataload, IOp (OpLog 0), IOp OpMsize]
              <> pushOps [0] <> [IOp OpMstore] <> pushOps [0x20, 0] <> [IOp OpReturn]
        _ <- checkCase 0 (fixedCase items (BS.replicate 36 0))
        pure ()
      , after AllFinish "msize-after-symbolic-access" $ test "calldata-offset-copy" $ do
        let items = concat
              [ pushOps [0xff, 8] <> [IOp OpMstore8]
              , pushOps [0xff, 1] <> [IOp OpMstore8]
              , pushOps [10, 4, 0] <> [IOp OpCalldatacopy]
              , pushOps [10, 0] <> [IOp OpReturn]
              ]
        _ <- checkCase 0 (fixedCase items (BS.pack [1, 2, 3, 4, 5, 6]))
        pure ()
    ]


lockstepTests :: TestTree
lockstepTests = testGroup "lockstep-fuzz"
  [ -- the case from HEVM_FUZZ_* with HEVM_FUZZ_PICKS and HEVM_FUZZ_MODE, that model-guided-lockstep prints
    test "model-guided-from-env" $ liftIO caseFromEnv >>= mapM_ (\c -> do
      picks <- liftIO $ maybe [] (map read . splitOn' ',') <$> lookupEnv "HEVM_FUZZ_PICKS"
      mode <- liftIO $ maybe SolverBranches modeOf <$> lookupEnv "HEVM_FUZZ_MODE"
      -- failures are raised; what is returned only labels the case
      void $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> modelGuided solvers mode c picks)
  , testProperty "model-guided-lockstep" $ \(c :: TestCase) -> forAll (vectorOf 50 (chooseInt (0, 7))) $ \picks ->
      forAll (elements [SolverBranches, ExplorerBranches, CheckedBranches]) $ \mode ->
      within 300_000_000 $ ioProperty $ runEnv testEnv $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
        liftIO $ writeCaseFile "model-guided-lockstep" $ show c <> "\nreproduce with: " <> reproduction c c.inputs
          <> " HEVM_FUZZ_PICKS=" <> intercalate "," (map show picks) <> " HEVM_FUZZ_MODE=" <> show mode
        modelGuided solvers mode c picks
  , testProperty "debugger-vs-geth" $ \(c :: TestCase) -> forAll (resize 25 (listOf genMove)) $ \moves -> forAll genSnapEvery $ \every ->
      within 300_000_000 $ ioProperty $ do
        writeCaseFile "debugger-vs-geth" $ show c <> "\nmoves: " <> show moves <> "\nreproduce with: " <> reproduction c c.inputs
        r <- debuggerVsGeth every c moves
        pure $ tabulate "steps compared with geth" [bucket r.steps]
             $ tabulate "states revisited and compared" [bucket r.revisits]
             $ tabulate "moves that went back" [bucket r.wentBack]
             $ tabulate "of them, back past a snapshot" [bucket r.acrossSnapshots]
             $ tabulate "outcome" [r.outcome]
             $ tabulate "max call depth" [show r.depth]
             $ tabulate "opcodes run, in cases" (Set.toList r.ops) True
  , test "extcodehash-after-symbolic-transfer" $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
      -- a value that may be 0 makes the precompile's balance symbolic
      let c = TestCase (Prog
            [ IPush 0 0, IPush 0 0, IPush 0 0, IPush 0 0, IPush 0 0, IOp OpCalldataload, IPush 1 4, IPush 3 0xffffff
            , IOp OpCall, IOp OpPop, IPush 1 4, IOp OpExtcodehash, IPush 0 0, IOp OpMstore, IPush 1 0x20, IPush 0 0, IOp OpReturn ] [])
            (Inputs "" mempty 0 0x10000000000) 931794 0x12c
      forM_ [SolverBranches, ExplorerBranches, CheckedBranches] $ \mode ->
        lockstepCase solvers mode c >>= \case
          Left err -> liftIO $ failWith c c.inputs (show mode <> ": " <> err)
          Right r -> liftIO $ unless (r.stopped == "halted") $ assertFailure ("stopped: " <> r.stopped)
  , -- the case from the HEVM_FUZZ_* variables that a failure prints, in every branch mode
    test "lockstep-from-env" $ liftIO caseFromEnv >>= mapM_ (\c ->
      withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> forM_ [SolverBranches, ExplorerBranches, CheckedBranches] $ \mode ->
        lockstepCase solvers mode c >>= \case
          Left err -> liftIO $ failWith c c.inputs (show mode <> ": " <> err)
          Right r -> liftIO $ putStrLn $ show mode <> ": " <> r.stopped <> " after " <> show r.steps <> " steps, "
                       <> show r.compared <> " values compared")
  , testProperty "symbolic-lockstep" $ \(c :: TestCase) -> forAll (elements [SolverBranches, ExplorerBranches, CheckedBranches]) $ \mode ->
      within 300_000_000 $ ioProperty $ runEnv testEnv $ withSolvers Z3 1 (Just 10) defMemLimit $ \solvers -> do
        -- to find a case that crashes, hangs or runs out of memory
        liftIO $ writeCaseFile "symbolic-lockstep" $ show c <> "\nmode: " <> show mode
          <> "\nreproduce with: " <> reproduction c c.inputs
        lockstepCase solvers mode c >>= \case
          Left err -> liftIO $ failWith c c.inputs err
          Right r -> pure $ tabulate "stopped" [r.stopped]
                          $ tabulate "opcodes compared after, in cases" (Set.toList r.ops)
                          $ tabulate "branch mode" [show mode]
                          $ tabulate "decided by simplification" [bucket r.static]
                          $ tabulate "steps" [bucket r.steps]
                          $ tabulate "branches taken" [bucket r.branches]
                          $ tabulate "sides retried" [bucket r.retries]
                          $ tabulate "values compared" [bucket r.compared]
                          $ tabulate "stack words left symbolic" [bucket r.opaque]
                          $ tabulate "merged jumps checked" [bucket r.merges] (property True)
  ]
  where
    bucket :: Int -> String
    bucket n | n == 0 = "0" | n < 10 = "1-9" | n < 100 = "10-99" | n < 1000 = "100-999" | otherwise = ">=1000"
