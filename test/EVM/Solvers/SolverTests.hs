{-# LANGUAGE QuasiQuotes #-}

module EVM.Solvers.SolverTests (tests, hangingSolverFlag, hangingSolverMain, randomSolverFlag, randomSolverMain) where

import GHC.TypeLits
import Control.Concurrent (forkIO, threadDelay, ThreadId, myThreadId)
import GHC.Conc (getNumProcessors)
import Control.Concurrent.STM (atomically, newTVarIO, readTVarIO, writeTVar)
import Control.Monad
import System.Environment (getExecutablePath)
import System.IO (hSetBuffering, stdout, BufferMode(..), isEOF, withFile, openFile, hClose, IOMode(..))
import GHC.IO.Handle.Lock (hLock, hTryLock, LockMode(..))
import System.Directory (listDirectory)
import System.Process (getCurrentPid)
import GHC.Clock (getMonotonicTimeNSec)
import Data.IORef (newIORef, readIORef, atomicModifyIORef')
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Control.Exception (IOException, evaluate, try)
import System.Timeout (timeout)
import Control.Monad.Reader (ReaderT)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Bits hiding (And, Xor)
import Data.Char (isSpace)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSLazy
import Data.Aeson qualified as JSON
import Data.Aeson.KeyMap qualified as KeyMap
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Data.Either
import Data.List qualified as List
import Data.Text.Lazy qualified as TL
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Test.Tasty.HUnit

import EVM.ABI
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (hexByteString)
import EVM.Progress (withProgress, ProgressOpts(..))
import EVM.SMT
import EVM.Solidity
import EVM.Solvers
import EVM.SymExec
import EVM.Equivalence
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.Keccak (concreteKeccaks, keccakAssumptions)

import EVM.Test.Helpers

tests :: [TestTree]
tests =
  [ testCase "default-solver-count" $ do
      cores <- fromIntegral <$> getNumProcessors
      n <- defaultSolverCount defMemLimit
      assertBool "at least one, at most one per core" (n >= 1 && n <= cores)
      huge <- defaultSolverCount (10 ^ (9 :: Int))
      assertEqual "a limit beyond the memory still leaves one" 1 huge
  , testGroup "SMT-encoding"
  [ testProperty "collapse-matches-writeByte-within-length" $ \(baseByte, NonNegative sz, ws) ->
      let base = W256 (fromIntegral (sz `mod` 200 :: Int))
          writes = [(W256 (fromIntegral (pos `mod` 300 :: Int)), b) | (NonNegative pos, b) <- take 20 ws]
          model = foldr (\(pos, b) acc -> Write b pos acc) (Base baseByte base) writes
          -- the definition: apply the writes, innermost first, with writeByte,
          -- and keep the model's length
          reference = foldr (\(pos, b) acc -> Expr.writeByte (Lit pos) (LitByte b) acc)
                            (ConcreteBuf (BS.replicate (fromIntegral base) baseByte)) writes
      in case reference of
           ConcreteBuf bs -> collapse (EVM.Types.Comp model) === Just (Flat (BS.take (fromIntegral base) bs))
           _ -> property False
  , testCase "buffer-model-drops-writes-past-length" $ do
      let getVal = \case
            "b_length " -> pure "((b_length #x000000000000000000000000000000000000000000000000000000000000001f))"
            _ -> pure $ "((b (store (store ((as const (Array (_ BitVec 256) (_ BitVec 8))) #x00) #x0000000000000000000000000000000000000000000000000000000000000000 #xff) "
                     <> "#xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff #xff)))"
      bufs <- runMaybeT $ getBufs getVal ["b"]
      assertEqual "" (Just (Map.singleton (AbstractBuf "b") (EVM.Types.Comp (Write 0xff 0 (Base 0 0x1f))))) bufs
  , testCase "parse-gas-names" $ do
      -- gas readings appear in models when they are part of a path condition
      assertEqual "plain" (Gas "" 2) (parseTxCtx "gas_2")
      assertEqual "equivalence prefix" (Gas "A-" 13) (parseTxCtx "gas_A-13")
  -- #1124: the encoder must not order gas readings by where they appear in the props
  , test "gas-order-not-from-props" $ do
      res <- withBitwuzlaSolver $ \s -> checkSatWithProps s [PLT (Gas "" 2) (Gas "" 1)]
      assertBoolM "a later reading can be lower" (isCex res)
  , testCase "encodeConcreteStore-overwrite" $
    assertEqual ""
      (pure "(store (store ((as const Storage) #x0000000000000000000000000000000000000000000000000000000000000000) (_ bv1 256) (_ bv2 256)) (_ bv3 256) (_ bv4 256))")
      (EVM.SMT.encodeConcreteStore ConcreteArith $ Map.fromList [(W256 1, W256 2), (W256 3, W256 4)])
  -- a lemma that names the other multiplication function constrains an
  -- application the goal never mentions, so it can never help
  , testCase "abstract-lemmas-match-goal-mul-encoding" $ do
      let x = Var "x"
          y = Var "y"
          -- x*1000 is a const-mul, so the goal encodes it (and the (x*1000/1000)*1000
          -- link product the saturation adds) with a native bvmul
          constMul = abstractQuery [PEq (Div (Mul (Lit 1000) x) (Lit 1000)) y]
          -- x*y is genuinely symbolic, so it stays abstract
          symMul = abstractQuery [PEq (Div (Mul x y) (Lit 1000)) (Var "z")]
      assertBool ("abstract mul over a literal factor:\n" <> constMul)
        (not ("(abst_evm_bvmul" `List.isInfixOf` constMul))
      assertBool ("div-mul link dropped for a literal divisor:\n" <> constMul)
        ("(bvmul (abst_evm_bvudiv" `List.isInfixOf` constMul)
      assertBool ("symbolic product not abstracted:\n" <> symMul)
        ("(abst_evm_bvmul" `List.isInfixOf` symMul)
  -- the terms 'saturate' adds exist only in the lemmas, so no proof can be
  -- relied on to notice one going missing
  , testCase "abstract-saturation-terms" $ do
      let x = Var "x"
          y = Var "y"
          z = Var "z"
          emits what needle q = assertBool (what <> " missing:\n" <> q) (needle `List.isInfixOf` q)
      emits "link product" "(abst_evm_bvmul (abst_evm_bvudiv x y) y)" $
        abstractQuery [PEq (Div x y) z]
      -- the goal's own terms are referred to by name, smallest first
      let reused = abstractQuery [PEq (Add (Div x y) (Mul y z)) (Lit 5)]
      emits "shared term" "(define-fun arith_term_1 () (_ BitVec 256) (abst_evm_bvmul y z))" reused
      emits "synthetic division by a reused factor" "(abst_evm_bvudiv arith_term_1 y)" reused
      let nested = abstractQuery [PEq (Div (Div (Mul x y) (Lit 1000)) (Lit 7)) z]
      emits "shared term" "(define-fun arith_term_0 () (_ BitVec 256) (abst_evm_bvmul x y))" nested
      emits "collapsed nested division" "(bvmul (abst_evm_bvudiv arith_term_0 (_ bv7000 256)) (_ bv7000 256))" nested
  , testCase "abstract-lemma-section-only-when-lemmas-fire" $ do
      let header = "multiplication abstraction lemmas"
          -- a lone constant product triggers no lemma: const-mul monotonicity
          -- needs a second product sharing the constant, and there is no division
          noLemmas = abstractQuery [PEq (Mul (Lit 1000) (Var "x")) (Lit 5)]
          -- the same product over a division does trigger some
          someLemmas = abstractQuery [PEq (Div (Mul (Lit 1000) (Var "x")) (Lit 1000)) (Var "y")]
      assertBool ("empty lemma section emitted:\n" <> noLemmas)
        (not (header `List.isInfixOf` noLemmas))
      assertBool ("lemma section missing:\n" <> someLemmas)
        (header `List.isInfixOf` someLemmas)
  ]
  , testGroup "Keccak assumptions"
    [ testCase "concrete-hashes-need-no-assumptions" $ do
        let a = Keccak (ConcreteBuf "first")
            b = Keccak (ConcreteBuf "second")
            nested = Keccak (WriteWord (Lit 0) a (ConcreteBuf ""))
        assertEqual "concrete hashes, including simplified inputs, need no assumptions"
          [] (keccakAssumptions mempty [a, b, nested])
    , testGroup "mixed-concrete-symbolic"
      [ testCase (show solver) $ runEnv (testEnv {config = testEnv.config {simp = False}}) $
          withSolvers solver 1 (Just 5) defMemLimit $ \s -> do
            let key = Var "key"
                symbolic = Keccak (WriteWord (Lit 0) key (ConcreteBuf ""))
                concrete = Keccak (ConcreteBuf (word256Bytes 7))
                h = Var "hash"
                base = [PEq h concrete]
            res <- checkSatWithProps s (PEq symbolic h : base)
            case res of
              Cex cex -> assertEqualM "the concrete preimage remains reachable"
                (Just 7) (Map.lookup key cex.vars)
              _ -> liftIO $ assertFailure $ "expected a model, got " <> show res
            forM_
              [ ("injectivity", [PEq key (Lit 8), PEq symbolic h])
              , ("field separation", [PEq key (Lit 8), PEq symbolic (Add h (Lit 1))])
              , ("congruence", [PEq key (Lit 7), PNeg (PEq symbolic h)])
              , ("output range", [PEq symbolic (Lit 0)])
              ] $ \(name, props) -> do
                result <- checkSatWithProps s (props <> base)
                assertBoolM (name <> ": expected unsat, got " <> show result) (isQed result)
      | solver <- [Bitwuzla, Z3]
      ]
    ]
  -- the progress log is process-wide, so these must not run concurrently
  , sequentialTestGroup "progress-log" AllFinish
    [ test "progress-log-is-valid-jsonl" $ do
        Just c <- solcRuntime "C" [i|
          contract C {
            function fun(uint x) external pure {
              if (x > 5) assert(x != 7);
            }
          } |]
        evs <- progressEvents $
          void $ withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
        forM_ ["start", "path-end", "query-start", "query-end", "end"] $ \ev ->
          assertBoolM ("missing event " <> ev) (ev `elem` map fst evs)
    , test "eq-progress-log-phases" $ do
        let a = fromJust (hexByteString "6001600055")
            b = fromJust (hexByteString "6002600055")
        evs <- progressEvents $ void $ withDefaultSolver $ \s -> do
          (calldata, _) <- mkCalldata Nothing []
          equivalenceCheck s Nothing a b defaultVeriOpts calldata False
        forM_ ["explore A", "explore B", "build-pairs", "check-pairs"] $ \ph ->
          forM_ ["phase-start", "phase-end"] $ \ev ->
            assertBoolM ("missing " <> ev <> " of " <> ph) ((ev, Just ph) `elem` evs)
    ]
  -- these test the abort itself: if it breaks, the fake solver never answers, so fail on a timeout instead of hanging
  , localOption (mkTimeout 20_000_000) $ testGroup "early-abort"
  [ test "abort-running-query" $ withHangingSolver $ \s -> do
      shouldAbort <- liftIO $ newTVarIO False
      _ <- liftIO $ forkIO $ threadDelay 300_000 >> atomically (writeTVar shouldAbort True)
      res <- checkSatWithPropsAbortable s (Just shouldAbort) hangingProps
      assertEqualM "Expected an aborted query" "Unknown \"Query aborted\"" (show res)
    , test "abort-before-query" $ withHangingSolver $ \s -> do
      shouldAbort <- liftIO $ newTVarIO True
      res <- checkSatWithPropsAbortable s (Just shouldAbort) hangingProps
      assertEqualM "Expected an aborted query" "Unknown \"Query aborted\"" (show res)
    , test "abort-frees-solver-slot" $ withHangingSolver $ \s -> do
      shouldAbort <- liftIO $ newTVarIO False
      _ <- liftIO $ forkIO $ threadDelay 300_000 >> atomically (writeTVar shouldAbort True)
      _ <- checkSatWithPropsAbortable s (Just shouldAbort) hangingProps
      let unsatQuery = SMT2 (SMTScript [SMTCommand "(set-info :status unsat)"]) mempty []
      res <- liftIO $ checkSat s Nothing (Right unsatQuery)
      assertBoolM ("Expected Qed from the only solver slot, got: " <> show res) (isQed res)
    , testCase "fake-solver-scan" $ do
      assertEqual "complete command" (0, True) (scanSMT "(check-sat)")
      assertEqual "incomplete command" (1, True) (scanSMT "(define-fun f () Word")
      assertEqual "blank line" (0, False) (scanSMT "")
      assertEqual "comment only" (0, False) (scanSMT "; a (comment")
      assertEqual "paren in string literal" (0, True) (scanSMT "(set-info :name \"a(b\")")
      assertEqual "paren in quoted symbol" (0, True) (scanSMT "(assert (= |a)b| x))")
    -- hevm builds some commands with their own trailing newline
    , test "fake-solver-trailing-newline" $ withHangingSolver $ \s -> do
      let unsatQuery = SMT2 (SMTScript [SMTCommand "(set-info :status unsat)\n"]) mempty []
      res <- liftIO $ checkSat s Nothing (Right unsatQuery)
      assertBoolM ("Expected Qed, got: " <> show res) (isQed res)
    -- aborts a run at a random moment while fake solvers answer after random delays
    , localOption (mkTimeout 1_800_000_000) $
      adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 30 else n)) $
      testProperty "early-abort-race" $
        forAll ((,,) <$> choose (1, 4 :: Int) <*> choose (0, 20) <*> choose (0, 400)) $ \(n, maxDelay, abortAfter) ->
          ioProperty $ earlyAbortRace (fromIntegral n) maxDelay abortAfter
    -- the same, exploring without checking leaves: paths running at the abort stop at their next step
    , localOption (mkTimeout 1_800_000_000) $
      adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 30 else n)) $
      testProperty "early-abort-race-interpret" $
        forAll ((,,) <$> choose (1, 4 :: Int) <*> choose (0, 20) <*> choose (0, 400)) $ \(n, maxDelay, abortAfter) ->
          ioProperty $ earlyAbortInterpretRace (fromIntegral n) maxDelay abortAfter
    , test "early-abort-verify" $ do
      Just c <- solcRuntime "C" [i|
          contract C {
            function stuff(uint a) public {
              for (uint i = 0; i < 10; i++) {
                unchecked { assert(i * a < 100); }
              }
            }
          } |]
      let abortEnv = Env { config = testEnv.config { earlyAbort = True } }
      (_, res) <- liftIO $ runEnv abortEnv $ withBitwuzlaSolver $ \s ->
        checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      assertBoolM "Expected a counterexample" (any isCex res)
      assertBoolM ("Expected only counterexamples, got: " <> show res) (all isCex res)
  ]
  , testGroup "calling-solvers"
  [ testGroup "enumerate-buffer-lengths"
      [ test (show solver) $ withSolvers solver 1 (Just 10) defMemLimit $ \s -> do
          conf <- readConfig
          let len = BufLength (AbstractBuf "buf")
              smt = assertProps conf
                [ PEq (Var "multiQueryVar") len
                , POr (PEq len (Lit 33)) (PEq len (Lit 65))
                ]
              options = MultiSol { maxSols = 2, numBytes = 2, var = "multiQueryVar" }
          -- Shrinking a buffer model to 64 bytes would silently exclude 65.
          vals <- liftIO $ checkMulti s smt options
          assertEqualM "all lengths remain possible" (Just (Set.fromList [33, 65])) (Set.fromList <$> vals)
          limited <- liftIO $ checkMulti s smt options { maxSols = 1 }
          assertEqualM "the width limit must not return an incomplete list" Nothing limited
      | solver <- [Z3, Bitwuzla]
      ]
    , testGroup "keccak-alias-of-folded-slot"
      [ test (show solver) $ withSolvers solver 3 Nothing defMemLimit $ \s ->
          forM_ [0, 5, 255] $ \offset -> do
            let foldedSlot = keccak' (word256Bytes 3 <> word256Bytes 0) + offset
                readAt slot = Add (Keccak (WriteWord (Lit 0) (Var "k") (ConcreteBuf (BS.replicate 32 0 <> word256Bytes slot)))) (Lit offset)
                store = ConcreteStore (Map.singleton foldedSlot 2)
                readQuery slot = [PNeg (PEq (SLoad (readAt slot) store) (Lit 0))]
            other <- checkSatWithProps s (readQuery 1)
            assertBoolM ("read of another mapping must be unsat, got " <> show other) (isQed other)
            same <- checkSatWithProps s (readQuery 0)
            case same of
              Cex cex -> assertEqualM "same mapping must alias at k = 3" (Just 3) (Map.lookup (Var "k") cex.vars)
              _ -> liftIO $ assertFailure $ "read of the same mapping must be sat, got " <> show same
      | solver <- [Z3, Bitwuzla]
      ]
    , test "keccak-alias-multiple-slots" $ do
      let foldedSlot key = keccak' (word256Bytes key <> word256Bytes 0)
          readB = Keccak (WriteWord (Lit 0) (Var "k") (ConcreteBuf (BS.replicate 32 0 <> word256Bytes 1)))
          store = ConcreteStore (Map.fromList [(foldedSlot 3, 2), (foldedSlot 4, 7)])
      withDefaultSolver $ \s -> do
        res <- checkSatWithProps s [PNeg (PEq (SLoad readB store) (Lit 0))]
        assertBoolM ("all folded slots must be separated, got " <> show res) (isQed res)
    , test "keccak-alias-unrecoverable-keeps-model" $ do
      let readB = Keccak (WriteWord (Lit 0) (Var "k") (ConcreteBuf (BS.replicate 32 0 <> word256Bytes 1)))
          store = ConcreteStore (Map.singleton 0xdeadbeef 2)
      withDefaultSolver $ \s -> do
        res <- checkSatWithProps s [PNeg (PEq (SLoad readB store) (Lit 0))]
        assertBoolM ("unrecoverable literals must stay unconstrained, got " <> show res) (isCex res)
    , testMaxBuf64 "no-error-on-large-buf" $ do
      -- These two tests generates a very large buffer that previously would cause an internalError when
      -- printed via "formatCex". We should be able to print it now.
      Just c <- solcRuntime "MyContract" [i|
          contract MyContract {
            function fun(bytes calldata a) external pure {
              if (a.length > 0x800000000000) {
                assert(false);
              }
            }
           } |]
      (_, [Cex cex]) <- withDefaultSolver $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
      liftIO $ void $ evaluate (T.length (formatCex (AbstractBuf "txdata") Nothing (snd cex)))
    , test "no-error-on-large-buf-pure-print" $ do
      let bufs = Map.singleton (AbstractBuf "txdata")
                  (EVM.Types.Comp Write {byte = 1, idx = 0x27, next = Base {byte = 0x66, length = 0xffff000000000000000}})
      let mycex = SMTCex {vars = mempty
                         , addrs = mempty
                         , buffers = bufs
                         , store = mempty
                         , blockContext = mempty
                         , txContext = Map.fromList [(TxValue,0x0)]
                         , unknownCalls = mempty}
      liftIO $ void $ evaluate (T.length (formatCex (AbstractBuf "txdata") Nothing mycex))
    , test "correct-model-for-empty-buffer" $ do
      withDefaultSolver $ \s -> do
        let props = [(PEq (BufLength (AbstractBuf "b")) (Lit 0x0))]
        res <- checkSatWithProps s props
        (cex) <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        let value = fromRight (error "cannot be") $ subModel cex (AbstractBuf "b")
        assertEqualM "Buffer must be empty" (ConcreteBuf "") value
    , test "correct-model-for-non-empty-buffer-of-all-zeroes" $ do
      withDefaultSolver $ \s -> do
        let props = [(PAnd (PEq (ReadByte (Lit 0x0) (AbstractBuf "b")) (LitByte 0x0)) (PEq (BufLength (AbstractBuf "b")) (Lit 0x1)))]
        res <- checkSatWithProps s props
        (cex) <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        let value = fromRight (error "cannot be") $ subModel cex (AbstractBuf "b")
        assertEqualM "Buffer must have size 1 and contain zero byte" (ConcreteBuf "\0") value
    , test "buffer-shrinking-does-not-loop" $ do
      withDefaultSolver $ \s -> do
        let props = [(PGT (BufLength (AbstractBuf "b")) (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb4))]
        res <- checkSatWithProps s props
        let
          sat = case res of
            Cex _ -> True
            _ -> False
        assertBoolM "Must be satisfiable!" sat
    , test "can-get-value-unrelated-to-large-buffer" $ do
      withDefaultSolver $ \s -> do
        let props = [(PEq (Var "a") (Lit 0x1)), (PGT (BufLength (AbstractBuf "b")) (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb4))]
        res <- checkSatWithProps s props
        cex :: SMTCex <- case res of
          Cex c -> pure c
          _ -> liftIO $ assertFailure "Must be satisfiable!"
        let value = subModel cex (Var "a")
        assertEqualM "Can get value out of model in the presence of large buffer!" value (Right $ Lit 0x1)
    , test "no-duplicates-with-concrete-keccak" $ do
      let props = [(PGT (Var "a") (Keccak (ConcreteBuf "abcdef"))), (PGT (Var "b") (Keccak (ConcreteBuf "abcdef")))]
      conf <- readConfig
      let SMT2 script _ _ = fromRight (internalError "Must succeed") (assertProps conf props)
      assertBoolM "There were duplicate commands in SMT encoding" $ not (hasDuplicateCommands script)
    , test "no-duplicates-with-read-assumptions" $ do
      let props = [(PGT (ReadWord (Lit 2) (AbstractBuf "test")) (Lit 0)), (PGT (Expr.padByte $ ReadByte (Lit 10) (AbstractBuf "test")) (Expr.padByte $ LitByte 1))]
      conf <- readConfig
      let SMT2 script _ _ = fromRight (internalError "Must succeed") (assertProps conf props)
      assertBoolM "There were duplicate lines in SMT encoding" $ not (hasDuplicateCommands script)
     , test "all-concrete-keccaks-discovered" $ do
      let buf1 = (Keccak (ConcreteBuf "abc"))
          eq = (Eq buf1 (Lit 0x12))
          buf2 = WriteWord eq (Lit 0x0) mempty
          props = [PEq (Keccak buf2) (Lit 0x123)]
          concrete = concreteKeccaks props
      assertEqualM "Must find two keccaks" 2 (length concrete)
    , test "recover-folded-mapping-slot" $ do
      let pre = word256Bytes 0x5eed1234 <> word256Bytes 255
          h = keccak' pre
          props value offset = [PEq (SLoad (Var "k") (ConcreteStore (Map.singleton (h + offset) value))) (Lit 0)]
      assertEqualM "unknown key" mempty (concreteKeccaks $ props 2 0)
      assertEqualM "candidate key and field offset" (Set.singleton (ConcreteBuf pre, h)) (concreteKeccaks $ props 0x5eed1234 255)
      assertEqualM "offset outside recovery range" mempty (concreteKeccaks $ props 0x5eed1234 256)
    -- the size is symbolic during execution, and a literal near 2^256 once the keccak is concretized
    -- the solver cannot encode the true side's exponentiation, but simplification
    -- refutes the false side, 10 + e == 0 and e <= 2^256 - 11
    , testCase "branch-side-refuted-as-recorded" $ runEnv testEnv $ do
      let e = Exp (Lit 0x41) (Xor (Lit 0x3) (ReadWord (Lit 0xa) (AbstractBuf "calldata")))
          cond = Or (EVM.Types.LT (Lit 0) (Add (Lit 0xa) e)) (EVM.Types.LT (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5) e)
      r <- withSolvers Z3 1 (Just 10) defMemLimit $ \s -> Fetch.checkBranch s cond (PBool True)
      liftIO $ case r of
        Case True -> pure ()
        other -> assertFailure $ "expected only the true side, got " <> show other
    , testCase "copy-sized-by-concrete-keccak" $ runEnv (testEnv {config = testEnv.config {simp = False}}) $ do
      let copied = CopySlice (Lit 0) (Lit 0) (Keccak (ConcreteBuf (BS.replicate 9 0))) (AbstractBuf "calldata") (ConcreteBuf "")
      res <- withDefaultSolver $ \s -> checkSatWithProps s [PEq (ReadWord (Lit 0) copied) (Lit 1)]
      assertBoolM ("copy beyond the memory access limit must be unsupported, got " <> show res) (isError res)
    , test "copy-with-symbolic-offset-encodes-it-once" $ do
      let dst = Add (Var "a") (Var "b")
          copied n = CopySlice (Lit 0) dst (Lit n) (AbstractBuf "calldata") (ConcreteBuf "")
          props n = [PEq (ReadWord (Lit 0) (copied n)) (Lit 1)]
      conf <- readConfig
      let smt = TL.toStrict . formatSMT2 $ fromRight (internalError "Must succeed") (assertProps conf (props 0x100))
      -- once in the copy, once in the buffer length
      assertEqualM "symbolic offset occurrences" 2 (T.count "(bvadd a b)" smt)
      assertBoolM "a huge copy must fail fast" $ isLeft (assertProps conf (props 0xca11ee))
    , testCase "store-over-concrete-buffer" $ runEnv (testEnv {config = testEnv.config {simp = False}}) $ do
      let
        as = AbstractStore (SymAddr "test") Nothing
        cs = ConcreteStore $ Map.fromList [(0x1,0x2)]
        e1 = SLoad (Lit 0x1) (SStore (Lit 0x8) (SLoad (Lit 0x40) as) cs)
        eq = PEq e1 (Lit 0x0)
      conf <- readConfig
      let SMT2 _ (CexVars _ _ _ storeReads _ _ _) _ = fromRight (internalError "Must succeed") (assertProps conf [eq])
      let expected = StorageReads $ Map.singleton (SymAddr "test", Nothing) (Set.singleton (Lit 0x40))
      assertEqualM "Reads must be properly collected" storeReads expected
    , test "all-abstract-reads-detected" $ do
      let mystore = (AbstractStore (SymAddr "test") Nothing)
      let props = [PGT (SLoad (Lit 2) mystore) (SLoad (Lit 0) mystore)]
      conf <- readConfig
      let SMT2 _ cexVars _ = fromRight (internalError "Must succeed") (assertProps conf props)
      let (StorageReads m) = cexVars.storeReads
      case Map.lookup ((SymAddr "test"), Nothing) m of
        Nothing -> assertBoolM "Address missing from storage reads" False
        Just storeReads -> assertBoolM "Did not collect all abstract reads!" $ (Set.size storeReads) == 2
  ]
  ]

-- | For tests that need buffers larger than the default 2^24 bytes
testMaxBuf64 :: TestName -> ReaderT Env IO () -> TestTree
testMaxBuf64 a b = testCase a $ runEnv (Env { config = testEnv.config { maxBufSize = 64 } }) b

-- | Runs an action with the progress log on, and returns each logged event's
-- name and phase. Fails if a line is not a JSON object with a time and a name.
progressEvents :: ReaderT Env IO () -> ReaderT Env IO [(String, Maybe String)]
progressEvents act = withRunInIO $ \runIO -> withSystemTempDirectory "progress" $ \dir -> do
  let f = dir </> "progress.jsonl"
  runIO $ withProgress (ProgressOpts (Just f) True False False) act
  ls <- BSLazy.split 10 <$> BSLazy.readFile f
  forM (filter (not . BSLazy.null) ls) $ \l -> case JSON.decode l of
    Just (JSON.Object o) | Just (JSON.String ev) <- KeyMap.lookup "ev" o, Just (JSON.Number _) <- KeyMap.lookup "t" o ->
      pure (T.unpack ev, case KeyMap.lookup "phase" o of
        Just (JSON.String ph) -> Just (T.unpack ph)
        _ -> Nothing)
    _ -> assertFailure $ "not a progress event: " <> show l

withHangingSolver :: App m => (SolverGroup -> m a) -> m a
withHangingSolver cont = do
  self <- liftIO getExecutablePath
  -- under -f devel the test binary starts one capability per core, each with its own nursery
  -- and stacks, which does not fit in the address space a real solver is limited to
  withSolvers (Custom (TL.pack self) [TL.pack hangingSolverFlag]) 1 Nothing (64 * defMemLimit) cont

earlyAbortRace :: Natural -> Int -> Int -> IO Property
earlyAbortRace n maxDelay abortAfter = do
  Just c <- runEnv testEnv $ solcRuntime "C" raceContract
  self <- getExecutablePath
  withSystemTempDirectory "hevm-fake-solver" $ \dir -> do
    let solver = Custom (TL.pack self) [TL.pack randomSolverFlag, TL.pack dir, TL.pack (show maxDelay)]
        unsatQuery = SMT2 (SMTScript [SMTCommand "(set-info :status unsat)"]) mempty []
    start <- getMonotonicTimeNSec
    res <- timeout 120_000_000 $ runEnv testEnv $ withSolvers solver n Nothing (64 * defMemLimit) $ \s -> do
      abort <- liftIO $ newTVarIO False
      _ <- liftIO $ forkIO $ threadDelay (abortAfter * 1000) >> atomically (writeTVar abort True)
      (calldata, _) <- mkCalldata (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) []
      vm <- liftIO $ stToIO $ abstractVM calldata c Nothing False
      lateQueries <- liftIO $ newIORef (Map.empty :: Map.Map ThreadId Int)
      allQueries <- liftIO $ newIORef (0 :: Int)
      -- each path runs in a thread of its own; it may have checked the flag just before it was
      -- set, but must stop after one more query
      let fetcher q = do
            case q of
              PleaseAskSMT {} -> liftIO $ do
                atomicModifyIORef' allQueries (\k -> (k + 1, ()))
                tid <- myThreadId
                readTVarIO abort >>= \a -> when a $ atomicModifyIORef' lateQueries (\m -> (Map.insertWith (+) tid 1 m, ()))
              _ -> pure ()
            Fetch.oracle s Nothing Fetch.noRpc q
      (ends, _) <- verifyAbortable abort s fetcher defaultVeriOpts vm (checkAssertions defaultPanicCodes) Nothing
      end <- liftIO getMonotonicTimeNSec
      free <- liftIO $ timeout 10_000_000 $ checkSat s Nothing (Right unsatQuery)
      late <- liftIO $ maximum . (0 :) . Map.elems <$> readIORef lateQueries
      nQueries <- liftIO $ readIORef allQueries
      pure (ends, free, end, late, nQueries)
    leftover <- solversLeft dir 50
    spawned <- length <$> listDirectory dir
    let bucket k = show (k `div` 20 * 20) <> "-" <> show (k `div` 20 * 20 + 19)
    pure $ tabulate "solvers spawned" [bucket spawned] $ case res of
      Nothing -> counterexample "the run did not return" False
      Just (ends, free, end, late, nQueries) -> tabulate "branch queries" [bucket nQueries] $ tabulate "most queries of a path after the abort" [show late] $
        let afterAbortMs = (fromIntegral (end - start) `div` 1_000_000) - abortAfter :: Int
        in tabulate "run" [if afterAbortMs < 0 then "finished before the abort" else "aborted"] $ conjoin
          [ counterexample ("returned " <> show afterAbortMs <> "ms after the abort") (afterAbortMs < 5000)
          , counterexample ("a solver slot is still taken: " <> show free) (maybe False isQed free)
          , counterexample ("solver processes left behind (pid, state): " <> show leftover) (null leftover)
          , counterexample "a path stopped by the abort was reported" (not (any isAborted ends))
          , counterexample (show late <> " branch queries of one path after the abort") (late <= 1)
          ]
  where
    isAborted = \case
      Partial _ _ (Aborted {}) -> True
      _ -> False

earlyAbortInterpretRace :: Natural -> Int -> Int -> IO Property
earlyAbortInterpretRace n maxDelay abortAfter = do
  Just c <- runEnv testEnv $ solcRuntime "C" raceContract
  self <- getExecutablePath
  withSystemTempDirectory "hevm-fake-solver" $ \dir -> do
    let solver = Custom (TL.pack self) [TL.pack randomSolverFlag, TL.pack dir, TL.pack (show maxDelay)]
    start <- getMonotonicTimeNSec
    res <- timeout 120_000_000 $ runEnv testEnv $ withSolvers solver n Nothing (64 * defMemLimit) $ \s -> do
      abort <- liftIO $ newTVarIO False
      _ <- liftIO $ forkIO $ threadDelay (abortAfter * 1000) >> atomically (writeTVar abort True)
      (calldata, _) <- mkCalldata (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) []
      vm <- liftIO $ stToIO $ abstractVM calldata c Nothing False
      leaves <- withRunAbort s abort $
        interpretAbortable abort (Fetch.oracle s Nothing Fetch.noRpc) defaultIterConf vm runExpr noopPathHandler
      end <- liftIO getMonotonicTimeNSec
      pure (leaves, end)
    leftover <- solversLeft dir 50
    pure $ case res of
      Nothing -> counterexample "the run did not return" False
      Just (_, end) ->
        let afterAbortMs = (fromIntegral (end - start) `div` 1_000_000) - abortAfter :: Int
        in tabulate "ms from the abort to the return" [show (afterAbortMs `div` 100 * 100)] $ conjoin
          [ counterexample ("returned " <> show afterAbortMs <> "ms after the abort") (afterAbortMs < 5000)
          , counterexample ("solver processes left behind (pid, state): " <> show leftover) (null leftover)
          ]

raceContract :: Text
raceContract = [i|
  contract C {
    function f(uint a, uint b) public pure {
      uint r = 0;
      for (uint i = 0; i < 10; i++) {
        if ((a >> i) & 1 == 1) r += b; else r ^= i;
        // concrete work, which a path that ignores the abort keeps doing
        for (uint j = 0; j < 900; j++) r = uint(keccak256(abi.encode(r, j)));
      }
      assert(r != 7);
    }
  } |]

-- | The fake solvers recorded in the directory that still exist after waiting up to tries * 100ms
-- for them to go: alive ones still hold the lock on their file, and on Linux /proc also shows the
-- exited ones not yet reaped
solversLeft :: FilePath -> Int -> IO [(String, String)]
solversLeft dir tries = do
  pids <- listDirectory dir
  states <- forM pids $ \pid -> (pid,) <$> solverState pid
  let left = [(pid, st) | (pid, Just st) <- states]
  if null left || tries <= 0 then pure left else threadDelay 100_000 >> solversLeft dir (tries - 1)
  where
    solverState pid = do
      -- on Windows, opening a file another process holds locked can fail
      locked <- try (withFile (dir </> pid) ReadWriteMode (\h -> hTryLock h ExclusiveLock)) >>= \case
        Left (_ :: IOException) -> pure True
        Right got -> pure (not got)
      if locked then pure (Just "locked") else procState pid
    procState pid = do
      r <- try (readFile ("/proc" </> pid </> "stat") >>= \st -> evaluate (length st) >> pure st)
      pure $ case r of
        Left (_ :: IOException) -> Nothing
        -- the state follows the parenthesised command name
        Right st -> Just (take 1 (drop 2 (dropWhile (/= ')') st)))

hangingProps :: [Prop]
hangingProps = [PEq (Var "x") (Lit 1)]

-- | The phase-one SMT for these props, encoded with abstract arithmetic.
abstractQuery :: [Prop] -> String
abstractQuery ps = case assertPropsAbstract cfg ps of
  Left e -> internalError $ "could not encode abstract query: " <> e
  Right q -> TL.unpack (formatSMT2 q.query)
  where cfg = testEnv.config { abstractArith = True, simp = False }

-- The test binary doubles as a fake SMT solver, so the fixture works on every OS and is never installed
hangingSolverFlag :: String
hangingSolverFlag = "--hevm-fake-hanging-solver"

-- Acks every command and never answers (check-sat), unless the query set :status unsat
hangingSolverMain :: IO ()
hangingSolverMain = fakeSolver $ \unsat -> if unsat then putStrLn "unsat" else forever $ threadDelay 1_000_000

randomSolverFlag :: String
randomSolverFlag = "--hevm-fake-random-solver"

-- Records its pid in the directory, holding a lock on that file until it exits, then answers each (check-sat) after up to maxDelay ms with
-- unsat or unknown at random, or unsat if the query set :status unsat. One in eight hangs for a
-- minute, so a query that an abort fails to cancel is noticed.
randomSolverMain :: FilePath -> Int -> IO ()
randomSolverMain dir maxDelay = do
  pid <- show <$> getCurrentPid
  h <- openFile (dir </> pid) ReadWriteMode
  hLock h ExclusiveLock
  t <- getMonotonicTimeNSec
  gen <- newIORef (t * 6364136223846793005 + read pid)
  fakeSolver $ \unsat -> do
    r <- atomicModifyIORef' gen (\x -> let x' = x * 6364136223846793005 + 1442695040888963407 in (x', x' `shiftR` 33))
    threadDelay (fromIntegral (r `mod` fromIntegral (maxDelay + 1)) * 1000)
    when (not unsat && r `shiftR` 11 `mod` 8 == 0) $ threadDelay 60_000_000
    putStrLn $ if unsat || even (r `shiftR` 7) then "unsat" else "unknown"
  hClose h

-- Acks every command, and calls the answer to (check-sat) with whether the query set :status unsat
fakeSolver :: (Bool -> IO ()) -> IO ()
fakeSolver answer = hSetBuffering stdout LineBuffering >> go False ""
  where
    go unsat pending = do
      eof <- isEOF
      unless eof $ do
        line <- getLine
        let cmd = if null pending then line else pending <> "\n" <> line
            (depth, sawToken) = scanSMT cmd
        if depth > 0 || not sawToken then go (sawUnsat unsat cmd) (if sawToken then cmd else "")
        else reply (sawUnsat unsat cmd) cmd
    sawUnsat unsat cmd = unsat || "(set-info :status unsat)" `List.isInfixOf` cmd
    reply unsat cmd
      | not ("(check-sat)" `List.isInfixOf` cmd) = putStrLn "success" >> go unsat ""
      | otherwise = answer unsat >> go unsat ""

data ScanState = Normal | InString | InQuoted | InComment

-- A command may span several lines, and one reply is owed per command rather
-- than per line, so the reader tracks paren depth. Parens inside string
-- literals, quoted symbols and comments are not structure. Also reports
-- whether any token was seen at all, so blank lines are not mistaken for a
-- complete command -- hevm emits some commands with a trailing newline.
scanSMT :: String -> (Int, Bool)
scanSMT = go Normal 0 False
  where
    go _ depth tok [] = (depth, tok)
    go Normal depth tok (c:cs) = case c of
      '(' -> go Normal (depth + 1) True cs
      ')' -> go Normal (depth - 1) True cs
      '"' -> go InString depth True cs
      '|' -> go InQuoted depth True cs
      ';' -> go InComment depth tok cs
      _   -> go Normal depth (tok || not (isSpace c)) cs
    go InString depth tok ('"':'"':cs) = go InString depth tok cs
    go InString depth tok ('"':cs) = go Normal depth tok cs
    go InQuoted depth tok ('|':cs) = go Normal depth tok cs
    go InComment depth tok ('\n':cs) = go Normal depth tok cs
    go st depth tok (_:cs) = go st depth tok cs
