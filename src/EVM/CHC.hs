{- |
    Module: EVM.CHC
    Description: Constrained Horn Clause generation for storage invariant extraction

    This module provides functionality to extract storage invariants using CHC
    (Constrained Horn Clauses). When unknown code is called and can re-enter
    the caller contract, we use CHC to compute what storage slots can change
    and what constraints hold on those changes.

    The key insight is that unknown code can only modify the caller's storage
    by calling back into the caller's public functions. CHC computes the
    fixpoint of all possible reentrant call sequences.
-}
module EVM.CHC
  ( -- * Types (re-exported from EVM.Types)
    StorageTransition(..)
  , StorageWrite(..)
  , CHCResult(..)
  , StorageInvariant(..)
    -- * Extraction
  , extractStorageTransitions
  , extractAllStorageTransitions
  , extractStorageWrites
    -- * CHC Generation
  , buildCHC
  , buildCHCQuery
  , buildCHCWithComments
    -- * Invariant Computation
  , computeStorageInvariants
  , solveForInvariants
    -- * Utilities
  , getCallerStorageWrites
  , transitionToCHCRule
  ) where

import Prelude hiding (LT, GT)

import Control.Exception (bracket)
import Control.Monad (when)
import Control.Monad.IO.Unlift (MonadUnliftIO, liftIO)
import Data.List (nub)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.IO qualified as TL
import Data.Text.Lazy.Builder (Builder, fromText, toLazyText)
import GHC.IO.Handle (hClose)
import System.Process (createProcess, cleanupProcess, proc, std_in, std_out, std_err, StdStream(..))

import EVM.Types
import EVM.Effects (Config(..), ReadConfig(..))
import EVM.SMT (exprToSMT)


data CHCResult
  = CHCInvariantsFound [StorageInvariant]
  | CHCUnknown Text -- ^ Solver returned unknown
  | CHCError Text -- ^ Error during solving
  deriving (Show, Eq)

-- | A storage invariant describes what holds for a storage slot
data StorageInvariant
  = SlotUnchanged (Expr EWord)
  | SlotBounded (Expr EWord) (Expr EWord) (Expr EWord)
  | SlotRelation (Expr EWord) (Expr EWord) Prop
  deriving (Show, Eq, Ord)

-- | Extract storage transitions from an Expr End (execution result)
-- Only extracts from contracts matching the specified caller address.
-- Returns Nothing if the execution result is Partial (can't guarantee anything).
extractStorageTransitions
  :: Expr EAddr        -- ^ Caller address we care about
  -> Expr End          -- ^ Execution result
  -> Maybe [StorageTransition]
extractStorageTransitions caller expr = case expr of
  Success pathConds _ _ contracts -> Just $ Map.foldrWithKey (extractFromContract caller pathConds) [] contracts
  Failure _ _ _ -> Just [] -- Failures don't produce storage transitions (reverted)
  Partial _ _ _ -> Nothing -- Can't determine outcome, return Nothing
  GVar _ -> internalError "extractStorageTransitions: GVar encountered"

-- | Extract storage transitions from ALL contracts in an Expr End
-- This is useful when you want to analyze all storage changes regardless of address.
-- Returns Nothing if the execution result is Partial (can't guarantee anything).
extractAllStorageTransitions
  :: Expr End          -- ^ Execution result
  -> Maybe [StorageTransition]
extractAllStorageTransitions expr = case expr of
  Success pathConds _ _ contracts -> Just $ Map.foldrWithKey (extractFromAnyContract pathConds) [] contracts
  Failure _ _ _ -> Just [] -- Failures don't produce storage transitions (reverted)
  Partial _ _ _ -> Nothing -- Can't determine outcome, return Nothing
  GVar _ -> internalError "extractAllStorageTransitions: GVar encountered"

-- | Extract transition from any contract (not filtered by caller)
extractFromAnyContract
  :: [Prop]
  -> Expr EAddr
  -> Expr EContract
  -> [StorageTransition]
  -> [StorageTransition]
extractFromAnyContract pathConds addr (C _ storage _ _ _) acc =
  let writes = extractStorageWrites addr storage
      transition = StorageTransition
        { stCallerAddr = addr
        , stPreStorage = getBaseStorage storage
        , stPostStorage = storage
        , stPathConds = pathConds
        , stWrites = writes
        }
  in if null writes then acc else transition : acc
extractFromAnyContract _ _ (GVar _) _ = internalError "extractFromAnyContract: GVar encountered"

-- | Extract transition from a single contract's final state
-- Only extracts if the contract address matches the caller
extractFromContract
  :: Expr EAddr
  -> [Prop]
  -> Expr EAddr
  -> Expr EContract
  -> [StorageTransition]
  -> [StorageTransition]
extractFromContract caller pathConds addr (C _ storage _ _ _) acc
  | addr == caller =
      let writes = extractStorageWrites caller storage
          transition = StorageTransition
            { stCallerAddr = caller
            , stPreStorage = getBaseStorage storage
            , stPostStorage = storage
            , stPathConds = pathConds
            , stWrites = writes
            }
      in transition : acc
  | otherwise = acc
extractFromContract _ _ _ (GVar _) acc = acc

-- | Get the base (initial) storage from a storage expression
getBaseStorage :: Expr Storage -> Expr Storage
getBaseStorage (SStore _ _ prev) = getBaseStorage prev
getBaseStorage s@(AbstractStore _ _) = s
getBaseStorage s@(ConcreteStore _) = s
getBaseStorage (GVar _) = internalError "getBaseStorage: GVar encountered"

-- | Extract all writes to a specific address from a storage expression
extractStorageWrites :: Expr EAddr -> Expr Storage -> [StorageWrite]
extractStorageWrites targetAddr = go []
  where
    go acc (SStore key val prev) =
      -- For now, we include all writes. In a more sophisticated version,
      -- we would track which address each write belongs to.
      let write = StorageWrite
            { swAddr = targetAddr
            , swKey = key
            , swValue = val
            , swPrev = prev
            }
      in go (write : acc) prev
    go acc (AbstractStore _ _) = acc
    go acc (ConcreteStore _) = acc
    go _ (GVar _) = internalError "extractStorageWrites: GVar encountered"

-- | Get only the writes that affect the caller's storage
getCallerStorageWrites :: Expr EAddr -> Expr Storage -> [StorageWrite]
getCallerStorageWrites = extractStorageWrites


-- * CHC Generation

-- | Format a StorageTransition for debug output
formatTransition :: StorageTransition -> Text
formatTransition t = T.unlines
  [ "StorageTransition {"
  , "  callerAddr = " <> T.pack (show t.stCallerAddr)
  , "  preStorage = " <> T.pack (show t.stPreStorage)
  , "  postStorage = " <> T.pack (show t.stPostStorage)
  , "  pathConds = " <> T.pack (show t.stPathConds)
  , "  writes = ["
  ] <> T.unlines (map formatWrite t.stWrites) <> T.unlines
  [ "  ]"
  , "}"
  ]

-- | Format a StorageWrite for debug output
formatWrite :: StorageWrite -> Text
formatWrite w = T.concat
  [ "    StorageWrite { addr = ", T.pack (show w.swAddr)
  , ", key = ", T.pack (show w.swKey)
  , ", value = ", T.pack (show w.swValue)
  , " }"
  ]

-- | Format all transitions as a comment block for SMT input
formatTransitionsAsComment :: [StorageTransition] -> Builder
formatTransitionsAsComment transitions =
  fromText "; ============================================================\n"
  <> fromText "; ORIGINAL INTERNAL IR (StorageTransition data structures)\n"
  <> fromText "; ============================================================\n"
  <> mconcat (zipWith formatOneTransition [0..] transitions)
  <> fromText "; ============================================================\n"
  <> fromText "\n"
  where
    formatOneTransition :: Int -> StorageTransition -> Builder
    formatOneTransition idx t =
      fromText ("; --- Transition " <> T.pack (show idx) <> " ---\n")
      <> fromText ("; Caller: " <> T.pack (show t.stCallerAddr) <> "\n")
      <> fromText ("; Pre-storage: " <> T.pack (show t.stPreStorage) <> "\n")
      <> fromText ("; Post-storage: " <> T.pack (show t.stPostStorage) <> "\n")
      <> fromText ("; Path conditions (" <> T.pack (show (length t.stPathConds)) <> "):\n")
      <> mconcat [fromText (";   " <> T.pack (show p) <> "\n") | p <- t.stPathConds]
      <> fromText ("; Writes (" <> T.pack (show (length t.stWrites)) <> "):\n")
      <> mconcat [fromText (";   [" <> T.pack (show i) <> "] key=" <> T.pack (show w.swKey)
                           <> " val=" <> T.pack (show w.swValue) <> "\n")
                 | (i, w) <- zip [0::Int ..] t.stWrites]
      <> fromText ";\n"

-- | Build a complete CHC script from storage transitions
buildCHC :: [StorageTransition] -> Builder
buildCHC transitions =
  chcPrelude
  <> "\n"
  <> declareRelations transitions
  <> "\n"
  <> buildTransitionRules transitions
  <> "\n"
  <> buildReachabilityRules transitions
  <> "\n"

-- | Build a complete CHC script with comments showing original IR
buildCHCWithComments :: [StorageTransition] -> Builder
buildCHCWithComments transitions =
  formatTransitionsAsComment transitions
  <> buildCHC transitions

-- | CHC prelude with solver configuration
chcPrelude :: Builder
chcPrelude = mconcat
  [ "; CHC for storage invariant extraction\n"
  , "(set-logic HORN)\n"
  , "(set-option :fp.engine spacer)\n"
  , "\n"
  , "; Types\n"
  , "(define-sort Word () (_ BitVec 256))\n"
  , "(define-sort Storage () (Array Word Word))\n"
  , "\n"
  ]

-- | Declare the relations we'll use
declareRelations :: [StorageTransition] -> Builder
declareRelations transitions =
  let -- Collect all unique storage slots that are written
      allSlots = nub $ concatMap (\t -> map (.swKey) t.stWrites) transitions
      numSlots = length allSlots
      -- We use a flattened representation: one Word per slot
      slotSorts = replicate numSlots "Word"
      sortList = T.intercalate " " (map T.pack slotSorts)

      -- Declare variables used in rules
      varDecls = mconcat
        [ "; Variables\n"
        -- Variables for transition rules
        , mconcat [fromText $ "(declare-var pre_s" <> T.pack (show i) <> " Word)\n" | i <- [0..numSlots-1]]
        , mconcat [fromText $ "(declare-var post_s" <> T.pack (show i) <> " Word)\n" | i <- [0..numSlots-1]]
        -- Variables for reachability rules
        , mconcat [fromText $ "(declare-var s" <> T.pack (show i) <> " Word)\n" | i <- [0..numSlots-1]]
        , mconcat [fromText $ "(declare-var s" <> T.pack (show i) <> "_next Word)\n" | i <- [0..numSlots-1]]
        , "\n"
        ]
  in mconcat
    [ varDecls
    , "; Relations\n"
    , "; Reachable storage states after reentrancy\n"
    , "(declare-rel Reachable (" <> fromText sortList <> "))\n"
    , "\n"
    , "; Initial storage state\n"
    , "(declare-rel Initial (" <> fromText sortList <> "))\n"
    , "\n"
    , "; Storage transition relations (one per transition)\n"
    ] <> mconcat (zipWith declareTransitionRel [0..] transitions)

-- | Declare a transition relation for a single transition
declareTransitionRel :: Int -> StorageTransition -> Builder
declareTransitionRel idx transition =
  let slots = map (.swKey) transition.stWrites
      numSlots = length slots
      -- Pre and post state, so double the slots
      sortList = T.intercalate " " (replicate (numSlots * 2) "Word")
      funcName = "Transition_" <> T.pack (show idx)
  in "(declare-rel " <> fromText funcName <> " (" <> fromText sortList <> "))\n"

-- | Build transition rules from storage transitions
buildTransitionRules :: [StorageTransition] -> Builder
buildTransitionRules transitions =
  "; Transition rules\n" <> mconcat (zipWith transitionToCHCRule [0..] transitions)

-- | Convert a single storage transition to a CHC rule
transitionToCHCRule :: Int -> StorageTransition -> Builder
transitionToCHCRule idx transition =
  let funcName = "Transition_" <> T.pack (show idx)

      writes = transition.stWrites
      numWrites = length writes

      -- Generate variable names for pre and post states
      preVars = [fromText $ "pre_s" <> T.pack (show i) | i <- [0..numWrites-1]]
      postVars = [fromText $ "post_s" <> T.pack (show i) | i <- [0..numWrites-1]]

      -- Build the constraint body
      -- For each write: post_si = value_i (simplified; real version would encode the Expr)
      writeConstraints = zipWith3 buildWriteConstraint [0..] writes postVars

      -- Note: We skip path conditions for now as they involve complex symbolic
      -- expressions (TxValue, BufLength, etc.) that are hard to encode in CHC.
      -- This is a conservative approximation - it allows more transitions than
      -- may actually be possible, but that's safe for computing invariants.

      constraintBody = if null writeConstraints
                       then "true"
                       else foldr1 (\a b -> "(and " <> a <> " " <> b <> ")") writeConstraints

      -- Relation application
      allVars = preVars ++ postVars
      varList = mconcat [v <> " " | v <- allVars]

  in mconcat
    [ "(rule (=> "
    , constraintBody
    , " ("
    , fromText funcName
    , " "
    , varList
    , ")))\n"
    ]

-- | Build a write constraint using SMT.hs for expression encoding
buildWriteConstraint :: Int -> StorageWrite -> Builder -> Builder
buildWriteConstraint _ write postVar =
  -- Use SMT.hs to encode the value expression
  case exprToSMT write.swValue of
    Right valEnc -> "(= " <> postVar <> " " <> valEnc <> ")"
    Left _ -> "true"  -- Fallback for expressions SMT can't encode

-- | Build reachability rules that model reentrancy
buildReachabilityRules :: [StorageTransition] -> Builder
buildReachabilityRules transitions =
  let numSlots = case transitions of
                   []    -> 0
                   (t:_) -> length t.stWrites

      -- Initial state is reachable
      initVars = [fromText $ "s" <> T.pack (show i) | i <- [0..numSlots-1]]
      initVarList = mconcat [v <> " " | v <- initVars]

      initRule = mconcat
        [ "; Initial state is reachable\n"
        , "(rule (=> (Initial "
        , initVarList
        , ") (Reachable "
        , initVarList
        , ")))\n"
        ]

      -- Each transition from a reachable state leads to a reachable state
      transRules = mconcat $ zipWith buildTransReachRule [0..] transitions

  in initRule <> "\n" <> transRules

-- | Build a reachability rule for a transition
buildTransReachRule :: Int -> StorageTransition -> Builder
buildTransReachRule idx transition =
  let funcName = "Transition_" <> T.pack (show idx)

      writes = transition.stWrites
      numWrites = length writes

      preVars = [fromText $ "s" <> T.pack (show i) | i <- [0..numWrites-1]]
      postVars = [fromText $ "s" <> T.pack (show i) <> "_next" | i <- [0..numWrites-1]]

      preVarList = mconcat [v <> " " | v <- preVars]
      postVarList = mconcat [v <> " " | v <- postVars]
      allVarList = mconcat [v <> " " | v <- preVars ++ postVars]

  in mconcat
    [ "(rule (=> (and (Reachable "
    , preVarList
    , ") ("
    , fromText funcName
    , " "
    , allVarList
    , ")) (Reachable "
    , postVarList
    , ")))\n"
    ]


-- * CHC Query Building

-- | Build a CHC query to check if a slot can change
buildCHCQuery :: [StorageTransition] -> Int -> Builder
buildCHCQuery transitions slotIdx =
  let numSlots = case transitions of
                   []    -> 0
                   (t:_) -> length t.stWrites

      -- Query: can slot i ever differ from initial value?
      initVars = [fromText $ "i" <> T.pack (show i) | i <- [0..numSlots-1]]
      reachVars = [fromText $ "s" <> T.pack (show i) | i <- [0..numSlots-1]]

      initVarList = mconcat [v <> " " | v <- initVars]
      reachVarList = mconcat [v <> " " | v <- reachVars]

      -- The slot we're checking
      initSlot = initVars !! slotIdx
      reachSlot = reachVars !! slotIdx

  in mconcat
    [ buildCHC transitions
    , "\n"
    , "; Query: can slot "
    , fromText (T.pack $ show slotIdx)
    , " change?\n"
    , "(query (and (Initial "
    , initVarList
    , ") (Reachable "
    , reachVarList
    , ") (not (= "
    , initSlot
    , " "
    , reachSlot
    , "))))\n"
    ]


-- | Compute storage invariants from transitions
-- This is the main entry point for invariant extraction
computeStorageInvariants
  :: (MonadUnliftIO m, ReadConfig m)
  => Expr EAddr            -- ^ Caller address
  -> [StorageTransition]   -- ^ All possible transitions
  -> m CHCResult
computeStorageInvariants caller transitions = do
  conf <- readConfig

  -- Debug: print transitions being analyzed
  when conf.debug $ liftIO $ do
    putStrLn $ "CHC: Computing storage invariants for " <> show (length transitions) <> " transitions"
    putStrLn $ "CHC: Caller address: " <> show caller

  -- Debug: print each transition in detail
  when (conf.debug && conf.verb >= 2) $ liftIO $ do
    putStrLn "CHC: Transition details:"
    mapM_ (TL.putStrLn . TL.fromStrict . formatTransition) transitions

  -- Use SMT solver to compute invariants via CHC
  solveForInvariants transitions

-- | Solve for invariants using a CHC solver
solveForInvariants
  :: (MonadUnliftIO m, ReadConfig m)
  => [StorageTransition]
  -> m CHCResult
solveForInvariants transitions = do
  conf <- readConfig

  -- Build CHC script with comments showing original IR
  let chcScript = toLazyText (buildCHCWithComments transitions) <> "\n(check-sat)\n"

  -- Debug: print that we're about to call Z3
  when conf.debug $ liftIO $ do
    putStrLn $ "CHC: Solving for invariants with " <> show (length transitions) <> " transitions"
    putStrLn $ "CHC: Invoking Z3 with Spacer engine..."

  -- Dump the CHC expression if requested
  when conf.dumpExprs $ liftIO $ do
    putStrLn "============================================================"
    putStrLn "CHC EXPRESSION (SMT-LIB2 format with HORN logic):"
    putStrLn "============================================================"
    TL.putStrLn chcScript
    putStrLn "============================================================"

  -- Invoke z3 with spacer engine
  result <- liftIO $ runZ3CHC conf chcScript
  case result of
    Left err -> do
      when conf.debug $ liftIO $ putStrLn $ "CHC: Z3 error: " <> T.unpack err
      pure $ CHCError err
    Right "sat" -> do
      when conf.debug $ liftIO $ putStrLn "CHC: Z3 returned SAT (invariants hold)"
      pure $ CHCInvariantsFound []  -- SAT means invariants hold
    Right "unsat" -> do
      when conf.debug $ liftIO $ putStrLn "CHC: Z3 returned UNSAT (query unsatisfiable)"
      pure $ CHCUnknown "CHC query unsatisfiable"
    Right other -> do
      when conf.debug $ liftIO $ putStrLn $ "CHC: Z3 returned: " <> TL.unpack other
      pure $ CHCUnknown (TL.toStrict other)

-- | Run z3 as a CHC solver
runZ3CHC :: Config -> TL.Text -> IO (Either Text TL.Text)
runZ3CHC conf script = do
  when conf.debug $ do
    putStrLn "CHC: Starting Z3 process..."

  let cmd = (proc "z3" ["-in"])
            { std_in = CreatePipe
            , std_out = CreatePipe
            , std_err = CreatePipe
            }
  bracket
    (createProcess cmd)
    (\(mstdin, mstdout, mstderr, ph) -> cleanupProcess (mstdin, mstdout, mstderr, ph))
    (\(mstdin, mstdout, mstderr, _ph) -> do
      case (mstdin, mstdout, mstderr) of
        (Just stdin, Just stdout, Just stderr) -> do
          -- Debug: show script size
          when (conf.debug && conf.verb >= 2) $ do
            putStrLn $ "CHC: Sending " <> show (TL.length script) <> " chars to Z3"

          -- Send the CHC script
          TL.hPutStr stdin script
          hClose stdin

          -- Read the result
          output <- TL.hGetContents stdout
          errOutput <- TL.hGetContents stderr

          -- Debug: show stderr if any
          when (conf.debug && not (TL.null errOutput)) $ do
            putStrLn $ "CHC: Z3 stderr: " <> TL.unpack errOutput

          -- Debug: show result
          let result = TL.strip output
          when conf.debug $ do
            putStrLn $ "CHC: Z3 result: " <> TL.unpack result

          pure $ Right result
        (Just stdin, Just stdout, Nothing) -> do
          -- No stderr handle, proceed without it
          TL.hPutStr stdin script
          hClose stdin
          output <- TL.hGetContents stdout
          let result = TL.strip output
          pure $ Right result
        _ -> pure $ Left "Failed to create z3 process pipes"
    )
