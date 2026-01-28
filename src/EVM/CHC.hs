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

    We use Z3's Spacer engine to synthesize invariants automatically. The solver
    finds the inductive invariant that proves the property, rather than us
    computing expected values and asking the solver to verify.
-}
module EVM.CHC
  ( -- * Types (re-exported from EVM.Types)
    StorageTransition(..)
  , StorageWrite(..)
  , CHCResult(..)
  , SynthesizedInvariant(..)
  , SlotConstraint(..)
    -- * Extraction
  , extractAllStorageTransitions
  , extractStorageWrites
    -- * CHC Generation
  , buildCHC
  , buildCHCWithComments
    -- * Invariant Computation
  , computeStorageInvariants
  , solveForInvariants
    -- * Utilities
  , getCallerStorageWrites
  , transitionToCHCRule
    -- * Certificate Parsing
  , parseCertificate
  ) where

import Prelude hiding (LT, GT)

import Control.Exception (bracket)
import Control.Monad (when)
import Control.Monad.IO.Unlift (MonadUnliftIO, liftIO)
import Data.List (nub, elemIndex)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.IO qualified as TL
import Data.Text.Lazy.Builder (Builder, fromText, toLazyText)
import GHC.IO.Handle (hClose)
import Numeric (readHex)
import System.Process (createProcess, cleanupProcess, proc, std_in, std_out, std_err, StdStream(..))

import EVM.Types
import EVM.Effects (Config(..), ReadConfig(..))
import EVM.Format (formatSynthesizedInvariant)
import EVM.SMT (exprToSMT)


data CHCResult
  = CHCInvariantSynthesized SynthesizedInvariant
    -- ^ Solver synthesized an invariant (returned UNSAT with certificate)
  | CHCNoInvariant Text
    -- ^ Solver returned SAT - no invariant exists (with counterexample info)
  | CHCUnknown Text
    -- ^ Solver returned unknown
  | CHCError Text
    -- ^ Error during solving
  deriving (Show, Eq)

-- SynthesizedInvariant and SlotConstraint are defined in EVM.Types

-- | Extract storage transitions from ALL contracts in an Expr End
-- This is useful when you want to analyze all storage changes regardless of address.
-- Returns Nothing if the execution result is Partial (can't guarantee anything).
extractAllStorageTransitions
  :: Expr EAddr -- ^ contract
  -> Expr End   -- ^ Execution result
  -> Maybe [StorageTransition]
extractAllStorageTransitions addr expr = case expr of
  Success pathConds _ _ contracts ->
     let filteredC = Map.filterWithKey (\caddr _ -> caddr == addr) contracts
     in Just $ Map.foldrWithKey (extractFromAnyContract pathConds) [] filteredC
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

-- | Get the base (initial) storage from a storage expression
getBaseStorage :: Expr Storage -> Expr Storage
getBaseStorage (SStore _ _ prev) = getBaseStorage prev
getBaseStorage s@(AbstractStore _ _) = s
getBaseStorage s@(ConcreteStore _) = s
getBaseStorage (GVar _) = internalError "getBaseStorage: GVar encountered"

-- | Extract all writes to a specific address from a storage expression
-- Handles both SStore chains and ConcreteStore (where writes are merged into the map)
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
    -- For ConcreteStore, each key-value pair represents a write from the initial 0 state
    -- We extract these as writes so CHC can analyze them
    go acc (ConcreteStore m) =
      let baseStore = ConcreteStore mempty
          writes = [StorageWrite
                     { swAddr = targetAddr
                     , swKey = Lit k
                     , swValue = Lit v
                     , swPrev = baseStore
                     }
                   | (k, v) <- Map.toList m
                   , v /= 0  -- Only include non-zero values (0 is the default)
                   ]
      in acc ++ writes
    go _ (GVar _) = internalError "extractStorageWrites: GVar encountered"

-- | Get only the writes that affect the caller's storage
getCallerStorageWrites :: Expr EAddr -> Expr Storage -> [StorageWrite]
getCallerStorageWrites = extractStorageWrites

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

-- | Build the base CHC script (without the query)
buildCHCBase :: [StorageTransition] -> Builder
buildCHCBase transitions =
  chcPrelude
  <> "\n"
  <> declareRelations transitions
  <> "\n"
  <> buildTransitionRules transitions
  <> "\n"
  <> buildReachabilityRules transitions

-- | Build a complete CHC script from storage transitions
-- The query asks for invariant synthesis - the solver discovers the invariant
buildCHC :: [StorageTransition] -> Builder
buildCHC transitions =
  buildCHCBase transitions
  <> "\n"
  <> buildSynthesisQuery transitions
  <> "\n"

-- | Build a complete CHC script with comments showing original IR
buildCHCWithComments :: [StorageTransition] -> Builder
buildCHCWithComments transitions =
  formatTransitionsAsComment transitions
  <> buildCHC transitions

-- | CHC prelude with solver configuration
-- Configures Z3's Spacer engine to synthesize and output invariants
chcPrelude :: Builder
chcPrelude = mconcat
  [ "; CHC for storage invariant synthesis\n"
  , "(set-logic HORN)\n"
  , "(set-option :fp.engine spacer)\n"
  , "; Disable inlining to preserve relation structure in certificate\n"
  , "(set-option :fp.xform.inline_eager false)\n"
  , "(set-option :fp.xform.inline_linear false)\n"
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

      -- Build a list of slot keys for substitution
      slotKeys = map (.swKey) writes

      -- Generate variable names for pre and post states
      preVars = [fromText $ "pre_s" <> T.pack (show i) | i <- [0..numWrites-1]]
      postVars = [fromText $ "post_s" <> T.pack (show i) | i <- [0..numWrites-1]]

      -- Build the constraint body
      -- For each write: post_si = value_i (simplified; real version would encode the Expr)
      writeConstraints = zipWith3 (buildWriteConstraint slotKeys) [0..] writes postVars

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
-- The slotKeys list maps slot indices to their key expressions
buildWriteConstraint :: [Expr EWord] -> Int -> StorageWrite -> Builder -> Builder
buildWriteConstraint slotKeys _ write postVar =
  -- Substitute SLoad expressions with pre-state variables before encoding
  let substValue = substSLoadsInExpr slotKeys write.swValue
  in case exprToSMT substValue of
    Right valEnc -> "(= " <> postVar <> " " <> valEnc <> ")"
    Left _ -> "true"  -- Fallback for expressions SMT can't encode

-- | Substitute SLoad expressions from base storage with pre-state variables
-- For example, SLoad (Lit 0) baseStorage becomes Var "pre_s0" if slot 0 is at index 0
substSLoadsInExpr :: [Expr EWord] -> Expr EWord -> Expr EWord
substSLoadsInExpr slotKeys = go
  where
    go :: Expr EWord -> Expr EWord
    go expr = case expr of
      -- Handle SLoad from base storage
      SLoad slot storage | isBaseStorage storage ->
        case elemIndex slot slotKeys of
          Just i  -> Var ("pre_s" <> T.pack (show i))
          Nothing -> expr  -- Slot not in our tracked list, keep as-is
      -- Recursively transform subexpressions
      Add a b -> Add (go a) (go b)
      Sub a b -> Sub (go a) (go b)
      Mul a b -> Mul (go a) (go b)
      Div a b -> Div (go a) (go b)
      SDiv a b -> SDiv (go a) (go b)
      Mod a b -> Mod (go a) (go b)
      SMod a b -> SMod (go a) (go b)
      AddMod a b c -> AddMod (go a) (go b) (go c)
      MulMod a b c -> MulMod (go a) (go b) (go c)
      Exp a b -> Exp (go a) (go b)
      SEx a b -> SEx (go a) (go b)
      Min a b -> Min (go a) (go b)
      Max a b -> Max (go a) (go b)
      LT a b -> LT (go a) (go b)
      GT a b -> GT (go a) (go b)
      LEq a b -> LEq (go a) (go b)
      GEq a b -> GEq (go a) (go b)
      SLT a b -> SLT (go a) (go b)
      SGT a b -> SGT (go a) (go b)
      Eq a b -> Eq (go a) (go b)
      IsZero a -> IsZero (go a)
      And a b -> And (go a) (go b)
      Or a b -> Or (go a) (go b)
      Xor a b -> Xor (go a) (go b)
      Not a -> Not (go a)
      SHL a b -> SHL (go a) (go b)
      SHR a b -> SHR (go a) (go b)
      SAR a b -> SAR (go a) (go b)
      -- Terminal cases - no transformation needed
      Lit _ -> expr
      Var _ -> expr
      -- Other cases - return as-is for now
      _ -> expr

    isBaseStorage :: Expr Storage -> Bool
    isBaseStorage (AbstractStore _ _) = True
    isBaseStorage (ConcreteStore _) = False
    isBaseStorage (SStore _ _ _) = False
    isBaseStorage (GVar _) = False

-- | Build reachability rules that model reentrancy
buildReachabilityRules :: [StorageTransition] -> Builder
buildReachabilityRules transitions =
  let numSlots = case transitions of
                   []    -> 0
                   (t:_) -> length t.stWrites

      -- Initial state fact: all storage slots are 0
      -- In Solidity, uninitialized storage is always 0
      zeroWord = "#x" <> T.replicate 64 "0"
      zeroArgs = T.intercalate " " (replicate numSlots zeroWord)
      initFact = mconcat
        [ "; Initial state: all storage slots are 0\n"
        , "(rule (Initial " <> fromText zeroArgs <> "))\n"
        ]

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

  in initFact <> "\n" <> initRule <> "\n" <> transRules

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

-- | Extract concrete literal values from an expression
extractLitValue :: Expr EWord -> Maybe W256
extractLitValue (Lit w) = Just w
extractLitValue _ = Nothing

-- | Collect all concrete values that can be written to each slot
-- Returns a list of (slot index, list of possible values including initial 0)
collectPossibleValues :: [StorageTransition] -> [[W256]]
collectPossibleValues transitions =
  let numSlots = case transitions of
                   []    -> 0
                   (t:_) -> length t.stWrites
      -- For each slot index, collect all concrete values written to it
      valuesPerSlot = [[0] | _ <- [0..numSlots-1]]  -- Start with initial value 0
      -- Extract values from each transition
      addTransitionValues acc transition =
        zipWith addValue acc (map (.swValue) transition.stWrites)
      addValue vals expr = case extractLitValue expr of
        Just v  -> nub (v : vals)
        Nothing -> vals  -- Keep existing values if not a literal
  in foldl addTransitionValues valuesPerSlot transitions

-- | Format a W256 as a 256-bit bitvector literal for SMT-LIB2
-- Uses decimal format: (_ bvN 256) where N is the decimal value
formatBV256 :: W256 -> Builder
formatBV256 w = "(_ bv" <> fromText (T.pack (show (toInteger w))) <> " 256)"

-- | Build a synthesis query that asks the solver to find an invariant
-- When Z3 returns UNSAT, it means no "bad" state is reachable, and the
-- certificate contains the synthesized invariant for the Reachable relation.
--
-- The key insight: we create a safety property based on the concrete values
-- observed in the code. The safety property says "error if we reach a state
-- that's not the initial value (0) and not any of the written values".
-- Z3 then computes the strongest invariant that proves this property.
buildSynthesisQuery :: [StorageTransition] -> Builder
buildSynthesisQuery transitions =
  let numSlots = case transitions of
                   []    -> 0
                   (t:_) -> length t.stWrites
      possibleValues = collectPossibleValues transitions
  in if numSlots == 0
     then "; No storage slots written, no query needed\n"
     else mconcat
       [ "; Query for invariant synthesis\n"
       , "; Safety property: storage can only have values that appear in the code\n"
       , "; (initial value 0 + all written values)\n"
       , "(declare-rel Err ())\n"
       , "\n"
       , "; Error if we reach a state outside the observed values\n"
       , buildErrorCondition numSlots possibleValues
       , "\n"
       , "; Request the invariant certificate\n"
       , "(query Err :print-certificate true)\n"
       ]

-- | Build the error condition based on possible values
-- Error if Reachable(s0, s1, ...) and none of the slots match their allowed values
buildErrorCondition :: Int -> [[W256]] -> Builder
buildErrorCondition numSlots possibleValues =
  let -- Build condition for each slot: (not (or (= si v1) (= si v2) ...))
      slotConditions = zipWith buildSlotCondition [0..] possibleValues

      -- Variables for the reachable state
      vars = [fromText $ "s" <> T.pack (show i) | i <- [0..numSlots-1]]
      varList = mconcat [v <> " " | v <- vars]

      -- Combine all slot conditions with AND
      -- Error if ANY slot is outside its allowed values
      combinedCondition = case slotConditions of
        []  -> "false"
        [c] -> c
        cs  -> "(or " <> mconcat [c <> " " | c <- cs] <> ")"

  in mconcat
       [ "(rule (=> (and (Reachable "
       , varList
       , ") "
       , combinedCondition
       , ") Err))\n"
       ]

-- | Build condition for a single slot being outside its allowed values
buildSlotCondition :: Int -> [W256] -> Builder
buildSlotCondition slotIdx values =
  let varName = fromText $ "s" <> T.pack (show slotIdx)
      -- (or (= si v1) (= si v2) ...) - slot matches one of the allowed values
      eqConditions = [(varName, v) | v <- values]
      orExpr = case eqConditions of
        []       -> "false"
        [(v, w)] -> "(= " <> v <> " " <> formatBV256 w <> ")"
        cs       -> "(or " <> mconcat ["(= " <> v <> " " <> formatBV256 w <> ") " | (v, w) <- cs] <> ")"
  in "(not " <> orExpr <> ")"



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
-- The solver synthesizes the invariant automatically via fixpoint computation.
-- - If Z3 returns UNSAT with a certificate, we extract the synthesized invariant.
-- - If Z3 returns SAT, there's a counterexample.
solveForInvariants
  :: (MonadUnliftIO m, ReadConfig m)
  => [StorageTransition]
  -> m CHCResult
solveForInvariants transitions = do
  conf <- readConfig

  let numSlots = case transitions of
                   []    -> 0
                   (t:_) -> length t.stWrites

      slotNames = ["s" <> T.pack (show i) | i <- [0..numSlots-1]]

  -- Handle the 0-slot case early - no storage is written, so the invariant is trivial
  when (numSlots == 0) $ do
    when conf.debug $ liftIO $
      putStrLn "CHC: No storage slots written, returning trivial invariant"
    pure ()

  if numSlots == 0
    then pure $ CHCInvariantSynthesized SynthesizedInvariant
           { siSlotNames = []
           , siRawSMT = "; No storage slots written"
           , siConstraints = []
           }
    else do
      -- Build CHC script - the solver will synthesize the invariant
      let chcScript = toLazyText (buildCHCWithComments transitions)

      -- Debug: print that we're about to call Z3
      when conf.debug $ liftIO $ do
        putStrLn $ "CHC: Requesting invariant synthesis for " <> show (length transitions) <> " transitions"
        putStrLn $ "CHC: Number of storage slots: " <> show numSlots
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
        Right output -> do
          let outputText = TL.toStrict (TL.strip output)
              outputLines = T.lines outputText

          when conf.debug $ liftIO $ do
            putStrLn $ "CHC: Z3 output lines: " <> show (length outputLines)

          case outputLines of
            ("unsat":certLines) -> do
              -- UNSAT - extract the synthesized invariant from the certificate
              let certificate = T.unlines certLines
              when conf.debug $ liftIO $ do
                if null certLines
                  then putStrLn "CHC: Z3 returned UNSAT (no certificate)"
                  else do
                    putStrLn "CHC: Z3 returned UNSAT with certificate"
                    putStrLn $ "CHC: Certificate:\n" <> T.unpack certificate

              -- Parse the certificate to extract the invariant
              let invariant = parseCertificate slotNames certificate
              when conf.debug $ liftIO $ do
                TL.putStrLn $ TL.fromStrict $ "CHC: " <> formatSynthesizedInvariant invariant

              pure $ CHCInvariantSynthesized invariant

            ("sat":cexLines) -> do
              -- SAT means there's a counterexample
              let cex = T.unlines cexLines
              when conf.debug $ liftIO $ do
                putStrLn "CHC: Z3 returned SAT - bad state is reachable"
                when (not (null cexLines)) $
                  putStrLn $ "CHC: Counterexample:\n" <> T.unpack cex
              pure $ CHCNoInvariant (if T.null cex then "Bad state is reachable" else cex)

            _ -> do
              when conf.debug $ liftIO $ putStrLn $ "CHC: Z3 returned unexpected: " <> T.unpack outputText
              pure $ CHCUnknown outputText


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


-- * Certificate Parsing

-- | Parse a Z3 certificate to extract the synthesized invariant
-- The certificate format from Z3's Spacer is typically:
--   (forall ((A (_ BitVec 256)) ...) (= (Reachable A ...) <body>))
-- where <body> describes the invariant and A, B, etc. are the slot variables.
parseCertificate :: [Text] -> Text -> SynthesizedInvariant
parseCertificate slotNames certificate =
  let -- Find the Reachable definition
      reachableDef = extractReachableDefinition certificate
      -- Extract the variable names from the forall or define-fun
      varNames = extractReachableVarNames certificate (length slotNames)
      constraints = parseConstraintsFromBody varNames reachableDef
  in SynthesizedInvariant
       { siSlotNames = slotNames
       , siRawSMT = certificate
       , siConstraints = constraints
       }

-- | Extract the body of the Reachable relation definition from the certificate
extractReachableDefinition :: Text -> Text
extractReachableDefinition cert =
  -- Look for (define-fun Reachable ... and extract the body
  let lines' = T.lines cert
      -- Find lines that are part of the Reachable definition
      inReachable = dropWhile (not . T.isInfixOf "Reachable") lines'
  in case inReachable of
       [] -> ""
       _  -> T.unlines inReachable

-- | Extract the variable names used in the Reachable relation from the certificate
-- Looks for patterns like:
--   (forall ((A (_ BitVec 256)) (B (_ BitVec 256))) (= (Reachable A B) ...))
-- or:
--   (define-fun Reachable ((A (_ BitVec 256)) (B (_ BitVec 256))) Bool ...)
-- Returns the variable names in order (e.g., ["A", "B"])
extractReachableVarNames :: Text -> Int -> [Text]
extractReachableVarNames cert numSlots =
  let -- Try to find forall pattern first
      forallVars = extractForallVars cert
      -- If that fails, try define-fun pattern
      defineFunVars = extractDefineFunVars cert
      foundVars = if null forallVars then defineFunVars else forallVars
  in if length foundVars >= numSlots
     then take numSlots foundVars
     else foundVars ++ [T.pack ("s" ++ show i) | i <- [length foundVars..numSlots-1]]

-- | Extract variable names from forall pattern
-- Pattern: (forall ((A (_ BitVec 256)) (B (_ BitVec 256))) (= (Reachable A B) ...))
extractForallVars :: Text -> [Text]
extractForallVars cert =
  -- Find "(forall ((" and extract the variable bindings
  case T.breakOn "(forall ((" cert of
    (_, "") -> []
    (_, rest) ->
      let afterForall = T.drop (T.length "(forall ((") rest
      in extractVarBindings afterForall

-- | Extract variable names from define-fun pattern
-- Pattern: (define-fun Reachable ((A (_ BitVec 256)) ...) Bool ...)
extractDefineFunVars :: Text -> [Text]
extractDefineFunVars cert =
  case T.breakOn "(define-fun Reachable ((" cert of
    (_, "") -> []
    (_, rest) ->
      let afterDefine = T.drop (T.length "(define-fun Reachable ((") rest
      in extractVarBindings afterDefine

-- | Extract variable names from a sequence of bindings like "A (_ BitVec 256)) (B (_ BitVec 256))"
extractVarBindings :: Text -> [Text]
extractVarBindings t = go t []
  where
    go txt acc =
      -- Each binding starts with a variable name followed by space
      let varName = T.takeWhile (\c -> c /= ' ' && c /= ')') txt
      in if T.null varName || T.head txt == ')'
         then reverse acc
         else
           -- Skip to after ")) (" or "))" for the next binding
           case T.breakOn "))" txt of
             (_, "") -> reverse (varName : acc)
             (_, rest) ->
               let afterClose = T.drop 2 rest
               in if T.null afterClose || T.head afterClose /= ' '
                  then reverse (varName : acc)  -- End of bindings
                  else
                    -- Check if next char after space is '('
                    let afterSpace = T.dropWhile (== ' ') afterClose
                    in if T.null afterSpace || T.head afterSpace /= '('
                       then reverse (varName : acc)
                       else go (T.drop 1 afterSpace) (varName : acc)  -- Skip '('

-- | Parse constraints from the body of the Reachable definition
-- This is a simplified parser that handles common patterns:
-- - (= s0 #xNNNN) for exact values
-- - (or (= s0 #xNNNN) (= s0 #xMMMM)) for disjunctions of exact values
-- - true for unbounded
parseConstraintsFromBody :: [Text] -> Text -> [SlotConstraint]
parseConstraintsFromBody slotNames body
  | T.null body = map (const SCUnbounded) slotNames
  | otherwise = map (parseSlotConstraint body) slotNames

-- | Parse constraint for a single slot from the invariant body
parseSlotConstraint :: Text -> Text -> SlotConstraint
parseSlotConstraint body slotName =
  -- Look for patterns involving this slot
  let -- Check for exact value patterns: (= slotName #xNNNN)
      exactVals = extractExactValues slotName body
  in case exactVals of
       [] -> -- No exact values found, check for other patterns
         if T.isInfixOf slotName body
         then SCRaw (extractSlotExpression slotName body)
         else SCUnbounded
       vals -> SCExactValues vals

-- | Extract exact values for a slot from expressions like (= s0 #x...)
-- Handles multi-line patterns where whitespace/newlines separate the variable and value
extractExactValues :: Text -> Text -> [W256]
extractExactValues slotName body =
  let -- Pattern: (= slotName #xHEX) - may have whitespace/newlines between variable and value
      -- We'll use a simple text-based extraction
      -- Try both single-space and newline patterns
      chunks = T.splitOn ("(= " <> slotName) body
  -- Deduplicate extracted values
  in nub $ concatMap extractHexValue (drop 1 chunks)

-- | Extract a hex value from a text chunk (after variable name, with possible whitespace)
extractHexValue :: Text -> [W256]
extractHexValue chunk =
  -- Strip leading whitespace (including newlines) before looking for #x or #b
  let stripped = T.dropWhile isSpace chunk
  in case T.stripPrefix "#x" stripped of
    Just rest ->
      let hexStr = T.takeWhile isHexDigit rest
      in case readHex (T.unpack hexStr) of
           [(val, "")] -> [val]
           _ -> []
    Nothing ->
      case T.stripPrefix "#b" stripped of
        Just rest ->
          let binStr = T.takeWhile (\c -> c == '0' || c == '1') rest
          in case readBin (T.unpack binStr) of
               Just val -> [val]
               Nothing -> []
        Nothing -> []
  where
    isSpace c = c == ' ' || c == '\n' || c == '\r' || c == '\t'
    isHexDigit c = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
    readBin :: String -> Maybe W256
    readBin = foldl addBit (Just 0)
      where
        addBit Nothing _ = Nothing
        addBit (Just acc) '0' = Just (acc * 2)
        addBit (Just acc) '1' = Just (acc * 2 + 1)
        addBit _ _ = Nothing

-- | Extract the sub-expression involving a specific slot
extractSlotExpression :: Text -> Text -> Text
extractSlotExpression slotName body =
  -- Simple extraction: find the smallest balanced parentheses containing the slot
  let idx = T.length (fst (T.breakOn slotName body))
  in if idx >= T.length body
     then ""
     else findBalancedExpr (T.drop idx body)

-- | Find a balanced parenthesized expression
findBalancedExpr :: Text -> Text
findBalancedExpr t =
  -- Back up to find the opening paren
  let prefix = T.takeWhile (/= ')') t
      suffix = T.drop (T.length prefix + 1) t
  in prefix <> ")" <> T.take 0 suffix  -- Just the first expression
