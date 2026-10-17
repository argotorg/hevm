{-# LANGUAGE BangPatterns #-}

-- | Fuzzes equivalence checking and the concrete replay of its counterexamples
-- on random programs that make STATICCALLs to unknown code.
module EVM.Equivalence.EquivFuzz (tests) where

import Control.Monad (forM)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (State, evalState, evalStateT, get, modify, liftIO)
import Data.Functor ((<&>))
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Either (rights)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Word (Word8)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, QuickCheckTests(..))

import EVM (makeVm, exec1, initialContract, defaultVMOpts)
import EVM.Exec (exec)
import EVM.Effects (App, Config, readConfig)
import EVM.Effects qualified as Effects
import EVM.Fetch qualified as Fetch
import EVM.Format (formatBinary)
import EVM.Op (intToOpName)
import EVM.Solvers (withSolvers, defMemLimit, Solver(..), SolverGroup)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Types

tests :: TestTree
tests = testGroup "Equivalence fuzzing"
  -- each case runs the solver, so the default of 100 cases is lowered; any other count is kept
  [ withResource (newIORef mempty) (printCoverage "eq-fuzz-cex-replays" genOpcodes) $ \cov ->
      adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 20 else n)) $
        testProperty "eq-fuzz-cex-replays" (prop_eqReplay cov)
  , withResource (newIORef mempty) (printCoverage "eq-fuzz-configs" (filter (/= "STATICCALL") genOpcodes)) $ \cov ->
      adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10 else n)) $
        testProperty "eq-fuzz-configs" (prop_eqConfigs cov)
  , testProperty "eq-fuzz-stub-code" prop_stubCode
  ]

-- | How many cases generated and executed each opcode
type Coverage = (Map String Int, Map String Int)

printCoverage :: String -> [String] -> IORef Coverage -> IO ()
printCoverage prop expected ref = do
  (gen, ex) <- readIORef ref
  let missing m = [o | o <- expected, Map.findWithDefault 0 o m == 0]
  if Map.null gen then pure () else do
    putStrLn $ prop <> ": never generated: " <> unwords (missing gen)
    putStrLn $ prop <> ": never executed: " <> unwords (missing ex)

addCoverage :: IO (IORef Coverage) -> Set String -> Set String -> IO ()
addCoverage cov generated executed = do
  ref <- cov
  let count = Map.unionWith (+) . Map.fromSet (const 1)
  atomicModifyIORef' ref (\(g, e) -> ((count generated g, count executed e), ()))

-- * Programs

data W
  = Const W256
  | EnvOp Word8
  | CdLoad W
  | Un Word8 W
  | Bin Word8 W W
  | Tern Word8 W W W
  | Mload Int
  | Sload W
  | Tload W
  | Sha3 Int Int
  deriving (Show, Eq)

data Callee = AtAddr Addr | FromCd Int
  deriving (Show, Eq)

data Flag = FPop | FStore W256
  deriving (Show, Eq)

data Stmt
  = Sstore W W
  | Tstore W W
  | Mstore Int W
  | Mstore8 Int W
  | Call Callee (Maybe W256) Int Int Int Int Flag -- ^ call id written at the start of the input, in offset, in size, out offset, out size
  | RdCopy Int Int Int
  | CdCopy Int W Int
  | Stack [W] Bool Int -- ^ push the words, then DUPn (True) or SWAPn, store the top and pop
  | If W [Stmt] [Stmt]
  | Halt Word8 Int Int
  deriving (Show, Eq)

binOps, unOps, ternOps, envOps :: [Word8]
binOps = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0a, 0x0b, 0x10, 0x11, 0x12, 0x13, 0x14, 0x16, 0x17, 0x18, 0x1a, 0x1b, 0x1c, 0x1d]
unOps = [0x15, 0x19]
ternOps = [0x08, 0x09]
envOps = [0x30, 0x32, 0x33, 0x34, 0x36, 0x3d, 0x41, 0x42, 0x43, 0x47, 0x59]

callees :: [Addr]
callees = [0x1234, 0xabcd]

-- | Every opcode the generator can emit
genOpcodes :: [String]
genOpcodes = map (intToOpName . fromIntegral) $ binOps <> unOps <> ternOps <> envOps
  <> [0x00, 0x20, 0x35, 0x37, 0x3e, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x5b, 0x5c, 0x5d, 0xf3, 0xfa, 0xfd]
  <> [0x5f .. 0x7f] <> [0x80 .. 0x8f] <> [0x90 .. 0x9f]

data Asm = Bytes [Word8] | PushLabel Int | Label Int

pushW :: W256 -> [Word8]
pushW 0 = [0x5f]
pushW w = let bs = BS.unpack (BS.dropWhile (== 0) (word256Bytes w)) in (0x5f + fromIntegral (length bs)) : bs

pushI :: Int -> Asm
pushI = Bytes . pushW . fromIntegral

asmW :: W -> [Asm]
asmW = \case
  Const w -> [Bytes (pushW w)]
  EnvOp o -> [Bytes [o]]
  CdLoad e -> asmW e <> [Bytes [0x35]]
  Un o e -> asmW e <> [Bytes [o]]
  Bin o a b -> asmW b <> asmW a <> [Bytes [o]]
  Tern o a b c -> asmW c <> asmW b <> asmW a <> [Bytes [o]]
  Mload off -> [pushI off, Bytes [0x51]]
  Sload e -> asmW e <> [Bytes [0x54]]
  Tload e -> asmW e <> [Bytes [0x5c]]
  Sha3 off sz -> [pushI sz, pushI off, Bytes [0x20]]

asmBlock :: Stmt -> State Int [Asm]
asmBlock = \case
  Sstore k v -> pure $ asmW v <> asmW k <> [Bytes [0x55]]
  Tstore k v -> pure $ asmW v <> asmW k <> [Bytes [0x5d]]
  Mstore off v -> pure $ asmW v <> [pushI off, Bytes [0x52]]
  Mstore8 off v -> pure $ asmW v <> [pushI off, Bytes [0x53]]
  Call c callId io is oo os flag -> pure $
    maybe [] (\i -> [Bytes (pushW i), pushI io, Bytes [0x52]]) callId
    <> [pushI os, pushI oo, pushI is, pushI io]
    <> (case c of
          AtAddr a -> [Bytes (pushW (fromIntegral a))]
          FromCd off -> [pushI off, Bytes [0x35]])
    <> [Bytes (pushW 0xffffffff), Bytes [0xfa]]
    <> (case flag of
          FPop -> [Bytes [0x50]]
          FStore slot -> [Bytes (pushW slot), Bytes [0x55]])
  RdCopy dst src sz -> pure [pushI sz, pushI src, pushI dst, Bytes [0x3e]]
  CdCopy dst src sz -> pure $ [pushI sz] <> asmW src <> [pushI dst, Bytes [0x37]]
  Stack ws dup n -> pure $ concatMap asmW ws
    <> [Bytes [if dup then 0x80 + fromIntegral n - 1 else 0x90 + fromIntegral n - 1], Bytes [0x60, 7, 0x55]]
    <> replicate (length ws - if dup then 0 else 1) (Bytes [0x50])
  If c t e -> do
    lt <- fresh
    le <- fresh
    t' <- asmBlocks t
    e' <- asmBlocks e
    pure $ asmW c <> [PushLabel lt, Bytes [0x57]] <> e' <> [PushLabel le, Bytes [0x56], Label lt] <> t' <> [Label le]
  Halt 0 _ _ -> pure [Bytes [0x00]]
  Halt o off sz -> pure [pushI sz, pushI off, Bytes [o]]
  where
    fresh = get >>= \l -> modify (+ 1) >> pure l

asmBlocks :: [Stmt] -> State Int [Asm]
asmBlocks bs = concat <$> mapM asmBlock bs

assemble :: [Stmt] -> ByteString
assemble prog = BS.pack (concatMap emit asm)
  where
    asm = evalState (asmBlocks prog) 0
    size = \case
      Bytes b -> length b
      PushLabel _ -> 3
      Label _ -> 1
    labels = Map.fromList [(l, p) | (Label l, p) <- zip asm (scanl (+) 0 (map size asm))]
    emit = \case
      Bytes b -> b
      PushLabel l -> let p = labels Map.! l in [0x61, fromIntegral (p `div` 256), fromIntegral (p `mod` 256)]
      Label _ -> [0x5b]

opcodesOf :: ByteString -> [String]
opcodesOf bs = case BS.uncons bs of
  Nothing -> []
  Just (o, rest)
    | o >= 0x60 && o <= 0x7f -> intToOpName (fromIntegral o) : opcodesOf (BS.drop (fromIntegral o - 0x5f) rest)
    | otherwise -> intToOpName (fromIntegral o) : opcodesOf rest

-- * Generators

genConst :: Gen W256
genConst = frequency
  [ (4, fromIntegral <$> choose (0 :: Int, 40))
  , (2, elements [2 ^ (255 :: Int), maxBound, maxBound - 1, 2 ^ (128 :: Int), 2 ^ (160 :: Int) - 1, 0xff, 0x100])
  , (3, do n <- choose (1, 32); word . BS.pack <$> vectorOf n arbitrary)
  ]

genOff, genSize :: Gen Int
genOff = elements [0, 1, 4, 31, 32, 33, 64, 100]
genSize = elements [0, 1, 4, 31, 32, 33, 64, 100]

genW :: Int -> Gen W
genW d
  | d <= 0 = leaf
  | otherwise = frequency
      [ (3, leaf)
      , (5, Bin <$> elements binOps <*> sub <*> sub)
      , (1, Un <$> elements unOps <*> sub)
      , (1, Tern <$> elements ternOps <*> sub <*> sub <*> sub)
      , (1, CdLoad <$> sub)
      , (1, Sload <$> sub)
      ]
  where
    sub = genW (d - 1)
    leaf = frequency
      [ (4, Const <$> genConst)
      , (4, CdLoad . Const <$> elements [0, 4, 32, 36, 64])
      , (2, EnvOp <$> elements envOps)
      , (2, Mload <$> genOff)
      , (1, Sload . Const <$> genSlot)
      , (1, Tload . Const <$> genSlot)
      , (1, Sha3 <$> genOff <*> genSize)
      ]

genSlot :: Gen W256
genSlot = fromIntegral <$> choose (0 :: Int, 3)

genKey :: Gen W
genKey = frequency [(4, Const <$> genSlot), (1, genW 1)]

genCall :: Gen Stmt
genCall = Call
  <$> frequency [(4, AtAddr <$> elements callees), (1, FromCd <$> elements [0, 32])]
  -- the model may answer equal calls differently, which the replay can't do, so mostly make them differ
  <*> frequency [(3, Just <$> genCallId), (1, pure Nothing)]
  <*> genOff <*> genSize <*> genOff <*> genSize
  <*> frequency [(1, pure FPop), (2, FStore <$> genSlot)]

-- no zero bytes, so even a one-byte input tells calls apart
genCallId :: Gen W256
genCallId = word . BS.pack <$> vectorOf 32 (choose (1, 255))

genStack :: Gen Stmt
genStack = do
  dup <- arbitrary
  n <- choose (1, 16)
  m <- choose (if dup then max 2 n else n + 1, 17)
  ws <- vectorOf m (genW 0)
  pure $ Stack ws dup n

genBlock :: Bool -> Int -> Gen Stmt
genBlock calls d = frequency
  [ (3, Sstore <$> genKey <*> genW 2)
  , (1, Tstore <$> genKey <*> genW 2)
  , (2, Mstore <$> genOff <*> genW 2)
  , (1, Mstore8 <$> genOff <*> genW 1)
  , (if calls then 5 else 0, genCall)
  , (1, RdCopy <$> genOff <*> elements [0, 1, 31, 32] <*> genSize)
  , (1, CdCopy <$> genOff <*> frequency [(3, Const <$> elements [0, 4, 32]), (1, genW 1)] <*> genSize)
  , (2, genStack)
  , (if d > 0 then 3 else 0, If <$> genW 2 <*> genBlocks calls (d - 1) <*> genBlocks calls (d - 1))
  , (1, genHalt)
  ]

genHalt :: Gen Stmt
genHalt = Halt <$> elements [0x00, 0xf3, 0xfd] <*> genOff <*> genSize

genBlocks :: Bool -> Int -> Gen [Stmt]
genBlocks calls d = choose (1, 4) >>= \n -> vectorOf n (genBlock calls d)

genProgram :: Bool -> Gen [Stmt]
genProgram calls = choose (1, 6) >>= \n -> vectorOf n (genBlock calls 2)

-- * Mutations

holes :: W -> [(W, W -> W)]
holes w = (w, id) : case w of
  CdLoad e -> inside CdLoad e
  Un o e -> inside (Un o) e
  Bin o a b -> inside (\x -> Bin o x b) a <> inside (Bin o a) b
  Tern o a b c -> inside (\x -> Tern o x b c) a <> inside (\x -> Tern o a x c) b <> inside (Tern o a b) c
  Sload e -> inside Sload e
  Tload e -> inside Tload e
  _ -> []
  where inside f e = [(s, f . k) | (s, k) <- holes e]

mutW :: W -> Gen (W, String)
mutW w = do
  (s, k) <- elements (holes w)
  (s', what) <- local s
  pure (k s', what)
  where
    local = \case
      Const c -> frequency
        [ (2, pure (Const (c + 1), "const +1"))
        , (1, pure (Const (c - 1), "const -1"))
        , (2, (\c' -> (Const c', "new const")) <$> genConst)
        ]
      Bin o a b -> oneof
        [ (\o' -> (Bin o' a b, "change binop")) <$> elements binOps
        , pure (Bin o b a, "swap operands")
        , fresh
        ]
      Un _ e -> oneof [(\o' -> (Un o' e, "change unop")) <$> elements unOps, pure (e, "drop unop")]
      Tern _ a b c -> oneof [(\o' -> (Tern o' a b c, "change ternop")) <$> elements ternOps, fresh]
      EnvOp _ -> oneof [(\o' -> (EnvOp o', "change env op")) <$> elements envOps, fresh]
      _ -> fresh
    fresh = (, "replace subterm") <$> genW 1

mutBlock :: Bool -> Stmt -> Gen (Stmt, String)
mutBlock calls = \case
  Sstore k v -> oneof [first' (`Sstore` v) <$> mutW k, first' (Sstore k) <$> mutW v]
  Tstore k v -> oneof [first' (`Tstore` v) <$> mutW k, first' (Tstore k) <$> mutW v]
  Mstore o v -> oneof [(\o' -> (Mstore o' v, "memory offset")) <$> genOff, first' (Mstore o) <$> mutW v]
  Mstore8 o v -> oneof [(\o' -> (Mstore8 o' v, "memory offset")) <$> genOff, first' (Mstore8 o) <$> mutW v]
  Call c t io is oo os f -> oneof
    [ (\c' -> (Call c' t io is oo os f, "call callee")) <$> frequency [(4, AtAddr <$> elements callees), (1, FromCd <$> elements [0, 32])]
    , (\i' -> (Call c i' io is oo os f, "call id")) <$> frequency [(3, Just <$> genCallId), (1, pure Nothing)]
    , (\x -> (Call c t x is oo os f, "call in offset")) <$> genOff
    , (\x -> (Call c t io x oo os f, "call in size")) <$> genSize
    , (\x -> (Call c t io is x os f, "call out offset")) <$> genOff
    , (\x -> (Call c t io is oo x f, "call out size")) <$> genSize
    , (\f' -> (Call c t io is oo os f', "call flag")) <$> frequency [(1, pure FPop), (2, FStore <$> genSlot)]
    ]
  RdCopy d s z -> oneof [(\x -> (RdCopy d x z, "returndatacopy offset")) <$> elements [0, 1, 31, 32], (\x -> (RdCopy d s x, "returndatacopy size")) <$> genSize]
  CdCopy d s z -> oneof [first' (\s' -> CdCopy d s' z) <$> mutW s, (\x -> (CdCopy d s x, "calldatacopy size")) <$> genSize]
  Stack ws dup n -> do
    i <- choose (0, length ws - 1)
    (w', what) <- mutW (ws !! i)
    pure (Stack (take i ws <> [w'] <> drop (i + 1) ws) dup n, what)
  If c t e -> oneof
    [ first' (\c' -> If c' t e) <$> mutW c
    , first' (\t' -> If c t' e) <$> mutBlocks calls t
    , first' (If c t) <$> mutBlocks calls e
    , pure (If c e t, "swap branches")
    ]
  Halt _ off sz -> oneof
    [ (\o -> (Halt o off sz, "halt kind")) <$> elements [0x00, 0xf3, 0xfd]
    , (, "halt region") <$> genHalt
    ]
  where first' f (x, w) = (f x, w)

mutBlocks :: Bool -> [Stmt] -> Gen ([Stmt], String)
mutBlocks calls bs = do
  i <- choose (0, length bs - 1)
  frequency
    [ (6, (\(b, w) -> (take i bs <> [b] <> drop (i + 1) bs, w)) <$> mutBlock calls (bs !! i))
    , (if length bs > 1 then 1 else 0, pure (take i bs <> drop (i + 1) bs, "delete block"))
    , (1, (\b -> (take i bs <> [b] <> drop i bs, "insert block")) <$> genBlock calls 1)
    , (if i + 1 < length bs then 1 else 0, pure (take i bs <> [bs !! (i + 1), bs !! i] <> drop (i + 2) bs, "swap blocks"))
    ]

data Pair = Pair { progA :: [Stmt], progB :: [Stmt], mutation :: String }
  deriving (Show)

-- | A program and a mutation of it, with or without calls to unknown code
genPair :: Bool -> Gen Pair
genPair calls = do
  a <- genProgram calls
  (b, m) <- mutBlocks calls a
  pure $ Pair a b m

instance Arbitrary Pair where
  arbitrary = genPair True
  shrink (Pair a b m) =
    [Pair a' b m | a' <- shrinkStmts a, not (null a')] <> [Pair a b' m | b' <- shrinkStmts b, not (null b')]

shrinkStmts :: [Stmt] -> [[Stmt]]
shrinkStmts ss = shrinkList shrinkStmt ss
  <> [take i ss <> t <> drop (i + 1) ss | (i, If _ t _) <- zip [0 ..] ss]
  <> [take i ss <> e <> drop (i + 1) ss | (i, If _ _ e) <- zip [0 ..] ss]

shrinkStmt :: Stmt -> [Stmt]
shrinkStmt = \case
  If c t e -> [If c t' e | t' <- shrinkStmts t] <> [If c t e' | e' <- shrinkStmts e] <> [If c' t e | c' <- shrinkW c]
  Sstore k v -> [Sstore k' v | k' <- shrinkW k] <> [Sstore k v' | v' <- shrinkW v]
  Tstore k v -> [Tstore k' v | k' <- shrinkW k] <> [Tstore k v' | v' <- shrinkW v]
  Mstore o v -> [Mstore o v' | v' <- shrinkW v]
  Mstore8 o v -> [Mstore8 o v' | v' <- shrinkW v]
  CdCopy d s z -> [CdCopy d s' z | s' <- shrinkW s]
  Stack ws dup n -> [Stack (take i ws <> [w'] <> drop (i + 1) ws) dup n | (i, w) <- zip [0 ..] ws, w' <- shrinkW w]
  Call c (Just _) io is oo os f -> [Call c Nothing io is oo os f]
  _ -> []

shrinkW :: W -> [W]
shrinkW = \case
  Const 0 -> []
  Const c -> [Const 0] <> [Const 1 | c /= 1]
  w -> [Const 0, Const 1] <> case w of
    CdLoad e -> e : map CdLoad (shrinkW e)
    Un o e -> e : map (Un o) (shrinkW e)
    Bin o x y -> [x, y] <> [Bin o x' y | x' <- shrinkW x] <> [Bin o x y' | y' <- shrinkW y]
    Tern o x y z -> [x, y, z] <> [Tern o x' y z | x' <- shrinkW x] <> [Tern o x y' z | y' <- shrinkW y] <> [Tern o x y z' | z' <- shrinkW z]
    Sload e -> map Sload (shrinkW e)
    Tload e -> map Tload (shrinkW e)
    _ -> []

-- * Concrete runs

data Run = Run
  { ops :: Set String          -- ^ opcodes executed by the called contract
  , stubRan :: Bool
  , outcome :: Either EvmError (Expr Buf)
  , store :: Maybe (Map W256 W256)
  }

runConcrete :: App m => SolverGroup -> VMOpts Concrete -> m Run
runConcrete s opts = do
  vm <- liftIO $ stToIO $ makeVm opts
  conf <- readConfig
  (ops, stub, end) <- Stepper.interpret (Fetch.oracle s Nothing Fetch.noRpc) vm (traced conf)
  let store = case (.storage) <$> Map.lookup opts.address end.env.contracts of
        Just (ConcreteStore m) -> Just m
        _ -> Nothing
      outcome = case end.result of
        Just (VMSuccess out) -> Right out
        Just (VMFailure e) -> Left e
        r -> internalError $ "concrete run did not finish: " <> show r
  pure $ Run ops stub outcome store
  where
    traced :: Config -> Stepper Concrete (Set String, Bool, VM Concrete)
    traced conf = go mempty False
      where
        go ops stub = do
          (ops', stub', vm) <- Stepper.evm (step ops stub)
          case vm.result of
            Just (HandleEffect (Query q)) -> Stepper.wait q >> go ops' stub'
            _ -> pure (ops', stub', vm)
        step !ops !stub = do
          vm <- get
          case vm.result of
            Nothing -> do
              let mine = vm.state.codeContract == opts.address
                  ops' = if mine then Set.insert (opAt vm) ops else ops
              exec1 conf
              step ops' (stub || not mine)
            Just _ -> pure (ops, stub, vm)
    opAt vm = case vm.state.code of
      RuntimeCode (ConcreteRuntimeCode bs) | vm.state.pc < BS.length bs -> intToOpName (fromIntegral (BS.index bs vm.state.pc))
      _ -> "STOP"

outcomeKind :: Either EvmError (Expr Buf) -> String
outcomeKind = \case
  Right _ -> "Return"
  Left (Revert _) -> "Revert"
  Left e -> takeWhile (/= ' ') (show e)

-- | Code that answers any call with words derived from the hash of its input
hashStub :: W256 -> Bool -> Int -> ByteString
hashStub salt ok len = BS.pack $
  [0x36, 0x5f, 0x5f, 0x37, 0x36, 0x5f, 0x20, 0x7f] <> BS.unpack (word256Bytes salt) <> [0x18]
  <> concat [[0x80, 0x60, fromIntegral i, 0x01, 0x61, fromIntegral (32 * i `div` 256), fromIntegral (32 * i `mod` 256), 0x52] | i <- [0 .. (len + 31) `div` 32 - 1]]
  <> [0x50] <> pushW (fromIntegral len) <> [0x5f, if ok then 0xf3 else 0xfd]

-- * Properties

bucket :: Int -> String
bucket n
  | n <= 1 = show n
  | n <= 4 = "2-4"
  | n <= 32 = "5-32"
  | n <= 100 = "33-100"
  | otherwise = ">100"

-- the replay can't reproduce these, and says so
expectedCannot :: T.Text -> Bool
expectedCannot why = any (`T.isInfixOf` why)
  [ "goes to precompile", "goes to the called contract itself", "answers the same call", "precompile address", "calldata of " ]

-- the solver may give keccak of symbolic data any value, which the replay then can't reproduce
keccakRan :: Maybe (Run, Run) -> Bool
keccakRan = maybe False (\(ra, rb) -> "SHA3" `Set.member` (ra.ops <> rb.ops))

replayReason :: CexReplay -> Maybe (Run, Run) -> String
replayReason r runs = case r of
  Validated {} -> "validated"
  NotReproducible {} | keccakRan runs -> "not reproducible, ran SHA3"
                     | otherwise -> "NOT REPRODUCIBLE"
  CannotReplay why -> "cannot replay: " <> T.unpack (T.unwords (filter (not . ("0x" `T.isPrefixOf`)) (T.words why)))

blockKinds :: Int -> [Stmt] -> [String]
blockKinds depth = concatMap $ \case
  Sstore {} -> ["SSTORE"]
  Tstore {} -> ["TSTORE"]
  Mstore {} -> ["MSTORE"]
  Mstore8 {} -> ["MSTORE8"]
  Call c i _ _ _ _ f -> ["call " <> maybe "without id" (const "with id") i, "call to " <> (case c of AtAddr _ -> "fixed callee"; FromCd _ -> "callee from calldata")
                      , "call flag " <> (case f of FPop -> "popped"; FStore _ -> "stored")]
  RdCopy {} -> ["RETURNDATACOPY"]
  CdCopy {} -> ["CALLDATACOPY"]
  Stack _ dup _ -> [if dup then "DUPn" else "SWAPn"]
  If _ t e -> ("if at depth " <> show depth) : blockKinds (depth + 1) (t <> e)
  Halt o _ _ -> [intToOpName (fromIntegral o)]

type Replay = (SMTCex, CexReplay, Maybe (Run, Run))

-- | Checks A and B for equivalence and replays each counterexample, also on
-- traced runs that record what the replay executes
checkAndReplay :: App m => SolverGroup -> ByteString -> ByteString -> m ([String], [Replay])
checkAndReplay s codeA codeB = do
  (calldata, _) <- mkCalldata Nothing []
  eq <- if codeA == codeB then pure mempty else equivalenceCheck s Nothing codeA codeB defaultVeriOpts calldata False
  let verdicts = nub $ map (verdict . fst) eq.res
                  <> ["partial" | not (null eq.partials)]
                  <> ["identical" | codeA == codeB]
                  <> ["equivalent" | null eq.res, null eq.partials, codeA /= codeB]
  replays <- forM (mapMaybe (getCex . fst) eq.res) $ \cex -> do
    r <- replayEqCex s False codeA codeB (fst calldata) cex
    runs <- case (r, stubAccounts (eqCexEntry cex) cex.unknownCalls, cexCalldata (fst calldata) cex) of
      (CannotReplay _, _, _) -> pure Nothing
      (_, Right stubs, Just cd) -> do
        ra <- runConcrete s (eqReplayVmOpts cex stubs codeA cd)
        rb <- runConcrete s (eqReplayVmOpts cex stubs codeB cd)
        pure $ Just (ra, rb)
      _ -> pure Nothing
    pure (cex, r, runs)
  pure (verdicts, replays)
  where
    verdict = \case
      Cex _ -> "cex"
      Qed -> "qed"
      Unknown _ -> "unknown"
      Error e -> "error: " <> take 60 e

isBad :: CexReplay -> Maybe (Run, Run) -> Bool
isBad r runs = case r of
  Validated {} -> False
  NotReproducible {} -> not (keccakRan runs)
  CannotReplay why -> not (expectedCannot why)

showPair :: [Stmt] -> [Stmt] -> [String]
showPair a b =
  [ "A: " <> show a, "B: " <> show b
  , "A code: " <> T.unpack (formatBinary (assemble a)), "B code: " <> T.unpack (formatBinary (assemble b)) ]

prop_eqReplay :: IO (IORef Coverage) -> Pair -> Property
prop_eqReplay cov (Pair a b mutation) = ioProperty $ Effects.runApp $ withSolvers Bitwuzla 1 (Just 20) defMemLimit $ \s -> do
  (verdicts, replays) <- checkAndReplay s codeA codeB
  random <- randomRuns s codeA codeB
  let equivalent = verdicts == ["equivalent"]
      runs = concat [[ra, rb] | (_, _, Just (ra, rb)) <- replays] <> concatMap (\(x, y) -> [x, y]) random
      calls = rights (concat [c.unknownCalls | (c, _, _) <- replays])
      bad = [ (c, r) | (c, r, runs') <- replays, isBad r runs' ]
      unsound = [ (x, y) | equivalent, (x, y) <- random, (x.outcome, x.store) /= (y.outcome, y.store) ]
      generated = Set.fromList (opcodesOf codeA <> opcodesOf codeB)
      executed = Set.unions (map (.ops) runs)
  liftIO $ addCoverage cov generated executed
  pure
    $ counterexample (report bad unsound)
    $ tabulate "mutation" [mutation]
    $ tabulate "program size (bytes)" [bucket (BS.length codeA)]
    $ tabulate "blocks in A" (nub (blockKinds 0 a))
    $ tabulate "generated opcodes" (Set.toList generated)
    $ tabulate "equivalence" verdicts
    $ tabulate "replay" (map (\(_, r, runs') -> replayReason r runs') replays)
    $ tabulate "calls in a cex" (map (\(c, _, _) -> bucket (length c.unknownCalls)) replays)
    $ tabulate "call answers" [(if m.success then "success" else "revert") <> ", returndata " <> bucket m.returndataLength | m <- calls]
    $ tabulate "call calldata length" [bucket (BS.length m.calldata) | m <- calls]
    $ tabulate "replay outcomes (A / B)" [outcomeKind ra.outcome <> " / " <> outcomeKind rb.outcome | (_, _, Just (ra, rb)) <- replays]
    $ tabulate "replay ran a stub" [show (ra.stubRan || rb.stubRan) | (_, _, Just (ra, rb)) <- replays]
    $ tabulate ("random runs (A / B), " <> (if equivalent then "equivalent" else "not equivalent")) [outcomeKind x.outcome <> " / " <> outcomeKind y.outcome | (x, y) <- random]
    $ tabulate "executed opcodes" (Set.toList executed)
    $ null bad && null unsound
  where
    codeA = assemble a
    codeB = assemble b
    report bad unsound = unlines $ showPair a b
      <> concat [["cex: " <> show c, "replay: " <> show r] | (c, r) <- bad]
      <> concat [["equivalent, but concretely: " <> show x.outcome <> " " <> show x.store <> " vs " <> show y.outcome <> " " <> show y.store] | (x, y) <- unsound]

-- | Runs A and B in random concrete environments, with callees that answer by
-- hashing their input. When hevm says A and B are equivalent, these must agree.
randomRuns :: App m => SolverGroup -> ByteString -> ByteString -> m [(Run, Run)]
randomRuns s codeA codeB = do
  envs <- liftIO $ generate (vectorOf 4 genEnv)
  forM envs $ \(cex, stubs, cd) -> do
    x <- runConcrete s (eqReplayVmOpts cex stubs codeA cd)
    y <- runConcrete s (eqReplayVmOpts cex stubs codeB cd)
    pure (x, y)

data Variant = Variant { name :: String, tweak :: Effects.Config -> Effects.Config }

instance Show Variant where
  show v = v.name

baseline :: Variant
baseline = Variant "baseline" id

variants :: [Variant]
variants =
  [ Variant "simp off" (\c -> c { Effects.simp = False })
  , Variant "abstractArith flipped" (\c -> c { Effects.abstractArith = not c.abstractArith })
  , Variant "decomposeStorage off" (\c -> c { Effects.decomposeStorage = False })
  , Variant "hashConsExplore flipped" (\c -> c { Effects.hashConsExplore = not c.hashConsExplore })
  , Variant "merging off" (\c -> c { Effects.mergeMaxBudget = 0 })
  ]

-- | Configurations must agree, on programs without calls: none may prove A and B
-- equivalent while another gives a counterexample that replays, random concrete
-- runs must agree when one proves them equivalent, and every counterexample must
-- replay as in 'prop_eqReplay'
prop_eqConfigs :: IO (IORef Coverage) -> Property
prop_eqConfigs cov = forAllShrink (genPair False) shrink $ \(Pair a b mutation) -> forAll (take 2 <$> shuffle variants) $ \vs -> ioProperty $ do
  let codeA = assemble a
      codeB = assemble b
      check v = Effects.runEnv (Effects.Env { Effects.config = v.tweak Effects.defaultConfig }) $
        withSolvers Bitwuzla 1 (Just 20) defMemLimit $ \s -> checkAndReplay s codeA codeB
  baseRes <- check baseline
  variantRes <- forM vs $ \v -> (v, ) <$> check v
  random <- Effects.runApp $ withSolvers Bitwuzla 1 (Just 20) defMemLimit $ \s -> randomRuns s codeA codeB
  let results = (baseline, baseRes) : variantRes
      equivalent = [v | (v, (verdicts, _)) <- results, verdicts == ["equivalent"]]
      validated = [(v, c, r) | (v, (_, replays)) <- results, (c, r@Validated {}, _) <- replays]
      bad = [(v, c, r) | (v, (_, replays)) <- results, (c, r, runs) <- replays, isBad r runs]
      clash = not (null equivalent) && not (null validated)
      unsound = [(x, y) | not (null equivalent), (x, y) <- random, (x.outcome, x.store) /= (y.outcome, y.store)]
      kind (verdicts, replays)
        | verdicts == ["equivalent"] = "equivalent"
        | any (\(_, r, _) -> case r of Validated {} -> True; _ -> False) replays = "validated cex"
        | "cex" `elem` verdicts = "unreplayed cex"
        | otherwise = unwords verdicts
      base = kind baseRes
      replayRuns = concat [[ra, rb] | (_, (_, replays)) <- results, (_, _, Just (ra, rb)) <- replays]
      generated = Set.fromList (opcodesOf codeA <> opcodesOf codeB)
      executed = Set.unions (map (.ops) (replayRuns <> concatMap (\(x, y) -> [x, y]) random))
  addCoverage cov generated executed
  pure
    $ counterexample (unlines $ showPair a b
        <> ["equivalent under: " <> show equivalent | clash || not (null unsound)]
        <> concat [["validated under " <> show v <> ": " <> show c, show r] | clash, (v, c, r) <- validated]
        <> concat [["bad replay under " <> show v <> ": " <> show c, show r] | (v, c, r) <- bad]
        <> ["but concretely: " <> show x.outcome <> " " <> show x.store <> " vs " <> show y.outcome <> " " <> show y.store | (x, y) <- unsound])
    $ tabulate "mutation" [mutation]
    $ tabulate "program size (bytes)" [bucket (BS.length codeA)]
    $ tabulate "blocks in A" (nub (blockKinds 0 a))
    $ tabulate "generated opcodes" (Set.toList generated)
    $ tabulate "executed opcodes" (Set.toList executed)
    $ tabulate "baseline" [base]
    $ tabulate "variant vs baseline" [v.name <> ": " <> (if k == base then "agrees" else k <> " vs " <> base) | (v, res) <- variantRes, let k = kind res]
    $ tabulate "replay" [v.name <> ": " <> replayReason r runs | (v, (_, replays)) <- results, (_, r, runs) <- replays]
    $ tabulate "replay outcomes (A / B)" [outcomeKind ra.outcome <> " / " <> outcomeKind rb.outcome | (_, (_, replays)) <- results, (_, _, Just (ra, rb)) <- replays]
    $ tabulate ("random runs (A / B), " <> (if null equivalent then "not proved equivalent" else "proved equivalent")) [outcomeKind x.outcome <> " / " <> outcomeKind y.outcome | (x, y) <- random]
    $ not clash && null bad && null unsound

genEnv :: Gen (SMTCex, [(Expr EAddr, Contract)], ByteString)
genEnv = do
  cdSize <- elements [0, 4, 31, 32, 36, 64, 68, 100]
  cd <- BS.pack <$> vectorOf cdSize arbitrary
  (entry, caller, origin, coinbase) <- (,,,) <$> genAddr <*> genAddr <*> genAddr <*> genAddr
  value <- frequency [(2, pure 0), (1, fromIntegral <$> choose (0 :: Int, 1000))]
  bal <- (+ value) . fromIntegral <$> choose (0 :: Int, 1000)
  ts <- fromIntegral <$> choose (0 :: Int, 2 ^ (40 :: Int))
  num <- fromIntegral <$> choose (0 :: Int, 2 ^ (30 :: Int))
  slots <- Map.fromList <$> listOf ((,) <$> (fromIntegral <$> choose (0 :: Int, 3)) <*> genConst)
  stubs <- forM callees $ \c -> do
    salt <- genConst
    ok <- frequency [(3, pure True), (1, pure False)]
    len <- elements [0, 1, 31, 32, 33, 64, 100]
    pure (LitAddr c, initialContract (RuntimeCode (ConcreteRuntimeCode (hashStub salt ok len))))
  let cex = (mempty :: SMTCex)
        { addrs = Map.fromList [(SymAddr "entrypoint", entry), (SymAddr "caller", caller), (SymAddr "origin", origin), (SymAddr "coinbase", coinbase)]
        , store = Map.singleton (SymAddr "entrypoint") slots
        , blockContext = Map.fromList [(Timestamp, ts), (BlockNumber, num)]
        , txContext = Map.fromList [(TxValue, value), (Balance (SymAddr "entrypoint"), bal)]
        }
  pure (cex, stubs, cd)
  where
    genAddr = ((fromIntegral :: W256 -> Addr) . word . BS.pack <$> vectorOf 20 arbitrary) `suchThat` (> 0x10000)

-- | 'stubCode' answers each of its calldatas as told, padding the returndata with zeros
-- to its length, and reverts with no data on any other calldata
prop_stubCode :: Property
prop_stubCode = forAll genAnswers $ \answers -> forAll (BS.pack <$> listOf arbitrary) $ \other ->
  ioProperty $ do
    let code = stubCode answers
        run input = stToIO $ do
          vm <- makeVm @Concrete (defaultVMOpts @Concrete)
            { contract = initialContract (RuntimeCode (ConcreteRuntimeCode code))
            , calldata = (ConcreteBuf input, [])
            , gas = 0xffffffffffffffff
            , gaslimit = 0xffffffffffffffff
            }
          evalStateT (exec Effects.defaultConfig) vm <&> \case
            VMSuccess out -> Just (Right out)
            VMFailure e -> Just (Left e)
            _ -> Nothing
    got <- mapM (run . fst) answers
    miss <- run other
    let want (ok, out, len) = let full = out <> BS.replicate (len - BS.length out) 0
                              in if ok then Right (ConcreteBuf full) else Left (Revert (ConcreteBuf full))
        okAll = and (zipWith (\(_, r) g -> g == Just (want r)) answers got)
        okMiss = other `elem` map fst answers || miss == Just (Left (Revert (ConcreteBuf "")))
    pure
      $ tabulate "answers" [bucket (length answers)]
      $ tabulate "returndata length" [bucket len | (_, (_, _, len)) <- answers]
      $ tabulate "zeros padded" [bucket (len - BS.length o) | (_, (_, o, len)) <- answers]
      $ tabulate "calldata length" [bucket (BS.length i) | (i, _) <- answers]
      $ tabulate "fails" [show (not ok) | (_, (ok, _, _)) <- answers]
      $ counterexample (show (zip answers got, miss))
      $ okAll && okMiss
  where
    genAnswers = do
      n <- choose (0, 12)
      inputs <- nub <$> vectorOf n (BS.pack <$> frequency [(3, listOf arbitrary), (1, pure []), (1, vectorOf 4 arbitrary)])
      forM inputs $ \i -> do
        ok <- arbitrary
        given <- frequency [(3, choose (0, 100)), (1, choose (0, 3000)), (1, pure 0)]
        out <- BS.pack <$> vectorOf given arbitrary
        zeros <- frequency [(3, pure 0), (2, choose (1, 100)), (1, choose (1, 70000))]
        pure (i, (ok, out, given + zeros))
