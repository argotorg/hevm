-- | Fuzzes storage fetched via RPC: programs must behave the same with the storage known up front
-- as with it fetched slot by slot from a pre-filled cache, concretely and symbolically.
module EVM.Fetch.RpcFuzz (tests) where

import Control.Concurrent.MVar (modifyMVar_)
import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.ST (stToIO)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Data.List (zip4)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Word (Word8)
import Test.QuickCheck hiding (Success, Failure)
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, QuickCheckTests(..))

import EVM (makeVm, initialContract, defaultVMOpts)
import EVM.Effects (App, Env(..), defaultConfig, runEnv)
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (formatBinary)
import EVM.Solvers (withSolvers, defMemLimit, Solver(..), SolverGroup)
import EVM.Stepper qualified as Stepper
import EVM.SymExec (interpret, defaultIterConf, runExpr, noopPathHandler)
import EVM.Traversals (mapExpr, mapProp)
import EVM.Types hiding (Env)

tests :: TestTree
tests = testGroup "RPC fuzzing"
  -- each case runs the solver, so the default of 100 cases is lowered; any other count is kept
  [ adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10 else n)) $
      testProperty "rpc-fuzz-storage" prop_rpcStorage
  ]

-- * Programs

data Key = KLit W256 | KCd Int -- ^ calldataload(off) & 3
  deriving (Show, Eq)

-- | Mapping slots hash their preimage at the given memory offset
data Slot = Plain Key | Mapping Int Key W256 | Nested Int Key Key W256
  deriving (Show, Eq)

data Val = VLit W256 | VCd Int | VLoad Slot | VAdd Val Val | VBal | VCodeSize -- ^ of 'remote2'
  deriving (Show, Eq)

-- | 'Call' passes a key, a value and a key to read to 'remote2', which is fetched on first use
data Stmt = Store Slot Val | Load Slot | Call Key Val Key
  deriving (Show, Eq)

-- | Pre-state storage of both remote contracts
type Slots = Map (Addr, W256) W256

remote, remote2 :: Addr
remote = 0x1234567890abcdef1234567890abcdef12345678
remote2 = 0x2234567890abcdef1234567890abcdef12345678

-- | sstore(cd[0], cd[32]); return sload(cd[64])
remote2Code :: ByteString
remote2Code = BS.pack [0x60, 0x20, 0x35, 0x5f, 0x35, 0x55, 0x60, 0x40, 0x35, 0x54, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]

keyMask :: W256
keyMask = 3

idxs :: [W256]
idxs = [0, 1]

cdOffs :: [Int]
cdOffs = [0, 32, 64, 96]

outBase :: Int
outBase = 0x200

mapSlot :: W256 -> W256 -> W256
mapSlot k idx = keccak' (word256Bytes k <> word256Bytes idx)

-- | Every slot a program can touch
domain :: [(Addr, W256)]
domain = map (remote,) (keys
  <> [mapSlot k i | k <- keys, i <- idxs]
  <> [mapSlot k2 (mapSlot k1 i) | k1 <- keys, k2 <- keys, i <- idxs])
  <> map (remote2,) keys
  where keys = [0 .. keyMask]

-- * Assembly

pushW :: W256 -> [Word8]
pushW 0 = [0x5f]
pushW w = let bs = BS.unpack (BS.dropWhile (== 0) (word256Bytes w)) in (0x5f + fromIntegral (length bs)) : bs

pushI :: Int -> [Word8]
pushI = pushW . fromIntegral

asmKey :: Key -> [Word8]
asmKey = \case
  KLit w -> pushW w
  KCd off -> pushW keyMask <> pushI off <> [0x35, 0x16]

asmSlot :: Slot -> [Word8]
asmSlot = \case
  Plain k -> asmKey k
  Mapping h k idx -> hash h (asmKey k) (pushW idx)
  Nested h k1 k2 idx -> hash h (asmKey k2) (asmSlot (Mapping h k1 idx))
  where
    -- the second word goes in first: it may itself hash at h
    hash h key second = second <> pushI (h + 32) <> [0x52] <> key <> pushI h <> [0x52]
      <> pushI 64 <> pushI h <> [0x20]

asmVal :: Val -> [Word8]
asmVal = \case
  VLit w -> pushW w
  VCd off -> pushI off <> [0x35]
  VLoad s -> asmSlot s <> [0x54]
  VAdd a b -> asmVal b <> asmVal a <> [0x01]
  VBal -> pushW (fromIntegral remote2) <> [0x31]
  VCodeSize -> pushW (fromIntegral remote2) <> [0x3b]

assemble :: [Stmt] -> ByteString
assemble prog = BS.pack $ concat (zipWith asm [0 ..] prog) <> pushI (32 * loads) <> pushI outBase <> [0xf3]
  where
    outputs = \case Store {} -> 0; _ -> 1
    loads = sum (map outputs prog)
    outOffs = scanl (\o s -> o + 32 * outputs s) outBase prog
    asm :: Int -> Stmt -> [Word8]
    asm i = \case
      Store s v -> asmVal v <> asmSlot s <> [0x55]
      Load s -> asmSlot s <> [0x54] <> pushI (outOffs !! i) <> [0x52]
      Call k v rk -> asmKey k <> pushI 0x100 <> [0x52] <> asmVal v <> pushI 0x120 <> [0x52]
        <> asmKey rk <> pushI 0x140 <> [0x52]
        <> pushI 32 <> pushI (outOffs !! i) <> pushI 96 <> pushI 0x100 <> pushW 0
        <> pushW (fromIntegral remote2) <> pushW 0xffffffff <> [0xf1, 0x50]

-- * Generators

genWord :: Gen W256
genWord = frequency
  [ (3, fromIntegral <$> choose (0 :: Int, 5))
  , (1, elements [maxBound, 2 ^ (255 :: Int)])
  , (3, word . BS.pack <$> vectorOf 32 arbitrary)
  ]

genKey :: Gen Key
genKey = oneof [KLit <$> elements [0 .. keyMask], KCd <$> elements cdOffs]

genSlot :: Gen Slot
genSlot = frequency
  [ (2, Plain <$> genKey)
  , (3, Mapping <$> hashOff <*> genKey <*> elements idxs)
  , (2, Nested <$> hashOff <*> genKey <*> genKey <*> elements idxs)
  ]
  where hashOff = elements [0, 0x40, 0xa0]

genVal :: Int -> Gen Val
genVal d = frequency $
  [ (3, VLit <$> genWord), (3, VCd <$> elements cdOffs), (2, VLoad <$> genSlot), (1, elements [VBal, VCodeSize]) ]
  <> [ (1, VAdd <$> genVal (d - 1) <*> genVal (d - 1)) | d > 0 ]

genStmt :: Gen Stmt
genStmt = frequency
  [(3, Store <$> genSlot <*> genVal 2), (3, Load <$> genSlot), (1, Call <$> genKey <*> genVal 1 <*> genKey)]

genState :: Gen Slots
genState = Map.fromList . concat <$> forM domain (\s ->
  frequency [(1, pure []), (2, (\v -> [(s, v)]) <$> genWord)])

genCalldata :: Gen ByteString
genCalldata = BS.concat <$> vectorOf (length cdOffs) (word256Bytes <$> genWord)

shrinkStmt :: Stmt -> [Stmt]
shrinkStmt = \case
  Store s v -> Load s : [Store s v' | v' <- shrinkVal v]
  Load _ -> []
  Call k v rk -> [Call k v' rk | v' <- shrinkVal v]
  where
    shrinkVal = \case
      VAdd a b -> [a, b]
      VLit w | w > 1 -> [VLit 0, VLit 1]
      _ -> []

-- * Runs

-- | What a run returned, and the final value of every domain slot
type Outcome = (Either String ByteString, Slots)

-- | Reads the domain slots of the final stores, falling back to the pre-state for slots (and
-- contracts) never fetched
finalSlots :: Slots -> Map (Expr EAddr) (Expr Storage) -> Either String Slots
finalSlots pre stores = Map.fromList <$> mapM slot domain
  where
    slot k@(a, s) = case Map.lookup (LitAddr a) stores >>= Expr.readStorage (Lit s) of
      Nothing -> Right (k, Map.findWithDefault 0 k pre)
      Just (Lit v) -> Right (k, v)
      Just e -> Left $ "undecided read of slot " <> show s <> " at " <> show a <> ": " <> show e

-- | Serves slots from the pre-filled cache only; anything else is recorded and answered with 0
cachedOracle :: App m => SolverGroup -> Fetch.Session -> IORef [String] -> Fetch.Fetcher t m
cachedOracle solvers sess unexpected q = case q of
  PleaseFetchSlot a s k | (a, s) `notElem` domain -> do
    record ("slot " <> show s <> " at " <> show a)
    pure (k 0)
  PleaseFetchContract a _ _ | a /= remote2 -> do
    record ("contract " <> show a)
    Fetch.oracle solvers Nothing Fetch.noRpc q
  _ -> Fetch.oracle solvers (Just sess) rpcInfo q
  where
    record m = liftIO $ atomicModifyIORef' unexpected (\ms -> (m : ms, ()))
    rpcInfo = Fetch.RpcInfo (Just (Fetch.BlockNumber 1, "http://mock.mock"))

mkCachedSession :: App m => Slots -> W256 -> m Fetch.Session
mkCachedSession pre bal2 = do
  sess <- Fetch.mkSessionWithoutCache
  liftIO $ modifyMVar_ sess.sharedCache $ \c -> pure c
    { Fetch.slotCache = Map.fromList [(k, Map.findWithDefault 0 k pre) | k <- domain]
    , Fetch.contractCache = Map.singleton remote2 (Fetch.RPCContract (ByteStringS remote2Code) 1 bal2) }
  pure sess

-- | 'remote2' with all its storage, as the ground truth knows it up front
knownRemote2 :: Slots -> W256 -> (Expr EAddr, Contract)
knownRemote2 pre bal2 =
  (LitAddr remote2, (contractWith remote2Code (storeOf pre remote2) False) { balance = Lit bal2, nonce = Just 1 })

storeOf :: Slots -> Addr -> Expr Storage
storeOf pre addr = ConcreteStore (Map.fromList [(s, v) | ((a, s), v) <- Map.toList pre, a == addr])

contractWith :: ByteString -> Expr Storage -> Bool -> Contract
contractWith code st ext = (initialContract (RuntimeCode (ConcreteRuntimeCode code)))
  { storage = st, origStorage = st, external = ext }

runConcrete :: App m => Fetch.Fetcher Concrete m -> Contract -> [(Expr EAddr, Contract)] -> ByteString -> Slots -> m (Either String Outcome)
runConcrete fetcher c others cd pre = do
  vm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Concrete)
    { contract = c, otherContracts = others, address = LitAddr remote, calldata = (ConcreteBuf cd, [])
    , gas = 0xffffffffffffffff, gaslimit = 0xffffffffffffffff }
  end <- Stepper.interpret fetcher vm Stepper.runFully
  let out = case end.result of
        Just (VMSuccess (ConcreteBuf bs)) -> Right bs
        Just (VMFailure e) -> Left (show e)
        r -> Left (show r)
  pure $ (out,) <$> finalSlots pre (fmap (.storage) end.env.contracts)

-- | The outcome of the symbolic leaf that the given calldata takes, if it is not a partial one
evalSymbolic :: [Expr End] -> ByteString -> Slots -> Either String (Maybe Outcome)
evalSymbolic leaves cd pre = case filter (taken . props) leaves of
  [Success _ _ buf cs] -> do
    out <- case sub buf of
      ConcreteBuf bs -> Right (Right bs)
      b -> Left ("undecided returndata: " <> show b)
    let stores = Map.fromList [(a, sub st) | (a, C _ st _ _ _) <- Map.toList cs]
    Just . (out,) <$> finalSlots pre stores
  [Partial {}] -> Right Nothing
  [Failure _ _ e] -> Right (Just (Left (show e), pre))
  ls -> Left ("calldata takes " <> show (length ls) <> " leaves")
  where
    sub :: Expr a -> Expr a
    sub = Expr.concKeccakSimpExpr . mapExpr (\case
      AbstractBuf "txdata" -> ConcreteBuf cd
      e -> e)
    taken ps = null $ Expr.concKeccakSimpProps (map (mapProp sub) ps)
    props :: Expr End -> [Prop]
    props = \case
      Success ps _ _ _ -> ps
      Failure ps _ _ -> ps
      Partial ps _ _ -> ps
      _ -> []

prop_rpcStorage :: Property
prop_rpcStorage =
  forAllShrink (choose (1, 8) >>= flip vectorOf genStmt) (shrinkList shrinkStmt) $ \prog ->
  forAllBlind genState $ \pre ->
  forAllBlind genWord $ \bal2 ->
  forAllBlind (vectorOf 3 genCalldata) $ \cds -> ioProperty $ do
    unexpected <- newIORef []
    let code = assemble prog
    runEnv (Env {config = defaultConfig}) $ withSolvers Bitwuzla 1 (Just 5) defMemLimit $ \solvers -> do
      sess <- mkCachedSession pre bal2
      truths <- mapM (\cd -> runConcrete (Fetch.oracle solvers Nothing Fetch.noRpc)
        (contractWith code (storeOf pre remote) False) [knownRemote2 pre bal2] cd pre) cds
      fetched <- mapM (\cd -> runConcrete (cachedOracle solvers sess unexpected)
        (contractWith code (ConcreteStore mempty) True) [] cd pre) cds
      symVm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Symbolic)
        { contract = contractWith code (ConcreteStore mempty) True, address = LitAddr remote
        , calldata = (AbstractBuf "txdata", []) }
      leaves <- interpret (cachedOracle solvers sess unexpected) defaultIterConf symVm runExpr noopPathHandler
      let symbolic = map (\cd -> sequence (evalSymbolic leaves cd pre)) cds
      unexp <- liftIO $ readIORef unexpected
      let partials = length [() | Nothing <- symbolic]
          mismatches =
            [ "calldata " <> T.unpack (formatBinary cd) <> "\n  " <> what <> ":\n" <> d
            | (cd, truth, conc, sym) <- zip4 cds truths fetched symbolic
            , (what, Just d) <-
                [ ("concrete via RPC", diff pre conc truth) ]
                <> [ ("symbolic via RPC", diff pre got truth) | Just got <- [sym] ]
            ]
      pure
        $ tabulate "statements" [show (length prog)]
        $ tabulate "statement kinds" [takeWhile (/= ' ') (show st) | st <- prog]
        $ tabulate "symbolic leaves" [show (length leaves)]
        $ tabulate "partial paths" [show partials]
        $ counterexample ("code: " <> T.unpack (formatBinary code))
        $ counterexample ("unexpected fetches: " <> show unexp)
        $ counterexample (unlines mismatches)
        $ null unexp && null mismatches

-- | How an outcome differs from the expected one: the returndata, and the slots that differ
diff :: Slots -> Either String Outcome -> Either String Outcome -> Maybe String
diff pre got want
  | got == want = Nothing
  | otherwise = Just . unlines . map ("    " <>) $ case (got, want) of
      (Right (o, st), Right (o', st')) ->
        [ "returned " <> hex o <> ", expected " <> hex o' | o /= o' ]
        <> [ "slot " <> show k <> ": " <> show v <> ", expected " <> show v'
               <> " (pre-state " <> show (Map.findWithDefault 0 k pre) <> ")"
           | (k, v) <- Map.toList st, let v' = Map.findWithDefault 0 k st', v /= v' ]
      _ -> ["got " <> show got, "expected " <> show want]
  where hex = either id (T.unpack . formatBinary)
