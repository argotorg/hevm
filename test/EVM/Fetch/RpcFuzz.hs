-- | Fuzzes state fetched via RPC: programs must behave the same with the whole world known up
-- front as with it fetched from a mock node, concretely and symbolically.
module EVM.Fetch.RpcFuzz (tests) where

import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (mapConcurrently, async, cancel, wait)
import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.IO.Unlift (withRunInIO)
import Control.Monad.ST (stToIO)
import Data.Aeson ((.=))
import Data.Aeson qualified as JSON
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Control.Concurrent.MVar (readMVar, modifyMVar_)
import Data.IORef (readIORef)
import Data.List (zip6)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Word (Word8)
import Numeric (readHex)
import Test.QuickCheck hiding (Success, Failure)
import Test.Tasty
import Test.Tasty.HUnit (testCase, (@?=), assertFailure)
import System.Directory (doesFileExist)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty.QuickCheck (testProperty, QuickCheckTests(..))

import EVM (makeVm, initialContract, defaultVMOpts)
import EVM.ABI (abiMethod, AbiValue(..))
import EVM.Assembler qualified as Assembler
import EVM.Concrete qualified as Concrete
import EVM.Effects (App, Env(..), defaultConfig, runEnv)
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Fetch.MockNode (Account(..), World, Node(..), Request(..), withMockNode, withSlowMockNode, eoa)
import EVM.Format (formatBinary)
import EVM.Progress qualified as Progress
import EVM.Solvers (withSolvers, defMemLimit, Solver(..))
import EVM.Solidity (solcRuntime)
import EVM.Stepper qualified as Stepper
import EVM.SymExec (interpret, defaultIterConf, runExpr, noopPathHandler)
import EVM.Traversals (mapExpr, mapProp)
import EVM.Types hiding (Env)

tests :: TestTree
tests = testGroup "RPC fuzzing"
  -- each case runs the solver, so the default of 100 cases is lowered; any other count is kept
  [ adjustOption (\(QuickCheckTests n) -> QuickCheckTests (if n == 100 then 10 else n)) $
      testProperty "rpc-fuzz" prop_rpc
  , testCase "rpc-eoa-balance" $ do
      let addr = 0x1111111111111111111111111111111111111111
          code = asmOps
            [ OpPush (Lit (fromIntegral (addr :: Addr))), OpBalance
            , OpPush0, OpMstore, OpPush (Lit 0x20), OpPush0, OpReturn ]
      res <- withMockNode 16 (Map.singleton addr (eoa 1 0x1234)) $ \node ->
        runEnv (Env {config = defaultConfig}) $ withSolvers Bitwuzla 1 Nothing defMemLimit $ \solvers -> do
          sess <- Fetch.mkSessionWithoutCache
          let rpcInfo = Fetch.RpcInfo (Just (Fetch.BlockNumber 16, node.url))
          runConcrete (Fetch.oracle solvers (Just sess) rpcInfo) mempty (initialContract (RuntimeCode (ConcreteRuntimeCode code))) [] mempty
      fmap (\(o, _, _) -> o) res @?= Right (Right (word256Bytes 0x1234))
  , testCase "rpc-racing-fetches-share-one" $ withSlowMockNode 100_000 16 slotWorld $ \node -> runEnv (Env {config = defaultConfig}) $ do
      sess <- Fetch.mkSessionWithoutCache
      slots <- liftIO $ mapConcurrently (const (fetchSlot sess node 16)) [1 .. 8 :: Int]
      accs <- liftIO $ mapConcurrently (const (Fetch.fetchAccountWithSession defaultConfig sess Fetch.Latest node.url remote)) [1 .. 8 :: Int]
      liftIO $ do
        [v | Fetch.FetchSuccess v _ <- slots] @?= replicate 8 0x1234
        length [() | Fetch.FetchSuccess _ Fetch.Fresh <- slots] @?= 1
        length [() | Fetch.FetchSuccess _ Fetch.Fresh <- accs] @?= 1
        reqs <- readIORef node.requests
        repeats reqs @?= []
  , testCase "rpc-racing-fetches-share-errors" $ withSlowMockNode 100_000 16 slotWorld $ \node -> runEnv (Env {config = defaultConfig}) $ do
      sess <- Fetch.mkSessionWithoutCache
      -- the node serves another block, so every request fails
      res <- liftIO $ mapConcurrently (const (fetchSlot sess node 17)) [1 .. 8 :: Int]
      liftIO $ do
        length [() | Fetch.FetchError _ <- res] @?= 8
        (length <$> readIORef node.requests) >>= (@?= 1)
        -- failures are not cached
        _ <- fetchSlot sess node 17
        (length <$> readIORef node.requests) >>= (@?= 2)
  , testCase "rpc-killed-fetch-is-taken-over" $ withSlowMockNode 300_000 16 slotWorld $ \node -> runEnv (Env {config = defaultConfig}) $ do
      sess <- Fetch.mkSessionWithoutCache
      liftIO $ do
        owner <- async (fetchSlot sess node 16)
        threadDelay 50_000
        waiter <- async (fetchSlot sess node 16)
        threadDelay 50_000
        cancel owner
        res <- wait waiter
        res @?= Fetch.FetchSuccess 0x1234 Fetch.Fresh
        (length <$> readIORef node.requests) >>= (@?= 2)
  , testCase "rpc-cache-is-reused" $ withSystemTempDirectory "rpc-cache" $ \dir -> withMockNode 16 slotWorld $ \node -> runEnv (Env {config = defaultConfig}) $ do
      let run = Fetch.withCachedSession (Just (Fetch.PerChainUnder dir)) (Just node.url) (Just 16) $ \sess -> liftIO $ do
            _ <- fetchSlot sess node 16
            Fetch.fetchAccountWithSession defaultConfig sess (Fetch.BlockNumber 16) node.url remote
      _ <- run
      fresh <- liftIO $ readIORef node.requests
      rerun <- run
      liftIO $ do
        case rerun of
          Fetch.FetchSuccess c Fetch.Cached -> c.balance @?= remoteBalance
          r -> assertFailure ("expected a cached account, got " <> show r)
        doesFileExist (dir </> "1" </> "rpc-cache-16.json") >>= (@?= True)
        new <- readIORef node.requests
        map (.method) (take (length new - length fresh) new) @?= ["eth_chainId"]
  , testCase "rpc-cached-concrete-slot" $ do
      Just code <- solcRuntime "C" $ T.unlines
        [ "contract C {"
        , "  uint256[256] values;"
        , "  function read(uint256 x) public view returns (uint256) {"
        , "    return values[uint256(keccak256(abi.encode(x))) & 255];"
        , "  }"
        , "}"
        ]
      let slot = And (Lit 255) (Keccak (ConcreteBuf (word256Bytes 1)))
          cached v = ConcreteStore (Map.singleton (keccak' (word256Bytes 1) `mod` 256) v)
          cd = ConcreteBuf $ abiMethod "read(uint256)" (AbiTuple (V.singleton (AbiUInt 256 1)))
          cases = [(cached v, Lit v) | v <- [0, 1337]]
            <> [(SStore slot (Var "newValue") (cached 1337), Var "newValue")]
      runEnv (Env {config = defaultConfig}) $ withSolvers Bitwuzla 1 (Just 5) defMemLimit $ \solvers ->
        forM_ cases $ \(st, expected) -> do
          vm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Symbolic)
            { contract = (initialContract (RuntimeCode (ConcreteRuntimeCode code))) { storage = st, external = True }
            , address = LitAddr remote, calldata = (cd, []) }
          let fetcher q = case q of
                PleaseFetchSlot {} -> liftIO $ assertFailure "cached reads must not fetch storage"
                _ -> Fetch.oracle solvers Nothing Fetch.noRpc q
          leaves <- interpret fetcher defaultIterConf vm runExpr noopPathHandler
          liftIO $ case leaves of
            [Success _ _ out _] -> Expr.readWord (Lit 0) out @?= expected
            _ -> assertFailure $ "expected one successful read, got " <> show leaves
  ]

slotWorld :: World
slotWorld = Map.singleton remote (Account mempty 1 remoteBalance (Map.singleton 1 0x1234))

fetchSlot :: Fetch.Session -> Node -> W256 -> IO (Fetch.FetchResult W256)
fetchSlot sess node blk = Fetch.fetchSlotWithCache defaultConfig sess (Fetch.BlockNumber blk) node.url remote 1

asmOps :: [Op] -> ByteString
asmOps = BS.pack . map (\case LitByte b -> b; b -> internalError ("symbolic byte: " <> show b)) . V.toList . Assembler.assemble

-- * Programs

data Key = KLit W256 | KCd Int -- ^ calldataload(off) & 3
  deriving (Show, Eq)

-- | Mapping slots hash their preimage at the given memory offset. 'Folded' reduces a slot
-- to 0..3 and adds an offset, like a fixed-size array indexed by a hash: the slot stays a
-- term over a keccak that only concretizing the keccak resolves.
data Slot = Plain Key | Mapping Int Key W256 | Nested Int Key Key W256 | Folded Fold W256 Slot
  deriving (Show, Eq)

data Fold = FAnd | FMod | FShr
  deriving (Show, Eq)

-- | An index into 'targets', or 'targetBase' plus calldataload(off) & 3
data Target = T Int | TCd Int
  deriving (Show, Eq)

data CallKind = KCall | KDelegate | KStatic
  deriving (Show, Eq)

data Val = VLit W256 | VCd Int | VLoad Slot | VAdd Val Val
  | VBal Target | VCodeSize Target | VCodeHash Target | VSelfBal
  deriving (Show, Eq)

-- | 'Call' passes a key, a value, a key to read and a revert flag to a target, sending the
-- given wei along. 'Create' deploys an empty contract with the given wei, and with a salt, by CREATE2.
data Stmt = Store Slot Val | Load Slot | Call CallKind Target Key Val Key Key Key | Create (Maybe W256) Key
  deriving (Show, Eq)

-- | Pre-state storage of all accounts
type Slots = Map (Addr, W256) W256

type Balances = Map Addr W256

remote :: Addr
remote = 0x1234567890abcdef1234567890abcdef12345678

-- | Accounts the program can touch besides 'remote', each a contract, an EOA or absent;
-- the burn address and a precompile, as low addresses, hold ether on chain too
targets :: [Addr]
targets = [targetBase + i | i <- [0 .. 3]] <> [0xdead, 0x4]

targetBase :: Addr
targetBase = 0x2234567890abcdef1234567890abcdef12345678

-- | Where the CREATEs and CREATE2s of 'remote' deploy, which may already hold an account on chain
created :: [Addr]
created = [a | n <- [1 .. 8], LitAddr a <- [Concrete.createAddress remote n]]
  <> [a | s <- salts, LitAddr a <- [Concrete.create2Address remote s initCode]]

-- | The first two CREATE addresses and the CREATE2 ones
preCreatable :: [Addr]
preCreatable = take 2 created <> drop 8 created

salts :: [W256]
salts = [0, 1]

-- | The init code that 'Create' deploys: a single STOP
initCode :: ByteString
initCode = BS.singleton 0

accounts :: [Addr]
accounts = remote : targets <> created

remoteBalance :: W256
remoteBalance = 1000

-- | sstore(cd[0], cd[32]); if cd[96] revert; return sload(cd[64])
targetCode :: ByteString
targetCode = asmOps $ store <> condJump revertAt <> ret <> [OpJumpdest, OpPush0, OpPush0, OpRevert]
  where
    store = [OpPush (Lit 0x20), OpCalldataload, OpPush0, OpCalldataload, OpSstore]
    condJump dst = [OpPush (Lit 0x60), OpCalldataload, OpPush (Lit dst), OpJumpi]
    ret = [OpPush (Lit 0x40), OpCalldataload, OpSload, OpPush0, OpMstore, OpPush (Lit 0x20), OpPush0, OpReturn]
    revertAt = fromIntegral $ BS.length $ asmOps (store <> condJump 0 <> ret)

keyMask :: W256
keyMask = 3

idxs :: [W256]
idxs = [0, 1]

foldOffs :: [W256]
foldOffs = [0, 0x10]

cdOffs :: [Int]
cdOffs = [0, 32, 64, 96]

outBase :: Int
outBase = 0x200

mapSlot :: W256 -> W256 -> W256
mapSlot k idx = keccak' (word256Bytes k <> word256Bytes idx)

-- | Every slot a program can touch
domain :: [(Addr, W256)]
domain = map (remote,) (keys
  <> [o + k | o <- drop 1 foldOffs, k <- keys]
  <> [mapSlot k i | k <- keys, i <- idxs]
  <> [mapSlot k2 (mapSlot k1 i) | k1 <- keys, k2 <- keys, i <- idxs])
  <> [(t, k) | t <- targets, k <- keys]
  where keys = [0 .. keyMask]

-- * Assembly

pushW :: W256 -> [Word8]
pushW 0 = [0x5f]
pushW w = let bs = BS.unpack (BS.dropWhile (== 0) (word256Bytes w)) in (0x5f + fromIntegral (length bs)) : bs

pushI :: Int -> [Word8]
pushI = pushW . fromIntegral

pushT :: Target -> [Word8]
pushT = \case
  T i -> pushW (fromIntegral (targets !! i))
  TCd off -> asmKey (KCd off) <> pushW (fromIntegral targetBase) <> [0x01]

asmKey :: Key -> [Word8]
asmKey = \case
  KLit w -> pushW w
  KCd off -> pushW keyMask <> pushI off <> [0x35, 0x16]

asmSlot :: Slot -> [Word8]
asmSlot = \case
  Plain k -> asmKey k
  Mapping h k idx -> hash h (asmKey k) (pushW idx)
  Nested h k1 k2 idx -> hash h (asmKey k2) (asmSlot (Mapping h k1 idx))
  Folded f off s -> (case f of
      FAnd -> asmSlot s <> pushW keyMask <> [0x16]
      FMod -> pushW (keyMask + 1) <> asmSlot s <> [0x06]
      FShr -> asmSlot s <> pushW 254 <> [0x1c])
    <> (if off == 0 then [] else pushW off <> [0x01])
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
  VBal t -> pushT t <> [0x31]
  VCodeSize t -> pushT t <> [0x3b]
  VCodeHash t -> pushT t <> [0x3f]
  VSelfBal -> [0x47]

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
      -- the success flag is stored too, as calls to accounts without code return nothing
      Call kind t k v rk rev wei -> asmKey k <> pushI 0x100 <> [0x52] <> asmVal v <> pushI 0x120 <> [0x52]
        <> asmKey rk <> pushI 0x140 <> [0x52] <> asmKey rev <> pushI 0x160 <> [0x52]
        <> pushI 32 <> pushI (outOffs !! i) <> pushI 128 <> pushI 0x100
        <> (case kind of KCall -> asmKey wei <> pushT t <> pushW 0xffffffff <> [0xf1]
                         KDelegate -> pushT t <> pushW 0xffffffff <> [0xf4]
                         KStatic -> pushT t <> pushW 0xffffffff <> [0xfa])
        <> pushI (outOffs !! i) <> [0x51, 0x01] <> pushI (outOffs !! i) <> [0x52]
      -- memory at 0x1f0 is never written, so the init code is a single STOP
      Create salt wei -> maybe [] pushW salt <> pushI 1 <> pushI 0x1f0 <> asmKey wei
        <> [maybe 0xf0 (const 0xf5) salt] <> pushI (outOffs !! i) <> [0x52]

-- * Generators

genWord :: Gen W256
genWord = frequency
  [ (3, fromIntegral <$> choose (0 :: Int, 5))
  , (1, elements [maxBound, 2 ^ (255 :: Int)])
  , (3, word . BS.pack <$> vectorOf 32 arbitrary)
  ]

genKey :: Gen Key
genKey = oneof [KLit <$> elements [0 .. keyMask], KCd <$> elements cdOffs]

genTarget :: Gen Target
genTarget = frequency [(4, T <$> choose (0, length targets - 1)), (1, TCd <$> elements cdOffs)]

genSlot :: Gen Slot
genSlot = frequency
  [ (4, base)
  , (1, Folded <$> elements [FAnd, FMod, FShr] <*> elements foldOffs <*> base)
  ]
  where
    base = frequency
      [ (2, Plain <$> genKey)
      , (3, Mapping <$> hashOff <*> genKey <*> elements idxs)
      , (2, Nested <$> hashOff <*> genKey <*> genKey <*> elements idxs)
      ]
    hashOff = elements [0, 0x40, 0xa0]

genVal :: Int -> Gen Val
genVal d = frequency $
  [ (3, VLit <$> genWord), (3, VCd <$> elements cdOffs), (2, VLoad <$> genSlot)
  , (2, oneof [VBal <$> genTarget, VCodeSize <$> genTarget, VCodeHash <$> genTarget, pure VSelfBal]) ]
  <> [ (1, VAdd <$> genVal (d - 1) <*> genVal (d - 1)) | d > 0 ]

genStmt :: Gen Stmt
genStmt = frequency
  [ (3, Store <$> genSlot <*> genVal 2), (3, Load <$> genSlot)
  , (2, Call <$> genKind <*> genTarget <*> genKey <*> genVal 1 <*> genKey <*> genRevert <*> genWei)
  , (1, Create <$> oneof [pure Nothing, Just <$> elements salts] <*> genWei) ]
  where
    genKind = frequency [(3, pure KCall), (1, pure KDelegate), (1, pure KStatic)]
    genRevert = frequency [(3, pure (KLit 0)), (1, pure (KLit 1)), (1, KCd <$> elements cdOffs)]
    -- symbolic wei costs a balance query per call on every path
    genWei = frequency [(3, KLit <$> elements [0 .. keyMask]), (1, KCd <$> elements cdOffs)]

-- | 'remote' and the targets, each of which may be a contract, an EOA or absent
genWorld :: Gen World
genWorld = do
  others <- forM targets $ \t -> do
    st <- genStorage t
    frequency
      [ (if t <= 0x11 then 0 else 2, (\n b -> [(t, Account targetCode n b st)]) <$> genNonce <*> genBalance)
      , (2, (\n b -> [(t, Account mempty n b mempty)]) <$> genNonce <*> genBalance)
      , (1, pure [])
      ]
  -- funded before the deployment, or taken: then the CREATE collides
  preCreated <- forM preCreatable $ \a -> frequency
    [ (3, pure [])
    , (2, (\b -> [(a, Account mempty 0 b mempty)]) <$> genBalance)
    , (1, (\n b -> [(a, Account mempty n b mempty)]) <$> (fromIntegral <$> choose (1 :: Int, 5)) <*> genBalance)
    , (1, (\b -> [(a, Account targetCode 1 b mempty)]) <$> genBalance)
    -- storage alone makes a collision (EIP-7610)
    , (1, (\b v -> [(a, Account mempty 0 b (Map.singleton 0 v))]) <$> genBalance <*> (genWord `suchThat` (/= 0)))
    ]
  st <- genStorage remote
  pure $ Map.fromList $ (remote, Account mempty 1 remoteBalance st) : concat others <> concat preCreated
  where
    -- far above the ether supply, but wrapping balances would make worlds no chain can reach
    genBalance = frequency [(1, fromIntegral <$> choose (0 :: Int, 5)), (2, (`mod` 2 ^ (96 :: Int)) <$> genWord)]
    genNonce = frequency [(1, pure 0), (3, fromIntegral <$> choose (1 :: Int, 1000))]
    genStorage a = Map.fromList . concat <$> forM [s | (a', s) <- domain, a' == a] (\s ->
      frequency [(1, pure []), (2, (\v -> [(s, v)]) <$> genWord)])

shrinkWorld :: World -> [World]
shrinkWorld w = [Map.delete t w | t <- targets <> created, Map.member t w]
  <> [Map.adjust (\(Account c n b _) -> Account c n b mempty) a w | (a, acc) <- Map.toList w, not (null acc.storage)]

genCalldata :: Gen ByteString
genCalldata = BS.concat <$> vectorOf (length cdOffs) (word256Bytes <$> genWord)

shrinkStmt :: Stmt -> [Stmt]
shrinkStmt = \case
  Store s v -> Load s : [Store s v' | v' <- shrinkVal v] <> [Store s' v | s' <- shrinkSlot s]
  Load s -> map Load (shrinkSlot s)
  Call kind t k v rk rev wei -> [Call KCall t k v rk rev wei | kind /= KCall]
    <> [Call kind t k v rk (KLit 0) wei | rev /= KLit 0]
    <> [Call kind t k v rk rev (KLit 0) | wei /= KLit 0]
    <> [Call kind t k v' rk rev wei | v' <- shrinkVal v]
  Create salt wei -> [Create Nothing wei | salt /= Nothing] <> [Create salt (KLit 0) | wei /= KLit 0]
  where
    shrinkVal = \case
      VAdd a b -> [a, b]
      VLit w | w > 1 -> [VLit 0, VLit 1]
      _ -> []
    shrinkSlot = \case
      Folded _ _ s -> [s]
      _ -> []

-- * Runs

-- | What a run returned, and the final storage and balances of every account
type Outcome = (Either String ByteString, Slots, Balances)

preSlots :: World -> Slots
preSlots w = Map.fromList [((a, s), v) | (a, acc) <- Map.toList w, (s, v) <- Map.toList acc.storage]

preBalances :: World -> Balances
preBalances w = Map.fromList [(a, maybe 0 (.balance) (Map.lookup a w)) | a <- accounts]

-- | Reads the final state from the given storage and balance of each account, falling back to
-- the pre-state for accounts and slots never touched
finalState :: World -> Map (Expr EAddr) (Expr Storage, Expr EWord) -> Either String (Slots, Balances)
finalState w accs = (,) <$> (Map.fromList <$> mapM slot domain) <*> (Map.fromList <$> mapM bal accounts)
  where
    slot k@(a, s) = case Map.lookup (LitAddr a) accs >>= Expr.readStorage (Lit s) . fst of
      Nothing -> Right (k, Map.findWithDefault 0 k (preSlots w))
      Just (Lit v) -> Right (k, v)
      Just e -> Left $ "undecided read of slot " <> show s <> " at " <> show a <> ": " <> show e
    bal a = case snd <$> Map.lookup (LitAddr a) accs of
      Nothing -> Right (a, Map.findWithDefault 0 a (preBalances w))
      Just (Lit v) -> Right (a, v)
      Just e -> Left $ "undecided balance of " <> show a <> ": " <> show e

contractOf :: Account -> Bool -> Contract
contractOf acc ext = (initialContract (RuntimeCode (ConcreteRuntimeCode acc.code)))
  { storage = st, origStorage = st, balance = Lit acc.balance, nonce = Just acc.nonce, external = ext }
  where st = ConcreteStore acc.storage

-- | 'remote' as the run starts with it: everything known but, when fetching, its storage
remoteContract :: ByteString -> World -> Bool -> Contract
remoteContract code w fetching = contractOf (acc { code = code, storage = if fetching then mempty else acc.storage }) fetching
  where acc = w Map.! remote

runConcrete :: App m => Fetch.Fetcher Concrete m -> World -> Contract -> [(Expr EAddr, Contract)] -> ByteString -> m (Either String Outcome)
runConcrete fetcher w c others cd = do
  vm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Concrete)
    { contract = c, otherContracts = others, address = LitAddr remote, calldata = (ConcreteBuf cd, [])
    , gas = 0xffffffffffffffff, gaslimit = 0xffffffffffffffff }
  end <- Stepper.interpret fetcher vm Stepper.runFully
  let out = case end.result of
        Just (VMSuccess (ConcreteBuf bs)) -> Right bs
        Just (VMFailure e) -> Left (show e)
        r -> Left (show r)
  pure $ (\(s, b) -> (out, s, b)) <$> finalState w (fmap (\c' -> (c'.storage, c'.balance)) end.env.contracts)

-- | The outcome of the symbolic leaf that the given calldata takes, if it is not a partial one.
-- When strict, the returndata must be concrete without concretizing keccaks: symbolic
-- execution on concrete calldata has every value it reads.
evalSymbolic :: Bool -> World -> [Expr End] -> ByteString -> Either String (Maybe Outcome)
evalSymbolic strict w leaves cd = case filter (taken . props) leaves of
  [Success _ _ buf cs] -> do
    out <- case (if strict then Expr.simplify buf else sub buf) of
      ConcreteBuf bs -> Right (Right bs)
      b -> Left ("undecided returndata: " <> show b)
    (s, b) <- finalState w (Map.fromList [(a, (sub st, sub bal)) | (a, C _ st _ bal _) <- Map.toList cs])
    pure $ Just (out, s, b)
  [Partial {}] -> Right Nothing
  [Failure _ _ e] -> Right (Just (Left (show e), preSlots w, preBalances w))
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

-- | Requests a run should never make: state outside what the program can touch
unexpected :: Request -> Maybe String
unexpected (Request m ps) = case (m, map hex ps) of
  ("eth_getStorageAt", Just a : Just s : _) | (fromIntegral a, s) `notElem` domain -> bad
  (_, Just a : _) | m `elem` ["eth_getCode", "eth_getBalance", "eth_getTransactionCount", "eth_getProof"]
                  , fromIntegral a `notElem` (targets <> created) -> bad
  _ -> Nothing
  where
    bad = Just (show (Request m ps))
    hex :: JSON.Value -> Maybe W256
    hex = \case
      JSON.String t | Just h <- T.stripPrefix "0x" t, [(n, "")] <- readHex (T.unpack h) -> Just (fromInteger n)
      _ -> Nothing

-- | Requests made more than once: a session caches everything it fetches
repeats :: [Request] -> [Request]
repeats rs = [r | (r, n) <- Map.elems counts, n > (1 :: Int)]
  where counts = Map.fromListWith (\(r, a) (_, b) -> (r, a + b)) [(show r, (r, 1)) | r <- rs]

-- | A session whose cache went through the JSON form it is saved to disk in
reloaded :: App m => Fetch.Session -> m Fetch.Session
reloaded old = do
  new <- Fetch.mkSessionWithoutCache
  cache <- liftIO $ readMVar old.sharedCache
  case JSON.eitherDecode @Fetch.FetchCache (JSON.encode cache) of
    Left e -> internalError ("cannot reload RPC cache: " <> e)
    Right c -> liftIO $ modifyMVar_ new.sharedCache (const (pure c))
  pure new

prop_rpc :: Property
prop_rpc =
  forAllShrink (choose (1, 8) >>= flip vectorOf genStmt) (shrinkList shrinkStmt) $ \prog ->
  forAllShrink genWorld shrinkWorld $ \world ->
  forAllBlind (vectorOf 3 genCalldata) $ \cds ->
  forAll ((,) . fromIntegral <$> choose (1 :: Int, 100) <*> arbitrary) $ \(blk, latest) ->
  forAll arbitrary $ \reload -> ioProperty $ withMockNode blk world $ \node -> do
    let code = assemble prog
        rpcInfo = Fetch.RpcInfo (Just (if latest then Fetch.Latest else Fetch.BlockNumber blk, node.url))
        known = [(LitAddr a, contractOf acc False) | (a, acc) <- Map.toList world, a /= remote]
    runEnv (Env {config = defaultConfig}) $ Progress.withProgressLogFromEnv "rpc-fuzz" $
      withSolvers Bitwuzla 1 (Just 5) defMemLimit $ \solvers -> do
      truths <- Progress.withPhase "concrete" [] (const []) $ mapM
        (runConcrete (Fetch.oracle solvers Nothing Fetch.noRpc) world (remoteContract code world False) known) cds
      let mark = liftIO $ length <$> readIORef node.requests
          runFetching sess = runConcrete (Fetch.oracle solvers (Just sess) rpcInfo) world (remoteContract code world True) []
      concSess <- Fetch.mkSessionWithoutCache
      fetched <- Progress.withPhase "concrete-rpc" [] (const []) $ mapM (runFetching concSess) cds
      afterConc <- mark
      -- the runs race on the same state through one session, as Echidna's workers do
      raced <- Progress.withPhase "concurrent-rpc" [] (const []) $ do
        sess <- Fetch.mkSessionWithoutCache
        withRunInIO $ \run -> mapConcurrently (run . runFetching sess) cds
      afterRaced <- mark
      symSess <- if reload then reloaded concSess else Fetch.mkSessionWithoutCache
      symVm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Symbolic)
        { contract = remoteContract code world True, address = LitAddr remote
        , calldata = (AbstractBuf "txdata", []) }
      leaves <- Progress.withPhase "symbolic" ["program" .= show prog] (\ls -> ["leaves" .= length ls]) $
        interpret (Fetch.oracle solvers (Just symSess) rpcInfo) defaultIterConf symVm runExpr noopPathHandler
      let symbolic = map (sequence . evalSymbolic False world leaves) cds
      symConcrete <- Progress.withPhase "symbolic-concrete" [] (const []) $ forM cds $ \cd -> do
        vm <- liftIO $ stToIO $ makeVm (defaultVMOpts @Symbolic)
          { contract = remoteContract code world True, address = LitAddr remote
          , calldata = (ConcreteBuf cd, []) }
        ls <- interpret (Fetch.oracle solvers (Just symSess) rpcInfo) defaultIterConf vm runExpr noopPathHandler
        pure $ sequence (evalSymbolic True world ls cd)
      reqs <- liftIO $ readIORef node.requests
      let since from to = take (to - from) (drop (length reqs - to) reqs)
          perSession = [ ("concrete" :: String, since 0 afterConc), ("concurrent", since afterConc afterRaced)
                       , ("symbolic", since afterRaced (length reqs)) ]
          repeated = [(phase, r) | (phase, rs) <- perSession, r <- repeats rs]
          unexp = mapMaybe unexpected reqs
          partials = length [() | Nothing <- symbolic]
          mismatches =
            [ "calldata " <> T.unpack (formatBinary cd) <> "\n  " <> what <> ":\n" <> d
            | (cd, truth, conc, race, sym, symConc) <- zip6 cds truths fetched raced symbolic symConcrete
            , (what, Just d) <-
                [ ("concrete via RPC", diff world conc truth) ]
                <> [ ("concurrently via RPC", diff world race truth) ]
                <> [ ("symbolic via RPC", diff world got truth) | Just got <- [sym] ]
                <> [ ("symbolic on concrete calldata via RPC", diff world got truth) | Just got <- [symConc] ]
            ]
      pure
        $ tabulate "statements" [show (length prog)]
        $ tabulate "statement kinds" [takeWhile (/= ' ') (show st) | st <- prog]
        $ tabulate "target kinds" [kind (Map.lookup t world) | t <- targets]
        $ tabulate "pre-created kinds" [kind (Map.lookup t world) | t <- preCreatable]
        $ tabulate "symbolic leaves" [show (length leaves)]
        $ tabulate "partial paths" [show partials]
        $ tabulate "partial reasons" [case r of UnexpectedSymbolicArg { opcode, msg } -> opcode <> ": " <> msg; _ -> takeWhile (/= ' ') (show r) | Partial _ _ r <- leaves]
        $ tabulate "RPC requests" [T.unpack r.method | r <- reqs]
        $ counterexample ("code: " <> T.unpack (formatBinary code))
        $ counterexample ("unexpected requests: " <> show unexp)
        $ counterexample ("requests repeated within a session: " <> show repeated)
        $ counterexample (unlines mismatches)
        $ null unexp && null repeated && null mismatches
  where
    kind = \case
      Nothing -> "absent"
      Just acc | BS.null acc.code -> "EOA"
               | otherwise -> "contract"

-- | How an outcome differs from the expected one: the returndata, and the slots and balances
-- that differ
diff :: World -> Either String Outcome -> Either String Outcome -> Maybe String
diff w got want
  | got == want = Nothing
  | otherwise = Just . unlines . map ("    " <>) $ case (got, want) of
      (Right (o, st, bs), Right (o', st', bs')) ->
        [ "returned " <> hex o <> ", expected " <> hex o' | o /= o' ]
        <> [ "slot " <> show k <> ": " <> show v <> ", expected " <> show v'
               <> " (pre-state " <> show (Map.findWithDefault 0 k (preSlots w)) <> ")"
           | (k, v) <- Map.toList st, let v' = Map.findWithDefault 0 k st', v /= v' ]
        <> [ "balance of " <> show a <> ": " <> show v <> ", expected " <> show v'
           | (a, v) <- Map.toList bs, let v' = Map.findWithDefault 0 a bs', v /= v' ]
      _ -> ["got " <> show got, "expected " <> show want]
  where hex = either id (T.unpack . formatBinary)
