module EVM.Expr.Generator where

import Prelude hiding (LT, GT)

import Control.Monad (replicateM)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.DoubleWord (Word128, Word256, Word160, fromHiAndLo)
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as T (pack)
import Data.Vector qualified as V
import Data.Word (Word8, Word64)
import GHC.TypeLits
import Witch (into)

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Instances.ByteString()

import EVM.Types (Expr(..), EType(..), W256(..), W64(..), internalError, Addr(..), Prop(..), ContractCode(..), RuntimeCode(..), EvmError(..))
import EVM.Expr qualified as Expr

-- GenWriteStorageLoad
newtype GenWriteStorageLoad = GenWriteStorageLoad (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenWriteStorageLoad where
  arbitrary = do
    load <- genStorageLoad 10
    pure $ GenWriteStorageLoad load

    where
      genStorageLoad :: Int -> Gen (Expr EWord)
      genStorageLoad sz = SLoad <$> genStorageKey <*> genStorage (sz `div` 10)

genStorage :: Int -> Gen (Expr Storage)
genStorage 0 = oneof
  [ AbstractStore <$> arbitrary <*> (pure Nothing)
  , ConcreteStore <$> resize 5 arbitrary
  ]
genStorage sz = SStore <$> genStorageKey <*> val <*> subStore
  where
    subStore = genStorage (sz `div` 10)
    val = defaultWord (sz `div` 5)

genStorageKey :: Gen (Expr EWord)
genStorageKey = frequency
     -- array slot
    [ (4, Expr.ArraySlotWithOffs <$> (genByteStringKey 32) <*> (genLit 5))
    , (4, Expr.ArraySlotZero <$> (genByteStringKey 32))
     -- mapping slot
    , (8, Expr.MappingSlot <$> (genByteStringKey 64) <*> (genLit 5))
     -- small slot
    , (4, genLit 20)
    -- unrecognized slot type
    , (1, genLit 5)
    ]

genByteStringKey :: W256 -> Gen (ByteString)
genByteStringKey len = do
  b :: Word8 <- arbitrary
  pure $ BS.pack ([ 0 | _ <- [0..(len-2)]] ++ [b `mod` 5])

genLit :: W256 -> Gen (Expr EWord)
genLit bound = do
  w <- arbitrary
  pure $ Lit (w `mod` bound)

defaultWord :: Int -> Gen (Expr EWord)
defaultWord = genWord 10

genWord :: Int -> Int -> Gen (Expr EWord)
genWord litFreq 0 = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
       , (1, pure 0)
       , (1, pure Expr.maxLit)
       , (1, arbitrary)
       ]
      pure $ Lit val
    )
  , (1, oneof
      [ pure Origin
      , pure Coinbase
      , pure Timestamp
      , pure BlockNumber
      , pure PrevRandao
      , pure GasLimit
      , pure ChainId
      , pure BaseFee
      --, liftM2 SelfBalance arbitrary arbitrary
      --, liftM2 Gas arbitrary arbitrary
      , fmap Lit arbitrary
      , fmap joinBytesFromList $ replicateM 32 arbitrary
      , fmap Var (genName "word")
      ]
    )
  ]
genWord litFreq sz = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
       , (1, arbitrary)
       ]
      pure $ Lit val
    )
  , (1, oneof
    [ Add <$> subWord <*> subWord
    , Sub <$> subWord <*> subWord
    , Mul <$> subWord <*> subWord
    , Div <$> subWord <*> subWord
    , SDiv <$> subWord <*> subWord
    , Mod <$> subWord <*> subWord
    , SMod <$> subWord <*> subWord
    -- We skip AddMod, MulMod and Exp intentionally
    , SEx <$> subWord <*> subWord
    , Min <$> subWord <*> subWord
    , LT <$> subWord <*> subWord
    , GT <$> subWord <*> subWord
    , LEq <$> subWord <*> subWord
    , GEq <$> subWord <*> subWord
    , SLT <$> subWord <*> subWord
    , SGT <$> subWord <*> subWord
    , Eq <$> subWord <*> subWord
    , IsZero <$> subWord
    , And <$> subWord <*> subWord
    , Or <$> subWord <*> subWord
    , Xor <$> subWord <*> subWord
    , Not <$> subWord
    , SHL <$> subWord <*> subWord
    , SHR <$> subWord <*> subWord
    , SAR <$> subWord <*> subWord
    , BlockHash <$> subWord
    --, liftM3 Balance arbitrary arbitrary subWord
    --, fmap CodeSize subWord
    --, fmap ExtCodeHash subWord
    , Keccak <$> subBuf
    , SLoad <$> subWord <*> subStore
    , ReadWord <$> genReadIndex <*> subBuf
    , BufLength <$> subBuf
    , do
      one <- subByte
      two <- subByte
      three <- subByte
      four <- subByte
      five <- subByte
      six <- subByte
      seven <- subByte
      eight <- subByte
      nine <- subByte
      ten <- subByte
      eleven <- subByte
      twelve <- subByte
      thirteen <- subByte
      fourteen <- subByte
      fifteen <- subByte
      sixteen <- subByte
      seventeen <- subByte
      eighteen <- subByte
      nineteen <- subByte
      twenty <- subByte
      twentyone <- subByte
      twentytwo <- subByte
      twentythree <- subByte
      twentyfour <- subByte
      twentyfive <- subByte
      twentysix <- subByte
      twentyseven <- subByte
      twentyeight <- subByte
      twentynine <- subByte
      thirty <- subByte
      thirtyone <- subByte
      thirtytwo <- subByte
      pure $ JoinBytes
        one two three four five six seven eight nine ten
        eleven twelve thirteen fourteen fifteen sixteen
        seventeen eighteen nineteen twenty twentyone
        twentytwo twentythree twentyfour twentyfive
        twentysix twentyseven twentyeight twentynine
        thirty thirtyone thirtytwo
    ])
  ]
 where
   subWord = genWord litFreq (sz `div` 5)
   subBuf = defaultBuf (sz `div` 10)
   subStore = genStorage (sz `div` 10)
   subByte = genByte (sz `div` 10)
   genReadIndex = do
    o :: (Expr EWord) <- subWord
    pure $ case o of
      Lit w -> Lit $ w `mod` into (maxBound :: Word64)
      _ -> o

genName :: String -> Gen Text
-- In order not to generate SMT reserved words, we prepend with "esc_"
genName ty = fmap (T.pack . (("esc_" <> ty <> "_") <> )) $ listOf1 (oneof . (fmap pure) $ ['a'..'z'] <> ['A'..'Z'])


genByte :: Int -> Gen (Expr Byte)
genByte 0 = fmap LitByte arbitrary
genByte sz = oneof
  [ IndexWord <$> subWord <*> subWord
  , ReadByte <$> subWord <*> subBuf
  ]
  where
    subWord = defaultWord (sz `div` 10)
    subBuf = defaultBuf (sz `div` 10)

defaultBuf :: Int -> Gen (Expr Buf)
defaultBuf = genBuf (4_000_000)

genBuf :: W256 -> Int -> Gen (Expr Buf)
genBuf _ 0 = oneof
  [ fmap AbstractBuf (genName "buf")
  , fmap ConcreteBuf arbitrary
  ]
genBuf bound sz = oneof
  [ WriteWord <$> (maybeBoundedLit bound) <*> subWord <*> subBuf
  , WriteByte <$> (maybeBoundedLit bound) <*> subByte <*> subBuf
  -- we don't generate copyslice instances where:
  --   - size is abstract
  --   - size > 100 (due to unrolling in SMT.hs)
  --   - literal dstOffsets are > 4,000,000 (due to unrolling in SMT.hs)
  -- n.b. that 4,000,000 is the theoretical maximum memory size given a 30,000,000 block gas limit
  , CopySlice <$> genReadIndex <*> (maybeBoundedLit bound) <*> smolLitWord <*> subBuf <*> subBuf
  ]
  where
    -- copySlice gets unrolled in the generated SMT so we can't go too crazy here
    smolLitWord = do
      w <- arbitrary
      pure $ Lit (w `mod` 100)
    subWord = defaultWord (sz `div` 5)
    subByte = genByte (sz `div` 10)
    subBuf = genBuf bound (sz `div` 10)
    genReadIndex = do
      o :: (Expr EWord) <- subWord
      pure $ case o of
        Lit w -> Lit $ w `mod` into (maxBound :: Word64)
        _ -> o

maybeBoundedLit :: W256 -> Gen (Expr EWord)
maybeBoundedLit bound = do
    o <- (arbitrary :: Gen (Expr EWord))
    pure $ case o of
            Lit w -> Lit $ w `mod` bound
            _ -> o

joinBytesFromList :: [Expr Byte] -> Expr EWord
joinBytesFromList [a0, a1, a2, a3, a4, a5, a6, a7,
                   a8, a9, a10, a11, a12, a13, a14, a15,
                   a16, a17, a18, a19, a20, a21, a22, a23,
                   a24, a25, a26, a27, a28, a29, a30, a31] =
  JoinBytes a0 a1 a2 a3 a4 a5 a6 a7
            a8 a9 a10 a11 a12 a13 a14 a15
            a16 a17 a18 a19 a20 a21 a22 a23
            a24 a25 a26 a27 a28 a29 a30 a31
joinBytesFromList _ = internalError "List must contain exactly 32 elements"

instance Arbitrary W256 where
  arbitrary = fmap W256 arbitrary

instance Arbitrary Word128 where
  arbitrary = fromHiAndLo <$> arbitrary <*> arbitrary

instance Arbitrary Word160 where
  arbitrary = fromHiAndLo <$> arbitrary <*> arbitrary

instance Arbitrary Word256 where
  arbitrary = fromHiAndLo <$> arbitrary <*> arbitrary

instance Arbitrary W64 where
  arbitrary = fmap W64 arbitrary

instance Arbitrary Addr where
  arbitrary = fmap Addr arbitrary

instance Arbitrary (Expr EAddr) where
  arbitrary = oneof
    [ fmap LitAddr arbitrary
    , fmap SymAddr (genName "addr")
    ]

instance Arbitrary (Expr Storage) where
  arbitrary = sized genStorage

instance Arbitrary (Expr EWord) where
  arbitrary = sized defaultWord

instance Arbitrary (Expr Byte) where
  arbitrary = sized genByte

newtype SymbolicJoinBytes = SymbolicJoinBytes [Expr Byte]
  deriving (Eq, Show)

instance Arbitrary SymbolicJoinBytes where
  arbitrary = SymbolicJoinBytes <$> replicateM 32 arbitrary

instance Arbitrary (Expr Buf) where
  arbitrary = sized defaultBuf

instance Arbitrary (Expr EContract) where
  arbitrary = sized genEContract

genEContract :: Int -> Gen (Expr EContract)
genEContract sz = do
  c <- arbitrary
  b <- defaultWord sz
  n <- arbitrary
  s <- genStorage sz
  ts <- genStorage sz
  pure $ C {code=c, storage=s, tStorage=ts, balance=b, nonce=n}

instance Arbitrary (Expr End) where
  arbitrary = sized genEnd

instance Arbitrary (ContractCode) where
  arbitrary = oneof
    [ fmap UnknownCode arbitrary
    , InitCode <$> arbitrary <*> arbitrary
    , fmap RuntimeCode arbitrary
    ]

instance Arbitrary (RuntimeCode) where
  arbitrary = oneof
    [ fmap ConcreteRuntimeCode arbitrary
    , fmap SymbolicRuntimeCode arbitrary
    ]

instance Arbitrary (V.Vector (Expr Byte)) where
  arbitrary = fmap V.fromList (listOf1 arbitrary)

-- ZeroDepthWord
newtype ZeroDepthWord = ZeroDepthWord (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary ZeroDepthWord where
  arbitrary = do
    fmap ZeroDepthWord . sized $ genWord 0


-- GenWriteStorageExpr
newtype GenWriteStorageExpr = GenWriteStorageExpr (Expr EWord, Expr Storage)
  deriving (Show, Eq)

instance Arbitrary GenWriteStorageExpr where
  arbitrary = do
    slot <- arbitrary
    let mkStore = oneof
          [ pure $ ConcreteStore mempty
          , fmap ConcreteStore arbitrary
          , do
              -- generate some write chains where we know that at least one
              -- write matches either the input addr, or both the input
              -- addr and slot
              let addWrites :: Expr Storage -> Int -> Gen (Expr Storage)
                  addWrites b 0 = pure b
                  addWrites b n = SStore <$> arbitrary <*> arbitrary <*> (addWrites b (n - 1))
              s <- arbitrary
              addMatch <- fmap (SStore slot) arbitrary
              let withMatch = addMatch s
              newWrites <- oneof [ pure 0, pure 1, fmap (`mod` 5) arbitrary ]
              addWrites withMatch newWrites
          , arbitrary
          ]
    store <- mkStore
    pure $ GenWriteStorageExpr (slot, store)

-- WriteWordBuf
newtype WriteWordBuf = WriteWordBuf (Expr Buf)
  deriving (Show, Eq)

instance Arbitrary WriteWordBuf where
  arbitrary = do
    let mkBuf = oneof
          [ pure $ ConcreteBuf ""       -- empty
          , fmap ConcreteBuf arbitrary  -- concrete
          , sized (genBuf 100)          -- overlapping writes
          , arbitrary                   -- sparse writes
          ]
    fmap WriteWordBuf mkBuf

-- GenCopySliceBuf
newtype GenCopySliceBuf = GenCopySliceBuf (Expr Buf)
  deriving (Show, Eq)

instance Arbitrary GenCopySliceBuf where
  arbitrary = do
    let mkBuf = oneof
          [ pure $ ConcreteBuf ""
          , fmap ConcreteBuf arbitrary
          , arbitrary
          ]
    fmap GenCopySliceBuf mkBuf

-- GenWriteByteIdx
newtype GenWriteByteIdx = GenWriteByteIdx (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenWriteByteIdx where
  arbitrary = do
    -- 1st: can never overflow an Int
    -- 2nd: can overflow an Int
    let mkIdx = frequency [ (10, genLit 1_000_000) , (1, fmap Lit arbitrary) ]
    fmap GenWriteByteIdx mkIdx

newtype LitOnly a = LitOnly a
  deriving (Show, Eq)

newtype LitWord (sz :: Nat) = LitWord (Expr EWord)
  deriving (Show)

instance (KnownNat sz) => Arbitrary (LitWord sz) where
  arbitrary = LitWord <$> genLit (fromInteger v)
    where
      v = natVal (Proxy @sz)

instance Arbitrary (LitOnly (Expr Byte)) where
  arbitrary = LitOnly . LitByte <$> arbitrary

instance Arbitrary (LitOnly (Expr EWord)) where
  arbitrary = LitOnly . Lit <$> arbitrary

instance Arbitrary (LitOnly (Expr Buf)) where
  arbitrary = LitOnly . ConcreteBuf <$> arbitrary

newtype LitProp = LitProp Prop
  deriving (Show, Eq)

instance Arbitrary LitProp where
  arbitrary = LitProp <$> sized (genProp True)

instance Arbitrary Prop where
  arbitrary = sized (genProp False)

genProps :: Bool -> Int -> Gen [Prop]
genProps onlyLits sz2 = listOf $ genProp onlyLits sz2

genProp :: Bool -> Int -> Gen (Prop)
genProp _ 0 = PBool <$> arbitrary
genProp onlyLits sz = oneof
  [ PEq <$> subWord <*> subWord
  , PLT <$> subWord <*> subWord
  , PGT <$> subWord <*> subWord
  , PLEq <$> subWord <*> subWord
  , PGEq <$> subWord <*> subWord
  , PNeg <$> subProp
  , PAnd <$> subProp <*> subProp
  , POr <$> subProp <*> subProp
  , PImpl <$> subProp <*> subProp
  ]
  where
    subWord = if onlyLits then frequency [(2, Lit <$> arbitrary)
                                         ,(1, pure $ Lit 0)
                                         ,(1, pure $ Lit Expr.maxLit)
                                         ]
                          else genWord 1 (sz `div` 2)
    subProp = genProp onlyLits (sz `div` 2)


newtype StorageExp = StorageExp (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary StorageExp where
  arbitrary = StorageExp <$> (genStorageExp)


genStorageExp :: Gen (Expr EWord)
genStorageExp = do
  fromPos <- genSlot
  storage <- genStorageWrites
  pure $ SLoad fromPos storage

genSlot :: Gen (Expr EWord)
genSlot = frequency [ (1, do
                        buf <- genConcreteBufSlot 64
                        case buf of
                          (ConcreteBuf b) -> do
                            key <- genLit 10
                            pure $ Expr.MappingSlot b key
                          _ -> internalError "impossible"
                        )
                     -- map element
                     ,(2, do
                        l <- genLit 10
                        buf <- genConcreteBufSlot 64
                        pure $ Add (Keccak buf) l)
                    -- Array element
                     ,(2, do
                        l <- genLit 10
                        buf <- genConcreteBufSlot 32
                        pure $ Add (Keccak buf) l)
                     -- member of the Contract
                     ,(2, pure $ Lit 20)
                     -- array element
                     ,(2, do
                        arrayNum :: Int <- arbitrary
                        offs :: W256 <- arbitrary
                        pure $ Lit $ fst (Expr.preImages !! (arrayNum `mod` 3)) + (offs `mod` 3))
                     -- random stuff
                     ,(1, pure $ Lit (maxBound :: W256))
                     ]

-- Generates an N-long buffer, all with the same value, at most 8 different ones
genConcreteBufSlot :: Int -> Gen (Expr Buf)
genConcreteBufSlot len = do
  b :: Word8 <- arbitrary
  pure $ ConcreteBuf $ BS.pack ([ 0 | _ <- [0..(len-2)]] ++ [b])

genStorageWrites :: Gen (Expr Storage)
genStorageWrites = do
  toSlot <- genSlot
  val <- genLit (maxBound :: W256)
  store <- frequency [ (3, pure $ AbstractStore (SymAddr "") Nothing)
                     , (2, genStorageWrites)
                     ]
  pure $ SStore toSlot val store

genWordArith :: Int -> Int -> Gen (Expr EWord)
genWordArith litFreq 0 = frequency
  [ (litFreq, fmap Lit arbitrary)
  , (1, oneof [ fmap Lit arbitrary ])
  ]
genWordArith litFreq sz = frequency
  [ (litFreq, fmap Lit arbitrary)
  , (20, frequency
    [ (20, Add <$> subWord <*> subWord)
    , (20, Sub <$> subWord <*> subWord)
    , (20, Mul <$> subWord <*> subWord)
    , (20, SEx <$> subWord <*> subWord)
    , (20, Xor <$> subWord <*> subWord)
    -- these reduce variability
    , (3 , Min  <$> subWord <*> subWord)
    , (3 , Div  <$> subWord <*> subWord)
    , (3 , SDiv <$> subWord <*> subWord)
    , (3 , Mod  <$> subWord <*> subWord)
    , (3 , SMod <$> subWord <*> subWord)
    , (3 , SHL  <$> subWord <*> subWord)
    , (3 , SHR  <$> subWord <*> subWord)
    , (3 , SAR  <$> subWord <*> subWord)
    , (3 , Or   <$> subWord <*> subWord)
    -- comparisons, reducing variability greatly
    , (1 , LEq  <$> subWord <*> subWord)
    , (1 , GEq  <$> subWord <*> subWord)
    , (1 , SLT  <$> subWord <*> subWord)
    , (1 , SGT  <$> subWord <*> subWord)
    , (1 , Eq   <$> subWord <*> subWord)
    , (1 , And  <$> subWord <*> subWord)
    , (1 , IsZero <$> subWord)
    -- Expensive below
    --(1,  liftM3 AddMod subWord subWord subWord
    --(1,  liftM3 MulMod subWord subWord subWord
    --(1,  liftM2 Exp subWord litWord
    ])
  ]
 where
   subWord = genWordArith (litFreq `div` 2) (sz `div` 2)

genEnd :: Int -> Gen (Expr End)
genEnd 0 = oneof
  [ fmap (Failure mempty mempty . UnrecognizedOpcode) arbitrary
  , pure $ Failure mempty mempty IllegalOverflow
  , pure $ Failure mempty mempty SelfDestruction
  ]
genEnd sz = oneof
  [ Failure <$> subProp <*> (pure mempty) <*> (fmap Revert subBuf)
  , Success <$> subProp <*> (pure mempty) <*> subBuf <*> arbitrary
  -- TODO Partial
  ]
  where
    subBuf = defaultBuf (sz `div` 2)
    subProp = genProps False (sz `div` 2)
