module EVM.Expr.Generator where

import Prelude hiding (LT, GT)

import Control.Monad (foldM, replicateM)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
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
import EVM.Traversals (mapExpr)

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

-- GenDecomposableLoad
-- Loads over chains of writes that storage decomposition must handle: small slots, arrays and
-- mappings mixed, over a concrete or abstract base. Written values can themselves be loads.
-- Array offsets are Lit or Var "i0"/"i1".
newtype GenDecomposableLoad = GenDecomposableLoad (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenDecomposableLoad where
  arbitrary = GenDecomposableLoad <$> frequency
    [ (3, genDecomposableLoad 1)
    , (1, Add <$> genDecomposableLoad 1 <*> genDecomposableLoad 0)
    ]

genDecomposableLoad :: Int -> Gen (Expr EWord)
genDecomposableLoad = genLoadOver genDecomposableKey

genLoadOver :: Gen (Expr EWord) -> Int -> Gen (Expr EWord)
genLoadOver genKey depth = do
  n <- chooseInt (1, 6)
  keys <- vectorOf n genKey
  vals <- vectorOf n $ frequency $
    [ (3, Lit . fromIntegral <$> chooseInt (1, 9))
    , (3, Var <$> elements ["v0", "v1"])
    ] <> [(1, genLoadOver genKey (depth - 1)) | depth > 0]
  baseSlots <- Map.fromList <$> listOf1 ((,) <$> (fromIntegral <$> chooseInt (0, 3)) <*> (fromIntegral <$> chooseInt (1, 9)))
  base <- frequency
    [ (1, pure $ ConcreteStore mempty)
    , (2, pure $ ConcreteStore baseSlots)
    , (2, (`AbstractStore` Nothing) <$> elements [SymAddr "a0", SymAddr "a1"])
    ]
  -- reading a written key, or a slot of the base, makes it likely that the read reaches deep
  key <- oneof $ [genKey, elements keys] <> [elements (Lit <$> Map.keys m) | ConcreteStore m <- [base], not (Map.null m)]
  pure $ SLoad key (foldr (uncurry SStore) base (zip keys vals))

genDecomposableKey :: Gen (Expr EWord)
genDecomposableKey = oneof
  [ Lit . fromIntegral <$> chooseInt (0, 3)
  , Expr.ArraySlotZero <$> slotId 32 (1, 3)
  , Expr.ArraySlotWithOffs <$> slotId 32 (1, 3) <*> oneof [smallLit (1, 3), Var <$> elements ["i0", "i1"]]
  , Expr.ArraySlotWithOffs2 <$> slotId 32 (1, 3) <*> (fromIntegral <$> chooseInt (1, 3)) <*> (Var <$> elements ["i0", "i1"])
  -- decomposition identifies a store by its slot alone, so an array and a mapping must not share one
  , Expr.MappingSlot <$> slotId 64 (4, 5) <*> oneof [smallLit (0, 3), Var <$> elements ["k0", "k1"]]
  -- a mapping access with a concrete key, as it looks once the preimage is folded: key || slot
  , (\key slot -> Keccak (ConcreteBuf (key <> slot))) <$> slotId 32 (0, 3) <*> slotId 32 (4, 5)
  ]
  where
    smallLit range = Lit . fromIntegral <$> chooseInt range

-- GenDecomposableProps
-- Props over decomposable loads. Some contain what decomposition must back off from: a key of an
-- unrecognized shape, an array and a mapping on the same slot, or an equality of whole stores.
newtype GenDecomposableProps = GenDecomposableProps [Prop]
  deriving (Show, Eq)

instance Arbitrary GenDecomposableProps where
  arbitrary = do
    (genKey, genOddProp) <- frequency
      [ (5, pure (genDecomposableKey, pure []))
      , (2, pure (frequency [(10, genDecomposableKey), (1, genOddKey)], frequency [(2, pure []), (1, pure <$> genUndecomposableProp)]))
      , (3, pure (frequency [(4, genDecomposableKey), (1, genClashKey)], pure []))
      ]
    let load = genLoadOver genKey 1
    n <- chooseInt (1, 3)
    props <- vectorOf n $ PEq <$> oneof [Lit . fromIntegral <$> chooseInt (0, 9), Var <$> elements ["r0", "r1"], load] <*> load
    oddProp <- genOddProp
    GenDecomposableProps <$> shuffle (props <> oddProp)

genOddKey :: Gen (Expr EWord)
genOddKey = elements
  [ Var "x"
  , Lit 1000
  -- a mapping at a symbolic slot
  , Keccak (WriteWord (Lit 32) (Var "s") (WriteWord (Lit 0) (Var "k0") (ConcreteBuf (BS.replicate 64 0))))
  -- ids of the wrong length
  , Expr.MappingSlot (BS.replicate 33 0) (Var "k0")
  , Expr.ArraySlotWithOffs (BS.replicate 64 0) (Var "i0")
  ]

-- an array on a slot that the mappings use
genClashKey :: Gen (Expr EWord)
genClashKey = oneof
  [ Expr.ArraySlotZero <$> slotId 32 (4, 5)
  , Expr.ArraySlotWithOffs <$> slotId 32 (4, 5) <*> oneof [Lit . fromIntegral <$> chooseInt (1, 3), Var <$> elements ["i0", "i1", "k0", "k1"]]
  ]

genUndecomposableProp :: Gen Prop
genUndecomposableProp = oneof
  [ pure $ PEq (SStore (Lit 0) (Var "v0") base) base
  -- a concrete base with a slot that is not a small one
  , pure $ PEq (Lit 1) (SLoad (Expr.MappingSlot (slot 64 4) (Var "k0")) (ConcreteStore (Map.singleton 1000 1)))
  ]
  where
    base = AbstractStore (SymAddr "a0") Nothing
    slot len n = BS.pack (replicate (len - 1) 0 ++ [n])

slotId :: Int -> (Int, Int) -> Gen ByteString
slotId len range = do
  slot <- chooseInt range
  pure $ BS.pack (replicate (len - 1) 0 ++ [fromIntegral slot])

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

-- | An arithmetic expression shaped to trigger the abstraction lemmas and the
-- div/mod encoding, together with concrete values for all of its symbolic
-- variables. The generic expression generator almost never produces these
-- related terms. @kind@ is the shape family (or "combined"/"nested"), @parts@
-- the base shapes it was built from, @components@ their expressions.
data AbstractArithCase = AbstractArithCase
  { kind       :: String
  , parts      :: [String]
  , expr       :: Expr EWord
  , components :: [Expr EWord]
  , bindings   :: [(Text, W256)]
  }
  deriving Show

instance Arbitrary AbstractArithCase where
  arbitrary = genAbstractArithCase

genAbstractArithCase :: Gen AbstractArithCase
genAbstractArithCase = do
  AbstractArithCase kind parts e comps bs <- frequency
    [ (6, genBaseArithCase)
    , (2, combinedCase)
    , (2, nestedCase)
    ]
  -- the smart constructors put a literal factor first; the encoder also has to
  -- cope with the other order, which unsimplified input can have
  reorder <- frequency [(3, pure id), (1, pure swapMulOperands)]
  pure $ AbstractArithCase kind parts (reorder e) (fmap reorder comps) bs
  where
    swapMulOperands :: Expr a -> Expr a
    swapMulOperands = mapExpr $ \case
      Mul a b -> Mul b a
      e -> e

    -- sums/differences of several shapes over the same variables, so their
    -- lemmas and saturated terms meet in one query
    combinedCase = do
      first <- genBaseArithCase
      rest <- chooseInt (1, 2) >>= flip vectorOf genBaseArithCase
      combined <- foldM combine first.expr (fmap (.expr) rest)
      bs <- elements (fmap (.bindings) (first : rest))
      pure $ AbstractArithCase "combined" (concatMap (.parts) (first : rest)) combined
        (concatMap (.components) (first : rest)) bs
    combine x y = elements [Expr.add x y, Expr.sub x y, Sub x y]

    -- one shape substituted for a variable of another, e.g. a telescope whose
    -- factor is itself a division
    nestedCase = do
      outer <- genBaseArithCase
      inner <- genBaseArithCase
      name <- elements [arithAName, arithBName, arithCName]
      bs <- elements [outer.bindings, inner.bindings]
      let nested = substVar name inner.expr outer.expr
      pure $ AbstractArithCase "nested" (outer.parts <> inner.parts) nested [inner.expr, nested] bs

genBaseArithCase :: Gen AbstractArithCase
genBaseArithCase = oneof
  [ withBindings "commutativity" (Expr.mul arithA arithB) []
  , identityCase
  , let q = Div arithA arithB
    in withBindings "division-multiplication link" (Expr.add q (Expr.mul q arithB)) []
  , withBindings "multiplication monotonicity"
      (Expr.add (Expr.mul arithA arithC) (Expr.mul arithB arithC)) [nearVar arithBName arithAName]
  , withBindings "dividend monotonicity"
      (Expr.add (Div arithA arithC) (Div arithB arithC)) [nearVar arithBName arithAName]
  , withBindings "divisor monotonicity"
      (Expr.add (Div arithA arithB) (Div arithA arithC)) [nearVar arithCName arithBName]
  , withBindings "product division bound" (Div (Expr.mul arithA arithB) arithC)
      [nearVar arithBName arithCName, nearVar arithAName arithCName]
  , withBindings "divisor reused as factor"
      (Expr.add (Div arithA arithB) (Div (Expr.mul arithB arithC) (Lit 7))) []
  , constMulMonoCase
  , constCancelCase
  , nestedDivCase
  , fracReduceCase
  , ceilDivCase
  , telescopeCase
  , withBindings "signed division and modulo"
      (Expr.add (SDiv arithA arithB) (SMod arithA arithB)) signedEdges
  , withBindings "unsigned modulo" (Mod (Expr.mul arithA arithB) arithC) []
  , shiftDividendCase
  , pow2DividendCase
  , congruenceCase "signed division congruence" SDiv
  , congruenceCase "signed modulo congruence" SMod
  , congruenceCase "unsigned modulo congruence" Mod
  , divisorCongruenceCase "signed division divisor congruence" SDiv
  , divisorCongruenceCase "signed modulo divisor congruence" SMod
  ]
  where
    withBindings shape e adjust = do
      bs <- genArithBindings
      bs' <- foldr (=<<) (pure bs) adjust
      pure $ AbstractArithCase shape [shape] e [e] bs'

    identityCase = do
      identity <- elements [0, 1]
      withBindings "zero/one identity" (Expr.mul arithA arithB)
        [pure . replaceBinding arithBName identity]

    constMulMonoCase = do
      coeff <- genArithConst
      withBindings "constant multiplication monotonicity"
        (Expr.add (Expr.mul (Lit coeff) arithA) (Expr.mul (Lit coeff) arithB))
        [nearOverflow arithAName coeff, nearVar arithBName arithAName]

    constCancelCase = do
      divisor <- genArithConst
      factor <- genSmallFactor
      let coeff = divisor * factor
      withBindings "constant cancellation" (Div (Expr.mul (Lit coeff) arithA) (Lit divisor))
        [nearOverflow arithAName coeff]

    nestedDivCase = do
      divisor1 <- genArithConst
      divisor2 <- genArithConst
      withBindings "nested division"
        (Div (Div (Expr.mul arithA arithB) (Lit divisor1)) (Lit divisor2)) []

    fracReduceCase = do
      coeff <- genArithConst
      factor <- genSmallFactor
      let divisor = coeff * factor
      withBindings "fraction reduction" (Div (Expr.mul (Lit coeff) arithA) (Lit divisor))
        [nearOverflow arithAName coeff]

    ceilDivCase = do
      divisor <- genArithConst
      factor <- genSmallFactor
      let coeff = divisor * factor
      withBindings "ceil-div cancellation"
        (Expr.add (Lit 1) (Div (Sub (Expr.mul (Lit coeff) arithA) (Lit 1)) (Lit divisor)))
        [nearOverflow arithAName coeff, nearValue arithAName 1]

    telescopeCase = do
      divisor <- genArithConst
      factor <- genSmallFactor
      let step = divisor * factor
          full = Div (Expr.mul arithA arithB) (Lit divisor)
          stepped = Div (Expr.mul arithA (Sub arithB (Lit step))) (Lit divisor)
      withBindings "scaled-product telescope" (Sub full stepped) [nearValue arithBName step]

    -- dividend a left shift, divisor around 2^k: the div/mod shift bounds
    shiftDividendCase = do
      -- a shift of 256 or more empties the dividend, and 2^k wraps to zero
      k <- frequency [(6, chooseInteger (0, 16)), (2, chooseInteger (0, 255)), (1, chooseInteger (256, 300))]
      op <- elements [Div, SDiv]
      withBindings "shift-dividend division" (op (SHL (Lit (fromInteger k)) arithA) arithB)
        [nearValue arithBName (2 ^ k)]

    pow2DividendCase = do
      k <- chooseInteger (1, 255)
      m <- genSmallNonZero
      withBindings "power-of-two dividend" (Div (Lit (m * 2 ^ k)) arithA)
        [nearValue arithAName (2 ^ k)]

    -- two ops of one kind whose operands can have equal magnitudes: congruence links
    congruenceCase shape op =
      withBindings shape (Expr.add (op arithA arithB) (op arithC arithB)) $
        (\bs -> do
            sameMagnitude <- elements [id, negate]
            pure $ replaceBinding arithCName (sameMagnitude (lookupBinding arithAName bs)) bs)
        : signedEdges

    -- same, with the divisor negated: the sign of the result then depends on
    -- which operand the op takes it from
    divisorCongruenceCase shape op =
      withBindings shape (Expr.add (op arithA arithB) (op arithA arithC)) $
        (\bs -> do
            sameMagnitude <- elements [id, negate]
            pure $ replaceBinding arithCName (sameMagnitude (lookupBinding arithBName bs)) bs)
        : signedEdges

    -- |2^255| wraps to 2^255, and 2^255 / -1 overflows
    signedEdges = [nearValue arithAName (2 ^ (255 :: Int)), nearValue arithBName maxBound]

arithAName, arithBName, arithCName :: Text
arithAName = T.pack "abstract_arith_a"
arithBName = T.pack "abstract_arith_b"
arithCName = T.pack "abstract_arith_c"

arithA, arithB, arithC :: Expr EWord
arithA = Var arithAName
arithB = Var arithBName
arithC = Var arithCName

genArithBindings :: Gen [(Text, W256)]
genArithBindings = mapM genBinding [arithAName, arithBName, arithCName]
  where
    genBinding name = do
      value <- genArithValue
      pure (name, value)

-- Small values exercise active lemma guards often; boundary values exercise
-- the overflow (2^128), sign (2^255) and zero-divisor guards.
genArithValue :: Gen W256
genArithValue = frequency
  [ (8, fromInteger <$> chooseInteger (0, 0xffff))
  , (2, negate . fromInteger <$> chooseInteger (1, 0xffff))
  , (3, elements [0, 1, 2, 2 ^ (128 :: Int) - 1, 2 ^ (128 :: Int), 2 ^ (128 :: Int) + 1
                 , 2 ^ (255 :: Int) - 1, 2 ^ (255 :: Int), 2 ^ (255 :: Int) + 1, maxBound - 1, maxBound])
  , (1, arbitrary)
  ]

-- Constants for the constant-lemma shapes: small, decimal scaling factors, or
-- near a power of two, so products of two constants can reach 2^256.
genArithConst :: Gen W256
genArithConst = frequency
  [ (6, genSmallNonZero)
  , (2, (10 ^) <$> chooseInteger (1, 27))
  , (1, chooseInteger (1, 255) >>= \k -> elements [2 ^ k - 1, 2 ^ k, 2 ^ k + 1])
  ]

genSmallNonZero :: Gen W256
genSmallNonZero = fromInteger <$> chooseInteger (1, 1000)

genSmallFactor :: Gen W256
genSmallFactor = fromInteger <$> chooseInteger (2, 1000)

-- Usually, move a binding to within one of a guard bound.
nearValue :: Text -> W256 -> [(Text, W256)] -> Gen [(Text, W256)]
nearValue name bound bs = do
  delta <- elements [Nothing, Just (-1), Just 0, Just 1]
  pure $ maybe bs (\d -> replaceBinding name (bound + d) bs) delta

-- Usually, move a binding to where its product with coeff starts to overflow.
-- A product of two constants can wrap to a zero coeff, which never overflows.
nearOverflow :: Text -> W256 -> [(Text, W256)] -> Gen [(Text, W256)]
nearOverflow name coeff
  | coeff == 0 = pure
  | otherwise = nearValue name (maxBound `div` coeff)

-- Usually, move a binding to within one of another binding.
nearVar :: Text -> Text -> [(Text, W256)] -> Gen [(Text, W256)]
nearVar name other bs = nearValue name (lookupBinding other bs) bs

lookupBinding :: Text -> [(Text, W256)] -> W256
lookupBinding name bs = case lookup name bs of
  Just value -> value
  Nothing -> internalError $ "missing arithmetic binding: " <> show name

replaceBinding :: Text -> W256 -> [(Text, W256)] -> [(Text, W256)]
replaceBinding name value = fmap $ \(key, oldValue) ->
  if key == name then (key, value) else (key, oldValue)

substVar :: Text -> Expr EWord -> Expr EWord -> Expr EWord
substVar name replacement = mapExpr go
  where
    go :: Expr a -> Expr a
    go (Var n) | n == name = replacement
    go e = e

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

-- | Subterms with their tree sizes, so that larger terms built from them share subterms
data Pool = Pool
  { pWords  :: [(Int, Expr EWord)]
  , pBufs   :: [(Int, Expr Buf)]
  , pStores :: [(Int, Expr Storage)]
  , pBytes  :: [(Int, Expr Byte)]
  , pAddrs  :: [Expr EAddr]
  }

poolVars :: [Text]
poolVars = ["esc_word_a", "esc_word_b", "esc_word_c"]

-- | Values that an offset, a size or a sum of the two carries past 2^256 (or past the sign bit)
genWrapValue :: Gen W256
genWrapValue = frequency
  [ (6, negate . fromInteger <$> chooseInteger (1, 100))
  , (1, (\d -> negate (Expr.maxBytes + 50 - fromInteger d)) <$> chooseInteger (0, 100))
  -- never just below maxBytes: the simplifier would materialize a buffer of that size
  , (1, (\d -> Expr.maxBytes + fromInteger d) <$> chooseInteger (0, 100))
  , (2, (\d -> 2 ^ (255 :: Int) + 50 - fromInteger d) <$> chooseInteger (0, 100))
  ]

-- | Sharing makes the tree size exponential in the depth, so entries above @cap@ are dropped
genPool :: Int -> Int -> Gen Pool
genPool steps cap = do
  lits <- (<>) <$> vectorOf 2 (fmap Lit arbitrary) <*> vectorOf 3 (Lit <$> genWrapValue)
  keys <- vectorOf 3 genStorageKey
  env <- elements [Origin, Coinbase, Timestamp, BlockNumber, PrevRandao, GasLimit, ChainId, BaseFee, TxValue]
  buf <- ConcreteBuf <$> resize 40 arbitrary
  store <- ConcreteStore . Map.fromList <$> listOf ((,) <$> (fromIntegral <$> chooseInt (0, 20)) <*> arbitrary)
  byte <- LitByte <$> arbitrary
  let leaf x = (1, x)
      seed = Pool
        { pWords = fmap leaf $ [Lit 0, Lit 1, Lit 32, Lit Expr.maxLit, env, Gas "esc_gas" 0, Gas "esc_gas" 1] <> fmap Var poolVars <> lits <> keys
        , pBufs = fmap leaf [ConcreteBuf "", AbstractBuf "esc_buf_a", AbstractBuf "esc_buf_b", buf]
        , pStores = fmap leaf [AbstractStore (SymAddr "esc_addr_a") Nothing, AbstractStore (SymAddr "esc_addr_a") (Just 1), AbstractStore (LitAddr 0x1234) Nothing, store]
        , pBytes = fmap leaf [LitByte 0, LitByte 0xff, byte]
        , pAddrs = [SymAddr "esc_addr_a", SymAddr "esc_addr_b", LitAddr 0x1234]
        }
  foldM (\p _ -> growPool cap p) seed [1 .. steps]

growPool :: Int -> Pool -> Gen Pool
growPool cap p = frequency
  [ (10, (\x -> p { pWords = keep x p.pWords }) <$> word)
  , (3, (\x -> p { pBufs = keep x p.pBufs }) <$> buf)
  , (3, (\x -> p { pStores = keep x p.pStores }) <$> (n3 SStore <$> w <*> w <*> s))
  , (2, (\x -> p { pBytes = keep x p.pBytes }) <$> oneof [n2 IndexWord <$> w <*> w, n2 ReadByte <$> idx <*> b])
  ]
  where
    keep :: (Int, a) -> [(Int, a)] -> [(Int, a)]
    keep x xs = if fst x <= cap then x : xs else xs
    w = elements p.pWords
    b = elements p.pBufs
    s = elements p.pStores
    y = elements p.pBytes
    a = (\x -> (1, x)) <$> elements p.pAddrs
    -- literal offsets are small or wrap around 2^256: the simplifier materializes concrete
    -- buffers up to a literal one
    idx = frequency
      [ (5, (\n -> (1, Lit (fromIntegral n))) <$> chooseInt (0, 100))
      , (3, (\x -> (1, Lit x)) <$> genWrapValue)
      , (2, n2 And (1, Lit 0x3ff) <$> w)
      , (1, n2 Sub <$> w <*> ((\n -> (1, Lit (fromIntegral n))) <$> chooseInt (1, 64)))
      , (1, w)
      ]
    size = frequency
      [ (5, (\n -> (1, Lit (fromIntegral n))) <$> chooseInt (0, 100))
      , (1, (\x -> (1, Lit x)) <$> genWrapValue)
      , (1, w)
      ]
    n1 f (sx, x) = (1 + sx, f x)
    n2 f (sx, x) (sy, x') = (1 + sx + sy, f x x')
    n3 f (sx, x) (sy, x') (sz, x'') = (1 + sx + sy + sz, f x x' x'')
    word = frequency
      [ (12, n2 <$> elements
          [ Add, Sub, Mul, Div, SDiv, Mod, SMod, Exp, SEx, Min, Max, LT, GT, LEq, GEq, SLT, SGT, Eq
          , And, Or, Xor, SHL, SHR, SAR ] <*> w <*> w)
      , (3, n1 <$> elements [IsZero, Not, CLZ] <*> w)
      , (2, n3 <$> elements [AddMod, MulMod, ITE] <*> w <*> w <*> w)
      , (2, n1 Keccak <$> b)
      , (1, n1 BufLength <$> b)
      , (3, n2 ReadWord <$> idx <*> b)
      , (3, n2 SLoad <$> w <*> s)
      , (1, n2 EqByte <$> y <*> y)
      , (1, (\ys -> (1 + sum (fmap fst ys), joinBytesFromList (fmap snd ys))) <$> vectorOf 32 y)
      , (1, oneof [n1 BlockHash <$> w, n1 WAddr <$> a, n1 Balance <$> a, n1 CodeSize <$> a, n1 CodeHash <$> a])
      ]
    buf = oneof
      [ n3 WriteWord <$> idx <*> w <*> b
      , n3 WriteByte <$> idx <*> y <*> b
      , (\(s1, so) (s2, d) (s3, sz) (s4, src) (s5, dst) -> (1 + s1 + s2 + s3 + s4 + s5, CopySlice so d sz src dst))
          <$> idx <*> idx <*> size <*> b <*> b
      ]

genPoolProp :: Pool -> Int -> Gen Prop
genPoolProp p 0 = elements [PEq, PLT, PGT, PLEq, PGEq] <*> w <*> w
  where w = snd <$> elements p.pWords
genPoolProp p depth = oneof
  [ genPoolProp p 0
  , PNeg <$> sub
  , elements [PAnd, POr, PImpl] <*> sub <*> sub
  ]
  where sub = genPoolProp p (depth - 1)

genPoolEnd :: Pool -> Gen (Expr End)
genPoolEnd p = oneof
  [ Failure <$> props <*> pure mempty <*> (Revert <$> b)
  , Success <$> props <*> pure mempty <*> b <*> (Map.fromList <$> resize 2 (listOf ((,) <$> elements p.pAddrs <*> contract)))
  ]
  where
    b = snd <$> elements p.pBufs
    s = snd <$> elements p.pStores
    props = resize 3 (listOf (genPoolProp p 1))
    contract = C <$> code <*> s <*> s <*> (snd <$> elements p.pWords) <*> arbitrary
    code = oneof
      [ UnknownCode <$> elements p.pAddrs
      , InitCode <$> resize 8 arbitrary <*> b
      , RuntimeCode . ConcreteRuntimeCode <$> resize 8 arbitrary
      , RuntimeCode . SymbolicRuntimeCode . V.fromList <$> resize 4 (listOf (snd <$> elements p.pBytes))
      ]

-- | A handful of terms of every type, all cut from one 'Pool' so they overlap heavily
data SharedTerms = SharedTerms
  { words  :: [Expr EWord]
  , bufs   :: [Expr Buf]
  , stores :: [Expr Storage]
  , bytes  :: [Expr Byte]
  , props  :: [Prop]
  , ends   :: [Expr End]
  }

-- the property that fails prints the offending term
instance Show SharedTerms where
  show t = "<SharedTerms: " <> show (length t.words) <> " words>"

instance Arbitrary SharedTerms where
  arbitrary = sized $ \sz -> do
    p <- genPool (10 + sz) 300
    let pick n xs = take n . fmap snd <$> shuffle xs
    SharedTerms
      <$> pick 12 p.pWords
      <*> pick 6 p.pBufs
      <*> pick 6 p.pStores
      <*> pick 6 p.pBytes
      <*> vectorOf 6 (genPoolProp p 2)
      <*> vectorOf 3 (genPoolEnd p)
