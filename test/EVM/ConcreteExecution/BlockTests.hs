{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module EVM.ConcreteExecution.BlockTests (tests) where

import Control.Monad (foldM, forM_, when)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (evalStateT, execStateT, runStateT)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Data.Vector.Unboxed qualified as U
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase)
import Witch (unsafeInto)

import EVM (defaultVMOpts, exec1, initialContract, makeVm, readMemory)
import EVM.Concrete.Blocks (newProgramCache, newScratch, prepareProgram, runConcreteBlocks)
import EVM.Effects (defaultConfig)
import EVM.Exec (exec, vmForEthrunCreation)
import EVM.Types qualified as EVM

tests :: TestTree
tests = testGroup "Concrete stack blocks"
  [ testCase "stack, gas, PC and visits agree with individual hevm steps" $ do
      base <- stToIO (vmForEthrunCreation BS.empty) :: IO (EVM.VM EVM.Concrete)
      scratch <- newScratch
      cache <- newProgramCache
      let straightLine = [0x60,0xa5,0x80,0x90,0x01,0x50,0x5b,0x00] -- PUSH, DUP, SWAP, ADD, POP
          programs =
            [ straightLine
            , [0x5b,0x60,0,0x56]                        -- backward jump until out of gas
            , [0x60,0x5b,0x60,1,0x56]                    -- jump into PUSH data
            , [0x60,0,0x60,0xff,0x57,0x5b,0]             -- false condition, invalid destination
            , [0x9f,0x8f,0x03,0x15,0x19,0x1b,0]
            , [0x62,0x11,0x22]                           -- truncated immediate
            , replicate 65 0x5f ++ replicate 65 0x50 ++ [0]
            ]
          single op = [op,0]
          oneStep = stToIO . execStateT (exec1 defaultConfig)
          observe v = (v.state.pc, v.state.gas, v.burned, v.state.stack)
      forM_ (programs ++ map single ([1,3,0x33,0x34,0x35,0x36,0x3d,0x5a] ++ [0x10..0x19] ++ [0x80..0x9f])) $ \ops -> do
        let code = EVM.RuntimeCode (EVM.ConcreteRuntimeCode (BS.pack ops))
        plan <- prepareProgram cache code
        forM_ [0,1,2,17,1023,1024] $ \depth -> forM_ [0,2,3,7,141] $ \gas -> do
          let stack = take depth (cycle [EVM.Lit 3,EVM.Lit (2^(255::Int)),EVM.Lit 0])
              frame = base.state { EVM.code = code, EVM.stack = stack, EVM.gas = gas
                                 , EVM.calldata = EVM.ConcreteBuf (BS.pack [1..36])
                                 , EVM.returndata = EVM.ConcreteBuf (BS.pack [1..12])
                                 , EVM.callvalue = EVM.Lit 19 }
              contracts = Map.insert frame.codeContract (initialContract code) base.env.contracts
              start :: EVM.VM EVM.Concrete
              start = base { EVM.state = frame, EVM.env = base.env { EVM.contracts = contracts } }
              visit pc seen = pure (pc:seen)
              visitMany pcs seen = foldM (flip visit) seen (U.toList pcs)
          (got, reversePCs) <- runConcreteBlocks scratch plan visit visitMany start []
          expected <- foldM (\vm pc -> assertEqual "covered PC" vm.state.pc pc >> oneStep vm)
                            start (reverse reversePCs)
          assertEqual (show (ops,depth,gas)) (observe expected) (observe got)
          when (ops == straightLine && depth == 0 && gas == 141) $
            assertEqual "full affordable block" [0,2,3,4,5,6] (reverse reversePCs)
  , testCase "literal calldata offsets include partially padded and very large reads" $ do
      base <- stToIO (vmForEthrunCreation BS.empty) :: IO (EVM.VM EVM.Concrete)
      scratch <- newScratch
      cache <- newProgramCache
      let code = EVM.RuntimeCode (EVM.ConcreteRuntimeCode (BS.pack [0x35,0]))
      plan <- prepareProgram cache code
      forM_ [BS.empty, BS.pack [1..63]] $ \bytes ->
        forM_ [0,1,31,32,62,63,64,maxBound-1,maxBound] $ \offset -> do
          let start :: EVM.VM EVM.Concrete
              start = base { EVM.state = base.state { EVM.code = code, EVM.gas = 10
                           , EVM.stack = [EVM.Lit offset], EVM.calldata = EVM.ConcreteBuf bytes } }
          (actual,seen) <- runConcreteBlocks scratch plan (\pc _ -> pure [pc]) (\_ xs -> pure xs) start []
          reference <- stToIO (execStateT (exec1 defaultConfig) start)
          assertEqual "executed calldata load" [0] seen
          assertEqual "calldata word" reference.state.stack actual.state.stack
          assertEqual "calldata gas" reference.state.gas actual.state.gas
  , testCase "word loads and stores match hevm on independent memory slices" $ do
      vm <- stToIO (vmForEthrunCreation BS.empty) :: IO (EVM.VM EVM.Concrete)
      scratch <- newScratch
      cache <- newProgramCache
      let value = 2^(255::Int) + 2^(150::Int) + 2^(65::Int) + 0x1234
      forM_ [[0x51,0], [0x52,0], [0x52,0x51,0]] $ \ops -> do
        let code = EVM.RuntimeCode (EVM.ConcreteRuntimeCode (BS.pack ops))
        plan <- prepareProgram cache code
        forM_ [0,1,8,32,65,96,97,maxBound] $ \offset ->
          forM_ [(0,1000),(32,5),(128,3),(128,2)] $ \(size,gas) ->
            forM_ [0,1] $ \shift -> do
              let fresh = do
                    backing <- VS.thaw (VS.fromList (take (128 + shift) (iterate (+ 101) 0)))
                    let frame = vm.state { EVM.code = code, EVM.gas = gas, EVM.memorySize = size
                                         , EVM.stack = map EVM.Lit [offset,value,offset]
                                         , EVM.memory = EVM.ConcreteMemory (VSM.slice shift 128 backing) }
                    pure (vm { EVM.state = frame } :: EVM.VM EVM.Concrete)
                  observe x = case x.state.memory of
                    EVM.ConcreteMemory mem -> do
                      bytes <- VS.freeze mem
                      pure (x.state.pc, x.state.gas, x.burned, x.state.stack, x.state.memorySize, bytes)
                    _ -> fail "expected concrete memory"
                  visit pc seen = pure (pc:seen)
              start <- fresh
              reference <- fresh
              (got, pcs) <- runConcreteBlocks scratch plan visit (\v xs -> foldM (flip visit) xs (U.toList v)) start []
              expected <- foldM (\before pc -> do
                assertEqual "word access PC" before.state.pc pc
                stToIO (execStateT (exec1 defaultConfig) before)) reference (reverse pcs)
              wanted <- observe expected
              actual <- observe got
              assertEqual (show (ops,offset,size,gas,shift)) wanted actual
              when (offset == 0 && size == 128 && gas >= 3) $
                assertBool "covered direct memory access" (0 `elem` pcs)
  , testCase "native offsets reject words outside the signed index range" $ do
      let largest = maxBound :: Int
          lastIndex = unsafeInto largest :: EVM.W256
      assertEqual "zero" (Just 0) (EVM.toIntOffset 0)
      assertEqual "last index" (Just largest) (EVM.toIntOffset lastIndex)
      assertEqual "sign bit" Nothing (EVM.toIntOffset (lastIndex + 1))
      assertEqual "high limb" Nothing (EVM.toIntOffset (2 ^ (64 :: Int)))
  , testCase "concrete memory reads return immutable snapshots of sliced backing" $ do
      vm <- stToIO (vmForEthrunCreation BS.empty) :: IO (EVM.VM EVM.Concrete)
      backing <- VS.thaw (VS.fromList [10,20,30,40])
      let mem = VSM.slice 1 2 backing
          start = vm { EVM.state = vm.state { EVM.memory = EVM.ConcreteMemory mem } }
                  :: EVM.VM EVM.Concrete
          readAt offset len = stToIO (evalStateT (readMemory (EVM.Lit offset) (EVM.Lit len)) start)
      snapshot <- readAt 0 2
      VSM.write mem 1 99
      assertEqual "original bytes" (EVM.ConcreteBuf (BS.pack [20,30])) snapshot
      assertEqual "extends past backing" (EVM.ConcreteBuf (BS.pack [99,0])) =<< readAt 1 2
      assertEqual "wide offset" (EVM.ConcreteBuf (BS.singleton 0)) =<< readAt (2^(64::Int)) 1
  , testCase "literal MSTORE preserves sparse bytes across frame growth" $ do
      vm <- stToIO (vmForEthrunCreation BS.empty) :: IO (EVM.VM EVM.Concrete)
      let code = EVM.RuntimeCode (EVM.ConcreteRuntimeCode (BS.singleton 0x52))
          writes = [(1, maxBound), (480, 42), (511, 256), (8190, 0xfedcba), (2, 17)]
          size = 8224
          write before (off, value) = do
            let frame = before.state { EVM.code = code, EVM.pc = 0, EVM.stack = [EVM.Lit (unsafeInto off),EVM.Lit value] }
            stToIO (execStateT (exec1 defaultConfig) (before { EVM.state = frame } :: EVM.VM EVM.Concrete))
          expected bytes (off, value) = BS.take off bytes <> EVM.word256Bytes value <> BS.drop (off+32) bytes
          start = vm { EVM.state = vm.state { EVM.gas = 1000000 } } :: EVM.VM EVM.Concrete
      result <- foldM write start writes
      assertEqual "logical size" (unsafeInto size) result.state.memorySize
      actual <- stToIO (evalStateT (readMemory (EVM.Lit 0) (EVM.Lit (unsafeInto size))) result)
      assertEqual "contents including unwritten gaps" (EVM.ConcreteBuf (foldl expected (BS.replicate size 0) writes)) actual
  , testCase "a plan for other runtime bytecode falls back" $ do
      vm <- stToIO (vmForEthrunCreation BS.empty) :: IO (EVM.VM EVM.Concrete)
      scratch <- newScratch
      cache <- newProgramCache
      let code ops = EVM.RuntimeCode (EVM.ConcreteRuntimeCode (BS.pack ops))
          start :: EVM.VM EVM.Concrete
          start = vm { EVM.state = vm.state { EVM.code = code [0x5f,0] } }
      plan <- prepareProgram cache (code [0x60,1,0])
      (_,visited) <- runConcreteBlocks scratch plan (\_ _ -> pure True) (\_ _ -> pure True) start False
      assertBool "stale plan bypassed" (not visited)
  , testCase "exec pauses for a query between blocks and resumes with the supplied balance" $ do
      -- BALANCE(0xcafe) + 2, returned as a 32-byte word.
      let code = EVM.RuntimeCode . EVM.ConcreteRuntimeCode . BS.pack
          ops = [0x61,0xca,0xfe,0x31,0x60,2,0x01,0x5f,0x52,0x60,32,0x5f,0xf3]
          account = (initialContract (code [])) { EVM.balance = EVM.Lit 40 } :: EVM.Contract
      start <- stToIO (makeVm defaultVMOpts { EVM.contract = initialContract (code ops) })
               :: IO (EVM.VM EVM.Concrete)
      (pending, paused) <- stToIO (runStateT (exec defaultConfig) start)
      case pending of
        EVM.HandleEffect (EVM.Query (EVM.PleaseFetchContract addr _ supply)) -> do
          assertEqual "account requested" 0xcafe addr
          result <- stToIO (evalStateT (supply account >> exec defaultConfig) paused)
          case result of
            EVM.VMSuccess buf -> assertEqual "returned word" (EVM.ConcreteBuf (EVM.word256Bytes 42)) buf
            other -> assertFailure (show other)
        other -> assertFailure (show other)
  ]
