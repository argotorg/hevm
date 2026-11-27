{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module EVM.ConcreteExecution.BlockTests (tests) where

import Control.Monad (foldM, forM_, when)
import Control.Monad.ST (stToIO)
import Control.Monad.State.Strict (evalStateT, execStateT)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Vector.Unboxed qualified as U
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)
import Witch (unsafeInto)

import EVM (exec1, initialContract, readMemory)
import EVM.Concrete.Blocks (newProgramCache, newScratch, prepareProgram, runConcreteBlocks)
import EVM.Effects (defaultConfig)
import EVM.Exec (vmForEthrunCreation)
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
  ]
