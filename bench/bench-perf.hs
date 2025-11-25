{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Control.Monad.State.Strict (liftIO)
import Data.ByteString.UTF8 as BSU 
import Data.Either
import Data.Function
import Data.Maybe
import Data.String.Here
import EVM
import EVM.ABI
import EVM.ConcreteExecution qualified as CE (execBytecode, RuntimeCode(..), ExecutionResult, CallData(..), CallValue(..), VMSnapshot(..))
import EVM.Effects (App, runApp)
import EVM.Fetch qualified as Fetch
import EVM.Solidity
import EVM.Stepper qualified as Stepper
import EVM.Transaction qualified
import EVM.Types
import EVM.UnitTest
import Test.Tasty.Bench
import Control.Monad.ST
import EVM.FeeSchedule (feeSchedule)

-- benchmark hevm using tasty-bench

vmFromRawByteString :: App m => ByteString -> m (VM Concrete)
vmFromRawByteString bs = liftIO $
  bs
    & ConcreteRuntimeCode
    & RuntimeCode
    & initialContract
    & vm0
    & stToIO
    & fmap EVM.Transaction.initTx

vm0 :: Contract -> ST RealWorld (VM Concrete)
vm0 c = makeVm $ vm0Opts c

vm0Opts :: Contract -> VMOpts Concrete
vm0Opts c =
  VMOpts
    { contract = c,
      calldata = (ConcreteBuf "", []),
      value = Lit 0xfffffffffffff, -- balance
      baseState = EmptyBase,
      address = LitAddr 0xacab,
      caller = LitAddr 0,
      origin = LitAddr 0,
      gas = 0xffffffffffffffff,
      baseFee = 0,
      priorityFee = 0,
      gaslimit = 0xffffffffffffffff,
      coinbase = LitAddr 0,
      number = Lit 0,
      timestamp = Lit 0,
      blockGaslimit = 0xffffffffffffffff,
      gasprice = 0,
      maxCodeSize = 0xffffffff,
      prevRandao = 0,
      schedule = feeSchedule,
      chainId = 1,
      create = False,
      txAccessList = mempty, -- TODO: support me soon
      allowFFI = False,
      otherContracts = [],
      freshAddresses = 0,
      beaconRoot = 0
    }

vmOptsToTestVMParams :: VMOpts Concrete -> TestVMParams
vmOptsToTestVMParams v =
  TestVMParams
    { address = v.address,
      caller = v.caller,
      origin = v.origin,
      gasCreate = v.gas,
      gasCall = v.gas,
      baseFee = v.baseFee,
      priorityFee = v.priorityFee,
      balanceCreate = case v.value of
        Lit x -> x
        _ -> 0,
      coinbase = v.coinbase,
      number = case v.number of
        Lit x -> x
        _ -> 0,
      timestamp = case v.timestamp of
        Lit x -> x
        _ -> 0,
      gaslimit = v.gaslimit,
      gasprice = v.gasprice,
      maxCodeSize = v.maxCodeSize,
      prevrandao = v.prevRandao,
      chainId = v.chainId
    }

callMainForBytecode :: App m => ByteString -> m (Either EvmError (Expr 'Buf))
callMainForBytecode bs = do
  vm <- vmFromRawByteString bs
  Stepper.interpret (Fetch.zero 0 Nothing) vm (Stepper.evm (abiCall (vmOptsToTestVMParams (vm0Opts (initialContract (RuntimeCode (ConcreteRuntimeCode bs))))) (Left ("main()", emptyAbi))) >> Stepper.execFully)

callMainForBytecode' :: ByteString -> CE.ExecutionResult
callMainForBytecode' bs = CE.execBytecode code calldata callvalue
  where
    code = CE.RuntimeCode bs
    calldata = CE.CallData $ abiMethod "main()" emptyAbi
    callvalue = CE.CallValue 0

forceExecution :: ByteString -> String
forceExecution bs =
  let (_, snapshot) = callMainForBytecode' bs
  in show snapshot.stack

benchMain :: (String, ByteString) -> Benchmark
benchMain (name, bs) = bench name $ nfIO $ runApp $ (\x -> if isRight x then () else internalError "failed") <$> callMainForBytecode bs

benchMain' :: (String, ByteString) -> Benchmark
benchMain' (name, bs) = bench name $ nf forceExecution bs

mkBench :: (Int -> IO a) -> [Int] -> IO [(String, a)]
mkBench f l = mapM (\n -> (show n,) <$> f n) l

main :: IO ()
main = do
  -- bs <- arrayCreationMem 2
  -- print $ forceExecution bs
  let f (name, prog, limit) = do
        ll <- mkBench prog [2 ^ n | n :: Int <- [1 .. fromMaybe 14 limit]]
        pure $ bgroup name (benchMain' <$> ll)
  let benchmarks = [ ("loop", simpleLoop, Nothing)
                   , ("primes", primes, Nothing)
                   , ("hashes", hashes, Nothing)
                   , ("hashmem", hashmem, Nothing)
                    -- ("balanceTransfer", balanceTransfer, Nothing)
                   , ("funcCall", funcCall, Nothing)
                  --  , ("contractCreation", contractCreation, Nothing)
                  --  , ("contractCreationMem", contractCreationMem, Nothing)
                   , ("arrayCreationMem", arrayCreationMem, Just 9)
                   , ("mapStorage", mapStorage, Nothing)
                   , ("swapOperations", swapOperations, Nothing)
                   ]
  defaultMain =<< mapM f benchmarks
  

-- Loop that adds up n numbers
simpleLoop :: Int -> IO ByteString
simpleLoop n = do
  let src =
        [i|
          contract A {
            function main() public {
              uint256 acc = 0;
              for (uint i = 0; i < ${n}; i++) {
                acc += i;
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Computes prime numbers and stores them up to n
primes :: Int -> IO ByteString
primes n = do
  let src =
        [i|
          contract A {
            mapping (uint => uint) public primes;
            function isPrime (uint n) public returns (bool) {
              if (n == 2) {
                return true;
              }
              if (n % 2 == 0) {
                return false;
              }
              for (uint i = 3; i * i < n; i += 2) {
                if (n % i == 0) {
                  return false;
                }
              }
              return true;
            }
            
            function main() public {
              uint n = 0;
              for (uint i = 0; i < ${n}; i++) {
                if (isPrime(i)) {
                  primes[n++] = i;
                }
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Program that repeatedly hashes a value
hashes :: Int -> IO ByteString
hashes n = do
  let src =
        [i|
          contract A {
            function main() public {
              bytes32 h = 0;
              for (uint i = 0; i < ${n}; i++) {
                h = keccak256(abi.encode(h));
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Program that repeatedly hashes a value and stores it in a map
hashmem :: Int -> IO ByteString
hashmem n = do
  let src =
        [i|
          contract A {
            mapping (uint256 => uint256) public map;
            function main() public {
              uint256 h = 0;
              for (uint i = 0; i < ${n}; i++) {
                uint256 x = h;
                h = uint256(keccak256(abi.encode(h)));
                map[x] = h;
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Transfer ETH to an address n times
balanceTransfer :: Int -> IO ByteString
balanceTransfer n = do
  let src =
        [i|
          contract A {
            function main() public {
              address payable to = payable(address(0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192)); 
              for (uint i = 0; i < ${n}; i++) {
                to.transfer(1);
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Call a public function n times
funcCall :: Int -> IO ByteString
funcCall n = do
  let src =
        [i|
          contract A {
            uint256 public acc;
            function f(uint256 x) public {
              acc += x;
            }
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                f(i);
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Creates n contracts
contractCreation :: Int -> IO ByteString
contractCreation n = do
  let src =
        [i|
          contract B { }
          contract A {
            B public b;
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                b = new B();
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Create n contracts with a string in them
contractCreationMem :: Int -> IO ByteString
contractCreationMem n = do
  let src =
        [i|
          contract B { string m = "the quick brown fox jumps over the lazy dog"; }
          contract A {
            B public b;
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                b = new B();
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Create large array in memory
arrayCreationMem :: Int -> IO ByteString
arrayCreationMem n = do
  let src =
        [i|
          struct C { int24 a; int24 b; uint256 c; uint128 d; }
          contract A {
            function work() public returns (C[] memory ret) {
                ret = new C[](${n});
                for(uint a = 0; a < ${n}; a++) {
                    ret[a] = C({a:1, b:1, c:0xffffffffffffff, d:5});
                }
                return ret;
            }
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                C[] memory ret = work();
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Create large map in storage
mapStorage :: Int -> IO ByteString
mapStorage n = do
  let src =
        [i|
          struct C { uint256 a; uint256 b; }
          contract A {
            mapping(uint256 => mapping(uint256 => C)) m;
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                m[i][${n}-i] = C(i, ${n});
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Do many swaps
swapOperations :: Int -> IO ByteString
swapOperations n = do
  let src =
        [i|
          contract A {
            function main() public pure {
                (uint a0, uint a1, uint a2, uint a3, uint a4, uint a5, uint a6, uint a7, uint a8, uint a9, uint a10, uint a11, uint a12, uint a13, uint a14, uint a15) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
                for (uint i = 0; i < ${n}; i++) {
                    (a0, a15) = (a15, a0);
                    (a1, a14) = (a14, a1);
                    (a2, a13) = (a13, a2);
                    (a3, a12) = (a12, a3);
                    (a4, a11) = (a11, a4);
                    (a5, a10) = (a10, a5);
                    (a6, a9) = (a9, a6);
                    (a7, a8) = (a8, a7);
                }
            }
        }
        |]
  fmap fromJust (runApp $ solcRuntime' "A" src True)
