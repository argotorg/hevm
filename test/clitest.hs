{-# LANGUAGE QuasiQuotes #-}

module Main where

{-|
Description : CLI tests

This module contains simple CLI test cases to make sure we don't accidentally
break the hevm CLI interface.

-}

import Test.Hspec
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Data.List.Split (splitOn)
import Data.Text qualified as T
import Data.String.Here
import System.IO.Temp
import System.Directory (doesFileExist, removeFile)

import EVM.Solidity
import EVM.Types qualified as Types
import EVM.Effects
import EVM.Test.Utils

testEnv :: Env
testEnv = Env { config = defaultConfig {
  dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , dumpTrace = False
  , decomposeStorage = True
  , verb = 1
  } }

runForge :: FilePath -> [String] -> IO (ExitCode, String, String)
runForge testFile extraOptions = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    let projectType = Foundry
    ret <- runEnv testEnv $ compileWithForge root testFile
    case ret of
      Left e -> do
        putStrLn e
        Types.internalError $ "Error compiling test file " <> show testFile <> " in directory "
          <> show root <> " using project type " <> show projectType
      Right _ -> do
        let options = ["run", "exe:hevm", "--", "test" , "--root", root] <> extraOptions
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" options ""
        pure (exitCode, stdout, stderr)

main :: IO ()
main = do
  hspec $
    describe "CLI" $ do
      it "hevm help works" $ do
        (_, stdout, _) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "--help"] ""
        stdout `shouldContain` "Usage: hevm"
        stdout `shouldContain` "test"
        stdout `shouldContain` "equivalence"
        stdout `shouldContain` "symbolic"
        stdout `shouldContain` "exec"
        stdout `shouldContain` "version"

      it "hevm symbolic tutorial works -- FAIL" $ do
        Just symbBin <- runApp $ solcRuntime (T.pack "MyContract") (T.pack [i|
          contract MyContract {
            function simple_symb() public pure {
              uint i;
              i = 1;
              assert(i == 2);
            }
          }
        |])
        let symbHex = Types.bsToHex symbBin
        (exitCode, stdout, _) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", symbHex] ""
        stdout `shouldContain` "Discovered the following"
        exitCode `shouldBe` ExitFailure 1

        (exitCode2, stdout2, _) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", symbHex, "--sig", "nonexistent()"] ""
        stdout2 `shouldContain` "QED"
        exitCode2 `shouldBe` ExitSuccess

      it "hevm equivalence tutorial works -- FAIL" $ do
        let torun = splitOn " " "equivalence --code-a 60003560000260005260016000f3 --code-b 7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260016000f3"
        (exitCode, stdout, _) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--" ] ++ torun) ""
        stdout `shouldContain` "Not equivalent"
        stdout `shouldContain` "FAIL"
        exitCode `shouldBe` ExitFailure 1

      it "hevm equivalence tutorial works -- PASS" $ do
        Just a <- runApp $ solcRuntime (T.pack "MyContract") (T.pack [i|
          contract MyContract {
            mapping (address => uint) balances;
            function my_adder(address recv, uint amt) public {
              if (balances[recv] + amt >= 100) { revert(); }
              balances[recv] += amt;
            }
          }
        |])
        let aHex = Types.bsToHex a
        Just b <- runApp $ solcRuntime (T.pack "MyContract") (T.pack [i|
          contract MyContract {
            mapping (address => uint) balances;
            function my_adder(address recv, uint amt) public {
              if (balances[recv] + amt >= 100) { revert(); }
              balances[recv] += amt/2;
              balances[recv] += amt/2;
              if (amt % 2 != 0) balances[recv]++;
            }
          }
        |])
        let bHex = Types.bsToHex b
        (exitCode, stdout, _) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--", "equivalence" , "--code-a", aHex, "--code-b", bHex ]) ""
        stdout `shouldContain` "No discrepancies found"
        stdout `shouldContain` "PASS"
        exitCode `shouldBe` ExitSuccess

      it "hevm concrete tutorial works" $ do
        let torun = splitOn " " "exec --code 0x647175696e6550383480393834f3 --gas 0xff"
        (exitCode, stdout, _) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--" ] ++ torun) ""
        stdout `shouldContain` "Return: 0x64"
        exitCode `shouldBe` ExitSuccess

      it "empty solver is always unknown" $ do
        Just c <- runApp $ solcRuntime (T.pack "C") (T.pack [i|
           contract C {
             function myfun(uint a) public returns (uint) {
                 uint ret = 4*a;
                 assert(ret == 4);
                 return ret;
             }
           }
          |])
        let hexStr = Types.bsToHex c
        (_, stdout, _) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--solver", "empty", "--code", hexStr] ""
        stdout `shouldContain` "SMT solver says: Result unknown by SMT solver"
      it "crash-of-hevm" $ do
        let hexStrA = "608060405234801561001057600080fd5b506004361061002b5760003560e01c8063efa2978514610030575b600080fd5b61004361003e3660046102ad565b610045565b005b60006100508561007a565b9050600061005d866100a8565b905080821461006e5761006e61034c565b50505050505050505050565b600061008761032e6103aa565b8261009457610197610098565b61013e5b6100a291906103e2565b92915050565b60006100b561032e6103aa565b6100be906103aa565b6100c7906103aa565b82806100d1575060005b806100da575060005b61013157605a6100ea60006103aa565b6100f3906103aa565b6100ff6001605a610404565b61010b6001605a610404565b61011891166101976103e2565b6101229190610493565b61012c9190610493565b610149565b604061013f8161013e6103e2565b6101499190610493565b61015391906103e2565b61016061032e60006103e2565b83801561016b575060015b15801590610177575060015b80156101a05750831515801561018b575060015b15158015610197575060015b806101a0575060005b610251576101976101b3605a602d610493565b602d60006101c2600182610493565b6101cd906001610404565b6101d8906001610404565b6101e1906103aa565b6101ea906103aa565b6101f491906103e2565b6101ff90605a610404565b604e61020c8160016103e2565b6102169190610493565b61022490600116605a610404565b1661022e906103aa565b61023891906103e2565b6102429190610493565b61024c9190610493565b610283565b604561025f8161013e6103e2565b6102699190610493565b60456102778161013e6103e2565b6102819190610493565b165b61028d91906103e2565b1692915050565b80358015155b81146100a257600080fd5b80358061029a565b600080600080600080600080610100898b0312156102ca57600080fd5b6102d48a8a610294565b97506102e38a60208b01610294565b96506102f28a60408b016102a5565b95506103018a60608b016102a5565b94506103108a60808b01610294565b935061031f8a60a08b016102a5565b925061032e8a60c08b01610294565b915061033d8a60e08b016102a5565b90509295985092959890939650565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052600160045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60007f800000000000000000000000000000000000000000000000000000000000000082036103db576103db61037b565b5060000390565b818103600083128015838313168383129190911617156100a2576100a261037b565b60008261043a577f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b7f800000000000000000000000000000000000000000000000000000000000000082147fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8414161561048e5761048e61037b565b500590565b80820160008212801584831290811690159190911617156100a2576100a261037b56fea26469706673582212200a37769e5bf4b8b890caac8ab643126d55feb821a0201d2f674203f23fa666ad64736f6c634300081e0033"

        (exitCode, _, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", hexStrA] ""
        stderr `shouldNotContain` "CallStack"
        exitCode `shouldBe` ExitSuccess

      -- both should fail with address 0x1234 -- a SPECIFIC address, not a ranomly generated one
      it "keccak-assumptions-setup" $ do
        (exitCode, stdout, stderr) <- runForge "test/contracts/fail/keccak-preimage-setup.sol" []
        stderr `shouldNotContain` "CallStack"
        stdout `shouldContain` "[validated]"
        stdout `shouldContain` "0x0000000000000000000000000000000000001234"
        exitCode `shouldBe` (ExitFailure 1)
      it "keccak-assumptions-constructor" $ do
        (exitCode, stdout, stderr) <- runForge "test/contracts/fail/keccak-preimage-constructor.sol" []
        stderr `shouldNotContain` "CallStack"
        stdout `shouldContain` "[validated]"
        stdout `shouldContain` "0x0000000000000000000000000000000000001234"
        exitCode `shouldBe` (ExitFailure 1)
      it "keccak-wrong-preimage" $ do
        (exitCode, stdout, stderr) <- runForge "test/contracts/fail/keccak-wrong-preimage.sol" []
        stderr `shouldNotContain` "CallStack"
        stdout `shouldContain` "[not reproducible]"
        exitCode `shouldBe` (ExitFailure 1)
      it "only-deployed-contracts" $ do
        (_, stdout, stderr) <- runForge "test/contracts/pass/only-deployed-contracts.sol" ["--only-deployed"]
        stderr `shouldNotContain` "CallStack"
        stdout `shouldContain` "[PASS]"
      it "only-deployed-contracts-force-addr" $ do
        (_, stdout, stderr) <- runForge "test/contracts/pass/only-deployed-force-addr.sol" ["--only-deployed"]
        stderr `shouldNotContain` "CallStack"
        stdout `shouldContain` "[FAIL]"
        stdout `shouldContain` "[validated]"
        stderr `shouldNotContain` "not reproducible"
      it "should-fail" $ do
        (_, stdout, stderr) <- runForge "test/contracts/fail/should-fail.sol" []
        stderr `shouldNotContain` "CallStack"
        stdout `shouldContain` "[FAIL]"
        stdout `shouldContain` "[validated]"
      it "dump unsolved" $ do
        -- >>> (139487132679483*2347234698674) % 982374892374389278894734
        -- 278198683154907855159120
        Just c <- runApp $ solcRuntime (T.pack "C") (T.pack [i|
           contract C {
             function stuff(uint a, uint b) public returns (uint) {
                 uint c = 0;
                 unchecked {
                 c = (a * b) % 982374892374389278894734;
                 }
                 assert (c != 278198683154907855159120);
                 return c;
             }
           }
          |])
        let hexStr = Types.bsToHex c
        _ <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", hexStr, "--smttimeout", "1", "--dump-unsolved", "."] ""
        let filename = "query-unsolved-0.smt2"
        fileExists <- doesFileExist filename
        shouldBe fileExists True
        removeFile filename
      it "early-abort" $ do
        (exitcode, stdout, stderr) <- runForge "test/contracts/pass/early-abort.sol" ["--max-iterations", "1000"]
        putStrLn $ "Exit code: " ++ show exitcode
        putStrLn stderr
        putStrLn stdout
        -- stdout `shouldContain` "[FAIL]"
        -- stdout `shouldContain` "abort"
        -- stderr `shouldNotContain` "CallStack"
      it "rpc-cache" $ do
        (_, stdout, stderr) <- runForge "test/contracts/fail/rpc-test.sol"
          ["--rpc", "http://mock.mock", "--prefix", "test_attack_symbolic"
          , "--number", "10307563", "--cache-dir", "test/contracts/fail/"]
        stdout `shouldContain` "[FAIL]"
        stderr `shouldNotContain` "CallStack"
