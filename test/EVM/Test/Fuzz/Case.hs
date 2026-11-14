{-|
Module      : EVM.Test.Fuzz.Case
Description : Reporting and reproducing failing fuzz cases

A failure prints the case as @HEVM_FUZZ_*@ variables, which the @*-from-env@
tests read back. @HEVM_FUZZ_CASE_FILE@ records the case each property is
running, to find one that crashes or hangs.
-}
module EVM.Test.Fuzz.Case
  ( caseFromEnv, failWith, modeOf, reproduction, splitOn', writeCaseFile
  ) where

import Data.ByteString.Char8 qualified as Char8
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, fromMaybe)
import System.Environment (lookupEnv)
import Test.Tasty.HUnit (assertFailure)
import EVM.Format (hexByteString)
import EVM.Types hiding (Env)
import EVM.Debugger (BranchMode(..))
import EVM.Test.Fuzz.Program

failWith :: TestCase -> Inputs -> String -> IO a
failWith c i msg = assertFailure $ msg
  <> "\ninputs: " <> show i
  <> "\nmain: " <> bsToHex (assembleItems c.prog.main)
  <> "\ncallee: " <> bsToHex (assembleItems c.prog.callee)
  <> "\nreproduce with: " <> reproduction c i

-- | Environment variables that 'caseFromEnv' reads back
reproduction :: TestCase -> Inputs -> String
reproduction c i = unwords
  [ "HEVM_FUZZ_MAIN=" <> hex (assembleItems c.prog.main), "HEVM_FUZZ_CALLEE=" <> hex (assembleItems c.prog.callee)
  , "HEVM_FUZZ_CALLDATA=" <> hex i.calldata, "HEVM_FUZZ_CALLVALUE=" <> show i.callvalue
  , "HEVM_FUZZ_TIMESTAMP=" <> show i.timestamp, "HEVM_FUZZ_STORE=" <> intercalate "," [ show k <> ":" <> show v | (k, v) <- Map.toList i.store ]
  , "HEVM_FUZZ_GASLIMIT=" <> show c.gasLimit, "HEVM_FUZZ_NUMBER=" <> show c.number ]
  where hex = bsToHex

-- | Records the case a property runs in HEVM_FUZZ_CASE_FILE, suffixed with the
-- property's name as properties run concurrently, to find one that crashes or hangs
writeCaseFile :: String -> String -> IO ()
writeCaseFile name content = lookupEnv "HEVM_FUZZ_CASE_FILE" >>= mapM_ (\f -> writeFile (f <> "." <> name) content)

splitOn' :: Char -> String -> [String]
splitOn' d str = case break (== d) str of
  (a, []) -> [a]
  (a, _ : rest) -> a : splitOn' d rest

modeOf :: String -> BranchMode
modeOf = \case
  "ExplorerBranches" -> ExplorerBranches
  "CheckedBranches" -> CheckedBranches
  _ -> SolverBranches

-- | The case 'reproduction' describes, if HEVM_FUZZ_MAIN is set
caseFromEnv :: IO (Maybe TestCase)
caseFromEnv = lookupEnv "HEVM_FUZZ_MAIN" >>= \case
  Nothing -> pure Nothing
  Just m -> do
    let var k d = fromMaybe d <$> lookupEnv ("HEVM_FUZZ_" <> k)
        bytes = fromJust . hexByteString . Char8.pack
        w256 :: String -> W256
        w256 = fromInteger . read
    callee <- var "CALLEE" ""
    cd <- var "CALLDATA" ""
    cv <- var "CALLVALUE" "0"
    ts <- var "TIMESTAMP" "1"
    st <- var "STORE" ""
    gl <- var "GASLIMIT" "300000"
    n <- var "NUMBER" "1"
    let store = Map.fromList [ (w256 k, w256 (drop 1 v)) | kv <- splitOn' ',' st, not (null kv), let (k, v) = break (== ':') kv ]
    pure $ Just $ TestCase (Prog [IRaw (bytes m)] [IRaw (bytes callee)]) (Inputs (bytes cd) store (w256 cv) (w256 ts)) (read gl) (w256 n)
