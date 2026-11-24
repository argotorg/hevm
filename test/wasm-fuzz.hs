-- | The fuzzers that need nothing outside hevm, which the wasm build can run too
module Main where

import Test.Tasty
import Test.Tasty.QuickCheck (QuickCheckTests(..))

import EVM.Equivalence.EquivFuzz qualified as EquivFuzz
import EVM.Expr.KeccakFuzz qualified as KeccakFuzz
import EVM.Expr.RewriteFuzz qualified as RewriteFuzz

main :: IO ()
main = defaultMain $ withDefaultTimeout $ testGroup "hevm"
  [ RewriteFuzz.tests
  , KeccakFuzz.tests
  , EquivFuzz.tests
  ]

-- | as in test.hs: 10 minutes per test, more for more QuickCheck tests
withDefaultTimeout :: TestTree -> TestTree
withDefaultTimeout t = askOption $ \(QuickCheckTests n) -> flip adjustOption t $ \case
  NoTimeout -> Timeout (600 * 1000000 * max 1 (toInteger n `div` 100)) "default"
  given -> given
