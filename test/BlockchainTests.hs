module Main where

import Test.Tasty
import EVM.Effects
import EVM.Test.BlockchainTestsAlt qualified as BlockchainTests

testEnv :: Env
testEnv = Env { config = defaultConfig }

main :: IO ()
main = do
  tests <- runEnv testEnv BlockchainTests.prepareTests
  defaultMain tests
