{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Files compiled into hevm, e.g. the debugger's web frontend
module EVM.Debugger.Embed (embedFile) where

import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackAddressLen)
import Language.Haskell.TH (Exp(..), Lit(..), Q, runIO)
import Language.Haskell.TH.Syntax (addDependentFile)
import System.IO.Unsafe (unsafePerformIO)

-- | The contents of a file, relative to the package root, as a strict ByteString
embedFile :: FilePath -> Q Exp
embedFile path = do
  addDependentFile path
  bytes <- runIO (BS.readFile path)
  pure $ AppE (VarE 'unsafePerformIO)
       $ AppE (AppE (VarE 'unsafePackAddressLen) (LitE (IntegerL (fromIntegral (BS.length bytes)))))
              (LitE (StringPrimL (BS.unpack bytes)))
