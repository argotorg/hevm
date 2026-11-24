-- | bitwuzla linked into the wasm build (wasm/bitwuzla/hevm_bitwuzla.cpp), which cannot
-- start solver processes
module EVM.Solvers.Bitwuzla (new) where

import Control.Exception (throwIO)
import Control.Monad (unless)
import Data.ByteString qualified as BS
import Data.IORef
import Data.Text qualified as TS
import Data.Text.Encoding qualified as TE
import Data.Text.Lazy qualified as T
import Foreign.C
import Foreign.Marshal.Alloc (alloca)
import Foreign.Marshal.Array (withArrayLen)
import Foreign.Marshal.Utils (withMany)
import Foreign.Ptr
import Foreign.Storable (peek)

data Instance

foreign import ccall unsafe "hevm_bitwuzla_new"
  c_new :: Ptr CString -> CSize -> IO (Ptr Instance)
foreign import ccall unsafe "hevm_bitwuzla_delete"
  c_delete :: Ptr Instance -> IO ()
foreign import ccall unsafe "hevm_bitwuzla_command"
  c_command :: Ptr Instance -> CString -> CSize -> IO ()
foreign import ccall unsafe "hevm_bitwuzla_output"
  c_output :: Ptr Instance -> Ptr CSize -> IO CString

-- | A bitwuzla with the given command line options, as functions that send it a line of
-- SMT-LIB, read a line of its output, and stop it
new :: [TS.Text] -> IO (T.Text -> IO (), IO T.Text, IO ())
new args = do
  p <- withMany (withCString . TS.unpack) args $ \cargs ->
    withArrayLen cargs $ \n arr -> c_new arr (fromIntegral n)
  pending <- newIORef []
  stopped <- newIORef False
  let send line = do
        BS.useAsCStringLen (TE.encodeUtf8 (T.toStrict line)) $ \(s, n) ->
          c_command p s (fromIntegral n)
        out <- alloca $ \lenPtr -> do
          s <- c_output p lenPtr
          n <- peek lenPtr
          BS.packCStringLen (s, fromIntegral n)
        modifyIORef' pending (<> T.lines (T.fromStrict (TE.decodeLatin1 out)))
      recvLine = do
        next <- atomicModifyIORef' pending $ \case
          [] -> ([], Nothing)
          l : ls -> (ls, Just l)
        maybe (throwIO (userError "bitwuzla printed nothing")) pure next
      stop = do
        done <- atomicModifyIORef' stopped (True,)
        unless done (c_delete p)
  pure (send, recvLine, stop)
