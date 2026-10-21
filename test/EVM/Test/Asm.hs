-- | Test programs written as opcodes
module EVM.Test.Asm (AsmOp(..), asm, offsets) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Vector qualified as V
import Data.Word (Word8)

import EVM.Assembler (assemble)
import EVM.Types

data AsmOp = I Op | Target Int

-- | Assembles the ops, with @Target n@ pushing the offset of the n-th JUMPDEST
asm :: [AsmOp] -> ByteString
asm ops = BS.pack . map byte . V.toList . assemble $ map resolve ops
  where
    resolve (I op) = op
    resolve (Target n) = OpPush (Lit (fromIntegral (jumpdests !! n)))
    jumpdests = [o | (I OpJumpdest, o) <- zip ops (offsets ops)]
    byte :: Expr Byte -> Word8
    byte (LitByte b) = b
    byte b = internalError $ "symbolic byte: " <> show b

-- | Where each op starts in the assembled code
offsets :: [AsmOp] -> [Int]
offsets ops = scanl (+) 0 (map size ops)
  where
    -- OpPush always assembles to PUSH32
    size :: AsmOp -> Int
    size = \case I (OpPush _) -> 33; Target _ -> 33; _ -> 1
