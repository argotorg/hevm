{-|
Module      : Assembler
Description : Assembler for EVM opcodes used in the HEVM symbolic checker
-}
module EVM.Assembler where

import EVM.Expr qualified as Expr
import EVM.Op
import EVM.Types

import Data.Vector (Vector)
import Data.Vector qualified as V

assemble :: [Op] -> Vector (Expr Byte)
assemble os = V.fromList $ concatMap go os
  where
    go :: Op -> [Expr Byte]
    go = \case
      OpStop -> [LitByte 0x00]
      OpAdd -> [LitByte 0x01]
      OpMul -> [LitByte 0x02]
      OpSub -> [LitByte 0x03]
      OpDiv -> [LitByte 0x04]
      OpSdiv -> [LitByte 0x05]
      OpMod -> [LitByte 0x06]
      OpSmod -> [LitByte 0x07]
      OpAddmod -> [LitByte 0x08]
      OpMulmod -> [LitByte 0x09]
      OpExp -> [LitByte 0x0A]
      OpSignextend -> [LitByte 0x0B]
      OpLt -> [LitByte 0x10]
      OpGt -> [LitByte 0x11]
      OpSlt -> [LitByte 0x12]
      OpSgt -> [LitByte 0x13]
      OpEq -> [LitByte 0x14]
      OpIszero -> [LitByte 0x15]
      OpAnd -> [LitByte 0x16]
      OpOr -> [LitByte 0x17]
      OpXor -> [LitByte 0x18]
      OpNot -> [LitByte 0x19]
      OpByte -> [LitByte 0x1A]
      OpShl -> [LitByte 0x1B]
      OpShr -> [LitByte 0x1C]
      OpSar -> [LitByte 0x1D]
      OpClz -> [LitByte 0x1E]
      OpSha3 -> [LitByte 0x20]
      OpAddress -> [LitByte 0x30]
      OpBalance -> [LitByte 0x31]
      OpOrigin -> [LitByte 0x32]
      OpCaller -> [LitByte 0x33]
      OpCallvalue -> [LitByte 0x34]
      OpCalldataload -> [LitByte 0x35]
      OpCalldatasize -> [LitByte 0x36]
      OpCalldatacopy -> [LitByte 0x37]
      OpCodesize -> [LitByte 0x38]
      OpCodecopy -> [LitByte 0x39]
      OpGasprice -> [LitByte 0x3A]
      OpExtcodesize -> [LitByte 0x3B]
      OpExtcodecopy -> [LitByte 0x3C]
      OpReturndatasize -> [LitByte 0x3D]
      OpReturndatacopy -> [LitByte 0x3E]
      OpExtcodehash -> [LitByte 0x3F]
      OpBlockhash -> [LitByte 0x40]
      OpCoinbase -> [LitByte 0x41]
      OpTimestamp -> [LitByte 0x42]
      OpNumber -> [LitByte 0x43]
      OpPrevRandao -> [LitByte 0x44]
      OpGaslimit -> [LitByte 0x45]
      OpChainid -> [LitByte 0x46]
      OpSelfbalance -> [LitByte 0x47]
      OpBaseFee -> [LitByte 0x48]
      OpBlobhash -> [LitByte 0x49]
      OpBlobBaseFee -> [LitByte 0x4A]
      OpPop -> [LitByte 0x50]
      OpMcopy -> [LitByte 0x5e]
      OpMload -> [LitByte 0x51]
      OpMstore -> [LitByte 0x52]
      OpMstore8 -> [LitByte 0x53]
      OpSload -> [LitByte 0x54]
      OpSstore -> [LitByte 0x55]
      OpTload -> [LitByte 0x5c]
      OpTstore -> [LitByte 0x5d]
      OpJump -> [LitByte 0x56]
      OpJumpi -> [LitByte 0x57]
      OpPc -> [LitByte 0x58]
      OpMsize -> [LitByte 0x59]
      OpGas -> [LitByte 0x5A]
      OpJumpdest -> [LitByte 0x5B]
      OpCreate -> [LitByte 0xF0]
      OpCall -> [LitByte 0xF1]
      OpStaticcall -> [LitByte 0xFA]
      OpCallcode -> [LitByte 0xF2]
      OpReturn -> [LitByte 0xF3]
      OpDelegatecall -> [LitByte 0xF4]
      OpCreate2 -> [LitByte 0xF5]
      OpRevert -> [LitByte 0xFD]
      OpSelfdestruct -> [LitByte 0xFF]
      OpDup n ->
        if 1 <= n && n <= 16
        then [LitByte (0x80 + (n - 1))]
        else internalError $ "invalid argument to OpDup: " <> show n
      OpSwap n ->
        if 1 <= n && n <= 16
        then [LitByte (0x90 + (n - 1))]
        else internalError $ "invalid argument to OpSwap: " <> show n
      OpLog n ->
        if 0 <= n && n <= 4
        then [LitByte (0xA0 + n)]
        else internalError $ "invalid argument to OpLog: " <> show n
      -- we just always assemble OpPush into PUSH32
      OpPush wrd -> (LitByte 0x7f) : [Expr.indexWord (Lit i) wrd | i <- [0..31]]
      OpPush0 -> [LitByte 0x5f]
      OpUnknown o -> [LitByte o]
