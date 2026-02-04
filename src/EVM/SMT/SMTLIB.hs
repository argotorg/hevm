
module EVM.SMT.SMTLIB (
  prelude,
  toText,
  hasDuplicateCommands
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder

import EVM.SMT.Types

prelude :: SMT2
prelude =  SMT2 src mempty mempty
  where
  src = SMTScript $ header <> types <> macros
  header = fmap SMTCommand [
    "(set-info :smt-lib-version 2.6)",
    "(set-logic ALL)",
    "(set-info :source |\n Generator: hevm\n Application: hevm symbolic execution system\n |)",
    "(set-info :category \"industrial\")"
    ]
  types = (SMTComment "types") : (fmap SMTCommand [
    "(define-sort Byte () (_ BitVec 8))",
    "(define-sort Word () (_ BitVec 256))",
    "(define-sort Addr () (_ BitVec 160))",
    "(define-sort Buf () (Array Word Byte))"
    ]) <> [(SMTComment "slot -> value"), SMTCommand "(define-sort Storage () (Array Word Word))"]
    <> (fmap SMTCommand [
        "(declare-fun keccak (Buf Word) Word)",
        "(declare-fun sha256 (Buf Word) Word)"
    ])
  macros = fmap SMTCommand [
    "(define-fun max ((a (_ BitVec 256)) (b (_ BitVec 256))) (_ BitVec 256) (ite (bvult a b) b a))",
    "(define-fun indexWord31 ((w Word)) Byte ((_ extract 7 0) w))",
    "(define-fun indexWord30 ((w Word)) Byte ((_ extract 15 8) w))",
    "(define-fun indexWord29 ((w Word)) Byte ((_ extract 23 16) w))",
    "(define-fun indexWord28 ((w Word)) Byte ((_ extract 31 24) w))",
    "(define-fun indexWord27 ((w Word)) Byte ((_ extract 39 32) w))",
    "(define-fun indexWord26 ((w Word)) Byte ((_ extract 47 40) w))",
    "(define-fun indexWord25 ((w Word)) Byte ((_ extract 55 48) w))",
    "(define-fun indexWord24 ((w Word)) Byte ((_ extract 63 56) w))",
    "(define-fun indexWord23 ((w Word)) Byte ((_ extract 71 64) w))",
    "(define-fun indexWord22 ((w Word)) Byte ((_ extract 79 72) w))",
    "(define-fun indexWord21 ((w Word)) Byte ((_ extract 87 80) w))",
    "(define-fun indexWord20 ((w Word)) Byte ((_ extract 95 88) w))",
    "(define-fun indexWord19 ((w Word)) Byte ((_ extract 103 96) w))",
    "(define-fun indexWord18 ((w Word)) Byte ((_ extract 111 104) w))",
    "(define-fun indexWord17 ((w Word)) Byte ((_ extract 119 112) w))",
    "(define-fun indexWord16 ((w Word)) Byte ((_ extract 127 120) w))",
    "(define-fun indexWord15 ((w Word)) Byte ((_ extract 135 128) w))",
    "(define-fun indexWord14 ((w Word)) Byte ((_ extract 143 136) w))",
    "(define-fun indexWord13 ((w Word)) Byte ((_ extract 151 144) w))",
    "(define-fun indexWord12 ((w Word)) Byte ((_ extract 159 152) w))",
    "(define-fun indexWord11 ((w Word)) Byte ((_ extract 167 160) w))",
    "(define-fun indexWord10 ((w Word)) Byte ((_ extract 175 168) w))",
    "(define-fun indexWord9 ((w Word)) Byte ((_ extract 183 176) w))",
    "(define-fun indexWord8 ((w Word)) Byte ((_ extract 191 184) w))",
    "(define-fun indexWord7 ((w Word)) Byte ((_ extract 199 192) w))",
    "(define-fun indexWord6 ((w Word)) Byte ((_ extract 207 200) w))",
    "(define-fun indexWord5 ((w Word)) Byte ((_ extract 215 208) w))",
    "(define-fun indexWord4 ((w Word)) Byte ((_ extract 223 216) w))",
    "(define-fun indexWord3 ((w Word)) Byte ((_ extract 231 224) w))",
    "(define-fun indexWord2 ((w Word)) Byte ((_ extract 239 232) w))",
    "(define-fun indexWord1 ((w Word)) Byte ((_ extract 247 240) w))",
    "(define-fun indexWord0 ((w Word)) Byte ((_ extract 255 248) w))",
    "(define-fun indexWord ((idx Word) (w Word)) Byte\
      \(ite (bvuge idx (_ bv32 256)) (_ bv0 8)\
      \(ite (= idx (_ bv31 256)) (indexWord31 w)\
      \(ite (= idx (_ bv30 256)) (indexWord30 w)\
      \(ite (= idx (_ bv29 256)) (indexWord29 w)\
      \(ite (= idx (_ bv28 256)) (indexWord28 w)\
      \(ite (= idx (_ bv27 256)) (indexWord27 w)\
      \(ite (= idx (_ bv26 256)) (indexWord26 w)\
      \(ite (= idx (_ bv25 256)) (indexWord25 w)\
      \(ite (= idx (_ bv24 256)) (indexWord24 w)\
      \(ite (= idx (_ bv23 256)) (indexWord23 w)\
      \(ite (= idx (_ bv22 256)) (indexWord22 w)\
      \(ite (= idx (_ bv21 256)) (indexWord21 w)\
      \(ite (= idx (_ bv20 256)) (indexWord20 w)\
      \(ite (= idx (_ bv19 256)) (indexWord19 w)\
      \(ite (= idx (_ bv18 256)) (indexWord18 w)\
      \(ite (= idx (_ bv17 256)) (indexWord17 w)\
      \(ite (= idx (_ bv16 256)) (indexWord16 w)\
      \(ite (= idx (_ bv15 256)) (indexWord15 w)\
      \(ite (= idx (_ bv14 256)) (indexWord14 w)\
      \(ite (= idx (_ bv13 256)) (indexWord13 w)\
      \(ite (= idx (_ bv12 256)) (indexWord12 w)\
      \(ite (= idx (_ bv11 256)) (indexWord11 w)\
      \(ite (= idx (_ bv10 256)) (indexWord10 w)\
      \(ite (= idx (_ bv9 256)) (indexWord9 w)\
      \(ite (= idx (_ bv8 256)) (indexWord8 w)\
      \(ite (= idx (_ bv7 256)) (indexWord7 w)\
      \(ite (= idx (_ bv6 256)) (indexWord6 w)\
      \(ite (= idx (_ bv5 256)) (indexWord5 w)\
      \(ite (= idx (_ bv4 256)) (indexWord4 w)\
      \(ite (= idx (_ bv3 256)) (indexWord3 w)\
      \(ite (= idx (_ bv2 256)) (indexWord2 w)\
      \(ite (= idx (_ bv1 256)) (indexWord1 w)\
      \(indexWord0 w)\
      \)))))))))))))))))))))))))))))))))",
    "(define-fun readWord ((idx Word) (buf Buf)) Word\
      \(concat (select buf idx)\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018))\
      \(concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d))\
      \(concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e))\
      \(select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f)\
      \)))))))))))))))))))))))))))))))))",
    "(define-fun writeWord ((idx Word) (val Word) (buf Buf)) Buf\
      \(store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store\
      \(store (store (store (store (store (store (store (store (store (store (store (store (store (store (store buf\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f) (indexWord31 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e) (indexWord30 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d) (indexWord29 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c) (indexWord28 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b) (indexWord27 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a) (indexWord26 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019) (indexWord25 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018) (indexWord24 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017) (indexWord23 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016) (indexWord22 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015) (indexWord21 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014) (indexWord20 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013) (indexWord19 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012) (indexWord18 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011) (indexWord17 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010) (indexWord16 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f) (indexWord15 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e) (indexWord14 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d) (indexWord13 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c) (indexWord12 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b) (indexWord11 val))\
      \(bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a) (indexWord10 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009) (indexWord9 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008) (indexWord8 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007) (indexWord7 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006) (indexWord6 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005) (indexWord5 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004) (indexWord4 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003) (indexWord3 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002) (indexWord2 val))\
      \(bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001) (indexWord1 val))\
      \idx (indexWord0 val)))",
    "(declare-fun blockhash (Word) Word)",
    "(declare-fun codesize (Addr) Word)",
    "(define-fun signext ( (b Word) (val Word)) Word\
      \(ite (= b (_ bv0  256)) ((_ sign_extend 248) ((_ extract 7    0) val))\
      \(ite (= b (_ bv1  256)) ((_ sign_extend 240) ((_ extract 15   0) val))\
      \(ite (= b (_ bv2  256)) ((_ sign_extend 232) ((_ extract 23   0) val))\
      \(ite (= b (_ bv3  256)) ((_ sign_extend 224) ((_ extract 31   0) val))\
      \(ite (= b (_ bv4  256)) ((_ sign_extend 216) ((_ extract 39   0) val))\
      \(ite (= b (_ bv5  256)) ((_ sign_extend 208) ((_ extract 47   0) val))\
      \(ite (= b (_ bv6  256)) ((_ sign_extend 200) ((_ extract 55   0) val))\
      \(ite (= b (_ bv7  256)) ((_ sign_extend 192) ((_ extract 63   0) val))\
      \(ite (= b (_ bv8  256)) ((_ sign_extend 184) ((_ extract 71   0) val))\
      \(ite (= b (_ bv9  256)) ((_ sign_extend 176) ((_ extract 79   0) val))\
      \(ite (= b (_ bv10 256)) ((_ sign_extend 168) ((_ extract 87   0) val))\
      \(ite (= b (_ bv11 256)) ((_ sign_extend 160) ((_ extract 95   0) val))\
      \(ite (= b (_ bv12 256)) ((_ sign_extend 152) ((_ extract 103  0) val))\
      \(ite (= b (_ bv13 256)) ((_ sign_extend 144) ((_ extract 111  0) val))\
      \(ite (= b (_ bv14 256)) ((_ sign_extend 136) ((_ extract 119  0) val))\
      \(ite (= b (_ bv15 256)) ((_ sign_extend 128) ((_ extract 127  0) val))\
      \(ite (= b (_ bv16 256)) ((_ sign_extend 120) ((_ extract 135  0) val))\
      \(ite (= b (_ bv17 256)) ((_ sign_extend 112) ((_ extract 143  0) val))\
      \(ite (= b (_ bv18 256)) ((_ sign_extend 104) ((_ extract 151  0) val))\
      \(ite (= b (_ bv19 256)) ((_ sign_extend 96 ) ((_ extract 159  0) val))\
      \(ite (= b (_ bv20 256)) ((_ sign_extend 88 ) ((_ extract 167  0) val))\
      \(ite (= b (_ bv21 256)) ((_ sign_extend 80 ) ((_ extract 175  0) val))\
      \(ite (= b (_ bv22 256)) ((_ sign_extend 72 ) ((_ extract 183  0) val))\
      \(ite (= b (_ bv23 256)) ((_ sign_extend 64 ) ((_ extract 191  0) val))\
      \(ite (= b (_ bv24 256)) ((_ sign_extend 56 ) ((_ extract 199  0) val))\
      \(ite (= b (_ bv25 256)) ((_ sign_extend 48 ) ((_ extract 207  0) val))\
      \(ite (= b (_ bv26 256)) ((_ sign_extend 40 ) ((_ extract 215  0) val))\
      \(ite (= b (_ bv27 256)) ((_ sign_extend 32 ) ((_ extract 223  0) val))\
      \(ite (= b (_ bv28 256)) ((_ sign_extend 24 ) ((_ extract 231  0) val))\
      \(ite (= b (_ bv29 256)) ((_ sign_extend 16 ) ((_ extract 239  0) val))\
      \(ite (= b (_ bv30 256)) ((_ sign_extend 8  ) ((_ extract 247  0) val)) val)\
      \)))))))))))))))))))))))))))))))",
    "(define-fun clz256 ((x (_ BitVec 256))) (_ BitVec 256)\
      \(let ((x128 (ite (bvuge x     #x0000000000000000000000000000000100000000000000000000000000000000)\
      \                (bvlshr x        (_ bv128 256)) x))\
      \      (n128 (ite (bvuge x     #x0000000000000000000000000000000100000000000000000000000000000000)\
      \                (_ bv0 256) (_ bv128 256))))\
      \(let ((x64  (ite (bvuge x128  #x0000000000000000000000000000000000000000000000010000000000000000)\
      \                (bvlshr x128     (_ bv64 256)) x128))\
      \      (n64  (ite (bvuge x128  #x0000000000000000000000000000000000000000000000010000000000000000)\
      \               n128  (bvadd n128 (_ bv64 256)))))\
      \(let ((x32  (ite (bvuge x64   #x0000000000000000000000000000000000000000000000000000000100000000)\
      \                (bvlshr x64      (_ bv32 256)) x64))\
      \      (n32  (ite (bvuge x64   #x0000000000000000000000000000000000000000000000000000000100000000)\
      \               n64   (bvadd n64  (_ bv32 256)))))\
      \(let ((x16  (ite (bvuge x32   #x0000000000000000000000000000000000000000000000000000000000010000)\
      \                (bvlshr x32      (_ bv16 256)) x32))\
      \      (n16  (ite (bvuge x32   #x0000000000000000000000000000000000000000000000000000000000010000)\
      \               n32   (bvadd n32  (_ bv16 256)))))\
      \(let ((x8   (ite (bvuge x16   #x0000000000000000000000000000000000000000000000000000000000000100)\
      \                (bvlshr x16      (_ bv8 256)) x16))\
      \      (n8   (ite (bvuge x16   #x0000000000000000000000000000000000000000000000000000000000000100)\
      \               n16   (bvadd n16  (_ bv8 256)))))\
      \(let ((x4   (ite (bvuge x8    #x0000000000000000000000000000000000000000000000000000000000000010)\
      \                (bvlshr x8       (_ bv4 256)) x8))\
      \      (n4   (ite (bvuge x8    #x0000000000000000000000000000000000000000000000000000000000000010)\
      \               n8    (bvadd n8   (_ bv4 256)))))\
      \(let ((x2   (ite (bvuge x4    #x0000000000000000000000000000000000000000000000000000000000000004)\
      \                (bvlshr x4       (_ bv2 256)) x4))\
      \      (n2   (ite (bvuge x4    #x0000000000000000000000000000000000000000000000000000000000000004)\
      \               n4    (bvadd n4   (_ bv2 256)))))\
      \(let ((x1   (ite (bvuge x2    #x0000000000000000000000000000000000000000000000000000000000000002)\
      \                (bvlshr x2       (_ bv1 256)) x2))\
      \      (n1   (ite (bvuge x2    #x0000000000000000000000000000000000000000000000000000000000000002)\
      \               n2    (bvadd n2   (_ bv1 256)))))\
      \(ite           (bvuge x1 (_ bv1 256))\
      \               n1    (bvadd n1   (_ bv1 256)))\
      \)))))))))"
   ]


toText :: SMTEntry -> Text
toText (SMTCommand b) = toLazyText b
toText (SMTComment b) = "; " <> toLazyText b

hasDuplicateCommands :: SMTScript -> Bool
hasDuplicateCommands (SMTScript entries) = length cmdTexts /= length (nubOrd cmdTexts)
  where
    cmdTexts = [toText c | c@(SMTCommand _) <- entries]
