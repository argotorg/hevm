# wasm backend: Word8 subtraction from a range check reused without narrowing

## Summary

With the wasm32-wasi backend, a `Word8` computed as `x - c + 1` inside a guard that
range-checks `x` comes out as a value above 255. `Swap (x - 0x90 + 1)` with
`x = 0x90` holds a `Word8` that `show` prints as `257`, and `fromIntegral` turns into
the `Int` 257. Native GHC gives 1.

It looks as if the range check `x >= 0x90 && x <= 0x9f` is compiled to an
unsigned comparison of `x - 0x90` (i.e. `x + 0x70`), and that sum is then reused
for the constructor field without being narrowed to 8 bits: `0x90 + 0x70 + 1 = 0x101`.

## Reproducer

```haskell
import Data.Word
import qualified Data.ByteString as BS
import System.Environment

data Op = Dup !Word8 | Swap !Word8 | Other deriving Show

{-# INLINE getOp #-}
getOp :: Word8 -> Op
getOp x | x >= 0x80 && x <= 0x8f = Dup (x - 0x80 + 1)
getOp x | x >= 0x90 && x <= 0x9f = Swap (x - 0x90 + 1)
getOp _ = Other

step :: BS.ByteString -> Int -> [Int] -> Either String [Int]
step code pc stk = case getOp (BS.index code pc) of
  Swap i -> let idx = fromIntegral i in case splitAt idx stk of
    (e0:middle, ei:after) -> Right (ei : middle ++ (e0 : after))
    _ -> Left ("underrun i=" ++ show i ++ " idx=" ++ show idx)
  Dup i -> Right (stk !! (fromIntegral i - 1) : stk)
  Other -> Right stk

main :: IO ()
main = do
  args <- getArgs
  let code = BS.pack (map read args)
  print [step code pc [2, 1] | pc <- [0 .. BS.length code - 1]]
```

```
$ wasm32-wasi-ghc -O1 -package bytestring W8b.hs -o w8b.wasm
$ wasmtime run w8b.wasm 144 145 128 0
[Left "underrun i=257 idx=257",Left "underrun i=258 idx=258",Right [2,2,1],Right [2,1]]
```

Expected, and what native GHC 9.12.3 prints with `-O1`:

```
[Right [1,2],Left "underrun i=2 idx=2",Right [2,2,1],Right [2,1]]
```

## Versions

- Wrong: wasm32-wasi-ghc 9.12.2.20250327 and 9.12.4.20260731 (ghc-wasm-meta
  `8079eb96`, flavour 9.12), at `-O1` and `-O2`; run with wasmtime 34 and 49.
- Right: native x86_64-linux GHC 9.12.3, `-O1`.

Smaller variants did not reproduce it: without `Dup` and `step`, or with the byte
read from a list instead of `BS.index`, the result is correct.

## Workaround

Do the arithmetic in `Int`, e.g. `Swap (fromIntegral (fromIntegral x - 0x90 + 1 :: Int))`.
hevm does this in `EVM.Op.opOffset`.
