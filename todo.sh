#!/bin/sh
# NOTE:
# Had to go into vendored/data-bword and do:
# cabal --with-compiler=wasm32-wasi-ghc --with-hc-pkg=wasm32-wasi-ghc-pkg v2-build --disable-shared --disable-profiling
# cabal --with-compiler=wasm32-wasi-ghc --with-hc-pkg=wasm32-wasi-ghc-pkg v2-build --disable-profiling
#
 # cabal --with-compiler=wasm32-wasi-ghc --with-hc-pkg=wasm32-wasi-ghc-pkg v2-build \
 #  --disable-shared \
 #  --disable-profiling \
 #  --ghc-options="-fPIC -staticlib" \
 #  --ld-options="-static -pthread"





# NOT using #ghc now -- and aiming for -dynamic-too
# compiled bword with: cabal --with-compiler=wasm32-wasi-ghc --with-hc-pkg=wasm32-wasi-ghc-pkg v2-build --disable-profiling
cabal --with-compiler=wasm32-wasi-ghc --with-hc-pkg=wasm32-wasi-ghc-pkg --with-hsc2hs=wasm32-wasi-hsc2hs v2-build --allow-newer=base,ghc-bignum,template-haskell --constraint="hashable>=1.5.0.0" --disable-tests --enable-library-vanilla --disable-library-for-ghci -j1 exe:hevm
