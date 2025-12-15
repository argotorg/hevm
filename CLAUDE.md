# Environment

Beware, we are in a NIX environment. Likely, sanboxing is NOT going to work.


# Compilation
You MUST compile with:

cabal --with-compiler=wasm32-wasi-ghc --with-hc-pkg=wasm32-wasi-ghc-pkg --with-hsc2hs=wasm32-wasi-hsc2hs v2-build --allow-newer=base,ghc-bignum,template-haskell --constraint="hashable>=1.5.0.0" --disable-tests --enable-library-vanilla --disable-library-for-ghci -j1 exe:hevm

