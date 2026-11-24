#!/usr/bin/env bash
# Builds hevm.wasm with ghc-wasm-meta's GHC 9.12 toolchain. Usage: wasm/build.sh [cabal build args]
set -euo pipefail

cd "$(dirname "$0")/.."
wasm_dir=${GHC_WASM:-$HOME/.ghc-wasm}
. "$wasm_dir/env"

deps=dist-wasm/deps
mkdir -p "$deps"
wasm32-wasi-cabal update
for p in wasm/patches/*.patch; do
  pkg=$(basename "$p" .patch)
  if [ ! -d "$deps/$pkg" ]; then
    # the wasm32-wasi-cabal wrapper passes --with-compiler, which get rejects
    CABAL_DIR="$wasm_dir/.cabal" "$wasm_dir/cabal/bin/cabal" get --destdir="$deps" "$pkg"
    patch -d "$deps/$pkg" -p1 < "$p"
  fi
done

wasm32-wasi-cabal --project-file=cabal.project.wasm --builddir=dist-wasm/build build -j"$(nproc)" exe:hevm "$@"
cp "$(wasm32-wasi-cabal --project-file=cabal.project.wasm --builddir=dist-wasm/build list-bin exe:hevm)" dist-wasm/hevm.wasm
echo "built dist-wasm/hevm.wasm"
