#!/usr/bin/env bash
# Installs the pinned ghc-wasm-meta toolchain (GHC 9.12, wasi-sdk, cabal, wasmtime, node) into dist-wasm/toolchain.
set -euo pipefail

cd "$(dirname "$0")/.."
# ghc-wasm-meta's autogen.json pins every component of the toolchain
meta_rev=8079eb96bbc63823d99ad8acaff0765532625474
meta=$PWD/dist-wasm/ghc-wasm-meta
prefix=$PWD/dist-wasm/toolchain

if [ "$(cat "$prefix/meta-rev" 2>/dev/null)" = "$meta_rev" ]; then
  echo "toolchain $meta_rev is already in $prefix"
  exit 0
fi

[ -d "$meta" ] || git clone https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta.git "$meta"
git -C "$meta" fetch -q origin
git -C "$meta" checkout -q "$meta_rev"

# setup.sh starts with rm -rf "$PREFIX"
PREFIX="$prefix" FLAVOUR=9.12 "$meta/setup.sh"
echo "$meta_rev" > "$prefix/meta-rev"
