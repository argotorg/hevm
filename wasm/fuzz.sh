#!/usr/bin/env bash
# Runs the wasm-fuzz test suite on the wasm build. Usage: [JOBS=n] wasm/fuzz.sh [tasty args, e.g. -p '/eq-fuzz/']
set -euo pipefail

cd "$(dirname "$0")/.."
wasm_dir=${GHC_WASM:-$PWD/dist-wasm/toolchain}
. "$wasm_dir/env"
[ -f dist-wasm/solver/prefix/lib/libhevm_bitwuzla.a ] || wasm/build-solver.sh

cabal=(wasm32-wasi-cabal --project-file=cabal.project.wasm --builddir=dist-wasm/build
       --extra-lib-dirs="$PWD/dist-wasm/solver/prefix/lib" --enable-tests)
"${cabal[@]}" build -j"${JOBS:-$(nproc)}" test:wasm-fuzz

# these need Z3: bitwuzla does not decide equality over constant arrays
skip='!/keccak-equal-prefix-same-hash/ && !/keccak-differing-input-may-differ/'
exec wasmtime run "$("${cabal[@]}" list-bin test:wasm-fuzz)" -p "$skip" "$@"
