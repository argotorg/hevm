#!/usr/bin/env bash
# Builds hevm.wasm with the toolchain of wasm/setup-toolchain.sh, or the one in $GHC_WASM. Usage: [JOBS=n] wasm/build.sh [cabal build args]
set -euo pipefail

cd "$(dirname "$0")/.."
if [ -z "${GHC_WASM:-}" ]; then
  wasm/setup-toolchain.sh
fi
wasm_dir=${GHC_WASM:-$PWD/dist-wasm/toolchain}
export GHC_WASM=$wasm_dir
. "$wasm_dir/env"

deps=dist-wasm/deps
mkdir -p "$deps"
# a flaky Hackage mirror should not stop a build that already has an index new enough for
# the index-state pinned in cabal.project.wasm
wasm32-wasi-cabal update || echo "warning: cabal update failed, using the existing package index" >&2
for p in wasm/patches/*.patch; do
  pkg=$(basename "$p" .patch)
  if [ ! -d "$deps/$pkg" ]; then
    # the wasm32-wasi-cabal wrapper passes --with-compiler, which get rejects
    CABAL_DIR="$wasm_dir/.cabal" "$wasm_dir/cabal/bin/cabal" get --destdir="$deps" "$pkg"
    patch -d "$deps/$pkg" -p1 < "$p"
  fi
done

[ -f dist-wasm/solver/prefix/lib/libhevm_bitwuzla.a ] && [ -f dist-wasm/solver/prefix/lib/libff.a ] ||
  wasm/build-solver.sh

cabal=(wasm32-wasi-cabal --project-file=cabal.project.wasm --builddir=dist-wasm/build
       --extra-lib-dirs="$PWD/dist-wasm/solver/prefix/lib")
# hevm.wasm, a WASI command, and hevm-web.wasm, a reactor for the website's debugger
for exe in hevm hevm-web; do
  bin=$("${cabal[@]}" list-bin "exe:$exe")
  # cabal does not see changes to the solver libraries: rebuilding the exe component relinks it
  rm -rf "$(dirname "$(dirname "$(dirname "$bin")")")"
  "${cabal[@]}" build -j"${JOBS:-$(nproc)}" "exe:$exe" "$@"
  cp "$bin" "dist-wasm/$exe.wasm"
done
# the JavaScript side of the reactor's JSFFI exports
node "$(wasm32-wasi-ghc --print-libdir)/post-link.mjs" -i dist-wasm/hevm-web.wasm -o dist-wasm/hevm-web.js
echo "built dist-wasm/hevm.wasm, dist-wasm/hevm-web.wasm and dist-wasm/hevm-web.js"
