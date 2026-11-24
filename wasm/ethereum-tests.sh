#!/usr/bin/env bash
# Runs the ethereum-tests fixtures on the wasm build and on a native one, a directory at a time,
# and shows the tests whose results differ. Usage, in nix develop:
#   [JOBS=n] wasm/ethereum-tests.sh "$HEVM_ETHEREUM_TESTS_REPO" "$(cabal list-bin -f ci -f devel ethereum-tests)"
set -euo pipefail

cd "$(dirname "$0")/.."
fixtures=$(realpath "$1")
native=$(realpath "$2")
. "${GHC_WASM:-$PWD/dist-wasm/toolchain}/env"

cabal=(wasm32-wasi-cabal --project-file=cabal.project.wasm --builddir=dist-wasm/build
       --extra-lib-dirs="$PWD/dist-wasm/solver/prefix/lib" --enable-tests)
"${cabal[@]}" build -j"${JOBS:-$(nproc)}" test:ethereum-tests
wasm=$("${cabal[@]}" list-bin test:ethereum-tests)

out=$PWD/dist-wasm/ethereum-tests
rm -rf "$out"
mkdir -p "$out"

# one directory per run: all the fixtures at once do not fit in wasm's 4 GB
units=$(cd "$fixtures" && find . -mindepth 2 -maxdepth 2 -type d ! -path ./static/state_tests;
        cd "$fixtures" && find ./static/state_tests -mindepth 1 -maxdepth 1 -type d)

run() {
  local unit=${1#./} name
  name=$(echo "$unit" | tr / _)
  HEVM_ETHEREUM_TESTS_REPO=$fixtures/$unit "$native" +RTS -N1 -M8g -RTS > "$out/$name.native" 2>&1 || true
  wasmtime run --dir "$fixtures/$unit::/fixtures" --env HEVM_ETHEREUM_TESTS_REPO=/fixtures \
    "$wasm" > "$out/$name.wasm" 2>&1 || true
}
export -f run
export fixtures native wasm out
printf '%s\n' $units | xargs -P"${JOBS:-$(nproc)}" -I{} bash -c 'run {}'

# tasty may print a test's output between its name and FAIL, but names every failure here
failures() { sed -nE "s|.*Use -p '/(.*)/' to rerun this test only.*|\1|p" "$1" | sed 's|\\/|/|g' | sort; }
summary() { grep -E '^(All [0-9]+ tests passed|[0-9]+ out of [0-9]+ tests failed)' "$1" | sed -E 's/ \([0-9.]+s\)//'; }

status=0
for n in "$out"/*.native; do
  w=${n%.native}.wasm
  # some fixtures are in a format the tests skip
  [ "$(summary "$n")" = "All 0 tests passed" ] && continue
  if ! diff -q <(failures "$n") <(failures "$w") > /dev/null || [ -z "$(summary "$w")" ]; then
    status=1
    echo "== $(basename "${n%.native}"): native: $(summary "$n"); wasm: $(summary "$w")"
    diff <(failures "$n") <(failures "$w") | sed -n 's/^> /  only on wasm: /p; s/^< /  only native:  /p' || true
  fi
done
[ $status = 0 ] && echo "the wasm build agrees with the native one on all $(echo "$units" | wc -l) directories"
exit $status
