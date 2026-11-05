#!/usr/bin/env bash
# HPC coverage of a fuzz run, listing never-taken source lines. Run inside `nix develop`.
# Usage: test/scripts/fuzz-coverage.sh [PATTERN=/rewrite-fuzz/] [TESTS=20000] [CORES=7] [MODULE=EVM.Expr]
set -euo pipefail
pattern=${1:-/rewrite-fuzz/}
tests=${2:-20000}
cores=${3:-7}
module=${4:-EVM.Expr}
out=tmp/fuzz-coverage

cabal build -j"$(nproc)" -f ci -f devel --enable-coverage --builddir dist-coverage test
bin=$(cabal list-bin -f ci -f devel --enable-coverage --builddir dist-coverage test)
mix=$(echo dist-coverage/build/*/ghc-*/hevm-*/build/extra-compilation-artifacts/hpc/vanilla/mix)
rm -rf "$out" && mkdir -p "$out"

# one capability per instance: with -f devel the binary is -N, and unpinned instances oversubscribe the machine
seq 1 "$cores" | xargs -P"$cores" -I{} sh -c "HPCTIXFILE=$out/{}.tix taskset -c \$(({}-1)) $bin -p '$pattern' \
  --quickcheck-tests $tests --quickcheck-replay {} +RTS -N1 -M3g -RTS > $out/{}.log 2>&1" \
  || { grep -l FAIL "$out"/*.log; exit 1; }

hpc sum --union --output="$out/all.tix" "$out"/[0-9]*.tix
hpc report --hpcdir="$mix" --include="$module" "$out/all.tix"
hpc markup --hpcdir="$mix" --srcdir=. --include="$module" --destdir="$out/html" "$out/all.tix" > /dev/null

# lines holding a never-evaluated expression, or a guard seen only one way
html=$(ls "$out"/html/*/"$module".hs.html)
grep -E 'nottickedoff|tickonly(true|false)' "$html" \
  | sed -E 's/.*class="lineno"> *([0-9]+) <\/span>(.*)/\1:\2/; s/<[^>]*>//g; s/&gt;/>/g; s/&lt;/</g; s/&amp;/\&/g' \
  | grep -E '^[0-9]+:' > "$out/untaken.txt" || true
echo "$(wc -l < "$out/untaken.txt") lines with untaken code: $out/untaken.txt, annotated source: $html"
