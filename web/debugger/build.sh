#!/bin/sh
# Usage: ./build.sh [test]  -- type-checks and bundles into dist/; with "test", runs the tests instead
set -eu
cd "$(dirname "$0")"
tsc -p tsconfig.json
if [ "${1:-}" = "test" ]; then
  rm -rf .test-dist
  esbuild test/*.test.ts --bundle --platform=node --format=esm --outdir=.test-dist --out-extension:.js=.mjs --log-level=warning --log-override:commonjs-variable-in-esm=silent
  node --test .test-dist/*.test.mjs
else
  esbuild src/main.ts --bundle --format=esm --target=es2022 --legal-comments=none --minify --outfile=dist/debugger.js --log-override:commonjs-variable-in-esm=silent
fi
