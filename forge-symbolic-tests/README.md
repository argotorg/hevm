# forge-symbolic-tests

This directory vendors the [`grandizzy/symbolic-bug-suite`][suite] Foundry project
as a git submodule and runs hevm against it.

The suite contains 22 minimal reproducers of real-world DeFi exploits.
We check that hevm finds the `[FAIL]` and then validates it via `[validated]`.

## Layout

- `symbolic-bug-suite/` — the vendored submodule (`src/NN_*.sol` reproducers and
  `test/NN_*.t.sol` symbolic invariants).
- The Haskell runner lives at [`../test/SymbolicTestSuite.hs`](../test/SymbolicTestSuite.hs)
  and is registered as the `symbolic-test` cabal test suite.

## Running

```bash
# first time / after a fresh clone: pull the submodule
git submodule update --init --recursive

nix develop -c -- cabal run symbolic-test
```
