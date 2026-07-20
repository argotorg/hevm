# forge-symbolic-tests

This directory vendors the [`grandizzy/symbolic-bug-suite`][suite] Foundry project
as a git submodule and runs hevm against it.

The suite contains 22 minimal reproducers of real-world DeFi exploits.
We check that hevm finds the `[FAIL]` and then validates it via `[validated]`.

## Layout

- `symbolic-bug-suite/` — the vendored submodule (`src/NN_*.sol` reproducers and
  `test/NN_*.t.sol` symbolic invariants).
- The Haskell runner lives at [`../test/ForgeSymbolicTestSuite.hs`](../test/ForgeSymbolicTestSuite.hs)
  and is registered as the `forge-symbolic-tests` cabal test suite.

## Running

```bash
# first time / after a fresh clone: pull the submodule
git submodule update --init --recursive

nix develop -c -- cabal run forge-symbolic-tests
```
