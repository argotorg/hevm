# Quick Installation Guide

To fastest way to start using hevm is to install
  [Foundry](https://book.getfoundry.sh/getting-started/installation#using-foundryup),
  e.g. via
```
curl -L https://foundry.paradigm.xyz | bash
```

Next, you need an SMT solver. hevm uses [bitwuzla](https://bitwuzla.github.io/)
by default; [Z3](https://github.com/Z3Prover/z3) and [cvc5](https://cvc5.github.io/)
are also supported, via "--solver z3" and "--solver cvc5". Bitwuzla is available
from many package managers, or as a binary from its [releases
page](https://github.com/bitwuzla/bitwuzla/releases). Z3 and cvc5 can often be
installed via:
```
$ sudo apt-get install z3 cvc5
```

or similar for Linux. For Mac:
```
brew install z3
brew install --cask cvc5
```

Finally, download the static hevm binary from [the GitHub
repository](https://github.com/argotorg/hevm/releases/) for your platform and
put it in your path so it can be executed via typing "hevm".

# How to Check if it Works

Once you have the above, and you have forge installed and a forge-based project
at hand, re-build it with `--ast` and run the tests with hevm:
```
$ forge clean
$ forge build --ast
[⠒] Compiling...
[⠆] Compiling 34 files with 0.8.19
[⠔] Solc 0.8.19 finished in 2.12s
Compiler run successful.
$ hevm test
Checking 1 function(s) in contract src/contract-pass.sol:MyContract
[RUNNING] prove_pass(address,uint256)
   [PASS] prove_pass(address,uint256)
```

See [Forge std-test tutorial](./std-test-tutorial.md) for details.

Note that Foundry provides the solidity compiler, hence there is no need to
install solidity separately.

# WebAssembly Build (Experimental)

hevm builds to WebAssembly (WASI) with the
[ghc-wasm-meta](https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta) GHC 9.12
toolchain, which `wasm/setup-toolchain.sh` installs at a pinned version into
`dist-wasm/toolchain` (or set `$GHC_WASM` to use another). Since wasm cannot start
processes, bitwuzla is compiled to wasm too and linked into hevm:
```
$ wasm/build.sh
$ dist-wasm/toolchain/wasmtime/bin/wasmtime run --dir . dist-wasm/hevm.wasm symbolic --code 0x600035602a14600a57005bfe
```

`wasm/build-solver.sh`, which `wasm/build.sh` runs first, builds GMP, MPFR,
bitwuzla and libff's BN254 curve with the toolchain's wasi-sdk. The build applies
the patches in `wasm/patches` to Haskell dependencies that do not yet build for
32-bit wasm. It has no solver other than bitwuzla, cannot run `solc` or `forge`, and
has no RPC and no debugger server. An error inside bitwuzla aborts hevm, as wasi-sdk
has no C++ exceptions.

`wasm/fuzz.sh` runs hevm's fuzzers that need nothing outside hevm (`eq-fuzz`, the
rewrite and keccak fuzzers) on the wasm build, and `wasm/ethereum-tests.sh` compares
it with a native build on the Ethereum blockchain tests.

`web/` is a website that compiles Solidity with soljson and runs `hevm.wasm` on it in
the browser, showing counterexamples at their place in the source. It can load a
contract verified on [Sourcify](https://sourcify.dev), with all its files and its solc
version, for tests of it to prove. Its Debugger tab is
hevm's interactive debugger on `hevm-web.wasm`, a build of hevm as a wasm reactor, for
replaying a counterexample or stepping through a test symbolically. Its Equivalence tab
checks that two contracts, or one compiled with different solc settings, behave the
same on every call. Each tab's Share button copies a link that opens the tab with its
code and runs it; the code travels in the link itself:
```
$ cd web && npm install && npm run dev
```

`npm test` there runs the TypeScript tests: unit tests, `hevm.wasm` under Node, and,
after `npm run build`, the site in headless Chromium (`$CHROME`, default
`/usr/bin/chromium`).
