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
