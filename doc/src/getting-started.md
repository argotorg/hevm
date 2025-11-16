# Getting Started

The hevm project is an implementation of the Ethereum Virtual Machine (EVM)
focused on symbolic analysis of EVM bytecode. This essentially means that hevm
can try out _all_ execution possibilities of your contract and see it can
somehow violate some assertions you have. These assertions can be e.g. the
total number of tokens must always be X, some value must never be
greater than Y, some value must never overflow, etc.

In some sense, hevm is similar to a fuzzer, but instead of only trying with random
values to trigger faults, it instead _computes_ whether a fault is possible. If
it is possible, it gives an example call to trigger the fault, and if it isn't
possible, it mathematically proves it so, and tells the user the contract is
safe. Note that while great pains have gone into making sure hevm's results can
be trusted, there can always be bugs in hevm or the libraries and tools it uses.

Hevm can not only be used to find bugs in programs, but can also help to make
sure that two programs behave equivalently from the outside. This may be
advantageous when one may be more efficient (use less gas) to execute, but
harder to reason about. This can be done via (equivalence
checking)[#equivalence-checking] where hevm either proves that the behaviour of
the two bytecodes is the same, or gives inputs where they differ.

## Practical Scenario

Let's say we have a function that allows transfer of money, but no balance can
be larger than or equal to 100. Let's see the contract and its associated check:

```solidity
pragma solidity ^0.8.19;
import "forge-std/Test.sol";

contract MyContract is Test {
  mapping (address => uint) balances;
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt > 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
}
```

Notice that this function has a bug: the `require` and the `assert` both check
for `<`, but the `if` checks for `>`, which should instead be `>=`. Let's see
if `hevm` can find this bug. In order to do that, we have to prepend the
function name with `prove_`, which we did.

### Building

We now need a copy of hevm (see
[releases](https://github.com/argotorg/hevm/releases)) and the SMT solver z3,
which can be installed e.g. with `apt-get` on ubuntu/debian or `homebrew` on Mac,
and a copy of [Foundry](https://getfoundry.sh/):

```shell
$ sudo apt-get install z3  # install z3
$ curl -L https://foundry.paradigm.xyz | bash # install foundryup
$ foundryup # install forge and other foundry binaries
$ mkdir mytest && cd mytest
$ wget https://github.com/argotorg/hevm/releases/download/release/0.55.1/hevm-x86_64-linux
$ chmod +x ./hevm-x86_64-linux
$ forge init .
$ cat <<EOF > src/contract.sol
pragma solidity ^0.8.19;
import "forge-std/Test.sol";

contract MyContract is Test {
  mapping (address => uint) balances;
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt > 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
}
EOF
$ forge build --ast
[⠊] Compiling...
[⠒] Compiling 1 files with 0.8.19
[⠢] Solc 0.8.19 finished in 14.27ms
Compiler run successful!
```

### Finding the Bug

Now let's run `hevm` to see if it finds the bug:

```shell
$ hevm test --solver z3
Running 1 tests for src/contract.sol:MyContract
[FAIL] prove_add_value(address,uint256)
  Counterexample:
    result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
    calldata: prove_add_value(0x0000000000000000000000000000000000000000,100)
```

### Fixing the Bug
This counterexample tells us that when sending exactly 100 to an empty account, the new
balance will violate the `< 100` assumption. Let's fix this bug, the new `prove_add_value`
should now say:

```solidity
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt >= 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
```

Let's re-build with forge and check with hevm once again:

```shell
$ forge build --ast
[⠰] Compiling...
[⠔] Compiling 1 files with 0.8.19
[⠒] Solc 0.8.19 finished in 985.32ms
Compiler run successful!

$ hevm test --solver z3
Running 1 tests for src/contract.sol:MyContract
[PASS] prove_add_value(address,uint256)
```

We now get a `PASS`. Notice that this doesn't only mean that hevm couldn't find
a bug within a given time frame. Instead, it means that there is surely no call
to `prove_add_value` such that our assertion can be violated. However, it *does
not* check for things that it was not asked to check for. In particular, it
does not check that e.g. the sender's balance is decremented. There is no such
test and so this omission is not detected.

## Capabilities

- Symbolic execution of solidity tests written using
    [`ds-test`](https://github.com/dapphub/ds-test/) (a.k.a "foundry tests").
    This allows one to find _all_ potential failure modes of a function.
- Fetch remote state via RPC so your tests can be rooted in the real-world,
    calling out to other, existing contracts, with existing state and already
    deployed bytecode.
- Prove equivalence of two different bytecode objects such as two functions or
    even entire contracts.

## History
Hevm was originally developed as part of the
[dapptools](https://github.com/dapphub/dapptools/) project, and was forked to
this repo by the Formal Verification team at the Ethereum Foundation in August 2022.
