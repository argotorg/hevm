# Invariant Testing Tutorial

An invariant is a property that must hold no matter which functions of a
contract are called, in which order, with which arguments, and by whom. hevm
checks `invariant_` functions of a Forge test contract symbolically: it
explores every sequence of calls up to a given length, with symbolic arguments
and callers, and checks the invariant in every state reached. Unlike fuzzing,
a `[PASS]` means no sequence of calls up to that length breaks the invariant.

## A simple example

The following token has a bug: a transfer to oneself creates tokens, because
the recipient's balance is read before the sender's is lowered. Save it as
`src/Token.sol`:

```solidity
pragma solidity ^0.8.19;

contract Token {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    function mint(uint256 amount) public {
        require(amount <= 100);
        balanceOf[msg.sender] += amount;
        totalSupply += amount;
    }

    function transfer(address to, uint256 amount) public {
        uint256 fromBalance = balanceOf[msg.sender];
        uint256 toBalance = balanceOf[to];
        require(fromBalance >= amount);
        balanceOf[msg.sender] = fromBalance - amount;
        balanceOf[to] = toBalance + amount;
    }
}
```

The test, in `test/Token.t.sol`, lets two users call the token, and checks
that together they never hold more than the total supply:

```solidity
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";
import {Token} from "../src/Token.sol";

contract TokenTest is Test {
    Token token;
    address constant alice = address(0x1000);
    address constant bob = address(0x2000);

    function setUp() public {
        token = new Token();
        targetSender(alice);
        targetSender(bob);
    }

    function invariant_supply() public view {
        assertLe(token.balanceOf(alice) + token.balanceOf(bob), token.totalSupply());
    }
}
```

`setUp()` deploys the token, so its non-view functions, `mint` and `transfer`,
are the ones hevm calls. Build with `forge build --ast` and run:

```shell
$ hevm test
Checking 1 function(s) in contract test/Token.t.sol:TokenTest
[RUNNING] invariant_supply()
   Counterexample:   [validated]
     calls:    Token.mint(93) from 0x0000000000000000000000000000000000002000
               Token.transfer(0x0000000000000000000000000000000000002000,93) from 0x0000000000000000000000000000000000002000
     calldata: invariant_supply()
     result:   Revert: Error("assertion failed: 186 > 93")
   [FAIL] invariant_supply
```

The counterexample lists the calls that lead to the bad state, with their
callers, and then the call of the invariant that fails in it. Bob mints 93
tokens and transfers them to himself, after which he holds 186 tokens of a
total supply of 93. `[validated]` means hevm replayed the calls concretely and
the invariant indeed failed.

The bug needs two calls. With `--invariant-depth 1` the invariant passes:

```shell
$ hevm test --invariant-depth 1
...
   [PASS] invariant_supply (3 states, up to 1 calls deep)
```

After fixing `transfer` to update the recipient's balance with
`balanceOf[to] += amount`, it passes at the default depth of 2, too:

```shell
$ hevm test
...
   [PASS] invariant_supply (7 states, up to 2 calls deep)
```

The number of states is how many distinct states hevm reached and checked the
invariant in, including the one after `setUp()`.

## How it works

hevm first runs `setUp()` concretely. From the state it reaches, it calls each
target function with symbolic arguments and a symbolic caller, and collects
the states at the end of the successful calls. From each of those it calls each
target function again, and so on, up to `--invariant-depth` calls. The
invariant is checked in every state reached, including the one right after
`setUp()`. In more detail:

- Each call has its own symbolic arguments and caller, so a sequence of `n`
  calls covers every choice of arguments and callers for all `n` calls.
- Between calls, the block timestamp may move forward, to any value below
  2^64. The block number does not change.
- A call that reverts reaches no new state. Only calls that can succeed under
  the path conditions so far are continued.
- A state that another sequence of calls already reached is not explored
  again. For example, a function that toggles a flag reaches only two states,
  however deep the exploration goes.
- The end states of a call that differ only in their path conditions, such as
  the two sides of an `if` that did not write to storage differently, are
  merged into one.
- An assertion that fails inside one of the calls fails the test too, even if
  the invariant itself holds. Each target function is reported at most once.
- The states reached are shared by all invariants of a test contract, so
  adding more invariants to the same contract is cheap.

The time and memory needed grow quickly with the depth, as each state may be
continued by a call to any of the target functions. Start with the default
and increase the depth as long as the run stays fast enough.

## Choosing what to call

By default, the target functions are all non-view, non-pure functions of the
contracts deployed in `setUp()`, other than the test contract itself, and they
may be called by any address. The same `forge-std` functions that Foundry uses
change this; call them in `setUp()`:

| Function | Effect |
|---|---|
| `targetContract(addr)` | Call only these contracts. The test contract itself can also be targeted, then its `test`, `prove`, `check`, `invariant_` and `setUp` functions are not called. |
| `excludeContract(addr)` | Do not call these contracts. |
| `targetSelector(FuzzSelector)` | Call only these functions of a contract. Overrides `excludeSelector` for that contract. View functions may be selected explicitly. |
| `excludeSelector(FuzzSelector)` | Do not call these functions of a contract. |
| `targetSender(addr)` | Only these addresses send the calls. |
| `excludeSender(addr)` | These addresses never send the calls. |

For example, to call only `mint` and `transfer` of a token, and never from the
zero address:

```solidity
function setUp() public {
    token = new Token();
    bytes4[] memory selectors = new bytes4[](2);
    selectors[0] = Token.mint.selector;
    selectors[1] = Token.transfer.selector;
    targetSelector(FuzzSelector({addr: address(token), selectors: selectors}));
    excludeSender(address(0));
}
```

Note that without `targetSender`, a caller can be any address, including the
test contract and the contracts deployed in `setUp()`. If a contract trusts
its deployer, exclude it, or list the senders that matter.

A common pattern is a handler contract that wraps the contract under test,
and is the only target. Its functions can bound the arguments, pick actors, or
set up the right preconditions, for example:

```solidity
contract Handler is Test {
    Token token;
    address[] actors;

    constructor(Token t) {
        token = t;
        actors.push(address(0x1000));
        actors.push(address(0x2000));
    }

    function transfer(uint256 from, uint256 to, uint256 amount) public {
        vm.prank(actors[from % actors.length]);
        token.transfer(actors[to % actors.length], amount);
    }
}
```

with `targetContract(address(new Handler(token)))` in `setUp()`.

A minimal proxy ([EIP-1167](https://eips.ethereum.org/EIPS/eip-1167) clone)
deployed in `setUp()` is called with the functions of the contract it
delegates to.

## Options

| Option | Effect |
|---|---|
| `--invariant-depth N` | Check the invariants in every state reached by at most `N` calls. Default: 2. |
| `--match REGEX` | Only check the invariants (and other tests) whose names match. `invariant_` functions are checked regardless of `--prefix`. |
| `--debug` | Also print the target functions, and the number of new states after each number of calls. |

The [common options](./common-options.md) apply to each call. For example,
`--max-iterations` bounds the iterations of each loop in each call separately,
and `--solver-timeout` applies to every query.

## Warnings

When hevm could not explore everything, it prints a warning, and the test
fails instead of passing:

- *some checks of the invariant were inconclusive*: the solver could not decide
  whether the invariant holds in some state, for example because it timed out.
- *the calls before the invariant were only partially explored*: some paths of
  the target functions were cut short, for example by a loop bound or an
  unsupported operation, so some states may have been missed.
- *these functions were not called, their arguments cannot be symbolic*:
  functions with arguments such as dynamic arrays are not called. Wrap them in
  a handler function with arguments hevm supports.

See [Limitations and Workarounds](./limitations-and-workarounds.md) for ways
around these.
