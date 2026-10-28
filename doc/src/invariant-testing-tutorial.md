# Invariant Testing Tutorial

An invariant is a property that must hold no matter which functions of a
contract are called, in which order, with which arguments, and by whom. hevm
checks `invariant_` functions of a Forge test contract symbolically: it
explores every sequence of calls up to a given length, with symbolic arguments
and callers, and checks the invariant in every state reached. Unlike fuzzing,
a `[PASS]` means no sequence of calls up to that length breaks the invariant.

## A simple example

The following token has a bug: `burn` lowers the total supply but not the
caller's balance. Save it as `src/Token.sol`:

```solidity
pragma solidity ^0.8.19;

contract Token {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    function mint(uint256 amount) public {
        require(amount <= 10);
        balanceOf[msg.sender] += amount;
        totalSupply += amount;
    }

    function burn(uint256 amount) public {
        require(balanceOf[msg.sender] >= amount);
        totalSupply -= amount;
    }
}
```

The test, in `test/Token.t.sol`, lets one user call the token, and checks that
they never hold more than the total supply:

```solidity
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";
import {Token} from "../src/Token.sol";

contract TokenTest is Test {
    Token token;
    address constant alice = address(0x1000);

    function setUp() public {
        token = new Token();
        targetSender(alice);
    }

    function invariant_supply() public view {
        assertLe(token.balanceOf(alice), token.totalSupply());
    }
}
```

`setUp()` deploys the token, so its non-view functions, `mint` and `burn`, are
the ones hevm calls. Build with `forge build --ast` and run:

```shell
$ hevm test
Checking 1 function(s) in contract test/Token.t.sol:TokenTest
[RUNNING] invariant_supply()
   Counterexample:   [validated]
     calls:    Token.mint(10)
               Token.burn(10)
     calldata: invariant_supply()
     result:   Revert: Error("assertion failed: 10 > 0")
   [FAIL] invariant_supply
```

The counterexample lists the calls that lead to the bad state, then the call
of the invariant that fails in it: after minting and burning 10 tokens, Alice
still holds 10 of a total supply of 0. `[validated]` means hevm replayed the
calls concretely and the invariant indeed failed.

The bug needs two calls. With `--invariant-depth 1` the invariant passes:

```shell
$ hevm test --invariant-depth 1
...
   [PASS] invariant_supply (3 states, up to 1 calls deep)
```

After adding `balanceOf[msg.sender] -= amount;` to `burn`, it passes at the
default depth of 2, too:

```shell
$ hevm test
...
   [PASS] invariant_supply (7 states, up to 2 calls deep)
```

The number of states is how many distinct states hevm reached and checked the
invariant in, including the one after `setUp()`.

## How it works

After `setUp()`, hevm repeatedly calls every target function with symbolic
arguments and caller, up to `--invariant-depth` calls, and checks the invariant
in every state reached. The timestamp may advance between calls. Reverting
calls and already-seen states are not explored further. A failing assertion
inside a call also fails the test. Cost grows quickly with depth.

## Choosing what to call

By default, the target functions are all non-view, non-pure functions of the
contracts deployed in `setUp()`, other than the test contract itself, and they
may be called by any address. The same `forge-std` functions that Foundry uses
change this; call them in `setUp()`:

| Function | Effect |
|---|---|
| `targetContract(addr)` | Call only these contracts |
| `excludeContract(addr)` | Never call these contracts |
| `targetSelector(FuzzSelector)` | Call only these functions of a contract |
| `excludeSelector(FuzzSelector)` | Never call these functions of a contract |
| `targetSender(addr)` | Only these addresses send calls |
| `excludeSender(addr)` | These addresses never send calls |

The test contract itself can be targeted too; its `test`, `prove`, `check`,
`invariant_` and `setUp` functions are then not called. `targetSelector` can
select view functions, and overrides `excludeSelector` for that contract.

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
