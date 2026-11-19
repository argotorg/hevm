# `hevm test`

```plain
Usage: hevm test [--root STRING] [--project-type PROJECTTYPE] [--rpc TEXT]
                 [--number W256] [--verb INT] [--match STRING]
                 [--solver TEXT] [--num-solvers NATURAL] ...

```

Execute all unit tests that make use of the `std-test` assertion library
a.k.a [Foundry tests](https://book.getfoundry.sh/forge/forge-std) on functions that
start with `prove_`, and [invariants](#invariant-tests). This command supports both Foundry- and
[Dapptools-](https://dapp.tools/)based projects. For a full listing of options,
see `hevm test --help`. For common options, see [here](./common-options.md).

## Simple example usage

If you are inside a forge project that has already been built via `forge build
--ast`, you can:

```shell
$ hevm test
Checking 1 function(s) in contract src/badvault-test.sol:BadVault
[RUNNING] prove_mytest(uint256)
   [PASS] prove_mytest(uint256)
```

To prove all function that start with `prove_` in all contracts.

## Invariant tests

Functions that start with `invariant_` are invariants: hevm checks them after
`setUp()`, and after every sequence of at most `--invariant-depth` (default: 2)
calls to the target functions, with symbolic arguments and callers. Between
calls, the block timestamp may move forward. The target functions are the
non-view functions of the contracts deployed in `setUp()`, other than the test
contract. As in Foundry, `targetContract`, `excludeContract`, `targetSelector`
and `excludeSelector` change them, and `targetSender` and `excludeSender` the
callers. A minimal proxy (EIP-1167 clone) gets the functions of the contract it
delegates to. A state that another sequence of calls already reached is not
explored again. An assertion that fails in one of the calls fails the test too.

```solidity
contract Counter {
    uint256 public count;
    function incr(uint256 x) public {
        require(x <= count);
        count += 1;
    }
}

contract CounterTest is Test {
    Counter c;
    function setUp() public {
        c = new Counter();
    }
    function invariant_below_two() public view {
        assertLt(c.count(), 2);
    }
}
```

```shell
$ hevm test --match invariant_below_two
Checking 1 function(s) in contract test/Counter.t.sol:CounterTest
[RUNNING] invariant_below_two()
   Counterexample:   [validated]
     calls:    Counter.incr(0)
               Counter.incr(0)
     calldata: invariant_below_two()
     result:   Revert: Error("assertion failed: 2 >= 2")
   [FAIL] invariant_below_two
```

Functions with arguments that cannot be symbolic, such as dynamic arrays, are
not called, and hevm warns about them.

## Further reading

See our
[tutorial here](std-test-tutorial.html) for more details. An overview of using
`std-test` for solidity testing can be found in the [foundry
book](https://book.getfoundry.sh/forge/tests).
