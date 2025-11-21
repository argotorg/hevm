# Forge std-test Usage Tutorial
First, install foundry:
```plain
curl -L https://foundry.paradigm.xyz | bash
foundryup
```

Then set up a forge project with `forge init`:
```plain
mkdir myproject
cd myproject
forge init --no-git .
```

Now, let's create a file `src/example-test.sol` with some simple code.
Test cases must be prepended with `prove_` and the testing contract must
inherit from `Test` from [Forge's standard test
library](https://book.getfoundry.sh/forge/forge-std). So let's import Test:
`import {Test} from "forge-std/Test.sol";` and then inherit from it via
` is Test`. This allows hevm to discover the test cases it needs
to run:
```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract Example is Test {
  function prove_mytest() public {
  // (1) environment setup, preconditions
  // (2) calls to test
  // (3) postcondition checks
  }
}
```

Once you have written such a test case, you need to compile with `forge build --ast`
(see [forge documentation](https://book.getfoundry.sh/forge/tests) for more
details) and then:

```plain
$ forge build --ast
$ hevm test --match "prove_mytest"
Checking 1 function(s) in contract src/example-test.sol:Example
[RUNNING] prove_mytest(uint256)
   [PASS] prove_mytest(uint256)
```

Here, hevm discovered the test case, and automatically checked it for
violations. If `hevm` is not in the global path, you can run hevm
from wherever it is installed, and specify the root of the foundry project,
like so:
```plain
./hevm test --root /path/to/foundry/project
```

The `--match ...` options is used to specify which test case(s) to run,
and it accepts a regular expression.

## Setting Up Test Context

Tests usually need to set up the environment in a particular way, such
as contract address, storage, etc. This can be done via Cheat Codes that
can change the address of the caller, set block number, etc. See [Cheat
Codes](#supported-cheat-codes) below for a range of cheat codes supported. Cheat Codes
are a standard method used by other tools, such as
[Foundry](https://book.getfoundry.sh/), so you should be able to re-use your
existing setup. An example setup could be put into `src/setup-test.sol`:
```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";

contract MyVault {
    mapping(address => uint256) public balance;
    function deposit() external payable {
        balance[msg.sender] += msg.value;
    }
}
contract MySetupTest is Test {
    MyVault vault;
    function setUp() public {
        vault = new MyVault();

        address user1 = address(42);
        vm.deal(user1, 7 ether);
        vm.prank(user1);
        vault.deposit{value: 7 ether}();
    }

    function prove_correct(uint8 amt) public {
        address k = address(42);
        uint pre = vault.balance(k);
        assert(pre == 7 ether);
        vm.prank(k);
        vault.deposit{value: amt}();
        assert(vault.balance(k) == pre + amt);
      }
}
```

The `setUp` function is called before each test case, and can be used to
set up the environment. In this case, we create a new vault, and deposit 7
ether into it for address 42: the `vm.deal` function sets the balance of the
user to 7 ether, and the `vm.prank` function sets the caller to address 42. This
should now pass our test:
```plain
$ hevm test
Checking 1 function(s) in contract src/setup-test.sol:MySetupTest
[RUNNING] prove_correct(uint8)
   [PASS] prove_correct
```

In general, the test should check the postconditions, e.g. the state of the
contract after the call(s) are complete. It should also check that
[invariants](https://en.wikipedia.org/wiki/Invariant_(mathematics)) of the
contract, such as total number of tokens, are not violated. You can read more
about testing and cheat codes in the (Foundry
Book)[https://book.getfoundry.sh/forge/cheatcodes] and you can see the
hevm-supported cheat codes [below](#supported-cheat-codes).

## Understanding Counterexamples
When hevm discovers a failure, it prints an example call how to trigger the
failure. Let's write the following simple solidity code to
`src/contract-fail.sol`:
```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract MyContract is Test {
  mapping (address => uint) balances;
  function prove_single_fail(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt > 100) { revert(); }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
}
```

When compiling our foundry project, we must either always pass the `--ast` flag
to `forge build`, or, much better, set the `ast = true` flag in the
`foundry.toml` file:
```toml
ast = true
```

In case neither `--ast` was passed, nor `ast = true` was set in the
`foundry.toml` file, when running hevm, we will get an error such as:
```plain
Error: unable to parse Foundry project JSON: [...]/out/Base.sol/CommonBase.json Contract: "CommonBase"
```

In these cases, issue `forge clean` and run `forge build --ast` again.

Once the project has been correctly built, we can run `hevm test`, and get:
```plain
$ hevm test
Checking 1 function(s) in contract src/contract-fail.sol:MyContract
[RUNNING] prove_single_fail(address,uint256)
   [FAIL] prove_single_fail(address,uint256)
   Counterexample:
     result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
     calldata: prove_single_fail(0x0000000000000000000000000000000000000000,100)
```

Here, hevm provided us with a calldata, where the receiver happens to be the
zero address, and the value sent is exactly 100. This indeed is the boundary
condition where the function call fails. The function should have had a `>=`
rather than a `>` in the `if`. Notice that in this case, while hevm filled in
the `address` to give a complete call, the address itself is irrelevant,
although this is not explicitly mentioned.

## Starting State is Always Concrete
In `test` mode, hevm runs with the starting state set to concrete values, as
dictated by the `setUp()` function explained above. This
means that with the solidity-generated default constructor of contracts, state
variables will be zero (unless set otherwise by `setUp()`),
and arrays and mappings will be empty. If you need a
different starting state, such as e.g. tokens already distributed to some
addresses, you can set that up in the `setUp()` phase of your test.

In case you need a symbolic starting state, see the [Symbolic execution
tutorial](#symbolic-execution-tutorial). Note that if all you need is a
symbolic calldata, then you don't need to run `hevm` in symbolic mode, you can
simply run `hevm test` and hevm will provide you with a symbolic calldata.

## Test Cases that Must Always Revert
Hevm assumes that a test case should not always revert. If you have such a test
case, hevm will warn you and return a FAIL. For example this toy contract:
```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract MyContract is Test {
  uint256 cntr;
  function prove_allrevert(uint256 val) public {
      if(val < 0) {
          unchecked { cntr = val; }
          revert();
      } else revert();
  }
}
```

When compiled with forge and then ran under hevm with `hevm test`, hevm returns:
```plain
Checking 1 function(s) in contract src/contract-allrevert.sol:MyContract
[RUNNING] prove_allrevert(uint256)
   [FAIL] prove_allrevert(uint256)
   Reason:
     No reachable assertion violations, but all branches reverted
     Prefix this testname with `proveFail` if this is expected
```

This is sometimes undesirable. In these cases, prefix your contract with
`proveFail_` instead of `prove_`:
```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract MyContract is Test {
  uint256 cntr;
  function proveFail_allrevert_expected(uint256 val) public {
      if(val < 0) {
          unchecked {
            cntr = val;
            cntr += 1;
          }
          revert();
      }
      else revert();
  }
}
```

When this is compiled with forge and then checked with hevm, it leads to:
```plain
Checking 1 function(s) in contract src/contract-allrevert-expected.sol:MyContract
[RUNNING] proveFail_allrevert_expected(uint256)
   [PASS] proveFail_allrevert_expected(uint256)
```

Which is now the expected outcome.

## Panic Codes
Solidity generates [different panic
codes](https://docs.soliditylang.org/en/latest/control-structures.html#panic-via-assert-and-error-via-require)
for different kinds of issues. The list of panic codes returned by Solidity
are:
- 0x00: Used for generic compiler inserted panics, such as e.g. wrong ABI
  encoding, or if the ABI decoder fails to decode a value.
- 0x01: If you call assert with an argument that evaluates to false.
- 0x11: If an arithmetic operation results in underflow or overflow outside of an unchecked { ... } block.
- 0x12; If you divide or modulo by zero (e.g. 5 / 0 or 23 % 0).
- 0x21: If you convert a value that is too big or negative into an enum type.
- 0x22: If you access a storage byte array that is incorrectly encoded.
- 0x31: If you call .pop() on an empty array.
- 0x32: If you access an array, bytesN or an array slice at an out-of-bounds or negative index (i.e. x[i] where i >= x.length or i < 0).
- 0x41: If you allocate too much memory or create an array that is too large.
- 0x51: If you call a zero-initialized variable of internal function type.

Of these, `hevm test` will only report counterexamples for 0x1, or for custom errors that
developers define, such as:
```solidity
error InsufficientBalance(uint256 requested, uint256 available);
....
uint requested = ...;
uint available = ...;
if (requested > available) {
    revert InsufficientBalance(requested, available);
}
```

Notice that for panic codes, the returned counterexample will produce
a return whose first 4 bytes will be:
```plain
$ cast keccak "Panic(uint256)" | cut -c 1-10
0x4e487b71
```

And if it's a custom error, the first 4 bytes will be:
```plain
$ cast keccak "Error(string)" | cut -c 1-10
0x08c379a0
```

## Supported Cheat Codes
Since hevm is an EVM implementation mainly dedicated to testing and
exploration, it features a set of "cheat codes" which can manipulate the
environment in which the execution is run. These can be accessed by calling
into a contract (typically called `Vm`) at address
`0x7109709ECfa91a80626fF3989D68f67F5b1DD12D`, which happens to be keccak("hevm cheat code"),
implementing the following methods:
| Function | Description |
| --- | --- |
|`function prank(address sender) public`| Sets `msg.sender` to the specified `sender` for the next call.|
|`function startPrank(address sender) public`| Sets `msg.sender` to the specified `sender` until `stopPrank()` is called.|
|`function stopPrank() public`| Resets `msg.sender` to the default sender.|
|`function deal(address usr, uint amt) public`| Sets the eth balance of `usr` to `amt`. Note that if `usr` is a symbolic address, then it must be the address of a contract that has already been deployed. This restriction is in place to ensure soundness of our symbolic address encoding with respect to potential aliasing of symbolic addresses.|
|`function store(address c, bytes32 loc, bytes32 val) public`| Sets the slot `loc` of contract `c` to `val`.|
|`function warp(uint x) public`| Sets the block timestamp to `x`.|
|`function roll(uint x) public`| Sets the block number to `x`.|
|`function assume(bool b) public`| Add the condition `b` to the assumption base for the current branch. This functions almost identically to `require`. For most users, `require` is preferable. However, in case you wish to understand & modify the internal IR of hevm, you may want to use `assume`.|
|`function load(address c, bytes32 loc) public returns (bytes32 val)`| Reads the slot `loc` of contract `c`.|
|`function sign(uint sk, bytes32 digest) public returns (uint8 v, bytes32 r, bytes32 s)`| Signs the `digest` using the private key `sk`. Note that signatures produced via `hevm.sign` will leak the private key.|
|`function addr(uint sk) public returns (address addr)`| Derives an ethereum address from the private key `sk`. Note that `hevm.addr(0)` will fail with `BadCheatCode` as `0` is an invalid ECDSA private key.|
|`function ffi(string[] calldata) external returns (bytes memory)`| Executes the arguments as a command in the system shell and returns stdout. Expects abi encoded values to be returned from the shell or an error will be thrown. Note that this cheatcode means test authors can execute arbitrary code on user machines as part of a call to `dapp test`, for this reason all calls to `ffi` will fail unless the `--ffi` flag is passed.|
|`function createFork(string calldata urlOrAlias) external returns (uint256)`| Creates a new fork with the given endpoint and the _latest_ block and returns the identifier of the fork.|
|`function selectFork(uint256 forkId) external`| Takes a fork identifier created by `createFork` and sets the corresponding forked state as active.|
|`function activeFork() external returns (uint256)`| Returns the identifier of the current fork.|
|`function label(address addr, string calldata label) external`| Labels the address in traces|
