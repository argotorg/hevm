# When to use Symbolic Execution

In the cryptocurrency world, it is exceedingly easy to lose a [lot of
assets](https://chainsec.io/defi-hacks/) due to bugs. While fuzz testing can
help find potential issues with digital contracts, it is a tool that can only
execute the program concretely, one execution at a time. In contrast, Symbolic
Execution can execute all potential values in a decision path "in one go",
creating a symbolic expression out of a path, and checking whether it
can trigger a fault. Hence, Symbolic Execution tends to be more efficient at
finding bugs than fuzzing when the bugs are rare, or explicitly (i.e.
maliciously) hidden. Symbolic Execution can also _prove_ that no postcondition
can be violated, increasing the overall confidence in the contract. Note, however,
that Symbolic Execution does not automatically generate postconditions for
well-known bug classes like static code analysis tools do. Instead, these
postconditions, and their sometimes associated preconditions, need to
be explicitly written.

## Fuzzing versus Symbolic Execution

Fuzzing tests usually have a set of (sometimes implicit) pre- and
postconditions, but the actual action (e.g. function call) is performed by an
external entity, the fuzzer. For C/C++ fuzzing, the implicit postcondition is
often e.g. that the system does not throw a segmentation fault. For EVM
bytecode, postconditions need to be explicit. Let's see an example:

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import "forge-std/Test.sol";

contract MyContract is Test {
  uint balance;
  function test_overflow(uint amt) public {
    unchecked {
     balance += amt;
    }
    assert(balance >= amt);
  }
}
```

This function is easy to break by picking an `amt` that overflows `balance`,
so that the postcondition `balance > amt` will not hold. A
[fuzzer](https://en.wikipedia.org/wiki/Fuzzing) finds this kind of bug very
easily. However, fuzzers have trouble finding bugs that are either specifically
hidden (e.g. by a malicious developer), or that have a complicated code path
towards them. Let's see a simple one:


```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import "forge-std/Test.sol";

contract MyContract is Test {
  uint balance;
  function prove_multiply(uint amt, uint amt2) public {
    require(amt != 1);
    require(amt2 != 1);
    require(amt < amt2);
    uint tmp;
    tmp = amt * amt2;
    if (tmp == 119274257) balance = 1337;
    else balance += tmp;
    assert(balance >= tmp);
  }
}
```

Calling this contract with `amt = 9479` and `amt2 = 12583` will set the balance
to 1337 which is less than `amt*amt2`, breaking the postcondition. However, a
fuzzer, e.g. [Echidna](https://github.com/crytic/echidna) will likely not find
those numbers, because `uint` has a potential range of `2**256` and so it'd be
looking for a needle in a haystack, when looking randomly. Here's how to run
Echidna on the multiplication test:

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
 // the rest is the same
}
```

Then run:
```
echidna --test-mode assertion src/multiply-test.sol
```

Echidna will terminate after 50k runs, with all tests passing. Notice that the
difference here, compared to the previous example, is that the overflow example
has _many_ different inputs that can break the postcondition, whereas here only
one can.

Hevm finds the bug in both of these functions. This is because
hevm (and symbolic execution frameworks in general) try to find the bug via
proof-directed search rather than using random inputs. In hevm, we try to prove
that there are no inputs to the test case such that given the preconditions, the
postconditions can be broken. While trying to construct this mathematical proof,
hevm finds a _countereexample_, an  input that breaks the postconditions:


```
$ hevm test
Checking 1 function(s) in contract src/multiply-test.sol:MyContract
[RUNNING] prove_multiply(uint256,uint256)
   [FAIL] prove_multiply(uint256,uint256)
   Counterexample:
     result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
     calldata: prove_multiply(9479,12583)

Checking 1 function(s) in contract src/overflow-test.sol:MyContract
[RUNNING] prove_overflow(uint256)
   [FAIL] prove_overflow(uint256)
   Counterexample:
     result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
     calldata: prove_overflow(00000000000000000000000000000000000000000000000100000000000000000182dad8c17bd5e89e8043a08ada90a6d5efdee4425f85cb863109783e158ba4fba908a0e6fae6c6b51002)
```

## Similarities and Differences to Other Tools

Fuzzers are exceedingly fast and efficient when there are many potential faults
with a function/contract, or if the faults are of a type that's easy to search
for (e.g. off-by-one). However, they rarely, if ever, find cases where the bug
is hidden deep in the branch logic, or needs very specific input parameters.
Hence, it is best to use fuzzers at first to find easy-to-find bugs, as fuzzers
are very efficient at that. Then, once the tests pass the fuzzer, it is
recommended to use a symbolic execution engine such as hevm.

hevm is similar to [Halmos](https://github.com/a16z/halmos) and
[Kontrol](https://docs.runtimeverification.com/kontrol/overview/readme) in its
approach. However, it is quite different from static code analysis tools such
as [Oyente](https://github.com/enzymefinance/oyente),
[Slither](https://github.com/crytic/slither), and
[Mythril](https://github.com/ConsenSys/mythril). While these 3 tools typically
use some form of symbolic execution to try to validate their results, their
main method of operation is not via symbolic execution, and they can, and do,
report false positives.

Notice that static code analysis tools can find bugs that the author(s) didn't
write a test case for, as they typically have a (large) set of preconfigured
test-cases that they can report on, if they can find a way to violate them. Hence,
it may be valuable to run static analysis tools alongside symbolic execution tools
such as hevm.

Finally,
[SMTChecker](https://github.com/argotorg/solidity/blob/develop/docs/smtchecker.rst)
may also be interesting to run alongside hevm. SMTChecker is very different
from both approaches detailed above. While SMTChecker is capable of reliably
finding both reentrancy and loop-related bugs, the tools above can only do so
on a best effort basis. Hevm often reports a warning of incompleteness for
such problems, while static code analysis tools either report potential
positives or may even not discover them at all.


| Tool | Approach | Primary Method | Notes |
| --- | --- | --- | --- |
| **hevm** | Symbolic analysis of EVM bytecode | Symbolic execution | Focuses on exploring all execution possibilities, identifying potential assertion violations, and optimizing gas usage. Can prove equivalence between bytecodes. |
| **Halmos** | Similar to hevm | Not specified | Approach similar to hevm, but the document does not detail specific methodologies or differences. |
| **Kontrol** | Similar to hevm | Not specified | Approach similar to hevm, with a focus presumably on symbolic analysis as well, but further details are not provided in the document. |
| **Oyente** | Static code analysis | Partial symbolic execution | Uses symbolic execution to validate results but primarily relies on static analysis. Can report false positives. |
| **Slither** | Static code analysis | Partial symbolic execution | Similar to Oyente, uses static analysis as its main method, complemented by symbolic execution for validation. Known for reporting false positives. |
| **Mythril** | Static code analysis | Partial symbolic execution | Combines static code analysis with symbolic execution for result validation. Like Oyente and Slither, can report false positives. |
| **SMTChecker** | Different from both hevm and static code analysis tools | SMT solving | Capable of finding reentrancy and loop-related bugs reliably, which other tools might miss or report incompletely. Offers a distinct approach from symbolic execution. |
