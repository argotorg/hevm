# Limitations and Workarounds

Symbolic execution in general, and hevm in particular, have a number of known
limitations. Many of these limitations can be worked around without too much
effort. This document describes some of the most common limitations and
workarounds.

## Loops and recursion
The most important issue related to symbolic execution is to do with loops and
recursion. For example, the following code is hard to deal with in a symbolic
context:

```solidity
function loop(uint n) {
  for(uint i = 0; i < n; i++) {
    mystate[i]++;
  }
}
```

When such a function is called, and `n` is a symbolic parameter (e.g. parameter
to a function `prove_`, such as `prove_correct(uint n)`), hevm would need to
create a new execution path for each potential value of `n`, which can be very
large. The same principle applies to recursion, where the depth of the
recursion may be unbounded or bounded only by a potentially very large number.

Hence, hevm only explores loops and recursions up to fixed depth `k`, a
parameter that can be adjusted from the command line via the `--max-iterations
k` parameter. Whenever the limit is hit, hevm warns of the incomplete exploration:

```shell
WARNING: hevm was only able to partially explore the call prefix 0x[...] due to the following issue(s):
  - Max Iterations Reached in contract: 0x[...] pc: [...]
```

In general, the workaround suggested is to try to write code without loops, if
possible, or to have a limit on the number of iterations. For example, by using
`max(k,n)` instead of `n` in the loop condition, where `k` is a fixed number.
Unbounded loops are a problem for digital contracts, as they may be forced by
an attacker to exhaust gas, thereby potentially e.g. deadlocking the contract.
This can lock in (large) funds, which can be a very serious issue. Hence,
limiting loop iterations is a good practice in general -- not only for symbolic
execution.

**Best Practices**:
- Try to write code without loops, if possible.
- Use `max(k,n)` instead of `n` in the loop condition, where `k` is a fixed number.
- Avoid unbounded loops to prevent potential gas exhaustion attacks

## Gas costs

Gas is hard to symbolically track, due to certain opcodes, such as SLOAD,
having different cost depending on the parameters to the opcode. Many symbolic
execution systems, including hevm, solve this by not fully tracking gas.
This means that hevm may report that an assertion
failure can occur through a particular execution trace, but that
trace would cost more to execute than the allowable gas limit.

In general, it is possible to check whether the issue can be hit by running the
hevm-provided counterexample in a concrete execution setting, thereby filtering
out false positives. However, it is strongly advisable to fix potential issues
that are only guarded due to gas exhaustion, as they may become exploitable in
the future, when gas costs change.

**Best Practices**:
- Don't rely on gas exhaustion as a security mechanism.
- Check potential issues by running the hevm-provided counterexample in a
  concrete execution setting.

## Symbolic arguments to certain EVM opcodes

When a symbolic argument is passed to an EVM opcode that hevm cannot deal with
symbolically, an error is raised. There are number of such EVM opcodes, for
example JUMP, JUMPI, CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE, CREATE2,
SELFDESTRUCT, etc. If any of these are called with an argument that is
symbolic, hevm raises an error, such as:

```shell
WARNING: hevm was only able to partially explore the call prefix 0x[...] due to the following issue(s):
  - Attempting to transfer eth to a symbolic address that is not present in the state
```

There is no single workaround for this class of issues, as it depends on the
specific circumstances of the code. In general, we suggest trying to concretize
the call to the code, such that only what is truly needed to be symbolic is
left symbolic. For example, you may be able to force partial concrete execution via
`require()` statements, thereby concretizing the potential symbolic value. Similarly,
dynamically computed JUMP destinations can be avoided via pre-computed jump tables, etc.

**Best Practices**:
* Use `require()` statements to concretize symbolic values
* Avoid dynamically computed jumps -- use pre-computed jump-tables, if necessary

## Jumping into symbolic code

Jumping into symbolic code is not supported by hevm. This can happen when, e.g.
a function creates a contract based on a symbolic value, and then jumps into
the code of that contract. In these cases, you will get a warning like the
following:

```shell
WARNING: hevm was only able to partially explore the call prefix 0x[...] due to the following issue(s):
  - Encountered a jump into a potentially symbolic code region while executing initcode. pc: [...] jump dst: [...]
```

For these cases, we suggest concretizing the call that creates the contract,
such that the bytecode created and later jumped to, is not symbolic.

## Setting block number

The [roll(uint256)
cheatcode](https://book.getfoundry.sh/cheatcodes/roll?highlight=roll#roll) can
be used to set the block number in the current EVM state. However, it does not
alter the block number that the RPC calls use. For that, one must use the
`--number` command line option. Hence, it is not possible to dynamically change
what block number the RPC calls fetch from, other than by restarting the hevm
process with a different block number.
