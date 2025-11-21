# Common options

The subcommands of hevm present a number
of common options. Here, we document these options in detail.

## Maximum Buffer Size, ``--max-buf-size``

The buffers in hevm are limited to a maximum size of 2^N bytes, where N is by
default 64, but adjustable via the `--max-buf-size` flag. This helps to prevent
the system from creating buffers that are too large and would exceed the gas
limit. Limiting this value further to e.g. 20 can help to force the system to
generate counterexamples that are easier to examine and understand.

## Choice of Solver, ``--solver``

hevm can use any SMT solver that supports the AUFBV theory and incremental
solving. Currently, z3, cvc5, and bitwuzla's interfaces are implemented. While
any of these solvers work, we recommend using bitwuzla as it is in general
extremely fast, almost always significantly faster than e.g. z3.

## Number of Solvers, ``--num-solvers``

hevm can run multiple solvers in parallel and will run as many solvers as it
detects the number of CPU cores on the machine. However, in some cases, that
may lead to memory outs, in case the solver happens to get queries that are
memory-intensive. In these cases, the number of solvers can be limited to a a
specific (low) number via the `--num-solvers` flag.

## Promising no reentrancy, ``--promise-no-reent``

hevm can be instructed to assume that no reentrancy will occur during the
execution of the contract. This is currently necessary to fully explore
certain contracts. This is because value transfer is usually done via a `CALL`,
which can be reentrant. By promising no reentrancy, the system can assume that
no reentrancy will occur and can explore the contract more fully.

## Timeout for SMT queries, ``--smttimeout``

Some queries take too long. With a timeout, we ensure that hevm eventually
terminates. However, endstates where the timeout was reached are considered
inditerminate, and will lead to a `WARNING` in the output. It is worthwhile
trying to switch to a different SMT solver such as bitwuzla, or increasing the
timeout if this happens.

## Loop Iteration Limit, ``--ask-smt-iterations``

Loops in the code cause a challenge to symbolic execution framework. In order
to not run indefinitely, hevm will only explore a certain number of iterations
of a loop before consideing abandoning the exploration of that branch. This
number can be set via the `--ask-smt-iterations` flag.

## Maximum Branch Width Limit, ``--max-width``

Limits the number of potential concrete values that are explored in case a
symbolic value is encountered, thus limiting branching width. For example, if a
JUMP instruction is called with a symbolic expression, the system will explore
all possible valid jump destinations, which may be too many. This option limits
the branching factor in these cases. Default is 100.

If there are more than the given maximum number of possible values, the system
will try to deal with the symbolic value, if possible, e.g. via
over-approximation. If over-approximation is not possible, symbolic execution
will terminate with a `Partial` node, which is often displayed as "Unexpected
Symbolic Arguments to Opcode" to the user when e.g. running `hevm test`.

## Maximum Branch Depth Limit, ``--max-depth``

Limits the number of branching points on all paths during symbolic execution.
This is helpful to prevent the exploration from running for too long. Useful in
scenarios where you use e.g. both symbolic execution and fuzzing, and don't
want the symbolic execution to run for too long. It will often read to
WARNING-s related to `Branches too deep at program counter`.
