# Common options

The subcommands of hevm present a number
of common options. Here, we document these options in detail.

## Maximum Buffer Size, ``--max-buf-size``

The buffers in hevm are limited to a maximum size of 2^N bytes, where N is by
default 24 (16 MB), but adjustable via the `--max-buf-size` flag (at most 64).
Gas limits keep real calldata and returndata well below 16 MB, so the default
covers all transactions that can actually be executed, while keeping
counterexamples small enough to examine and to replay. Limiting this value
further to e.g. 20 can make counterexamples even easier to understand.

## Choice of Solver, ``--solver``

hevm can use any SMT solver that supports the AUFBV theory and incremental
solving. Currently, z3, cvc5, and bitwuzla's interfaces are implemented. While
any of these solvers work, bitwuzla is the default, as it is in general
extremely fast, almost always significantly faster than e.g. z3.

## Number of Solvers, ``--num-solvers``

hevm can run multiple solvers in parallel and will run as many solvers as it
detects the number of CPU cores on the machine. However, in some cases, that
may lead to memory outs, in case the solver happens to get queries that are
memory-intensive. In these cases, the number of solvers can be limited to a a
specific (low) number via the `--num-solvers` flag.

## Promising no reentrancy, ``--promise-no-reent``

hevm can be instructed to assume that no reentrancy will occur during the
execution of the contract. This is currently neccessary to fully explore
certain contracts. This is because value transfer is usually done via a `CALL`,
which can be reentrant. By promising no reentrancy, the system can assume that
no reentrancy will occur and can explore the contract more fully.

## Timeout for SMT queries, ``--smt-timeout``, ``--smt-branch-timeout``

Some queries take too long. With a timeout, we ensure that hevm eventually
terminates. However, endstates where the timeout was reached are considered
inditerminate, and will lead to a `WARNING` in the output. It is worthwhile
trying to switch to a different SMT solver such as bitwuzla, or increasing the
timeout if this happens. The default is 300 seconds.

The queries that decide which side of a branch can be taken have their own,
shorter timeout, `--smt-branch-timeout`, 20 seconds by default and at most
`--smt-timeout`. When the solver cannot decide a branch, hevm explores both
sides, so a timeout there costs no counterexamples, only time spent on paths
that may be impossible.

## Loop Iteration Limits, ``--max-iterations``, ``--max-concrete-iterations``

hevm explores a loop whose condition depends on symbolic values at most
`--max-iterations` times, 5 by default, and warns that the exploration was
partial when it stops there. Loops whose condition is concrete, such as a
loop over state fetched with `--rpc`, run until they end, up to
`--max-concrete-iterations`, 10000 by default. That limit only exists because
hevm does not track gas symbolically, so a loop that never ends would
otherwise never stop. Set either to -1 for no limit.

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

When a symbolic jump target, or a jump condition, is decided by a subterm with
at most this many possible values, such as `selector mod n` in a jumptable
dispatcher, or a loop bound limited by an earlier check, the values are
enumerated directly instead of asking the SMT solver for them.

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

## Progress, ``--no-progress``, ``--progress-log``, ``--progress-exprs``

While `hevm symbolic` and `hevm equivalence` run, a status line on stderr
shows the current phase, the number of finished paths, the SMT queries done,
being solved and waiting for a free solver, the program counter whose queries
took the most solver time in this phase, and the interpreter tasks. Finished
phases stay on screen as a line of their own. When stderr is not a terminal, the
status is printed as a plain line every 30 seconds instead. `--no-progress`
turns it off.

`--progress-log FILE` (or `--verb 3`, which writes `hevm-progress.jsonl`)
writes a JSONL log of what the interpreter and the solvers are doing: forks,
finished paths with the reason for partial ones, every SMT query with the
program counter that issued it, how long it waited for a free solver and how
long it was solved for, and its result, the phases of equivalence checking with
a summary of each (the program counters with the most solver time and forks,
and the queries by kind and result), and every 2 seconds a snapshot of what
each worker and each running query is doing. Every line is flushed, so the log of a run that
was killed or timed out is still complete up to that point, which shows where
it got stuck. `--progress-exprs` (or `--verb 4`) also logs the expressions and
path conditions sent to the solver.
