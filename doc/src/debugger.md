# Interactive debugger

> The debugger is new and still changing: its commands and HTTP API may change
> between releases. This page covers the concepts only.

`hevm test`, `hevm symbolic` and `hevm exec` take `--interactive`. Instead of
running to the end, hevm then starts a debugger that serves the execution over
HTTP on localhost, by default at port 7317 (`--port`):

```shell
$ hevm test --root . --match prove_transfer --interactive
hevm debugger at http://127.0.0.1:7317
```

## Stepping forward and back

The debugger steps one instruction at a time, by source line, over or out of
calls, or until a breakpoint (a pc, an opcode or a source line). It can also
step back. The EVM cannot run backwards, so the debugger keeps snapshots of the
VM, by default every 50 steps (`--interactive-snapshot-every`), and goes back by
restoring the latest snapshot before the target and replaying from there.
Going back therefore shows exactly the state the run had at that step.

## Symbolic execution

With symbolic inputs, a branch may go either way. Exploration in `hevm test`
and `hevm symbolic` follows every side; the debugger stops instead and lets
you pick the side to follow. Going back to before a branch lets you take the
other side. How the sides offered are decided is a setting:

- **solver** (the default): the SMT solver rules out sides that cannot be
  taken, so only feasible ones are offered;
- **explorer**: sides are ruled out the way exploration does it, by
  simplification alone, so the debugger follows what `hevm test` would do;
- **checked**: as explorer, and the solver checks every decision
  simplification made. This is for finding bugs in hevm itself.

Symbolic values are shown simplified, as the solver would see them. This can
be turned off to see the expressions as execution built them.
