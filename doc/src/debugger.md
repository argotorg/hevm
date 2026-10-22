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

## Clients

hevm itself has no user interface: everything goes through the HTTP API, so
several clients can drive the same session.

- **hevm-web-ui**, a web page, kept as a separate project. It shows the source
  line, the code, the stack, memory, storage, the call trace, pending branches,
  breakpoints and statistics.
- **Any program**, such as a script or an LLM agent, through the HTTP API.
  `GET /api` describes it. Views are JSON with values unformatted, words as
  hex and symbolic ones as expressions, so each client shows them its own way.

The `help` command lists the commands.

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

Unlike exploration, the debugger never merges the two sides of a short branch:
every step is one instruction.

Symbolic values are shown simplified, as the solver would see them. This can
be turned off to see the expressions as execution built them.
