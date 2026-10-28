# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## Added
- Abstract arithmetic lemmas for dividends a literal apart over one divisor,
  `(x-k)/z <= x/z <= (x-k)/z + k`, as in a `ceilDiv` next to a round-down, and
  for `(r + c*q)/c == q` when `r < c`.
- Abstract arithmetic lemmas relating `a/c` to `x` when `a` is bounded by `c*x`,
  bounding `ceilDiv(c1*x, c2)` by `x/(c2/c1)` when `c1` divides `c2`, and bounding
  remainders: `a%b <= a` and `a%b < b`.
- The simplifier drops an `ITE c t k` whose literal `k` is what `t` is when `c` is 0,
  such as the product a short-circuited overflow check leaves after a merge.
- The simplifier splits `b ** ITE c x y` with literal `b`, `x` and `y` into two
  constants, and folds `x < x - x % c`, also masked to `uintN`, to false.
- A memory offset or size that depends on a merged condition, such as an array
  length picked by a ternary, forks on that condition, so memory stays concrete.
- `test` takes `--run-log FILE`, appending a line when each test starts and ends,
  and `--yul-verbosity N`. Tests time out after 10 minutes by default.
- The progress log gives the source location of forks and of the locations in
  its summaries, when there is debug info.
- Invariant testing: `hevm test` checks `invariant_` functions after every
  sequence of at most `--invariant-depth` calls to the target contracts, with
  symbolic arguments, callers and timestamps. States reached before are not
  explored again. Assertion failures in the calls fail the test, and minimal
  proxies (EIP-1167 clones) can be targets.
- An invariant testing tutorial in the docs.
- A worked example in the docs: finding the Abracadabra `cook()` exploit on a mainnet fork.
- `--smt-branch-timeout`, 20 seconds by default, for the queries that decide which
  branches to explore.
- `--max-concrete-iterations`, 10000 by default, bounds loops whose condition is
  concrete. `--max-iterations` now only bounds loops with symbolic conditions.
- A worked example in the docs: finding the Truebit exploit on a mainnet fork.
- The symbolic execution fuzzers check that a model reaching another leaf via a
  symbolic keccak gives each hashed input one hash, and generate comparisons of
  hashes of calldata. The equivalence fuzzer generates CREATE and CREATE2 and
  compares all accounts in its concrete runs.
- With `--rpc` at a fixed block, fetched state is cached by default in the user's
  cache directory, per chain, and reused by later runs. `--no-rpc-cache` turns
  this off. The cache is saved however the run ends, merged with what other runs
  saved.
- Concurrent RPC fetches of the same storage slot, account or latest block
  share one request.
- The RPC fuzzer's mock node delays requests and fails them by HTTP 429, JSON-RPC
  rate limit errors and dropped connections, and the fuzzer races
  8 runs on one session and checks that no session repeats a request.
- `--interactive` for `symbolic`, `exec` and `test` starts an interactive debugger
  served over HTTP on localhost, with symbolic branches,
  stepping back, breakpoints, storage, call traces and statistics. Its views
  are JSON for clients to format.
  `--interactive-snapshot-every` sets how often it snapshots for stepping back.
- `--serve` serves the progress of a run over HTTP, at `/progress`.
- `--check-static-branches` checks branch decisions made without the solver
  against the solver.
- The symbolic execution fuzzer runs symbolic and concrete execution in
  lockstep, also along paths given by solver models, and
  checks the debugger's stepping, back and forth, against geth.
- Word reads that straddle literal bytes and written words, such as calldata's
  selector and first argument, simplify to the written parts shifted and or-ed.
- Reads of all-zero buffers simplify to zero.
- `hevm symbolic` replays each counterexample concretely and marks it
  `[validated]` or `[not reproducible]`, like `hevm test`.
- The symbolic execution fuzzer generates mapping and array storage accesses,
  and checks that `hevm symbolic`'s replay of each model agrees with geth.
- Byte reads through a word read at a concrete offset now resolve against its
  source buffer, allowing unaligned copies to preserve concrete mapping keys.
- KECCAK256 folds memory that becomes concrete after simplification, including
  CREATE2 preimages containing concrete hashes, while retaining nested preimages
  for the solver's keccak assumptions.
- The symbolic execution fuzzer runs random programs with abstract calldata,
  storage, callvalue and timestamp, checks the leaf the concrete inputs reach
  against geth, replays solver models of other leaves in geth, and reports
  opcode coverage.
- The symbolic execution fuzzer also creates contracts whose deployed code size
  depends on a symbolic CREATE value.
- Property tests check that `--arg` values parse back to the generated ABI
  value and encode to the canonical calldata.
- Equality of a keccak hash with a literal at most 256 now simplifies to false,
  matching the existing SMT assumption.
- Equality of a keccak hash with a literal above 2^256 - 257 also simplifies to
  false, matching the SMT assumption.
- Masked `Div` and `SHR` reads now simplify through packed-word writes,
  allowing reads of Solidity-packed fields to reduce to the written value.
- Masked and shifted reads of packed words drop `Or` operands that cannot
  reach the read bits, also through intermediate masks and shifts, without
  distributing the mask over the remaining operands.
- Small, word-aligned keccak inputs are canonicalized so equivalent mapping
  keys built from memory writes or copies can resolve to the same storage entry.
- Storage reads resolve concrete keccak slots, including nested hashes and
  literal offsets, when comparing writes or looking up a concrete store.
- Keccak equality and storage reads now use known differences in input lengths
  or words to rule out aliases, including struct offsets below 256, under the
  existing keccak assumptions.
- `copySlice` now trims irrelevant writes and base bytes from concrete source
  windows, allowing mapping keys built over different scratch memory to compare equal.
- Symbolic execution now avoids forking when simplification shows that
  the path conditions imply the branch condition.
- Symbolic jump targets and jump conditions that depend on a subterm with few
  possible values, e.g. `selector mod n` in jumptable dispatchers or a loop bound
  limited by an earlier check, are resolved by enumerating those values instead
  of asking the SMT solver.
- `hevm equivalence` replays every counterexample concretely and marks it as
  validated, not reproducible, or not replayable. It only reports that the
  contracts do not behave equivalently if a counterexample is validated.
- A live status line on stderr for `hevm symbolic`, `hevm equivalence` and
  `hevm test` (disable with `--no-progress`), with a summary line per finished
  phase or test that includes its slowest SMT query, and a JSONL log of interpreter and solver
  progress (`--progress-log FILE` or `--verb 3`; `--progress-exprs` or `--verb 4`
  also logs solver expressions).
- The progress log tells the time a query waited for a solver apart from the
  time it was solved for, gives the reason a query for multiple solutions gave
  up, and ends each phase with a summary of where its solver time and forks
  went. The status line shows queued queries and the program counter with the
  most solver time. With expressions logged, each `sat` query also logs the
  props it was built from.
- Abstract arithmetic, on by default (disable with `--no-abstract-arith`):
  symbolic multiplication and division are encoded as uninterpreted functions
  constrained by sound algebraic lemmas, and are equated with the native bitvector operations only when the abstract query
  comes back satisfiable. This proves many `mulDiv`-style properties that the
  solver otherwise cannot discharge. Caveats: the lemma families range over
  pairs of collected terms, so the number of emitted assertions is quadratic in
  the number of products and divisions in a query and is currently uncapped;
  and a query the abstraction cannot answer is retried with native arithmetic,
  so it can take up to three times the SMT timeout.
- Traces are now built as `prettyprinter` documents with semantic annotations
  (`showTraceDoc`, `traceDocForest`, `TraceAnn`), so frontends can style them
  without parsing ANSI escape codes. Terminal output is unchanged.
- Hash-consing of symbolic terms, on by default (`hashConsExplore` config
  option); disable it with `--no-hash-cons`.
- Comparisons of a literal with `c - x`, where `x` is bounded by `c`, now
  simplify using the lower bound of the difference.
- The RPC fuzzer fetches all state from a mock JSON-RPC node, with EOAs and
  nonexistent accounts, symbolic addresses, value transfers, reverting,
  delegated and static calls, and CREATEs and CREATE2s onto existing accounts.
- The symbolic execution fuzzer generates BALANCE, EXTCODESIZE, EXTCODEHASH,
  EXTCODECOPY, CREATE and CREATE2, over a pre-state with EOAs, an empty
  account and accounts at the addresses the program creates. Each case also
  runs with all state but the contract's code fetched from a mock RPC node.
- The equivalence fuzzer checks contract creation, and generates storage
  writes of zero.

## Changed
- Deciding a branch without the solver reuses the simplified path conditions
  of the earlier branches on the path, kept in the new `VM` field
  `simpConstraints`, and first tries the branch condition alone, which
  simplification can decide where it cannot with the path conditions.
- State merging also merges if/else branches and ternaries, where the two
  sides meet after the jump target, and follows the branches inside a merged
  side that its own condition decides, such as the overflow check of `a - b`
  under `a > b`. A branch reached again in a loop is not merged, so the loop
  bound applies. `MergeState` has `msAssume` instead of `msRemainingBudget`.
- Invariant testing merges the states after a call that differ only in their
  path conditions into one state with the disjunction of those conditions, and
  drops the logs of earlier calls. The disjunction drops conditions whose
  negation is the only difference between two of its parts.
- Symbolic execution explores the newest pending path first, depth-first,
  which keeps fewer paths pending.
- The Solidity ASTs are no longer kept after reading the build output:
  `SourceCache` has no `asts`, `DappInfo` no `astIdMap` and `astSrcMap`.
- Invariant testing keeps only the states of feasible calls, checked by the
  solver, and drops the states seen before as soon as they are reached. It keeps
  the state after a call without that call's memory and traces.
- The default number of solvers is at most half of the available memory divided
  by `--smt-memory`, so that the solvers running at once fit in memory.
- Solidity's overflow check of a multiplication by a literal, `y == 0 || (y * c) / y == c`,
  also once simplification has distributed `y * c` or dropped `y == 0`,
  simplifies to a bound on `y`, and the overflow checks of multiplications use bounds that hold
  through comparisons with other bounded values.
- Constant propagation substitutes any term that the props fix to a constant,
  not only variables.
- Invariant tests print the paths they only partially explored grouped by
  source location, as `prove` tests do, instead of printing their expressions.
- `EVM.SymExec` is split: concrete replay of counterexamples moves to
  `EVM.CexReplay`, and equivalence checking to `EVM.Equivalence`. Symbolic
  calldata (`EVM.SymExec.Calldata`) and counterexample models and printing
  (`EVM.SymExec.Cex`) are re-exported by `EVM.SymExec`.
- A storage read blocked by a write to a symbolic slot drops the writes below it that
  cannot alias the slot read, or are overwritten by a later write to the same slot.
- `hevm test` and `hevm symbolic` stop at the first counterexample, cancelling the
  solver queries still running. `--no-early-abort` explores every path and
  replaces `--early-abort`.
- `hevm test` shows the result of the concrete replay of a validated counterexample,
  so failed assertions on symbolic values show the values.
- Checked multiplication, `x == (x * d) / d`, is encoded for the SMT solver as an
  overflow check instead of a division.
- `hevm test --coverage`, which did nothing, is removed.
- The test suite shows the output of `hevm test` only for failing tests.
- Results that revert with `Error(string)` show the decoded message instead of hex.
- Solver queries for branch conditions and symbolic values also get the keccak
  preimages recorded during concrete execution, as the final queries do.
- A symbolic value that depends on several symbolic subterms with few possible
  values each, such as the slot of a nested mapping with two such keys, is now
  split into cases on all of them, instead of asking the solver for its values.
  Reading such a slot from storage fetched via RPC now works.
- The default SMT solver is now bitwuzla instead of z3. hevm now stops with an
  error at startup if the selected solver is not installed.
- The default `--max-buf-size` is now 24 (calldata and returndata of up to
  16 MB) instead of 64, which is still more than gas limits allow.
- Counterexamples have bold section headings, and `hevm equivalence` shows the
  result of replaying each one as a coloured tag, as `hevm test` does.
- `hevm equivalence` replays counterexamples with calls to unknown code by
  putting code at each callee that returns what the counterexample says, and
  logs each replay to the progress log.
- Exponentiation by a literal is encoded into SMT by squaring, and exponents of
  1000 and more no longer make the query fail.
- The simplifier rewrites modulo and division by a power of two to bit
  operations.
- The simplifier composes nested shifts by literals into one shift and a mask.
- The simplifier tracks which bits of a word can be set, to drop redundant
  masks and decide equalities and comparisons with literals.
- The simplifier cancels additions, subtractions, xors, negations and
  multiplications by odd literals in equalities.
- The simplifier moves operations with literals into ITEs with literal
  branches, as path merging creates, and turns comparisons with them into
  conditions.
- The simplifier cancels an operand against its inverse in sums, differences,
  xors and with its negation, and moves negation through literal operations.
- The simplifier drops the writes and zeroes the concrete bytes a copy
  overwrites, and reads zero from all-zero concrete buffers at any offset.
- The simplifier turns overflow checks of adding or subtracting a literal,
  such as `x < x + c`, into comparisons of `x` against a literal.
- The simplifier decides `x == (x * d) / d`, as in Solidity's
  checked-multiplication guard or scaling by a literal and back, when bounds from
  the path conditions and from the structure of `x` and `d` rule out overflow.
- The simplifier cancels common factors of the literals in `(a * x) / b` when
  the structure of `x`, or bounds from the path conditions, rule out overflow,
  and folds nested divisions by literals.
- The simplifier uses the condition of an ITE in its branches, and splits a
  comparison of an ITE with one literal branch into cases, so the bounds in
  Solidity's short-circuited `&&` and `||` reach the path conditions.
- The simplifier cancels addends common to both sides of a subtraction.
- Reads from buffers written at offsets from the same symbolic pointer skip
  the writes they are disjoint from and resolve the writes they hit.
- Path merging keeps stack slots that both branches leave equal as they are,
  instead of simplifying an ITE of them.

## Fixed
- Symbolic execution leaked memory: every trace kept the whole VM it was made
  in, and memory size and loop visit counters kept the earlier frame states.
- Memory snapshots at forks no longer copy the unused zeros of the memory buffer.
- Source locations of contracts with immutables are found in Foundry projects.
- Source locations are right after an incremental `forge build`, whose
  build-infos number the source files independently.
- `prank` and `startPrank` with a symbolic address, e.g. one picked from a list
  by a symbolic index, explore each possible address instead of failing.
- SMT queries skip assumptions between concrete keccak hashes, whose values
  are already known, avoiding unnecessary quadratic growth.
- Constant propagation checks disequalities and disjunctions against the
  constants of all path conditions, not only of those before them. The debugger
  no longer offers an infeasible branch side when the solver cannot encode the
  path conditions.
- Loop iterations are counted per call, so repeated calls into the same contract
  no longer hit `--max-iterations`.
- Keccak assumptions compare only the hashed bytes of inputs of concrete length,
  so one input no longer gets two hashes (spurious counterexamples).
- Equivalence checking compares the code of contracts the programs create, and
  CREATE2 with a symbolic deployer gives addresses that depend on the salt and
  init code, CREATE ones that depend on the nonce.
- The concrete replay of equivalence counterexamples compares the code, storage
  and nonce of every account, not only the called contract's storage.
- `envBytes` cheatcodes take `string` arguments, as in forge-std.
- `eth_chainId` requests no longer pass a block number, which nodes reject.
- JSON-RPC rate limit errors (codes 429, -32005 and -32007) are retried with
  backoff instead of aborting the run.
- Contracts added with `addFetchCache` concurrently are no longer lost.
- `hevm equivalence` with `--sig` or `--calldata` prints and replays the
  counterexample's calldata instead of empty calldata.
- Storage reads return cached concrete values immediately when folding keccaks
  in the slot resolves the lookup.
- Storage reads resolve slots computed from concrete keccaks by any arithmetic,
  such as `keccak(x) & 255`, instead of leaving them symbolic.
- Equivalence checking treats a storage slot written with 0 as equal to an
  unset one.
- Equivalence counterexamples now include the initial storage value of slots
  that the contracts write but never read, so replaying them reproduces the
  difference.
- MCOPY of a symbolic size now grows memory.
- A copy within symbolic memory, e.g. an MCOPY in a loop, no longer makes
  expressions grow exponentially when its source bytes are known.
- Huge copies, logs and return data in symbolic execution are no longer read or
  printed byte by byte; traces show their first 64 KiB.
- A precompile call that runs out of gas now leaves an error trace.
- A branch side the solver refutes is no longer explored when it could not decide
  the other side, e.g. one it cannot encode.
- EXTCODEHASH of an account with no code or nonce and a symbolic balance is 0
  when that balance is 0, instead of the hash of empty code.
- A copy with a symbolic offset is encoded in SMT once instead of once per byte,
  and copies over 1 MiB are not encoded, so large copies no longer exhaust memory.
- An exception during symbolic exploration is now rethrown, instead of being
  printed and followed by `thread blocked indefinitely in an STM transaction`.
- Counterexamples found with storage decomposition show each mapping and array
  entry at its real storage slot, instead of dropping entries and showing keys
  as slots.
- Memory accesses whose offset or size is an address (e.g. from CREATE or
  CALLER) are now charged gas and checked for overflow.
- Counterexample block and transaction context values (callvalue, balances,
  timestamp, ...) are now substituted when concretizing expressions.
- `--arg` accepts negative values for `int<N>` arguments, encoding them
  sign-extended, and rejects values outside the type's range.
- `--arg` now works for `bytesN`, `bytes`, `string` and array arguments.
- A constructor returning deployed code of symbolic size no longer crashes; the
  size is resolved by the solver, or the path is reported as partial.
- CALLDATACOPY, CODECOPY and EXTCODECOPY with a symbolic source offset or size
  reaching past 2^256 no longer wrap around to the start of the source buffer.
- Concrete copies whose source range ends exactly at 2^256 now simplify.
- Calls to unknown code with more value than the caller's balance now fail with
  empty returndata, avoiding spurious counterexamples.
- Copies out of an empty buffer at a symbolic offset simplify to zeros.
- Comparisons of literals with concrete keccak hashes, which simplification
  turns back from literals, now evaluate.
- Retain `NonexistentFork` for source compatibility with callers such as Echidna.
- Enumerating symbolic values no longer shrinks buffer models and silently drops
  possible values, which could leave symbolic jump paths unexplored.
- Forward jumps whose conditions become concrete after folding keccak hashes
  skip speculative merging, keeping their results concrete.
- `--sig` with `bytes` or `string` arguments lays out the calldata by their
  symbolic lengths, instead of assuming each takes `--max-dyn-size` bytes. Shorter
  inputs were missed.
- Without `--rpc`, `hevm symbolic` treats the block number, base fee and
  prevrandao as symbolic instead of 0. `hevm equivalence` and the library's
  symbolic VMs treat the base fee and prevrandao as symbolic too.
- `--basefee` is no longer ignored.
- BLOCKHASH with a symbolic block number or argument is 0 outside the 256 most
  recent blocks.
- State merging no longer merges code that reads GAS, creates a contract or
  calls unknown code; it reused the variable of that GAS reading, address or
  call result for the next one.
- When hevm enumerates the values of a symbolic address, it constrains only its
  low 20 bytes. Addresses with higher bytes set were on no path.
- Calls to unknown code with a symbolic target expand the memory over their
  input and output ranges.
- `vm.expectRevert` is satisfied by a call that ends in an exceptional halt
  (e.g. INVALID or out-of-gas), as in forge.
- A call to a precompile consumes a pending `vm.prank` or `vm.expectRevert`.
- `assertApproxEqAbs(int256,int256,uint256)` with symbolic operands uses the
  signed difference.
- `hevm test` replays counterexamples that depend on `tx.origin` or
  `block.coinbase` instead of crashing, and replays them with the model's caller.
- Counterexample decoding follows the ABI offsets of dynamic arguments.
- `hevm test` skips, with a warning, non-test contracts that use unlinked
  external libraries, instead of rejecting the whole project.
- ECRECOVER rejects `v` other than 27 and 28.
- Restoring a cleared storage slot takes back one refund, not every equal
  refund of the contract.
- Precompiles 0x0a-0x11 and 0x100 are pre-warmed, and symbolic addresses can no
  longer take their values.
- `hevm symbolic` no longer prints QED when some paths were only partially
  explored; it prints the partial-exploration warning and exits with an error.
- `hevm symbolic --create` and `hevm exec --create` run the init code instead of
  treating the contract being created as an address collision.
- Calls to unknown code no longer return equal results just because their other
  inputs are equal: the callee gets unknown gas, which differs between calls.
- `hevm test` checks the fail flag that forge-std's `fail()` sets in its default
  mode too; `--assertion-type` has no effect anymore.
- In `hevm test`, a cheatcode that cannot handle its symbolic arguments, and
  `expectRevert` with symbolic revert data, leave the path partially explored
  instead of reverting, which made the test pass.
- In `hevm test`, `vm.selectFork` with a nonexistent fork fails the test instead
  of ending the path in an error that counted as passing.
- Hash-consing no longer segfaults intermittently with several capabilities: GHC's
  `makeStableName` races with growing the stable name table, so calls are serialized.
- With `--rpc`, accessing an account without code (an EOA) no longer aborts
  with an oracle error.
- With `--rpc`, accounts at addresses up to 0xdeadbeef, such as the burn
  address and the precompiles, are fetched instead of treated as empty.
- With `--rpc`, CREATE and CREATE2 fetch the account at the new address, so
  they keep its balance and detect collisions with accounts on chain,
  including ones with only storage (EIP-7610), via `eth_getProof`.
- With `--rpc`, SSTORE gas and refunds use the slot's value on chain, and
  CALL and SELFDESTRUCT only charge the new account cost when the recipient
  does not exist on chain.
- Buffer equality in SMT queries now also compares lengths, so the equivalence
  checker no longer misses return or revert data that differs only in length.
- Replaying equivalence counterexamples no longer keeps the final VMs of every
  replay alive until the results are shown.
- Words parsed from JSON, e.g. RPC responses, no longer keep their text alive
  until they are used.
- Encoding a copy whose size becomes a literal at or beyond the 256MB memory
  access limit, e.g. a keccak, is reported as unsupported instead of exhausting
  memory.
- A path whose conditions became unsatisfiable at a solver-checked branch now
  ends there, instead of continuing down one side of the branch, e.g. until the
  loop iteration limit.
- A symbolic `JUMP` or `JUMPI` target with bytes set above its low two bytes now
  gives a path that ends in a `BadJumpDestination` error. Before, such targets
  were on no path at all. Code is at most 49,152 bytes (EIP-3860), so such a
  target is past its end. Code
  longer than 64KB, which hevm can run when given raw bytecode, could have a
  valid jump destination there.
- Buffer models from the solver drop bytes past the buffer's length, so a
  counterexample with such bytes can be replayed.
- CALLDATACOPY, CODECOPY and EXTCODECOPY with a literal source range past 2^256
  now copy zeros instead of wrapping around to the start of the source.
- BLOBBASEFEE returns 1, the minimum blob base fee, instead of 0.
- Logs emitted by a call or creation that reverts or fails are discarded.
- MSIZE accounts for memory accessed at a symbolic offset or size.
- Counterexample buffers have the length the solver gave them, instead of
  being extended by bytes the model sets past that length.
- Precompile calls copy at most their output into memory, instead of
  zero-filling the rest of the return buffer, and clear the return data when
  they fail.
- Partial leaves for reaching the maximum number of loop iterations now carry
  their path conditions.
- Execution traces are built in linear time in their length.
- Removed an unsound simplification that folded `SLT (Sub (Max (Lit a) x) (Lit b)) (Lit c)`
  to false, ignoring that the unsigned `Max` can be negative as a signed word.
- A storage slot fetched via RPC no longer shadows symbolic writes made to it
  earlier in the same execution.
- The SMT encoding of a copy into a buffer named `src` no longer reads the
  source of the copy in place of that buffer.
- `hevm equivalence` no longer reports a difference only because one program
  made a call to unknown code that changed nothing.
- Symbolic execution starts the transient storage of the called contract empty,
  instead of with arbitrary values.
- Symbolic execution treats the block number and timestamp as symbolic instead
  of 0.
- Symbolic `CALLDATALOAD` from within 31 bytes of 2^256 gives zero instead of
  wrapping around to the start of calldata.
- A call to unknown code moves its value to the callee, and the callee may send
  the caller ether, in symbolic execution.
- The concrete replay of equivalence counterexamples compares final balances.
- The concrete replay of equivalence counterexamples keeps long return data of
  calls to unknown code compact, instead of running out of memory.
- A call to unknown code now writes the data it returns to the output region
  of the call in memory. Before, the region kept its old contents, so code that
  read the result from there could pass assertions it does not satisfy.
- `hevm equivalence` no longer crashes printing a counterexample that sets the
  balance of the contract, and uses that balance when replaying it. The block
  context of counterexamples is now printed instead of the transaction context.
- The hash-consing tables are reset once they grow past a size limit, instead of
  growing without bound after exploration.
- Symbolic `GAS` readings are now only ordered within a call frame, so a caller
  can have more gas left after a call than its callee had.
- Calls to unknown code with the same inputs now return the same results, also
  between the two programs of `hevm equivalence`, which no longer reports
  differences that only come from such calls returning different results.
- `hevm equivalence` no longer reports each partially explored path once per end
  state of the other program, which inflated the counts in its warnings.
- Simplification and the other `Expr` traversals now also reach revert data, the
  terms in errors and partial executions, `BALANCE` addresses and log topics.
- Storage reads now skip writes at lower struct field offsets as well as higher
  offsets. Unsigned subtraction previously left these reads unresolved.
- Recover compiler-folded mapping slot preimages when building keccak assumptions,
  preventing spurious counterexamples ([#1103](https://github.com/argotorg/hevm/issues/1103)).
- Preimage recovery also covers array slots, slots nested in mappings and arrays,
  and hashes written as parent slots into keccak inputs.
- Keccak results are assumed to be below 2^256 - 256, so adding a field offset to
  one does not wrap around to a small storage slot.
- Storage decomposition no longer swaps key and slot for concrete mapping
  hashes, which caused spurious counterexamples and false proofs when concrete
  and symbolic mapping accesses were mixed ([#1099](https://github.com/argotorg/hevm/issues/1099)).
  To make sure this issue doesn't happen again, the storage decomposition fuzzer
  now also generates concrete-key mapping accesses
- Storage decomposition no longer treats an array and a mapping that share a
  storage slot as one store, which caused false proofs and spurious
  counterexamples ([#1101](https://github.com/argotorg/hevm/issues/1101)).
  Solidity never lays storage out that way, but other bytecode can.
  Decomposition is now skipped for such queries. The check that was meant to
  refuse mixed access types never triggered and is removed
- A symbolic-key `SLOAD` over a `ConcreteStore` is now resolved during execution
  instead of being carried into a fork as an unresolved read: an empty store
  reads 0 at every slot, and a symbolic mapping read filters out concrete
  entries whose recorded keccak preimage identifies a different mapping
  (keccak injectivity). Fixes non-termination/blowup on symbolic mapping reads
  over concretely-initialized storage ([#1082](https://github.com/argotorg/hevm/issues/1082))
- Cheatcode string arguments are now decoded leniently instead of crashing on
  invalid UTF-8: ABI `string` values are raw bytes, so e.g. `vm.setEnv`,
  `vm.envString` and `vm.label` no longer abort the whole run when handed a
  byte sequence that is not valid UTF-8 ([#1076](https://github.com/argotorg/hevm/issues/1076))
- Storage decomposition no longer drops array writes that sit below a write to
  a different store, which caused spurious counterexamples ([#1086](https://github.com/argotorg/hevm/issues/1086))
- Storage decomposition no longer empties a concrete base store when reading a
  small slot, which made such reads return 0 instead of the stored value
- `--early-abort` now kills SMT solver processes that are still running when a
  counterexample is found, instead of waiting for them to finish ([#938](https://github.com/argotorg/hevm/issues/938))
- `--early-abort` no longer deadlocks ("thread blocked indefinitely in an STM
  transaction") when paths are still queued at the time of the abort, and no
  longer reports a spurious "all branches reverted" warning
- Calling a recognized but unimplemented precompile (`0x0a`–`0x11`, `0x100`)
  no longer crashes with an internal error during gas calculation; it now
  fails with `NonexistentPrecompile` (concrete) or a `PrecompileMissing`
  partial (symbolic) ([#1084](https://github.com/argotorg/hevm/issues/1084))
- A `WriteWord` whose offset wraps past 2^256 is no longer moved below an
  earlier `WriteWord` that it overlaps
- `simplify` no longer loops forever on a `CopySlice` of fewer than 32 bytes
  out of a `WriteWord` into an abstract buffer
- `ReadWord` at an index that wraps past 2^256 no longer skips a `WriteByte` or
  `CopySlice` at a low index
- `BufLength` of a `CopySlice` with a symbolic size no longer counts the copy
  when the size is zero
- `Show Addr` no longer corrupts the text printed after the address

## [0.58.0] - 2026-06-26

## Added
- New `forge-symbolic-tests` test suite that runs hevm against the vendored
  [`grandizzy/symbolic-bug-suite`](https://github.com/grandizzy/symbolic-bug-suite)
  (git submodule under `forge-symbolic-tests/`), a set of 22 real-world DeFi exploit
  reproducers, asserting hevm finds a validated counterexample for each
- RPC retry with exponential backoff and a shared cooldown across workers, so transient
  network errors and rate limits (e.g. HTTP 429) no longer abort symbolic execution
- Support for a subset of the [`expectRevert`](https://www.getfoundry.sh/reference/cheatcodes/expect-revert#expectrevert) family of foundry cheatcodes:
  - `expectRevert()`
  - `expectRevert(bytes)`
  - `expectRevert(bytes4)`
  - `expectRevert(address)`
  - `expectRevert(bytes4,address)`
  - `expectRevert(bytes,address)`
  - `expectPartialRevert(bytes4)`
  - `expectPartialRevert(bytes4,address)`
- Support for Foundry/Hardhat `console.log` — calls to the console address are intercepted and decoded in traces
- Source location info (file, line, code snippet) is now shown in state merge debug messages
- New opcode: CLZ
- New POr/PAnd/PImpl/Or/And simplification rules
- Support for `--early-abort` flag that aborts symbolic execution as soon as a counterexample is found
- Support for `vm.etch(address, bytecode)` cheatcode to set the code of a contract at a given address
- State merging via speculative execution of both branches of a JUMPI, joining the
  resulting states whenever possible. Amount of speculative execution is
  controlled via `merge-max-budget`
- Missing simplifications for Eq, Mod, SMod, XOR, SHL, SHR, and Or
- A few more simplification rules around Eq, SHL/SHR, Sub+Add combos, and Xor
- Symbolic execution now supports dynamic `bytes`/`string` calldata arguments,
  with their length bounded by `--max-dyn-size` (default 64). When such a bound
  is applied the result carries a program-wide `[CAVEAT]` noting that
  counterexamples requiring longer inputs may be missed (rather than a per-path
  `Partial`)
- `readWord` disjointness rule for `WriteWord (Add (Lit c) X) …` with bounded `X`.

## Changed
- Simplifier now rewrites `Mul(-1, x)` and `~x + 1` to `Sub(0, x)`
- `AbiFunction` and `AbiBytes` parser is now more strict
- We now check length of AbiArrayDynamic and don't crash in case it's too large
- SMT queries now run in separate processes, which allows us to better manage
  timeouts and memory usage by the SMT solver.
- We now allow limiting the SMT solver's memory usage via `--smt-memory` (in MB).
- The option `--smttimeout` is now called `--smt-timeout` for consistency with other
  options.
- We now abort VM run on a failed `assume`.
- Removed SHA256 from the Expr since it was not being used
- When doing CopySlice of exactly one concrete byte, we now correctly simplify

## [0.57.0] - 2026-01-08

## Added
- We support RPC in equivalence checking now
- Inequality propagation in constant propagation to prune impossible execution paths earlier.
  The constraint solver now tracks lower and upper bounds for symbolic values and detects
  conflicts (e.g., x < 5 && x > 10), significantly reducing the number of paths explored
- Encode symbolic power of 2 as bit-shift in SMT encoding.
- Limit the expansion of the EXP operation to avoid blow-up in the size of the SMT expressions.
- New EXP rewrite rule for base-2 exponents

## Fixed
- Fix incorrect simplification rule for `PEq (Lit 1) (IsZero (LT a b))`

## Changed
- Replaced RPC mocking by a full block cache support. This allows users to cache responses from an RPC
  node via `--cache-dir dir`.
- Changed `verify*` methods to always require postcodition.
- We now use a symbolic execution queue, so as not to run out of resources when there are
  too many branches to explore.
- Removed type parameter of mutable memory from VM definition.
- Removed simplification that were rewriting concrete bytes-to-be-overwritten
  with zero bytes. Benefits were unclear while it had negative effect on
  analysis' performance.
- We now use the symbolic execution queue to also run the SMT solver in `test` mode,
  and verify the results using a cexHandler

## [0.56.0] - 2025-10-13

## Added
- Output geth compatible jsonl traces in `hevm exec` via `--json-trace`
- Allow dumping unsolved SMT files via `--dump-unsolved`
- Allow resolving unknown addresses to only those that are already deployed
  via option `--only-deployed`
- New empty solver option that simply makes sure that all SMT queries return
  unknown
- Allow `verifyInputs` to return partial expressions
- Counterexamples are now validated when running in `hevm test` mode
- RPC mocking framework that allows users to mock responses from an RPC
  node via `--mock-file FILE.json`. This will improve reliability of
  tests that depend on RPC responses
- We now map back (add,pc) warnings to lines of source code
- Calldata decoding is now more robust: we try to decode
  as much as possible even in case of trailing bytes

## Fixed
- We now extract more Keccak computations than before from the Props to assert
  more Keccak equalities.
- Fixed false positive caused by loss of information about concrete
  Keccak computations.
- Faster word256Bytes and word160Bytes functions to help concrete execution
  performance
- We avoid crashing if a cheatcode or a precompiled is invalid or not implemented in concrete mode
- RPC fetching was sometimes incorrect in case of writing to storage
  before fetching it via RPC
- We no longer increment branch depth twice when branching both ways
- We now take into account loop heuristic setting for `test`
- We no longer fetch `Latest` more than once, thereby potentially having
  more than one interpretation of `Latest`. Instead, we fetch it once, and
  fix any further `Latest` block to the previously fetched fixed block number
- RPC fetching is now done through a single HTTPS session.
- RPC cache is now more effective, as it's persisted through different
  threads of the symbolic execution
- During running in --only-deployed mode, we forgot to force the address
  in the constraints to be the one we computed it to be. Fixed.
- We now properly collect all storage reads from the program and build
  a proper counterexample. Previously, some information might have been missing.
- Fixed int calldata decoding of solc's v1 ABI encoding

## Changed
- Updated forge to 1.2.3 and forge-std to 60acb7aa (1.9.7+)
- We now gather Keccak axioms during `setUp()` and inject them into the SMT solver.
  This helps us finding more correct Keccak preimages
- The "origin" address is now symbolic by default when running in `symbolic` mode
- The printed expressions when running in `symbolic` mode are now simplified
- The printed reachable expression is now simplified
- hevm and solidity has been moved to under github.com/argotorg
- Extra range constraints for ABI symbolic types are no longer added. They are
  not needed as they are enforced in the bytecode.
- We no longer try to fuzz the Expr to find a concrete value that satisfies
  the expression. This was not very effective and made the system more complex
  to maintain. Echidna is an excellent fuzzer that can be used instead.
- Shrinking of the calldata is now more aggressive, shrinking even small (<1024B)
  buffers
- Rename confusing function name runSolidityTest to runForgeTest

## [0.55.1] - 2025-07-22

## Added
- When a staticcall is made to a contract that does not exist, we overapproximate
  and return symbolic values
- More simplification rules for Props
- JoinBytes simplification rule
- New simplification rule to help deal with abi.encodeWithSelector
- More simplification rules for Props
- Using the SMT solver to get a single concrete value for a symbolic expression
  and continue running, whenever possible
- STATICCALL abstraction is now performed in case of symbolic arguments
- Better error messages for JSON parsing
- Multiple solutions are allowed for a single symbolic expression, and they are
  generated via iterative calls to the SMT solver for quicker solving
- Aliasing works much better for symbolic and concrete addresses
- Constant propagation for symbolic values
- Allow reading bytecode via --code-file or --code-a-file/--code-b-file. Strips
  `\n`, spaces, and ignores leading `0x` to make it easier to use via e.g.
  `jq '.deplayedBytecode.object file.json > file.txt'` to parse Forge JSON output
  This alleviates the issue when the contract is large and does not fit the command line
  limit of 8192 characters
- Two more simplification rules: `ReadByte` & `ReadWord` when the `CopySlice`
  it is reading from is writing after the position being read, so the
  `CopySlice` can be ignored
- More simplification rules that help avoid symbolic copyslice in case of
  STATICCALL overapproximation
- Test to make sure we don't accidentally overapproximate a working, good STATICCALL
- Allow EXTCODESIZE/HASH, BALANCE to be abstracted to a symbolic value.
- Allow CALL to be extracted in case `--promise-no-reent` is given, promising
  no reentrancy of contracts. This may skip over reentrancy vulnerabilities
  but allows much more thorough exploration of the contract
- Allow controlling the max buffer sizes via --max-buf-size to something smaller than 2**64
  so we don't get too large buffers as counterexamples
- More symbolic overapproximation for Balance and ExtCodeHash opcodes, fixing
  CodeHash SMT representation
- Add deployment code flag to the `equivalenceCheck` function
- PNeg + PGT/PGEq/PLeq/PLT simplification rules
- We no longer dispatch Props to SMT that can be solved by a simplification
- Allow user to change the verbosity level via `--verb`. For the moment, this is only to
  print some warnings related to zero-address dereference and to print `hemv test`'s
  output in case of failure
- Simple test cases for the CLI
- Allow limiting the branch depth and width limitation via --max-depth and --max-width
- When there are zero solutions to a multi-solution query it means that the
  currently executed branch is in fact impossible. In these cases, unwind all
  frames and return a Revert with empty returndata.
- More rewrite rules for PEq, PNeg, missing eqByte call, and distributivity for And
- Allow changing of the prefix from "prove" via --prefix in `test` mode
- More complete simplification during interpretation
- SMT-based resolving of addresses now works for delegatecall and staticcall
  opcodes as well
- UNSAT cache is now in `Solvers.hs` and is therefore shared across all threads.
  Hence, it is now active even during branch queries.
- Rewrite rule to deal with some forms of argument packing by Solidity
  via masking
- More rewrite rules for (PLT (Lit 0) _) and (PEq (Lit 1) _)
- Simplification can now be turned off from the cli via --no-simplify
- When doing Keccak concretization, and simplification is enabled,
  we do both until fixedpoint
- When gathering Keccak axioms, we simplify the bytestring that
  the keccak is applied to
- More rewrite rules for MulMod, AddMod, SHL, SHR, SLT, and SignExtend
- PLEq is now concretized in case it can be computed
- More SignExtend test cases
- Rewrite rules to deal with specific exponentiation patterns
- Added missing simplification and concretization of the SAR instruction

## Fixed
- We now try to simplify expressions fully before trying to cast them to a concrete value
  This should improve issues when "Unexpected Symbolic Arguments to Opcode" was
  unnecessarily output
- Not all testcases ran due to incorrect filtering, fixed
- Removed dead code related to IOAct in the now deprecated and removed debugger
- Base case of exponentiation to 0 was not handled, leading to infinite loop
- Better exponential simplification
- Dumping of END states (.prop) files is now default for `--debug`
- When cheatcode is missing, we produce a partial execution warning
- Size of calldata can be up to 2**64, not 256. This is now reflected in the documentation
- We now have less noise during test runs, and assert more about symbolic copyslice tests
- CopySlice rewrite rule is now less strict while still being sound
- Assumptions about reading from buffer after its size are now the same in all cases.
  Previously, they were too weak in case of reading 32 bytes.
- The equivalence checker now is able to prove that an empty store is
  equivalent to a store with all slots initialized to 0.
- Equivalence checking was incorrectly assuming that overapproximated values
  were sequentially equivalent. We now distinguish these symbolic values with
  `A-` and `B-`
- Buffer of all zeroes was interpreted as an empty buffer during parsing SMT model.
  The length of the buffer is now properly taken into account.
- It was possible to enter an infinite recursion when trying to shrink a buffer found by
  the SMT solver. We now properly detect that it is not possible to shrink the buffer.
- Pretty printing of buffers is now more robust. Instead of throwing an `internal error`,
  we now try best to print everything we can, and print an appropriate error message
  instead of crashing.
- We no longer produce duplicate SMT assertions regarding concrete keccak values.
- Ord is now correctly implemented for Prop.
- Signed and unsigned integers have more refined ranges.
- Symbolic interpretation of assertGe/Gt/Le/Lt over signed integers now works correctly.
- SignExtend is now correctly being constant-folded
- Some of our property-based testing was ineffective because of inadvertent
  simplification  happening before calling the SMT solver. This has now been fixed.
- When pranking an address, we used the non-pranked address' nonce
  to calculate the new address. This was incorrect, and lead to address clash,
  as the nonce was never incremented.
- We only report FAIL in `test` mode for assertion failures that match the
  string prefix "assertion failed", or match function selector Panic(uint256)
  with a parameter 0x1. Previously, `require(a==b, "reason")` was a cause for
  FAIL in case a!=b was possible. This has now been fixed.
- Out of bounds reads could occur in Haskell when trying to determine
  valid jump destinations. This has now been fixed.

## Changed
- Warnings now lead printing FAIL. This way, users don't accidentally think that
  their contract is correct when there were cases/branches that hevm could not
  fully explore. Printing of issues is also now much more organized
- Expressions that are commutative are now canonicalized to have the smaller
  value on the LHS. This can significantly help with simplifications, automatically
  determining when (Eq a b) is true when a==b modulo commutativity
- `hevm test`'s flag ` --verbose` is now `--verb`, which also increases verbosity
  for other elements of the system
- Add `--arrays-exp` to cvc5 options.
- We now use Options.Applicative and a rather different way of parsing CLI options.
  This should give us much better control over the CLI options and their parsing.
- block.number can now be symbolic. This only affects library use of hevm
- Removed `--smtoutput` since it was never used
- We now build with -DCMAKE_POLICY_VERSION_MINIMUM=3.5 libff, as cmake deprecated 3.5
- CheckSatResult has now been unified with ProofResult via SMTResult
- If counterexample would require a buffer that's larger than 1GB, we abandon
  shrinking it.
- If solver is not able to solve a query while attempting to shrink the model, we
  abandon the attempt gracefully instead of crashing with internal error.
- Buffers are now handled more lazily when inspecting a model, which avoids some
  unnecesary internal errors.
- EVM memory is now grown on demand using a 2x factor, to avoid repeated smaller
  increases which hurt concrete execution performance due to their linear cost.
- The concrete MCOPY implementation has been optimized to avoid freezing the whole
  EVM memory.
- We no longer accept `check` as a prefix for test cases by default.
- The way we print warnings for `symbolic` mode now matches that of `test` mode.

## [0.54.2] - 2024-12-12

## Fixed
- Fixed GitHub release action to upload release binaries

## [0.54.1] - 2024-12-12

## Fixed
- Fixed GitHub release action to create release binaries

## [0.54.0] - 2024-12-10

## Changed
- Improved printing of results. Should be more intuitive to understand what hevm found.
- More complete and precise array/mapping slot rewrite, along with a copySlice improvement
- Use a let expression in copySlice to decrease expression size
- The `--debug` flag now dumps the internal expressions as well
- hevm now uses the forge-std library's way of detecting failures, i.e. through
  reverting with a specific error code unless --assertion-type DSTest is passed
- Default max iterations is 5 now. `--max-iters -1` now signals no bound. This change is to match other
  symbolic execution frameworks' default bound and to not go into an infinite loop by default when
  there could be other, interesting and reachable bugs in the code
- Update to GHC version 9.6.5
- Abstraction-refinement is no longer an option, it was never really useful and not well-tested

## Added
- More POr and PAnd rules
- Array/Map slot decomposition can be turned off via a flag
- More PEq, PLEq, and PLT rules
- New `label` cheatcode.
- Updated Bitwuzla to newer version
- New cheatcodes `startPrank()` & `stopPrank()`
- ARM64 and x86_64 Mac along with Linux x86_64 static binaries for releases
- Tutorial for symbolic execution
- PAnd props are now recursively flattened
- Double negation in Prop are removed
- Updated forge to modern version, thereby fixing JSON parsing of new forge JSONs
- Fixed RPC fetching of contract data
- Symbolic ABI encoding for tuples, fuzzer for encoder
- Printing `Addrs` when running `symbolic` for counterexamples and reachable end states
- Improved symbolic execution tutorial
- More Mod, SMod, Div, and SDiv simplification rules
- Add `freshAddresses` field in `VMOpts` so that initial fresh address can be given as input
- Add documentation about limitations and workarounds
- More verbose error messages in case of symbolic arguments to opcode
- Tests to enforce that in Expr and Prop, constants are on the LHS whenever possible
- Support for MCOPY and TSTORE/TLOAD, i.e. EIP 5656 + 1153 + 4788
- All fuzz tests now run twice, once with expected SAT and once with expected UNSAT to check
  against incorrectly trivial UNSAT queries
- Allow --num-solvers option for equivalence checking, use num cores by default
- Preliminary support for multi-threaded Z3
- Skip over SMT generation issues due to e.g. CopySlice with symbolic arguments, and return
  partial results instead of erroring out
- Fix interpreter's MCOPY handling so that it doesn't error out on symbolic arguments
- More desciptive errors in case of a cheatcode issue
- Better and more pretty debug messages
- Many env* cheatcodes are now supported

## Fixed
- `vm.prank` is now respected during calls to create
- `concat` is a 2-ary, not an n-ary function in SMT2LIB, declare-const does not exist in QF_AUFBV, replacing
   with declare-fun
- CVC5 needs `--incremental` flag to work properly in abstraction-refinement mode
- cli.hs now uses with-utf8 so no release binary will have locale issues anymore
- Took ideas for simplification rules from "Super-optimization of Smart Contracts" paper by Albert et al.
- Printing panic uint256 as hex, not as int
- Decomposition does not take place when entire states are compared, as that would necessitate
  a different approach.
- `initial-storage` option of `hevm symbolic` is respected
- `caller` option of `hevm symbolic` is now respected
- Thanks to the new simplification rules, we can now enable more conformance tests
- Multi-threaded running of Tracing.hs was not possible due to IO race. Fixed.
- Fixed multi-threading bug in symbolic interpretation
- Fixed simplification of concrete CopySlice with destination offset beyond destination size
- Fixed a bug in our SMT encoding of reading multiple consecutive bytes from concrete index
- Fixed bug in SMT encoding that caused empty and all-zero byte arrays to be considered equal
  and hence lead to false negatives through trivially UNSAT SMT expressions
- Respect --smt-timeout in equivalence checking
- Fixed the handling of returndata with an abstract size during transaction finalization
- Error handling for user-facing cli commands is much improved
- Fixed call signature generation for test cases
- Fixing prank so it doesn't override the sender address on lower call frames

## [0.53.0] - 2024-02-23

## Changed

- Minimum distance requirements are now asserted for Keccak function calls. They assert that it's hard to generate two Keccak's that are less than 256 afar.
- Keccak concretization is now done only after all simplifications are performed. This helps with simplification pre-concretization
- Added an IllegalOverflow error in case the system tries to allocate a large amount of memory during
  abstract gas execution but concrete running. In these cases, the interpreter can out-of-heap
  as the only check is that the size allocated is less than $2**{64}$, but that is too large to fit in memory. Now,
  we check more stringently, and still return an IllegalOverflow
- Fixed `--root` option for the `test` subcommand
- Use `-Wunused-packages` and eliminate unused deps.

## Added

- Optimized smt queries that significantly improve performance when dealing with solidity mappings and arrays
- Support for using Bitwuzla as a solver
- More efficient encoding for failure in ds-test style tests
- Symbolic tests now support statically sized arrays as parameters
- `hevm test` now has a `num-solvers` parameter that controls how many solver instances to spawn
- New solc-specific simplification rules that should make the final Props a lot more readable
- Prop is now correctly ordered, better BufLength and Max simplifications of Expr,
  and further solc-specific simplifications of Expr
- Simplify earlier and don't check reachability for things statically determined to be FALSE
- New concrete fuzzer that can be controlled via `--num-cex-fuzz`
- Partial support for dynamic jumps when the jump destination can be computed
  given already available information
- Added three forking cheatcodes: `createFork`, `selectFork`, and `activeFork`

## Fixed

- Traces now correctly perform source mapping to display contract details
- Event traces now correctly display indexed arguments and argument names
- JSON reading of foundry JSONs was dependent on locale and did not work with many locales.

## [0.52.0] - 2023-10-26

This is a major breaking release that removes several user facing features and includes non trivial
breakage for library users. These changes mean the code is significantly simpler, more performant,
and allow support for new features like fully symbolic addresses.

In addition to the changes below, this release includes significant work on performance
optimization for symbolic execution.

## Added

The major new user facing feature in this release is support for fully symbolic addresses (including
fully symbolic addresses for deployed contracts). This allows tests to be writen that call
`vm.prank` with a symbolic value, making some tests (e.g. access control, token transfer logic) much
more comprehensive.

Some restrictions around reading balances from and transfering value between symbolic addresses are
currently in place. Currently, if the address is symbolic, then you will only be able to read it's
balance, or transfer value to/from it, if it is the address of a contract that is actually deployed.
This is required to ensure soundness in the face of aliasing between symbolic addresses. We intend
to lift this restriction in a future release.

### Other

- Support for `vm.deal`
- Support for `vm.assume` (this is semantically identical to using `require`, but does simplify the
    process of porting exisitng fuzz tests to be symbolic)
- the `check` prefix now recognized for symbolic tests
- `hevm test` now takes a `--number` argument to specify which block should be used when making rpc queries

## Changed

### Revert Semantics in Solidity Tests

solidity tests no longer consider reverts to be a failure, and check only for the ds-test failed bit
or user defined assertion failures (i.e. `Panic(0x01)`). This makes writing tests much easier as
users no longer have to consider trivial reverts (e.g. arithmetic overflow).

A positive (i.e. `prove`/`check`) test with no rechable assertion violations that does not have any
succesful branches will still be considered a failure.

## Removed

hevm has been around for a while, and over time has accumulated many features. We decided to remove
some of these features in the interest of focusing our attention, increasing our iteration speed and
simplifying maintainance. The following user facing features have been removed from this release:

- The visual debugger has been removed
- All concrete ds-test executors have been removed (i.e. plain, fuzzer, invariant)
- Rpc caching and state serialization has been removed (i.e. all `--cache` / `--state` flags)
- The various `DAPP_TEST` variables are no longer observed
- The `--initial-storage` flag no longer accepts a concrete prestore (valid values are now `Empty` or `Abstract`)

## Fixed

This release also includes many small bugfixes:

- CopySlice wraparound issue especially during CopyCallBytesToMemory
- Contracts deployed during symbolic execution are created with an empty storage (instead of abstract in previous versions)
- EVM.Solidity.toCode to include contractName in error string
- Better cex reconstruction in cases where branches do not refer to all input variables in calldata
- Correctly handle empty bytestring compiled contracts' JSON
- No more false positives when keccak is called with inputs of different sizes
- `test` now falls back to displaying an unecoded bytestring for calldata when the model returned by the solver has a different length the length of the arguments in the test signature.
- we now generate correct counterexamples for branches where only a subset of input variables are referenced by the path conditions
- `vm.prank` now works correctly when passed a symbolic address
- `vm.prank` now works correctly when the next call transfers value
- storage layout information will now be parsed from the output of `forge build` if it is available

## API Changes

### Reworked Storage Model / Symbolic Addresses

Adding symbolic addresses required some fairly significant changes to the way that we model storage.
We introduced a new address type to `Expr` (`Expr EAddr`), that allows us to model fully symbolic
addresses. Instead of modelling storage as a global symbolic 2D map (`address -> word -> word`) in
`vm.env`, each contract now has it's own symbolic 1D map (`word -> word`), that is stored in the
`vm.contracts` mapping. `vm.contracts` is now keyed on `Expr EAddr` instead of `Addr`. Addresses
that are keys to the `vm.contracts` mapping are asserted to be distinct in our smt encoding. This
allows us to support symbolic addresses in a fully static manner (i.e. we do not currently need to
make any extra smt queries when looking up storage for a symbolic address).

### Mutable Memory & ST

We now use a mutable representation of memory if it is currently completely concrete. This is a
significant performance improvement, and fixed a particulary egregious memory leak. It does entail
the use of the `ST` monad, and introduces a new type parameter to the `VM` type that tags a given
instance with it's thread local state. Library users will now need to either use the ST moand and
`runST` or `stToIO` to compose and sequence vm executions.

## GHC 9.4

Hevm is now built with ghc9.4. While earlier compiler versions may continue to work for now, they
are no longer explicitly tested or supported.

### Other

- Contract balances can now be fully symbolic
- Contract code can now be fully abstract. Calls into contracts with unknown code will fail with `UnexpectedSymbolicArg`.
- Run expression simplification on branch conditions
- SLoad/SStore simplifications based on assumptions regarding Keccak non-collision&preimage
- Improved Prop simplification
- CopySlice+WriteWord+ConcreteBuf now truncates ConcreteBuf in special cases
- Better simplification of Eq IR elements
- Run a toplevel constant folding reasoning system on branch conditions
- Global config via a monad, which should allow for more refactoring
- `evalProp` is renamed to `simplifyProp` for consistency
- Mem explosion in `writeWord` function was possible in case `offset` was close to 2^256. Fixed.
- BufLength was not simplified via bufLength function. Fixed.
- Add and Mul are associative, let's use that to make Expr more canonical
- `VMOpts` no longer takes an initial store, and instead takes a `baseState`
  which can be either `EmptyBase` or `AbstractBase`. This controls whether
  storage should be inialized as empty or fully abstract. Regardless of this
  setting contracts that are deployed at runtime via a call to
  `CREATE`/`CREATE2` have zero initialized storage.

## [0.51.3] - 2023-07-14

## Fixed

- Path joining on Windows
- Fixed overflow issue in stripWrites
- Automatic tests are now more reproducible

## Changed

- Removed sha3Crack which has been deprecated for keccakEqs
- Abstraction-refinement for more complicated expressions such as MULMOD

## Added

- Added flag `-f debug` to add debug flags to cabal/GHC

## [0.51.2] - 2023-07-11

## Fixed

- SMT encoding of Expr now has assertions for the range of environment values that are less than word size (256 bits).
- Trace now contains the cheat code calls
- More consistent error messages

## Changed

- SMT2 scripts are now being reprocessed to put one sexpr per line. Having sepxrs that span across multiple lines trigers a bug in CVC5.
- Removing long-running tests so we can finish all unit tests in approx 10 minutes on a current-gen laptop CPU
- Added git revision to `hevm version`

## Added

- execution traces are now shown for failed `prove_` tests

## [0.51.1] - 2023-06-02

## Fixed

- hevm now gracefully handles missing `out` directories
- Constraints are correctly propogated to the final output expression during symbolic execution

## Changed

- HEVM is now fully compliant with the Shanghai hard fork

## [0.51.0] - 2023-04-27

## Added

- `hevm` can now execute unit tests in foundry projects. Just run `hevm test` from the root of a foundry repo, and all unit tests will be executed (including prove tests).
- A new stack based loop detection heuristic
- Analysis of partial execution traces is now supported

## Changed

- `hevm dapp-test` has been replaced with `hevm test --project-type DappTools`.
- `hevm test` no longer supports parsing solidity output in the combined json format.
- The default value for `--ask-smt-iterations` has been changed to 1
- The SMT solver is never queried for branch conditions that do not occur in a loop (as determined by the loop detection heuristic)

## Fixed

- `--max-iterations` is respected in cases where path conditions have become inconsistent
- `--max-iterations` is now respected for loops with a concrete branch condition

## Fixed

- Fixed a bug where underflow was possible when transfering eth

## [0.50.5] - 2023-04-18

## Changed

- The `--storage-model` parameter has been replaced with `--initial-storage`
- The `--smttimeout` argument now expects a value in seconds not milliseconds
- The default smt timeout has been set to 5 minutes
- `hevm symbolic` now searches only for user defined assertions by default

### Fixed

- The `prank` cheatcode now transfers value from the correct address
- Fixed an off-by-one error in `EVM.Debug.srcMapCodePos`

## [0.50.4] - 2023-03-17

### Fixed

- The `--solvers` cli option is now respected (previously we always used Z3)
- The `equivalence` command now fails with the correct status code when counterexamples are found
- The `equivalence` command now respects the given `--sig` argument
- Correct symbolic execution for the `SGT` opcode

### Changed

- The `equivalence` command now pretty prints discovered counterexamples

### Added

- Implemented a shrinking algorithm for counterexamples
- A new differential fuzzing test harness that compares the concrete semantics, as well as parts of the symbolic semantics against the geth evm implementation
- The `hevm` library can now be built on Windows systems.
- `equivalence` can now be checked for fully or partially concrete calldata
- Support for function pointers in ABI

## [0.50.3] - 2023-02-17

### Fixed

- `hevm symbolic` exits with status code `1` if counterexamples or timeouts are found
- Calldata reads beyond calldata size are provably equal to zero.

### Added

- New cheatcode `prank(address)` that sets `msg.sender` to the specified address for the next call.
- Improved equivalence checker that avoids checking similar branches more than once.
- Improved simplification for arithmetic expressions
- Construction of storage counterexamples based on the model returned by the SMT solver.
- Static binaries for macos

### Changed
- SMT encoding of buffer length without using uninterpreted functions.

## [0.50.2] - 2023-01-06

### Fixed

- Arithmetic overflow in concrete `SAR` edge case ([#163](https://github.com/ethereum/hevm/pull/163))
- Unexpected abstract term application during fully concrete execution ([#163](https://github.com/ethereum/hevm/pull/163))

## [0.50.1] - 2022-12-29

### Fixed

- `hevm exec` no longer fails with `hevm: No match in record selector smttimeout`
- the `gas`, `gaslimit`, `priorityfee`, and `gasprice` cli options are now respected
- cleaner formatting for the gas value in the visual debugger

### Changed

- we now build with ghc 9.2.4 by default
- various perf improvements for concrete execution ([#157](https://github.com/ethereum/hevm/pull/157), [#152](https://github.com/ethereum/hevm/pull/152))

## [0.50.0] - 2022-12-19

### Changed

The symbolic execution engine has been rewritten. We have removed our dependency on sbv, and now
symbolic execution decompiles bytecode into a custom IR, and smt queries are constructed based on
the structure of the term in this IR.

This gives us much deeper control over the encoding, and makes custom static analysis and
simplification passes much easier to implement.

The symbolic execution engine is now parallel by default, and will distribute granular SMT queries
across a pool of solvers, allowing analysis to be scaled out horizontally across many CPUs.

more details can be found in the [architecuture](../../architecture.md) docs.

### Removed

The following cli commands have been removed:

- `abiencode`
- `rlp`
- `flatten`
- `strip-metadata`

## [0.49.0] - 2021-11-12

### Added

- Support for solc 0.8.10
- Support for solc 0.8.11

### Changed

- Clearer display for the invalid opcode (`0xfe`) in debug view
- Better error messages when trying to deploy unlinked bytecode
- `bytesX` arguments to `hevm abiencode` are automatically padded

### Fixed

- Test contracts with no code (e.g. `abstract` contracts) are now skipped
- Replay data for invariant tests is now displayed in a form that does not cause errors when used with `dapp test --replay`

## [0.48.1] - 2021-09-08

### Added

- Support for 0.8.4 custom error types in stack traces

### Changed

- Contract feching happens synchronously again.
- Invariants checked before calling methods from targetContracts.

### Fixed

- The block gas limit and basefee are now correctly fetched when running tests via rpc

## 0.48.0 - 2021-08-03

### Changed

- Updated to London hard fork!
- The configuration variable `DAPP_TEST_BALANCE_CREATE` has been renamed to `DAPP_TEST_BALANCE`
- Default `smttimeout` has been increased to 1 minute.
- A new flag has been added to hevm (`--ask-smt-iterations`) that controls the number of iterations
  at which the symbolic execution engine will stop eager evaluation and begin to query the smt
  solver whether a given branch is reachable or not.
- Contract fetching now happens asynchronously.
- Fixed no contract definition crashes
- Removed NoSuchContract failures

## 0.47.0 - 2021-07-01

### Added

- A new test runner for checking invariants against random reachable contract states.
- `hevm symbolic` can search for solc 0.8 style assertion violations, and a new `--assertions` flag
  has been added allowing users to customize which assertions should be reported
- A new cheatcode `ffi(string[])` that executes an arbitrary command in the system shell

### Changed

- Z3 is once again the default smt solver
- Updated nixpkgs to the `21.05` channel

### Fixed

- Sourcemaps for contracts containing `immutable` are now shown in the debug view.

## 0.46.0 - 2021-04-29

### Added

- Updated to Berlin! Conformant with GeneralStateTests at commit hash `644967e345bbc6642fab613e1b1737abbe131f78`.

### Fixed

- ADDMOD and MULMOD by zero yields zero.
- Address calculation for newly created contracts.
- Accomodated for the notorious "anomolies on the main network" (see yellow paper Appendix K for trivia)
- A hevm crash when debugging a SELFDESTRUCT contract.

## 0.45.0 - 2021-03-22

### Added

- Two new cheatcodes were added: `sign(uint sk, bytes message)` and `addr(uint sk)`. Taken together
  these should allow for much more ergonomic testing of code that handles signed messages.
- Symbolic execution can deal with partially symbolic bytecode, allowing for symbolic constructor arguments to be given in tests.

### Fixed

- Fixed a bug in the abiencoding.
- Fixed the range being generated by ints.
- `hevm flatten` combines the SPDX license identifiers of all source files.

### Changed

- updated `nixpkgs` to the `20.09` channel
- Arbitrary instance of AbiType can no longer generate a tuple

## 0.44.1 - 2020-02-02

### Changed

- hevm cheatcodes now accept symbolic arguments, allowing e.g. symbolic jumps in time in unit tests
- More efficient arithmetic overflow checks by translating queries to a more [intelligent form](www.microsoft.com/en-us/research/wp-content/uploads/2016/02/z3prefix.pdf).

## 0.44.0 - 2020-01-26

### Added

- `hevm` now accepts solidity json output built via `--standard-json` as
  well as `--combined-json`.
- addresses in the trace output are prefixed with `ContractName@0x...`
  if there is a corresponding contract and `@0x...` otherwise.

### Fixed

- Symbolic execution now generates calldata arguments restricted to the proper ranges,
  following the semantics of fuzzing.
- If the `--address` flag is present in `hevm exec` or `hevm symbolic`,
  it overrides the contract address at which a contract will be created.
- Address pretty printing
- Updated sbv to `8.9.5` to fix "non-const in array declaration" cvc4 issue with ds-test.

### Changed

- Use cvc4 as default smt solver

## 0.43.2 - 2020-12-10

### Changed

- The default smttimeout has been increased from 20s to 30s

## 0.43.1 - 2020-12-10

### Changed

- Counterexamples from symbolic tests now show clearer failure reasons

### Fixed

- Symbolic tests now work with RPC
- Branch selection is working again in the interactive debugger

## 0.43.0 - 2020-11-29

### Added

- A `--show-tree` option to `hevm symbolic` which prints the execution tree explored.
- Some symbolic terms are displayed with richer semantic information, instead of the black box `<symbolic>`.
- `hevm dapp-test` now supports symbolic execution of test methods that are prefixed with `prove` or `proveFail`
- The `hevm interactive` alias has been removed, as it is equivalent to `hevm dapp-test --debug`
- `hevm dapp-test --match` now matches on contract name and file path, as well as test name
- Step through the callstack in debug mode using the arrow keys

### Changed

- `dapp-test` trace output now detects ds-note events and shows `LogNote`
- create addresses are shown with `@<address>` in the trace
- `DSTest.setUp()` is only run if it exists, rather than failing
- support new ds-test `log_named_x(string, x)` (previously bytes32 keys)
- return arguments are fully displayed in the trace (previously only a single word)
- return/revert trace will now show the correct source position

## 0.42.0 - 2020-10-31

### Changed

- z3 updated to 4.8.8
- optimize SMT queries
- More useful trace output for unknown calls
- Default to on chain values for `coinbase`, `timestamp`, `difficulty`, `blocknumber` when rpc is provided
- Perform tx initialization (gas payment, value transfer) in `hevm exec`, `hevm symbolic` and `hevm dapp-test`.

### Added

- TTY commands `P` and `c-p` for taking larger steps backwards in the debuger.
- `--cache` flag for `dapp-test`, `exec`, `symbolic`, `interactive`,
  enabling caching of contracts received by rpc.
- `load(address,bytes32)` cheat code allowing storage reads from arbitrary contracts.

## 0.41.0 - 2020-08-19

### Changed

- Switched to [PVP](https://github.com/haskell/pvp/blob/master/pvp-faq.md) for version control, starting now at `0.41.0` (MAJOR.MAJOR.MINOR).
- z3 updated to 4.8.7
- Generate more interesting values in property based testing,
  and implement proper shrinking for all abi values.
- Fixed soundness bug when using KECCAK or SHA256 opcode/precompile
- Fixed an issue in debug mode where backstepping could cause path information to be forgotten
- Ensure that pathconditions are consistent when branching, and end the execution with VMFailure: DeadPath if this is not the case
- Fixed a soundness bug where nonzero jumpconditions were assumed to equal one.
- default `--smttimeout` changed from unlimited to 20 seconds
- `hevm symbolic --debug` now respects `--max-iterations`

### Added

- `hevm exec --trace` flag to dump a trace
- Faster backstepping in interactive mode by saving multiple snapshot states.
- Support for symbolic storage for multiple contracts

## 0.40 - 2020-07-22

- hevm is now capable of symbolic execution!

### Changed

As a result, the types of several registers of the EVM have changed to admit symbolic values as well as concrete ones.

- state.stack: `Word` -> `SymWord`.
- state.memory: `ByteString` -> `[SWord 8]`.
- state.callvalue: `W256` -> `SymWord`.
- state.caller: `Addr` -> `SAddr`.
- state.returndata: `ByteString` -> `[SWord 8]`.
- state.calldata: `ByteString` -> `([SWord 8], (SWord 32))`. The first element is a list of symbolic bytes, the second is the length of calldata. We have `fst calldata !! i .== 0` for all `snd calldata < i`.

- tx.value: `W256` -> `SymWord`.

- contract.storage: `Map Word Word` -> `Storage`, defined as:

```hs
data Storage
  = Concrete (Map Word SymWord)
  | Symbolic (SArray (WordN 256) (WordN 256))
  deriving (Show)
```

### Added

New cli commands:

- `hevm symbolic`: search for assertion violations, or step through a symbolic execution in debug mode.
- `hevm equivalence`: compare two programs for equivalence.

See the README for details on usage.

The new module `EVM.SymExec` exposes several library functions dealing with symbolic execution.
In particular,

- `SymExec.interpret`: implements an operational monad script similar to `TTY.interpret` and `Stepper.interpret`, but returns a list of final VM states rather than a single VM.
- `SymExec.verify`: takes a prestate and a postcondition, symbolically executes the prestate and checks that all final states matches the postcondition.

### Removed

The concrete versions of a lot of arithmetic operations, replaced with their more general symbolic counterpart.

## 0.39 - 2020-07-13

- Exposes abi encoding to cli
- Added cheat code `hevm.store(address a, bytes32 location, bytes32 value)`
- Removes `ExecMode`, always running as `ExecuteAsBlockchainTest`. This means that `hevm exec` now finalizes transactions as well.
- `--code` is now entirely optional. Not supplying it returns an empty contract, or whatever is stored in `--state`.

## 0.38 - 2020-04-23

- Exposes metadata stripping of bytecode to the cli: `hevm strip-metadata --code X`. [357](https://github.com/dapphub/dapptools/pull/357).
- Fixes a bug in the srcmap parsing introduced in 0.37 [356](https://github.com/dapphub/dapptools/pull/356).
- Fixes a bug in the abi-encoding of `bytes` with size > 32[358](https://github.com/dapphub/dapptools/pull/358).

## 0.37 - 2020-03-24

- Sourcemap parser now admits `solc-0.6.0` compiled `.sol.json` files.

## 0.36 - 2020-01-07

- Implement Istanbul support [318](https://github.com/dapphub/dapptools/pull/318)
- Fix a bug introduced in [280](https://github.com/dapphub/dapptools/pull/280) of rlp encoding of transactions and sender address [320](https://github.com/dapphub/dapptools/pull/320/).
- Make InvalidTx a fatal error for vm tests and ci.
- Suport property based testing in unit tests. [313](https://github.com/dapphub/dapptools/pull/313) Arguments to test functions are randomly generated based on the function abi. Fuzz tests are not present in the graphical debugger.
- Added flags `--replay` and `--fuzz-run` to `hevm dapp-test`, allowing for particular fuzz run cases to be rerun, or for configuration of how many fuzz tests are run.
- Correct gas readouts for unit tests
- Prevent crash when trying to jump to next source code point if source code is missing

## 0.35 - 2019-11-02

- Merkle Patricia trie support [280](https://github.com/dapphub/dapptools/pull/280)
- RLP encoding and decoding functions [280](https://github.com/dapphub/dapptools/pull/280)
- Extended support for Solidity ABI encoding [259](https://github.com/dapphub/dapptools/pull/259)
- Bug fixes surrounding unit tests and gas accounting (https://github.com/dapphub/dapptools/commit/574ef401d3e744f2dcf994da056810cf69ef84fe, https://github.com/dapphub/dapptools/commit/5257574dd9df14edc29410786b75e9fb9c59069f)

## 0.34 - 2019-08-28

- handle new solc bzzr metadata in codehash for source map
- show VM hex outputs as hexadecimal
- rpc defaults to latest block
- `hevm interactive`:
- fix rpc fetch
- scrollable memory pane
- Fix regression in VMTest compliance.
- `hevm exec` ergonomics:
- Allow code/calldata prefixed with 0x
- create transactions with specific caller nonce
- interactive help pane
- memory pane scrolling

## 0.33 - 2019-08-06

- Full compliance with the [General State Tests][245] (with the
  BlockchainTest format), using the Yellow and Jello papers as
  reference, for Constantinople Fix (aka Petersburg). Including:
- full precompile support
- correct substate accounting, including touched accounts,
  selfdestructs and refunds
- memory read/write semantics
- many gas cost corrections
- Show more information for non solc bytecode in interactive view
  (trace and storage)
- Help text for all cli options
- Enable `--debug` flag in `hevm dapp-test`

[245]: https://github.com/dapphub/dapptools/pull/245

## 0.32 - 2019-06-14

- Fix dapp-test [nonce initialisation bug][224]

[224]: https://github.com/dapphub/dapptools/pull/224

## 0.31 - 2019-05-29

- Precompiles: SHA256, RIPEMD, IDENTITY, MODEXP, ECADD, ECMUL,
  ECPAIRING, MODEXP
- Show the hevm version with `hevm version`
- Interactive mode:
- no longer exits on reaching halt
- new shortcuts: 'a' / 'e' for start / end
- allow returning to test picker screen
- Exact integer formatting in dapp-test and tty

## 0.30 - 2019-05-09

- Adjustable verbosity level for `dapp-test` with `--verbose={0,1,2}`
- Working stack build

## 0.29 - 2019-04-03

- Significant jump in compliance with client tests
- Add support for running GeneralStateTests

## 0.28 - 2019-03-22

- Fix delegatecall gas metering, as reported in
  https://github.com/dapphub/dapptools/issues/34

## 0.27 - 2019-02-06

- Fix [hevm flatten issue](https://github.com/dapphub/dapptools/issues/127)
  related to SemVer ranges in Solidity version pragmas

## 0.26 - 2019-02-05

- Format Solidity Error(string) messages in trace

## 0.25 - 2019-02-04

- Add SHL, SHR and SAR opcodes

## 0.24 - 2019-01-23

- Fix STATICCALL for precompiled contracts
- Assume Solidity 0.5.2 in tests

## 0.23 - 2018-12-12

- Show passing test traces with --verbose flag

## 0.22 - 2018-11-13

- Simple memory view in TTY

## 0.21 - 2018-10-29

- Fix Hackage package by including C header files for ethjet

## 0.20 - 2018-10-27

- Parse constructor inputs from Solidity AST

## 0.19 - 2018-10-09

- Enable experimental 'cheat' address, allowing for modification of the
  EVM environment from within the tests. Currently just the block
  timestamp can be adjusted.

## 0.18 - 2018-10-09

- Fix [duplicate address bug](https://github.com/dapphub/dapptools/issues/70)

## 0.17 - 2018-10-05

- Semigroup/Monoid fix

## 0.16 - 2018-09-19

- Move ethjet into hevm

## [0.15] - 2018-05-09

- Fix SDIV/SMOD definitions for extreme case

## [0.14.1] - 2018-04-17

- Improve PC display in TTY

## [0.14] - 2018-03-08

- Implement STATICCALL

## [0.13] - 2018-02-28

- Require specific block number for RPC debugging
- Implement RETURNDATACOPY and RETURNDATASIZE
- Fix bug where created contracts didn't get their balance

## [0.12.3] - 2017-12-19

- More useful RPC debugging because we strip the entire BZZR metadata

## [0.12.2] - 2017-12-17

- Experimental new ecrecover implementation via libethjet
- Correct error checking for setUp() invocations

## [0.12.1] - 2017-11-28

- Test name regex matching via --match
- Fixed source map parsing bug when used with solc --optimize
- TTY: fix a padding-related display glitch

## [0.12] - 2017-11-14

- Use 13 different environment variables to control block parameters
  for unit testing, e.g. block number, timestamp, initial balance, etc.

  Full list:

  - `DAPP_TEST_ADDRESS`
  - `DAPP_TEST_CALLER`
  - `DAPP_TEST_ORIGIN`
  - `DAPP_TEST_GAS_CREATE`
  - `DAPP_TEST_GAS_CALL`
  - `DAPP_TEST_BALANCE_CREATE`
  - `DAPP_TEST_BALANCE_CALL`
  - `DAPP_TEST_COINBASE`
  - `DAPP_TEST_NUMBER`
  - `DAPP_TEST_TIMESTAMP`
  - `DAPP_TEST_GAS_LIMIT`
  - `DAPP_TEST_GAS_PRICE`
  - `DAPP_TEST_DIFFICULTY`

## [0.11.5] - 2017-11-14

- Use --state with --exec --debug

## [0.11.4] - 2017-11-12

- Fix bug when unit test contract has creations in constructor

## [0.11.3] - 2017-11-08

- Fix array support in ABI module

## [0.11.2] - 2017-11-04

- TTY: show a help bar with key bindings at the bottom

## [0.11.1] - 2017-11-02

- TTY: fix a display glitch
- TTY: improve display of ABI hashes on the stack

## [0.11] - 2017-10-31

- Add "hevm flatten" for Etherscan-ish source code concatenation
- Simplify code by removing concrete/symbolic machine abstraction

## [0.10.9] - 2017-10-23

- Fix bugs in ABI formatting

## [0.10.7] - 2017-10-19

- Fix library linking bug
- Fix gas consumption of DELEGATECALL
- Better error tracing
- Experimental "contract browser" (stupid list of addresses)

## [0.10.6] - 2017-10-19

- Enable library linking for unit tests and debugger
- Use the same default gas/balance values as `ethrun`

## [0.10.5] - 2017-10-17

- Better trace output including arguments and return values
- Proof of concept coverage analysis via `dapp-test --coverage`

## [0.10] - 2017-10-10

- Enable new trace output by default for failing tests
- Exit with failure code from test runner when tests fail
- More fixes to improve Ethereum test suite compliance

## [0.9.5] - 2017-10-06

- Prototype of new trace output with `hevm dapp-test --verbose`
- Nicer trace tree in the TTY debugger
- Many fixes to improve Ethereum test suite compliance

## [0.9] - 2017-09-29

- Integrates with live chains via RPC (read-only)
- Exposes a special contract address with test-related functionality (time warp)

## [0.8.5] - 2017-09-22

- Renames `hevm` from its maiden name `hsevm` :sparkles:

## [0.8] - 2017-09-21

- Implements gas metering (Metropolis rules by default)
- Shows gas counter in the terminal interface
- Enables debugger for consensus test executions
- Consensus test runner script with HTML reporting
- Passes 564 of the `VMTests`; fails 115 (see [0.8 test report])
- Command line options for specifying initial gas amounts and balances
- Improved TTY UI layout

## [0.7] - 2017-09-07

- Can save and load contract states to disk using a Git-backed store (only `--exec`)
- Can debug raw EVM bytecode using `exec --debug`
- Fixes `exec --value`
- Has smarter defaults for command line when running tests or debugging
- Fixes bug with `MSIZE` in `CALL` context

## [0.6.5] - 2017-09-01

- Fixes `exec` with regards to exit codes and error messages

## [0.6.1] - 2017-08-03

- TTY: Adds command `C-n` in TTY for "stepping over"

## [0.6] - 2017-08-03

- TTY: Adds second line to stack entries with humanized formatting
- TTY: Gets rid of the separate log pane in favor of a unified trace pane

## [0.5] - 2017-08-02

- TTY: Adds `p` command for stepping backwards
- Adds ability to track origins of stack and heap words
- Tracks Keccak preimage for words that come from the `SHA3` instruction

## [0.4] - 2017-07-31

- Parallelizes unit test runner
- Improves speed by changing representation of memory
- Internal refactoring for future support of symbolic execution
- Adds logs to the trace pane

## [0.3.2] - 2017-06-17

- Adds `REVERT` opcode
- Sets `TIMESTAMP` value to `1` in unit tests

## [0.3.0] - 2017-06-14

- Reverts contract state after `CALL` fails
- Improves test runner console output

## [0.2.0] - 2017-06-13

- Fixes bug in `CALL`

## [0.1.0.1] - 2017-03-31

- Highlights Solidity exactly on character level
- Adds `N` command for stepping by Solidity source position instead of by opcode

## 0.1.0.0 - 2017-03-29

- First release

[0.8 test report]: https://hydra.dapp.tools/build/135/download/1/index.html
[0.12]: https://github.com/dapphub/hevm/compare/0.11.5...0.12
[0.11.5]: https://github.com/dapphub/hevm/compare/0.11.4...0.11.5
[0.11.4]: https://github.com/dapphub/hevm/compare/0.11.3...0.11.4
[0.11.3]: https://github.com/dapphub/hevm/compare/0.11.2...0.11.3
[0.11.2]: https://github.com/dapphub/hevm/compare/0.11.1...0.11.2
[0.11.1]: https://github.com/dapphub/hevm/compare/0.11...0.11.1
[0.11]: https://github.com/dapphub/hevm/compare/0.10.9...0.11
[0.10.9]: https://github.com/dapphub/hevm/compare/0.10.7...0.10.9
[0.10.7]: https://github.com/dapphub/hevm/compare/0.10.6...0.10.7
[0.10.6]: https://github.com/dapphub/hevm/compare/0.10.5...0.10.6
[0.10.5]: https://github.com/dapphub/hevm/compare/0.10...0.10.5
[0.10]: https://github.com/dapphub/hevm/compare/0.9.5...0.10
[0.9.5]: https://github.com/dapphub/hevm/compare/0.9...0.9.5
[0.9]: https://github.com/dapphub/hevm/compare/v0.8.5...v0.9
[0.8.5]: https://github.com/dapphub/hevm/compare/v0.8...v0.8.5
[0.8]: https://github.com/dapphub/hevm/compare/v0.7...v0.8
[0.7]: https://github.com/dapphub/hevm/compare/v0.6.5...v0.7
[0.6.5]: https://github.com/dapphub/hevm/compare/v0.6.1...v0.6.5
[0.6.1]: https://github.com/dapphub/hevm/compare/v0.6...v0.6.1
[0.6]: https://github.com/dapphub/hevm/compare/v0.5...v0.6
[0.5]: https://github.com/dapphub/hevm/compare/v0.4...v0.5
[0.4]: https://github.com/dapphub/hevm/compare/v0.3.2...v0.4
[0.3.2]: https://github.com/dapphub/hevm/compare/v0.3.0...v0.3.2
[0.3.0]: https://github.com/dapphub/hevm/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/dapphub/hevm/compare/v0.1.0.1...v0.2.0
[0.1.0.1]: https://github.com/dapphub/hevm/compare/v0.1.0.0...v0.1.0.1
