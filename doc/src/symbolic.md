# `hevm symbolic`

```plain
Usage: hevm symbolic [--code TEXT] [--code-file STRING] [--calldata TEXT] [--address ADDR]
                     [--caller ADDR] [--origin ADDR] [--coinbase ADDR]
                     [--value W256] [--nonce WORD64] [--gas WORD64]
                     [--number W256] [--timestamp W256] [--basefee W256] ...
```

Run a symbolic execution against the given parameters, searching for assertion
violations. For a full listing of options, see `hevm symbolic --help`.
For common options, see [here](./common-options.md).

Counterexamples are returned for any reachable assertion violations. Where
an assertion violation is defined as either an execution of the invalid opcode
(`0xfe`), or a revert with a message of the form
`abi.encodeWithSelector('Panic(uint256)', errCode)` with `errCode` being one of
the predefined solc assertion codes defined
[here](https://docs.soliditylang.org/en/latest/control-structures.html#panic-via-assert-and-error-via-require).

Each counterexample is replayed on a concrete EVM, and marked `[validated]` if the
replay violates the assertion too, or `[not reproducible]` if it does not. Runs
that fetch state over RPC, and contract creation, are not replayed.

## Arithmetic overflow

By default hevm ignores assertion violations that result from arithmetic
overflow (`Panic(0x11)`), although this behaviour can be customised via the
`--assertions` flag. For example, the following will return counterexamples for
arithmetic overflow (`0x11`) and user defined assertions (`0x01`):

```
hevm symbolic --code $CODE --assertions '[0x01, 0x11]'
```

The default value for `calldata` and `caller` are symbolic values, but can be
specialized to concrete functions with their corresponding flags. So is the
timestamp (`--timestamp`), and, unless `--rpc` is given, the block number, base
fee and prevrandao (`--number`, `--basefee`, `--prev-randao`). The gas price is
0 unless `--gasprice` is given.

## Specializing calldata

One can also specialize specific arguments to a function signature, while
leaving others abstract. If `--sig` is given, calldata is assumed to be of the
form suggested by the function signature. With this flag, specific arguments
can be instantiated to concrete values via the `--arg` flag.

This is best illustrated through a few examples:

Calldata specialized to the bytestring `0xa9059cbb` followed by 64 symbolic bytes:

```shell
hevm symbolic --sig "transfer(address,uint256)" --code $(<dstoken.bin-runtime)
```

Calldata specialized to the bytestring
`0xa9059cbb0000000000000000000000007cfa93148b0b13d88c1dce8880bd4e175fb0dedf`
followed by 32 symbolic bytes.

```shell
hevm symbolic --sig "transfer(address,uint256)" --arg 0x7cFA93148B0B13d88c1DcE8880bd4e175fb0DeDF --code $(<dstoken.bin-runtime)
```

Calldata specialized to the bytestring `0xa9059cbb` followed by 32 symbolic
bytes, followed by the bytestring
`0000000000000000000000000000000000000000000000000000000000000000`:

```shell
hevm symbolic --sig "transfer(address,uint256)" --arg "<symbolic>" --arg 0 --code $(<dstoken.bin-runtime)
```

Values are written as: decimal or `0x` hex numbers (negative ones like `-1` for
`int<N>`), `true`/`false`, `0x` hex for `bytesN` and `bytes`, a double-quoted
string for `string`, and `[a,b,...]` for arrays. Tuple arguments cannot be given
concretely.

If the `--get-models` flag is given, example input values will be returned for
each possible execution path. This can be useful for automatic test case
generation.

The default timeout for SMT queries is no timeout. If your program is taking
longer than a couple of minutes to run, you can experiment with configuring the
timeout to somewhere around 10s by doing `--smttimeout 10000`

## Storage

Storage can be initialized in two ways:

- `Empty`: all storage slots for all contracts are initialized to zero
- `Abstract`: all storage slots are initialized as unconstrained abstract values

## Exploration strategy

`hevm` uses an eager approach for symbolic execution, meaning that it will
first attempt to explore all branches in the program (without querying the smt
solver to check if they are reachable or not). Once the full execution tree has
been explored, the postcondition is checked against all leaves, and the solver
is invoked to check reachability for branches where a postcondition violation
could occur. While our tests have shown this approach to be significantly
faster, when applied without limits it would always result in infinite
exploration of code involving loops, so after some predefined number of
iterations (controlled by the `--ask-smt-iterations` flag), the solver will be
invoked to check whether a given loop branch is reachable. In cases where the
number of loop iterations is known in advance, you may be able to speed up
execution by setting this flag to an appropriate value.

## Further reading

For a tutorial on symbolic execution with `hevm`, see the [the page
here](symbolic-execution-tutorial.html).
An older blog post on symbolic execution with `hevm` can be found
[here](https://fv.ethereum.org/2020/07/28/symbolic-hevm-release).
