# `hevm exec`

Run an EVM computation using specified parameters.

```plain
Usage: hevm exec [--code ARG] [--code-file ARG] [--project-type ARG] [--create]
                 [--json-trace] [--address ARG] [--caller ARG] [--origin ARG]
                 [--coinbase ARG] [--value ARG] [--nonce ARG] [--gas ARG]
                 [--number ARG] [--timestamp ARG] [--basefee ARG]
                 [--priority-fee ARG] [--gaslimit ARG] [--gasprice ARG]
                 [--maxcodesize ARG] [--prev-randao ARG] [--chainid ARG]
                 [--rpc ARG] [--block ARG] [--ask-smt-iterations ARG]
                 [--loop-detection-heuristic ARG] [--no-decompose]
                 [--solver ARG] [--debug] [--calldata ARG] [--trace]
                 [--verb ARG] [--root ARG] [--assertion-type ARG]
                 [--smt-timeout ARG] [--smt-memory ARG] [--smtdebug]
                 [--dump-unsolved ARG] [--num-solvers ARG]
                 [--max-iterations ARG] [--promise-no-reent]
                 [--max-buf-size ARG] [--max-width ARG] [--max-depth ARG]
                 [--no-simplify] [--only-deployed] [--cache-dir ARG]
```

Concretely execute a given EVM bytecode with the specified parameters. Minimum
required flags: either you must provide `--code` or you must both pass `--rpc`
and `--address`. For a full listing of options, see `hevm exec --help`.

If the execution returns an output, it will be written
to stdout. Exit code indicates whether the execution was successful or
errored/reverted.

## Simple example usage

```shell
$ hevm exec --code 0x647175696e6550383480393834f3 --gas 0xff
"Return: 0x647175696e6550383480393834f3"
```

Which says that given the EVM bytecode `0x647175696e6550383480393834f3`, the Ethereum
Virtual Machine will put `0x647175696e6550383480393834f3` in the RETURNDATA.

To execute a mainnet transaction:

```shell
$ export ETH_RPC_URL=https://mainnet.infura.io/v3/YOUR_API_KEY_HERE
$ export TXHASH=0xd2235b9554e51e8ff5b3de62039d5ab6e591164b593d892e42b2ffe0e3e4e426
hevm exec --caller $(cast tx $TXHASH from) --address $(cast tx $TXHASH to) \
    --calldata $(cast tx $TXHASH input) --rpc $ETH_RPC_URL \
    --block $(($(cast tx $TXHASH blockNumber)-1)) --gas $(cast tx $TXHASH gas)
```
