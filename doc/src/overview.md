# Overview

The `hevm` project is an implementation of the Ethereum Virtual Machine (EVM) focused on symbolic
analysis of evm bytecode. It can:

- symbolically execute a smart contract and find reachable assertion violations
- prove equivalence of two different bytecode objects
- execute symbolic solidity tests written using [`ds-test`](https://github.com/dapphub/ds-test/) (a.k.a "foundry tests")
- fetch remote state via rpc
- automatically create test cases

It was originally developed as part of the [dapptools](https://github.com/dapphub/dapptools/) project, and was forked to this repo by the formal methods team at the Ethereum Foundation in August 2022.
