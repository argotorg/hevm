# Completeness Warnings and False Positives

hevm attempts to give no false negatives without warnings, but can sometimes
give false positives. Whenever hevm could not prove the absence of negatives,
it prints a warning(`[WARN]`). While hevm attempts to give no false negatives,
it can, in rare occasions, give false positives, indicated by `[not
reproducible]`. This section explains why these happen, and how to interpret
them.

## Completeness Warnings

When hevm gives a completeness warning, it is indicating that it had to
give up exploration because of certain factors during symbolic execution.
Hence, it may be possible that some assertion violations could be violated, but
hevm could not explore that path.

These warnings are prefixed with `[WARN]` and are collated together with the text
`hevm was only able to partially explore XYZ due to:` and can be either:
* A set of error(s), such as SMT solver internal errors, or SMT translation
  issues related to dynamic datastructures
* A set of unknown result(s) from the SMT solver, such as timeouts
* A set of partial executions, such as missing implementation of a precompile,
  cheatcode, etc.

Partial executions are usually the most common cause of incompleteness. They can be
due to:
* *Unexpected symbolic argument to an opcode* For example, if a symbolic address is given to
  a `CALL` instruction, hevm will not be able to determine which contract is being called,
  and hence will not be able to explore that path. This can be alleviated with the option
  `--only-deployed`, which will restrict the analysis to only the contracts that are deployed
  during the `setUp()` phase of the test.
* *Maximum iterations reached* This happens when we have too many iterations in a loop,
  and we have reached the maximum number of iterations allowed. This can be configured
  with the `--max-iterations` option.
* *Jump into symbolic code* This can happen in case the contract generates code at runtime,
  deploys it, and jumps into it. hevm does not support this, and will give up exploration.
* *Branch too deep* This happens when the call depth has been limited via the `--max-depth`
  option, and hevm has reached that limit during exploration.
* *Cheat code missing* This happens when a cheatcode is called that is not yet implemented
  in hevm.

## False Positives

hevm attempts to validate every counterexample it can find. In case the
counterexample validates, it marks it via `[validated]`. In case there is an
error in validating the counterexample, it marks it via `[error attempting to
reproduce...]`. When the counterexample cannot be validated, it marks it via
`[not reproducible]`.

False positives can happen in two different scenarios. Firstly, in some cases,
hevm attempts to overapproximate the behaviour of the EVM, so that it doesn't
have to give up exploration. However, this overapproximation can lead to
behaviour that is not actually possible in the real world. This kind of
overapproximation happens mostly with a STATICCALL to an unknown address.

Secondly, false positives can happen, because hevm overapproximates the Keccak
hash function via a so-called uninterpreted function. This means that hevm does
not precisely model the Keccak function, but instead treats it as a black box.
This can lead to keccak hash pairs that are not possible in the real
world.
