# Exploit demos: hevm finds the bug on a mainnet fork

Each demo forks mainnet at the block before the exploit, makes the attacker's
inputs symbolic, and asserts an invariant the developers could have written
before deployment. hevm must produce the counterexample, which we then replay
concretely against the same fork.

## 1. Resupply (26 Jun 2025, ~$9.6M)

- Exploit tx `0xffbbd492e0605a8bb6d490c3cd879e87ff60862b0684160d08fd5711e7a872d3`,
  block 22785461 (the attack runs in a contract constructor). Fork at 22785460.
- ResupplyPair `0x6e90c85a495d54c6d7e1f3400fef1f6e59f86bd6`, collateral is the
  near-empty cvcrvUSD ERC4626 vault.
- Bug: `_exchangeRate = 1e36 / oracle.getPrices(collateral)`. Donating to the
  vault pushes the share price above 1e36, the rate rounds to 0, and the LTV
  check `_ltv <= _maxLTV` passes for any borrow against 1 wei of collateral.
- Property: with symbolic donation, deposit and borrow amounts, a successful
  `borrow` never exceeds collateral value * max LTV.

## 2. Truebit (8 Jan 2026, ~$26.6M)

- Exploit tx `0xcd4755645595094a8ab984d0db7e3b4aabde72a5c87c4f176a030629c47fb014`,
  block 24190507. Fork at 24190506.
- Purchase contract (proxy) `0x764c64b2a09b09acb100b80d8c505aa6a0302ef2`,
  implementation `0xc186e6f0163e21be057e95aa135edd52508d14d3` (never
  source-verified), TRU token `0xf65b5c5104c4fafd4b709d9d60a185eae063276c`.
  The proxy held ~8535 ETH.
- Bug: `getPurchasePrice(amount)` is computed without overflow checks
  (pre-0.8 Solidity). For `amount = 240442509453545333947284131` the numerator
  wraps and the price is 0, so `buyTRU` mints ~240M TRU for free, which
  `sellTRU` turns into ETH. Repeated four more times in the same transaction.
- Property: with symbolic `amount`, buying at `getPurchasePrice(amount)` and
  then selling the same amount never returns more ETH than was paid.
- Selling point: hevm works on bytecode, no source needed.

## 3. Abracadabra `cook()` (4 Oct 2025, ~$1.8M)

- Cauldron V4 `cook(actions, values, datas)`: action 5 (borrow) sets
  `needsSolvencyCheck`, a following action 0 resets the cook status, so the
  final solvency check is skipped.
- Property: with 2-3 symbolic action ids and symbolic parameters, the caller
  is solvent after `cook` returns.
- Tx, block and addresses: TBD.

## hevm work these need

- Replay counterexamples against RPC-fetched state (`cli/cli.hs` currently
  says "state fetched over RPC is not replayed").
- Fetch only what execution touches. Accounts and concrete slots are already
  fetched lazily and cached; symbolic slots on fetched contracts are
  concretized (`accessStorage` in `src/EVM.hs`), which can multiply fetches.
- Solver performance on the non-linear overflow search (Truebit).
