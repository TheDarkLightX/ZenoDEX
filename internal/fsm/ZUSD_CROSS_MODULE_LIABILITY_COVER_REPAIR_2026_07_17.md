# zUSD Cross-Module Liability Cover Repair

Date: 2026-07-17
Profile: `zenodex/zusd-liquity-v1-minimum`
Status: implemented locally; targeted evidence green; broader promotion gates pending

## Counterexample

At the pre-repair boundary, canonical zUSD moved from a wallet into a DEX pool
disappeared from `_assert_free_debt_liability_cover`. The DEX transition was
locally conserving, yet the next stream-11 operation rejected permanently:

```text
mint 1,000 zUSD
create pool with 900 zUSD
wallet cover observed by stream 11 = 100 zUSD
core free debt = 1,000 zUSD
next repay rejects with a 900 zUSD mismatch
```

This was a composition-spec omission. The pool reserve remained present and
spendable in DEX state. The zUSD shell's global inventory did not represent it.

## ShapeForge working model

```text
Phi := <
  M   = committed Tau app state plus committed zUSD monetary state,
  S   = cross-module canonical-zUSD custody composition,
  A   = add DEX-pool custody as an explicit free-debt domain,
  T   = exact typed liability breakdown plus pre/post shell checks,
  V   = wallet, pool, perps, three fee domains, SP escrow, core debt,
  O   = global liability-cover decision,
  G   = exact nonnegative integer E8 amounts and committed policy binding,
  Obs = accept/reject, expected cover, actual debt, published app root,
  K   = canonical asset id and SP principal from committed runtime policy,
  E   = BDD, typed Python core, replay regression, mutation replay, Lean theorem,
  Gap = runtime extraction completeness still requires custody-domain audit,
  N   = local conservation does not imply cross-module liability cover,
  Delta = enumerate and check every authoritative canonical-zUSD location
>
```

## Normative relation

Let all terms be E8-denominated nonnegative integers:

```text
free_debt =
    wallet_zusd
  + dex_pool_zusd
  + perps_zusd
  + protocol_fee_reserve_zusd
  + staking_fee_pool_zusd
  + host_fee_pool_zusd

sp_debt = stability_pool_ledger_zusd
```

Wallet-to-pool movement of amount `x <= wallet_zusd` preserves the first sum:

```text
(wallet_zusd - x) + (dex_pool_zusd + x)
= wallet_zusd + dex_pool_zusd
```

The shell derives the canonical asset and SP principal from the committed zUSD
runtime policy. It checks the relation after loading state and after composing
all app streams. A rejected check returns the original serialized state and
publishes no state hash or balance patch.

## Construction and authority

- `ZUSDFreeDebtLiabilityBreakdown` is a frozen, slotted value with one named
  field per free-debt custody domain.
- Booleans, floats, strings, and negative amounts cannot enter the pure
  liability decision.
- The pure decision has no state, I/O, clock, signature, or commit authority.
- The integration bridge alone extracts amounts from committed runtime state.
- Pool extraction is deterministic by sorted pool id and counts either reserve
  side when its asset equals canonical zUSD.
- The app shell checks both prestate and the fully composed poststate, covering
  token, DEX, perps, proof-mining, and zUSD stream interactions.

## Evidence map

| Claim | Evidence |
|---|---|
| exact typed sum | `src/core/zusd_liability_cover.py` and core tests |
| wallet-to-pool sum preservation | `Proofs/ZUSDGlobalLiabilityCover.lean` |
| legitimate pool liquidity remains live | app-bridge replay regression |
| counterfeit pool reserve rejects atomically | mutated-snapshot replay regression |
| shell binds pool reserve extraction | integration regression over serialized `DexState` |

## Explicit nonclaims

- The Lean theorem proves the abstract arithmetic relation, not completeness of
  the runtime custody inventory.
- Python/Lean agreement does not prove perps' internal liability extraction is
  economically complete; that remains a separately audited binding claim.
- This repair does not complete Liquity V1 vault, redistribution, redemption,
  oracle, shutdown, migration, or multi-vault semantics.
- No production-ready zUSD or release-green claim is made by this slice.
