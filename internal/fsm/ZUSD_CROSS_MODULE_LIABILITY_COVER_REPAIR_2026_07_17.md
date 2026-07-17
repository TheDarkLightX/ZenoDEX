# zUSD Cross-Module Liability Cover Repair

Date: 2026-07-17
Profile: `zenodex/zusd-liquity-v1-minimum`
Status: pure complete relation implemented; mounted extraction still pending

## Counterexamples

### Omitted DEX custody

At the pre-repair boundary, canonical zUSD moved from a wallet into a DEX pool
disappeared from the free-debt inventory. The DEX transition was locally
conserving, yet the next stream-11 operation rejected permanently:

```text
mint 1,000 zUSD
create pool with 900 zUSD
wallet cover observed by stream 11 = 100 zUSD
core free debt = 1,000 zUSD
next repay rejects with a 900 zUSD mismatch
```

### Omitted Gas Pool reserve

The first repair enumerated wallets, DEX pools, perps, and three fee domains,
but called that six-domain sum complete. Liquity-minimum liquidation separately
requires each active vault's fixed zUSD reserve to remain in Gas Pool custody
until it transfers to the keeper without mint or burn. Omitting that domain
would make a semantically complete open-vault state unrepresentable or force the
reserve to masquerade as an unrelated wallet or fee balance.

## Normative relation

Let all terms be nonnegative source-unit integers:

```text
free_debt =
    wallet_zusd
  + dex_pool_zusd
  + perps_zusd
  + protocol_fee_reserve_zusd
  + staking_fee_pool_zusd
  + host_fee_pool_zusd
  + gas_pool_reserve_zusd

sp_debt = stability_pool_ledger_zusd

total_debt = free_debt + sp_debt

total_debt = enumerated_free_liabilities + stability_pool_ledger_zusd
```

The complete decision preserves four independent obligations in canonical
order:

1. enumerated free liabilities equal core free debt;
2. Stability Pool custody equals core Stability Pool debt;
3. core free debt plus core Stability Pool debt equals core total debt;
4. all externally owned scoped liabilities equal core total debt.

A failure in one obligation does not hide another failure.

## Preserving movements

Wallet-to-pool movement of `x <= wallet_zusd` preserves free and global cover:

```text
(wallet_zusd - x) + (dex_pool_zusd + x)
= wallet_zusd + dex_pool_zusd
```

Gas-Pool-to-keeper movement of `g <= gas_pool_reserve_zusd` also preserves free
and global cover without mint or burn:

```text
(wallet_zusd + g) + (gas_pool_reserve_zusd - g)
= wallet_zusd + gas_pool_reserve_zusd
```

Both preservation theorems are machine checked in Lean.

## Construction and authority

- `ZUSDFreeDebtLiabilityBreakdown` is a frozen, slotted value with one named
  field per admitted free-debt custody domain, including Gas Pool reserve.
- Every component and aggregate is checked in the U256 domain.
- `ZUSDGlobalDebtCoverDecision` contains a unique, canonically ordered tuple of
  every failed equality and rederives that tuple in its constructor.
- Booleans, floats, strings, negative values, overflowed components, overflowed
  sums, forged decisions, duplicate violations, and reordered violations reject.
- These values perform no I/O, signature checking, extraction, or commit. They
  cannot authorize a live transition by themselves.
- A mounted shell must extract each domain from the same committed snapshot,
  call the pure relation on loaded prestate and fully composed poststate, and
  atomically reject before publishing any state root or effect when violations
  are nonempty.

## Evidence map

| Claim | Evidence |
|---|---|
| exact typed free-liability sum | `src/core/zusd_liability_cover.py` and core tests |
| exact typed global debt/custody relation | `src/core/zusd_global_debt_cover.py` and core tests |
| wallet-to-pool preservation | `Proofs/ZUSDGlobalLiabilityCover.lean` |
| Gas-Pool-to-keeper preservation | `Proofs/ZUSDGlobalLiabilityCover.lean` |
| component cover implies global cover | `Proofs/ZUSDGlobalDebtCover.lean` |
| independent failed obligations survive | canonical violation-vector regression |

## Explicit nonclaims

- The Lean theorems prove arithmetic relations over supplied inventories, not
  completeness of mounted runtime extraction.
- Python/Lean agreement does not prove that perps, pools, fee ledgers, Gas Pool,
  or Stability Pool are read from one atomic committed snapshot.
- This repair does not yet mint the fixed Gas Pool reserve when opening a vault
  or transfer it during mounted liquidation.
- It does not complete redistribution, Recovery Mode liquidation, redemption,
  owner close, shutdown, migration, or multi-vault semantics.
- No production-ready zUSD, runtime refinement, settlement authority, or
  release-green claim is made by this slice.
