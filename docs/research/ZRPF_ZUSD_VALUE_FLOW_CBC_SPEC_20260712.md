# ZRPF zUSD Value-Flow CBC Specification

Date: 2026-07-12

Status: proof-neutral deterministic reference under implementation; no receipt
or settlement authority

## Disaster state

A local zUSD transition can change collateral, debt supply, stability-pool
escrow, protocol fees, or liquidation balances. A recursive root is unsafe if
it treats an incomplete mint-only row as complete lifecycle conservation.

## Typed reference scope

The V1 reference covers these value-moving operations:

```text
deposit collateral
withdraw collateral
mint principal plus rounded-up fee
repay and burn
stability-pool deposit
stability-pool withdrawal
redeem and burn with floor-priced collateral plus rounded-up fee
liquidate with stability-pool burn and capped liquidator compensation
```

Each operation produces deterministic one-sided rows. For each asset:

```text
sum(debit_atoms) + sum(authorized_mint_atoms)
  = sum(credit_atoms) + sum(authorized_burn_atoms)
```

| Operation | Derived rows |
| --- | --- |
| Deposit collateral | depositor debit; vault credit |
| Withdraw collateral | vault debit; recipient credit |
| Mint | recipient mint-credit principal; optional protocol mint-credit fee |
| Repay | payer burn-debit |
| Stability-pool deposit | depositor debit; stability-pool credit |
| Stability-pool withdrawal | stability-pool debit; recipient credit |
| Redeem | redeemer burn-debit; vault collateral debit; redeemer and optional protocol collateral credits |
| Liquidate | stability-pool burn-debit; vault collateral debit; optional stability-pool and liquidator collateral credits |

Fee and compensation arithmetic mirrors the current single-vault zUSD core:

```text
ceil(a * b / 10_000) = (a * b + 9_999) / 10_000
redemption_gross_collateral = floor(zusd_atoms * 100_000_000 / oracle_price_e8)
liquidator_comp = min(collateral, fixed_comp + ceil(collateral * comp_bps / 10_000))
```

All products and sums use checked `u128` arithmetic. Inputs are capped at the
current zUSD amount domain of `10^30` atoms. Operations and rows are bounded,
sorted by action and leg index, duplicate action indices reject, and the exact
proposal codec rejects trailing, oversized, and noncanonical bytes.

The arithmetic formulas mirror `src/core/zusd.py` and the promoted single-vault
Rust shadow in `rust-runtime/crates/zenodex-runtime-core/src/zusd.rs`. Fixed
vectors cover upward rounding, downward redemption conversion, compensation
capping, and zero-fee or zero-compensation row omission. This slice does not
provide a full transition differential against either runtime.

## Authority boundary

The source-transition hash, receipt-claim hash, and oracle-binding hashes are
host-proposed commitments. The reference binds their identity and derives row
structure. A future guest and sealed verifier must authenticate the governed
source transition, exact receipt, image ID, policy, oracle binding, and state
continuity before these rows may enter an authority-bearing root.

The operation ID is proposal-local structural identity. It is not an
authenticated global economic-action nullifier. A future authority path must
derive the economic identity independently of source program, proof encoding,
lane assignment, and task identity before enforcing global uniqueness.

## Required negative evidence

- zero, oversized, overflow-risk, or aliased-scope operation;
- duplicate action index;
- missing, duplicated, reordered, relabeled, or unbalanced row;
- wrong mint or burn authority;
- fee consuming all redeemed collateral;
- source-transition, receipt-claim, or oracle-binding substitution;
- operation or row count above the governed bound;
- trailing, oversized, or noncanonical proposal bytes.

## Explicit non-claims

This reference authenticates no receipt or guest execution. It does not prove
oracle truth, MCR or recovery-mode validity, external collateral finality,
account balances, source state continuity, data availability, durable atomic
admission, settlement authority, release authority, privacy, throughput, or
production readiness. The mixed mint-and-burn proposal also does not map
directly into the historical V1 aggregate row shape, which permits only one
authority root per aggregated asset row.

## Next authority step

Implement a zUSD lifecycle guest that derives the same operations and rows from
a checked pre-state, command, and post-state. Then add a sealed verifier, fresh
receipt evidence, exact mutation rejects, and atomic ZenoLedger application of
the authenticated effect plan.
