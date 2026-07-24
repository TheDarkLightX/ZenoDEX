# Spot V7 state/effect binding kernel

This standalone `no_std` crate closes one proof-neutral relation for the
restricted singleton Spot profile:

```text
complete bounded pre/post snapshots
  + exact Spot state-root V7 journal
  -> recomputed legacy app and nonce commitments
  -> recomputed state-root-v5 pre/post roots
  -> four typed account/pool balance transitions
  -> exact canonical V7 SettlementEffectPlanV2 derived inside the kernel
  -> fixed state/effect binding journal
```

The four permitted cell transitions are:

1. sender input-asset debit;
2. pool input-reserve credit;
3. pool output-reserve debit;
4. recipient output-asset credit.

The kernel rejects extra state changes, changed pool metadata, changed LP or
fee state, mismatched state roots, mismatched action semantics, mismatched
effect commitments, substituted cell hashes, substituted asset amounts, and
messages, carry rows, or rewards.

This bounded kernel does not establish intent-signature validity, swap-price or
CPMM arithmetic, slippage policy, source-child receipt authority, or blob
availability. Those facts must arrive through the authenticated semantic
execution and replay path before this state/effect projection can be promoted.

## Two-plan contract

The source and derived plans serve different purposes:

```text
Plan A: authenticated V6 source plan
  one opaque sparse-state cell write
  exact bytes reopened from the authenticated V6 child
  supplies application, domain, action type, authorization, epoch, policy,
  grant, and consumed-object lineage

Plan B: derived V7 state/effect plan
  four typed cell writes and two exact ordinary asset effects
  created only by this kernel from Plan A lineage plus complete state openings
  never supplied as an independently selectable host plan
```

Plan B preserves the authorization grant-spend identity because application,
domain, grant, and nonce remain unchanged. Its action ID changes because the
state root, exact semantics, effect commitment, and consumed lineage are more
specific. The binding journal commits both Plan A and Plan B.

## Authority boundary

This crate authenticates no receipt. A RISC0 child receipt exposes its journal;
it does not expose the private child input that produced the journal. A future
receipt-bearing guest must receive the complete committed snapshot blobs through
an authenticated replay/data-availability path, re-run this kernel, and commit
the resulting fixed journal.

The intended authority order is:

```text
verify the final source settlement receipt and exact journal
  -> bind the DA certificate to the authenticated child DA root
  -> validate the exact replay blob against that certificate
  -> decode the complete pre/post snapshots
  -> require replay Plan A bytes to equal the authenticated child Plan A bytes
  -> derive Plan B inside this state/effect kernel
  -> emit one combined journal binding the child claim, DA root, replay blob,
     Plan A, Plan B, and state/effect binding commitment
```

Both exported authority constants remain `false`:

```text
SPOT_SETTLEMENT_V7_EFFECT_BINDING_RECEIPT_AUTHORITY=false
SPOT_SETTLEMENT_V7_EFFECT_BINDING_SETTLEMENT_AUTHORITY=false
```

Settlement promotion still requires a governed V7 guest/image, a sealed host
verifier, finality and data-availability checks, and one atomic transaction that
persists the authenticated pre/post application state together with all replay,
action, authorization, receipt, and proof indexes.

## Local checks

```bash
cargo fmt --all -- --check
cargo test --locked --all-targets
cargo test --locked --doc
cargo clippy --locked --all-targets -- -D warnings
```
