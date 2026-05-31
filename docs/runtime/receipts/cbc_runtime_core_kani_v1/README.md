# CBC Runtime Core Kani Receipt

This receipt records Kani evidence for CBC contracts on the actual
`zenodex-runtime-core` crate, not on the experimental `experiments/cbc_core_v0`
ports.

## Environment

- Date: 2026-05-31
- Branch: `claude/finish-rust-runtime-authority`
- Tool: `cargo-kani 0.60.0`
- Crate: `rust-runtime/crates/zenodex-runtime-core`

## Command

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --lib --output-format terse -j 4 --harness-timeout 10m -Z unstable-options
```

## Result

```text
Manual Harness Summary:
Complete - 19 successfully verified harnesses, 0 failures, 19 total.
```

Kani emitted compile-time warnings about unsupported constructs
(`caller_location`, one foreign function) and target features (`x87`, `sse2`).
The harness run still completed successfully. Those constructs were not reachable
from the verified harnesses.

## Harnesses Verified

Balance kernel:

- `balance_kernel::kani_contracts::covers_are_reachable`
- `balance_kernel::kani_contracts::credit_covers_are_reachable`
- `balance_kernel::kani_contracts::settle_credit_is_total`
- `balance_kernel::kani_contracts::settle_credit_mints_or_overflows`
- `balance_kernel::kani_contracts::settle_transfer_conserves_and_moves_exact`
- `balance_kernel::kani_contracts::settle_transfer_is_total`
- `balance_kernel::kani_contracts::settle_transfer_reject_precedence`

Fee router:

- `fee_router::kani_contracts::covers_are_reachable`
- `fee_router::kani_contracts::dust_from_remainders_total_and_exact`
- `fee_router::kani_contracts::split_is_total`

Perp funding-auto bounded-sink arithmetic:

- `perp_funding_auto::kani_contracts::account_collateral_delta_is_negative_payment`
- `perp_funding_auto::kani_contracts::covers_are_reachable`
- `perp_funding_auto::kani_contracts::replay_predicate_matches_open_same_epoch`
- `perp_funding_auto::kani_contracts::sink_delta_moves_all_mirrors_exactly`
- `perp_funding_auto::kani_contracts::two_account_conservation`

Replay guard:

- `replay_guard::kani_contracts::classify_accept_iff_successor`
- `replay_guard::kani_contracts::classify_is_total`
- `replay_guard::kani_contracts::classify_reject_codes_exact`
- `replay_guard::kani_contracts::covers_are_reachable`

## Scope

This proves bounded, heap-free arithmetic and decision contracts inside the
running Rust crate:

- balance transfer totality, exact movement, conservation, credit mint-or-overflow,
  reject precedence, and non-vacuity covers;
- replay nonce classifier totality, exact accept/reject semantics, and non-vacuity
  covers;
- fee-router dust-core totality/exactness and split totality;
- funding-auto sink mirror movement, per-account collateral/payment relation,
  replay predicate, two-account conservation, and non-vacuity covers.

It does not prove the heap-heavy JSON/CLI bridge, `BTreeMap` state-root hashing,
or Python integration shell. Those remain covered by differential, disaster-state,
and live-path tests.
