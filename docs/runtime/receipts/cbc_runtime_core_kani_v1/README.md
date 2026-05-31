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
Complete - 35 successfully verified harnesses, 0 failures, 35 total.
```

Kani emitted compile-time warnings about unsupported constructs
(`caller_location`, one foreign function) and target features (`x87`, `sse2`).
The harness run still completed successfully. Those constructs were not reachable
from the verified harnesses.

## Harnesses Verified

Arithmetic core:

- `arith::kani_contracts::checked_add_total_and_exact`
- `arith::kani_contracts::floor_div_i128_is_total`
- `arith::kani_contracts::mul_div_floor_is_total`

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

Burn accounting rails:

- `burn_receipts::kani_contracts::accepted_rails_enforce_conservation`
- `burn_receipts::kani_contracts::covers_are_reachable`
- `burn_receipts::kani_contracts::verify_rails_is_total`

CPMM settlement primitive, tractable Kani slice:

- `cpmm_swap::kani_contracts::covers_are_reachable`
- `cpmm_swap::kani_contracts::checked_ceil_mul_div_zero_denominator_is_total`
- `cpmm_swap::kani_contracts::exact_in_calc_small_domain_total_and_accept_shape`
- `cpmm_swap::kani_contracts::fee_ceil_mul_div_small_domain_is_total_and_bounded`
- `cpmm_swap::kani_contracts::fee_validation_boundary_cases`
- `cpmm_swap::kani_contracts::init_pool_accept_shape`
- `cpmm_swap::kani_contracts::init_pool_is_total`
- `cpmm_swap::kani_contracts::uninitialized_pool_rejects_all_swaps`

Perp stateless math checked-effect helpers:

- `perp_math::kani_contracts::checked_margin_helpers_are_total_for_any_i128`
- `perp_math::kani_contracts::covers_are_reachable`

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
- arithmetic helper totality for checked addition, floor division, and
  multiply-divide floor;
- fee-router dust-core totality/exactness and split totality;
- burn rail totality, accept-implies exact supply/budget/batch conservation, and
  non-vacuity covers;
- CPMM initialization totality, accepted initialization shape, invalid-fee
  boundary handling, zero-denominator fail-closed helper behavior, small-domain
  symbolic fee-ceil boundedness, small-domain exact-in reserve-shape behavior,
  uninitialized swap fail-closed behavior, and non-vacuity covers;
- stateless perps checked-effect helper totality over arbitrary `i128` inputs,
  plus non-vacuity covers for success and overflow paths;
- funding-auto sink mirror movement, per-account collateral/payment relation,
  replay predicate, two-account conservation, and non-vacuity covers.

It does not prove the heap-heavy JSON/CLI bridge, `BTreeMap` state-root hashing,
or Python integration shell. It also does not prove the full CPMM exact-in/out
swap arithmetic over symbolic live-domain `u128` multiplication/division. Direct
public-swap harnesses and an exact-out helper harness timed out under CBMC; the
tracked Kani obligations therefore stop at checked helper boundaries and a
small-domain exact-in proof. The remaining CPMM arithmetic is still covered by
Rust proptests, Python/Rust differentials, disaster-state, live-path tests, and
Tau/ESSO/Lean model evidence. It also does not prove full-domain symbolic
equivalence between the checked and plain perps math helpers; these remain
covered by Rust proptests, Python/Rust differentials, disaster-state, and
live-path tests.
