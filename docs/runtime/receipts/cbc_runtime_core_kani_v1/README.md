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
Complete - 63 successfully verified harnesses, 0 failures, 63 total.
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

Canonical primitive helpers:

- `canonical::kani_contracts::ascii_hex_digit_classifier_is_exact`
- `canonical::kani_contracts::domain_label_byte_classifier_is_exact`
- `canonical::kani_contracts::uvarint_encoded_len_boundary_cases`

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

Perp stateless math checked-effect helpers and bridge-domain guards:

- `perp_math::kani_contracts::abs_val_is_total_on_bridge_domain`
- `perp_math::kani_contracts::checked_margin_helpers_are_total_for_any_i128`
- `perp_math::kani_contracts::covers_are_reachable`
- `perp_math::kani_contracts::domain_classifiers_are_total_and_exact`
- `perp_math::kani_contracts::flat_positions_are_never_liquidatable_on_bridge_domain`
- `perp_math::kani_contracts::oracle_helpers_are_total_on_bridge_domain`
- `perp_math::kani_contracts::sign_classifiers_are_exact_on_bridge_domain`

Perp stateful global ops:

- `perp_advance_epoch::kani_contracts::advance_epoch_accept_shape_is_exact`
- `perp_advance_epoch::kani_contracts::advance_epoch_covers_are_reachable`
- `perp_advance_epoch::kani_contracts::advance_epoch_is_total_for_any_i128_input`
- `perp_advance_epoch::kani_contracts::phase_classifier_is_exact`
- `perp_publish_clearing_price::kani_contracts::phase_classifier_is_exact`
- `perp_publish_clearing_price::kani_contracts::publish_clearing_price_accept_shape_is_exact`
- `perp_publish_clearing_price::kani_contracts::publish_clearing_price_covers_are_reachable`
- `perp_publish_clearing_price::kani_contracts::publish_clearing_price_is_total_for_any_i128_input`

Perp stateful account-op tractable slice:

- `perp_account_ops::kani_contracts::account_op_covers_are_reachable`
- `perp_account_ops::kani_contracts::clear_breaker_total_and_accept_shape`
- `perp_account_ops::kani_contracts::deposit_collateral_total_and_accept_shape`
- `perp_account_ops::kani_contracts::domain_predicate_is_total_for_any_i128_input`

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

State-root scalar guards:

- `state_root::kani_contracts::duration_metadata_presence_is_exact`
- `state_root::kani_contracts::nonce_guard_is_exact`
- `state_root::kani_contracts::pool_fee_bps_guard_is_exact`
- `state_root::kani_contracts::pool_status_codes_are_in_domain_and_distinct`

zUSD scalar risk helpers:

- `zusd::kani_contracts::debt_floor_guard_is_exact`
- `zusd::kani_contracts::decayed_base_rate_never_increases`
- `zusd::kani_contracts::effective_fee_is_capped_and_respects_floor_when_ordered`
- `zusd::kani_contracts::oracle_freshness_is_exact_and_total`

## Scope

This proves bounded, heap-free arithmetic and decision contracts inside the
running Rust crate:

- balance transfer totality, exact movement, conservation, credit mint-or-overflow,
  reject precedence, and non-vacuity covers;
- replay nonce classifier totality, exact accept/reject semantics, and non-vacuity
  covers;
- arithmetic helper totality for checked addition, floor division, and
  multiply-divide floor;
- canonical helper predicates for ASCII domain labels, ASCII hex digits, and
  selected LEB128 length boundaries;
- fee-router dust-core totality/exactness and split totality;
- burn rail totality, accept-implies exact supply/budget/batch conservation, and
  non-vacuity covers;
- CPMM initialization totality, accepted initialization shape, invalid-fee
  boundary handling, zero-denominator fail-closed helper behavior, small-domain
  symbolic fee-ceil boundedness, small-domain exact-in reserve-shape behavior,
  uninitialized swap fail-closed behavior, and non-vacuity covers;
- stateless perps checked-effect helper totality over arbitrary `i128` inputs,
  bridge-domain classifiers, `abs_val` safety under the bridge domain, oracle
  helper totality, exact sign classifiers, flat-position liquidation rejection,
  and non-vacuity covers for success and overflow paths;
- stateful perps global-op totality, exact accept-shape contracts, phase
  classifiers, and reject/accept non-vacuity covers for `advance_epoch` and
  `publish_clearing_price`;
- stateful perps account-op domain totality, deposit accept shape, clear-breaker
  accept shape, and account-op accept/reject non-vacuity covers;
- funding-auto sink mirror movement, per-account collateral/payment relation,
  replay predicate, two-account conservation, and non-vacuity covers.
- state-root scalar guards for pool fee bps, nonce bounds, LP duration metadata
  presence, and pool-status code distinctness.
- zUSD scalar risk helpers for oracle freshness, base-rate decay, fee capping,
  and debt-floor admission.

It does not prove the heap-heavy JSON/CLI bridge, full canonical `Vec`/`String`
encoders, SHA-256, `BTreeMap` state-root section ordering/duplicate detection,
BigUint curve-parameter parsing, zUSD BigUint CDP ratio arithmetic, or Python
integration shell. It also does not prove the full CPMM exact-in/out swap
arithmetic over symbolic live-domain `u128` multiplication/division. Direct
public-swap harnesses and an exact-out helper harness timed out under CBMC; the
tracked Kani obligations therefore stop at checked helper boundaries and a
small-domain exact-in proof. The remaining CPMM arithmetic is still covered by
Rust proptests, Python/Rust differentials, disaster-state, live-path tests, and
Tau/ESSO/Lean model evidence. It also does not prove full-domain symbolic
equivalence between the checked and plain perps math helpers, or full symbolic
live-domain multiplication/division for notional, PnL, funding, margin, and
liquidation arithmetic. Those remain covered by Rust proptests, Python/Rust
differentials, disaster-state, and live-path tests. For stateful account ops,
withdraw and set-position margin paths also remain differential/live-shadow
backed.
