//! Stateful perps E2 — isolated `advance_epoch` shadow.
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_advance_epoch`.
//! The action is global-only: it does not mutate account state. It advances the
//! epoch and resets the phase to `Open`.
//!
//! ## Faithfulness contract
//!
//! The Python authority applies **no phase precondition** to `advance_epoch`:
//! the kernel guard (`perp_v2/guards.py::guard_advance_epoch`) is exactly
//! `now_epoch + delta <= MAX_EPOCH`, and the kernel param-domain requires
//! `delta in [1, PERP_ADVANCE_EPOCH_DELTA_MAX]`. The only phase-related gate is
//! at the integration layer: the current epoch must be oracle-settled
//! (`oracle_last_update_epoch == now_epoch`), checked *before* the delta domain.
//!
//! `PerpMarketState._validate_isolated_state_consistency` (`src/core/perps.py`)
//! guarantees `oracle_last == now` holds **only** for `Settled` or the `now == 0`
//! bootstrap (`Open & now>0` and `PricePublished` both require `oracle_last < now`).
//! So for every *reachable* state the oracle-settled gate alone reproduces the
//! authority's accept set, and no explicit phase guard is required.
//!
//! As fail-closed defense, the shadow additionally encodes the oracle clauses of
//! that state-consistency invariant as an explicit precondition
//! (`REJ_INCONSISTENT_STATE`): it rejects phase/oracle combinations the authority
//! can never hold. This branch is never reached by the differential (which only
//! feeds validator-passing states); it guards direct/fuzzed CLI input.
//!
//! Python remains authority. This is a shadow/checker surface only.

pub const MAX_EPOCH: i128 = 1_000_000;
pub const MAX_DELTA: i128 = 10_000;

pub const PHASE_OPEN: i128 = 0;
pub const PHASE_PRICE_PUBLISHED: i128 = 1;
pub const PHASE_SETTLED: i128 = 2;

pub const REJ_OUT_OF_DOMAIN: &str = "advance_epoch_out_of_domain";
pub const REJ_INCONSISTENT_STATE: &str = "advance_epoch_inconsistent_state";
pub const REJ_PARAM_DELTA: &str = "param_domain_delta";
pub const REJ_EPOCH_NOT_SETTLED: &str = "epoch_not_settled";
pub const REJ_GUARD: &str = "advance_epoch_guard";
pub const REJ_OVERFLOW: &str = "advance_epoch_arithmetic_overflow";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvanceEpochInput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub oracle_last_update_epoch: i128,
    pub delta: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdvanceEpochOutput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub oracle_last_update_epoch: i128,
}

#[inline]
fn in_closed(x: i128, lo: i128, hi: i128) -> bool {
    lo <= x && x <= hi
}

#[inline]
fn valid_phase(x: i128) -> bool {
    matches!(x, PHASE_OPEN | PHASE_PRICE_PUBLISHED | PHASE_SETTLED)
}

/// Oracle clauses of `PerpMarketState._validate_isolated_state_consistency`
/// (`src/core/perps.py`). The authority can never hold a state violating this:
///
/// * `Open` & `now > 0`  => `oracle_last != now` (oracle is stale for an open epoch)
/// * `PricePublished`     => `oracle_last != now`
/// * `Settled`            => `oracle_last == now`
///
/// (The clearing-price clauses are not modelled — this surface carries only
/// `now_epoch`, `epoch_phase`, `oracle_last_update_epoch`.)
#[inline]
fn state_consistent(phase: i128, now: i128, oracle_last: i128) -> bool {
    match phase {
        PHASE_OPEN => !(now > 0 && oracle_last == now),
        PHASE_PRICE_PUBLISHED => oracle_last != now,
        PHASE_SETTLED => oracle_last == now,
        _ => false,
    }
}

pub fn advance_epoch(input: &AdvanceEpochInput) -> Result<AdvanceEpochOutput, &'static str> {
    // (1) Numeric input domain (malformed CLI input). `oracle_last` is bounded by
    //     `now_epoch`: an oracle update from a future epoch is impossible.
    if !in_closed(input.now_epoch, 0, MAX_EPOCH)
        || !in_closed(input.oracle_last_update_epoch, 0, input.now_epoch)
        || !valid_phase(input.epoch_phase)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }

    // (2) State-consistency invariant: reject phase/oracle states the authority
    //     can never hold (fail-closed; not reached by validator-passing inputs).
    if !state_consistent(
        input.epoch_phase,
        input.now_epoch,
        input.oracle_last_update_epoch,
    ) {
        return Err(REJ_INCONSISTENT_STATE);
    }

    // (3) Integration gate: the current epoch must be oracle-settled. This is the
    //     authority's only phase-related gate, and it runs before the delta domain.
    if input.oracle_last_update_epoch != input.now_epoch {
        return Err(REJ_EPOCH_NOT_SETTLED);
    }

    // (4) Kernel param-domain: delta in [1, MAX_DELTA].
    if !in_closed(input.delta, 1, MAX_DELTA) {
        return Err(REJ_PARAM_DELTA);
    }

    // (5) Kernel guard: now + delta <= MAX_EPOCH (checked arithmetic, fail-closed).
    let next_epoch = input
        .now_epoch
        .checked_add(input.delta)
        .ok_or(REJ_OVERFLOW)?;
    if next_epoch > MAX_EPOCH {
        return Err(REJ_GUARD);
    }

    // (6) Transition: now += delta, phase resets to Open, oracle unchanged.
    Ok(AdvanceEpochOutput {
        now_epoch: next_epoch,
        epoch_phase: PHASE_OPEN,
        oracle_last_update_epoch: input.oracle_last_update_epoch,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn input(
        now_epoch: i128,
        phase: i128,
        oracle_last_update_epoch: i128,
        delta: i128,
    ) -> AdvanceEpochInput {
        AdvanceEpochInput {
            now_epoch,
            epoch_phase: phase,
            oracle_last_update_epoch,
            delta,
        }
    }

    #[test]
    fn advances_settled_epoch_and_resets_phase_open() {
        let out = advance_epoch(&input(7, PHASE_SETTLED, 7, 3)).unwrap();
        assert_eq!(out.now_epoch, 10);
        assert_eq!(out.epoch_phase, PHASE_OPEN);
        assert_eq!(out.oracle_last_update_epoch, 7);
    }

    #[test]
    fn initial_epoch_zero_can_advance() {
        // Bootstrap: Open at now==0 with oracle_last==0 is the one Open state with
        // oracle_last == now permitted by the consistency invariant.
        let out = advance_epoch(&input(0, PHASE_OPEN, 0, 1)).unwrap();
        assert_eq!(out.now_epoch, 1);
        assert_eq!(out.epoch_phase, PHASE_OPEN);
    }

    #[test]
    fn rejects_unsettled_epoch_before_delta_domain() {
        // Open & now>0 with stale oracle is reachable; the oracle gate fires before
        // the (here out-of-domain) delta, matching the authority's ordering.
        assert_eq!(
            advance_epoch(&input(5, PHASE_OPEN, 4, 0)).unwrap_err(),
            REJ_EPOCH_NOT_SETTLED
        );
    }

    #[test]
    fn rejects_open_now_positive_oracle_stale_as_not_settled() {
        assert_eq!(
            advance_epoch(&input(5, PHASE_OPEN, 3, 1)).unwrap_err(),
            REJ_EPOCH_NOT_SETTLED
        );
    }

    #[test]
    fn rejects_price_published_oracle_stale_as_not_settled() {
        assert_eq!(
            advance_epoch(&input(5, PHASE_PRICE_PUBLISHED, 3, 1)).unwrap_err(),
            REJ_EPOCH_NOT_SETTLED
        );
    }

    #[test]
    fn rejects_delta_out_of_domain() {
        assert_eq!(
            advance_epoch(&input(5, PHASE_SETTLED, 5, 0)).unwrap_err(),
            REJ_PARAM_DELTA
        );
        assert_eq!(
            advance_epoch(&input(5, PHASE_SETTLED, 5, MAX_DELTA + 1)).unwrap_err(),
            REJ_PARAM_DELTA
        );
    }

    #[test]
    fn rejects_epoch_guard_overflow() {
        assert_eq!(
            advance_epoch(&input(MAX_EPOCH - 1, PHASE_SETTLED, MAX_EPOCH - 1, 2)).unwrap_err(),
            REJ_GUARD
        );
    }

    #[test]
    fn rejects_invalid_numeric_domain() {
        // Invalid phase code.
        assert_eq!(
            advance_epoch(&input(1, 99, 1, 1)).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
        // oracle_last ahead of now_epoch is impossible (out of domain).
        assert_eq!(
            advance_epoch(&input(1, PHASE_OPEN, 2, 1)).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
    }

    #[test]
    fn rejects_states_violating_consistency_invariant() {
        // Open & now>0 with a fresh oracle: forbidden by the state invariant.
        assert_eq!(
            advance_epoch(&input(1, PHASE_OPEN, 1, 1)).unwrap_err(),
            REJ_INCONSISTENT_STATE
        );
        // PricePublished with a fresh oracle: forbidden by the state invariant.
        assert_eq!(
            advance_epoch(&input(5, PHASE_PRICE_PUBLISHED, 5, 1)).unwrap_err(),
            REJ_INCONSISTENT_STATE
        );
        // Settled with a stale oracle: forbidden by the state invariant.
        assert_eq!(
            advance_epoch(&input(3, PHASE_SETTLED, 2, 1)).unwrap_err(),
            REJ_INCONSISTENT_STATE
        );
    }

    proptest! {
        #[test]
        fn prop_accepted_transition_shape(
            now in 0i128..=990_000,
            delta in 1i128..=10_000,
        ) {
            // Settled with oracle_last == now is the canonical accept precondition.
            let inp = input(now, PHASE_SETTLED, now, delta);
            let out = advance_epoch(&inp).unwrap();
            prop_assert_eq!(out.now_epoch, now + delta);
            prop_assert_eq!(out.epoch_phase, PHASE_OPEN);
            prop_assert_eq!(out.oracle_last_update_epoch, now);
        }

        #[test]
        fn prop_total_over_modelled_domain(
            now in 0i128..=MAX_EPOCH,
            phase in 0i128..=2,
            oracle in 0i128..=MAX_EPOCH,
            delta in -5i128..=15_000,
        ) {
            // Total over the modelled domain: every input yields Ok or a known Err.
            let r = advance_epoch(&input(now, phase, oracle, delta));
            match r {
                Ok(out) => {
                    // Accept implies oracle was settled and delta was in domain.
                    prop_assert_eq!(out.epoch_phase, PHASE_OPEN);
                    prop_assert_eq!(out.oracle_last_update_epoch, oracle);
                    prop_assert_eq!(out.now_epoch, now + delta);
                    prop_assert_eq!(oracle, now);
                    prop_assert!((1..=MAX_DELTA).contains(&delta));
                }
                Err(code) => {
                    prop_assert!(matches!(
                        code,
                        REJ_OUT_OF_DOMAIN
                            | REJ_INCONSISTENT_STATE
                            | REJ_EPOCH_NOT_SETTLED
                            | REJ_PARAM_DELTA
                            | REJ_GUARD
                            | REJ_OVERFLOW
                    ));
                }
            }
        }
    }
}
