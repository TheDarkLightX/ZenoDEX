//! Stateful perps E2 — isolated `publish_clearing_price` shadow.
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_publish_clearing_price`.
//! The action is global-only: it does not mutate account state. It records the
//! epoch's clearing price and moves the phase `Open -> PricePublished`.
//!
//! ## Faithfulness contract
//!
//! Authority reject precedence (verified against the real authority):
//!   1. `price_e8 < 0`            -> `price_e8 must be non-negative`      (integration)
//!   2. `price_e8 == 0`           -> `publish_clearing_price requires price_e8 > 0` (integration)
//!   3. `price_e8 > PRICE_MAX`    -> `param_domain:price_e8`              (kernel param-domain)
//!   4. `!(phase==Open && clearing_price_epoch < now_epoch)` -> `guard`  (kernel guard)
//!
//! `guard_publish_clearing_price` (`perp_v2/guards.py`) is exactly
//! `phase == Open && clearing_price_epoch < now_epoch`; there is **no** oracle
//! freshness check and **no** clamp here (the `Open & now>0` state-consistency
//! invariant already forces `oracle_last < now`, and `clearing_price_epoch < now`
//! forces `now >= 1`, so the resulting `PricePublished` state is always valid).
//!
//! On accept the transition sets `clearing_price_seen = true`,
//! `clearing_price_epoch = now_epoch`, `clearing_price_e8 = price_e8`,
//! `epoch_phase = PricePublished` (`now_epoch` and the oracle are unchanged).
//!
//! As fail-closed defense the shadow encodes the `PerpMarketState` state-consistency
//! invariant (`src/core/perps.py`) as an explicit precondition
//! (`REJ_INCONSISTENT_STATE`); it is never reached by the differential (which only
//! feeds validator-passing states).
//!
//! Python remains authority. This is a shadow/checker surface only.

pub const MAX_EPOCH: i128 = 1_000_000;
/// `PERP_PARAM_AMOUNT_MAX` (`perp_v2`): the kernel param-domain upper bound for `price_e8`.
pub const PRICE_MAX: i128 = 1_000_000_000_000;

pub const PHASE_OPEN: i128 = 0;
pub const PHASE_PRICE_PUBLISHED: i128 = 1;
pub const PHASE_SETTLED: i128 = 2;

pub const REJ_OUT_OF_DOMAIN: &str = "publish_clearing_price_out_of_domain";
pub const REJ_INCONSISTENT_STATE: &str = "publish_clearing_price_inconsistent_state";
pub const REJ_PRICE_NEGATIVE: &str = "price_e8_negative";
pub const REJ_PRICE_NOT_POSITIVE: &str = "price_e8_not_positive";
pub const REJ_PARAM_PRICE: &str = "param_domain_price_e8";
pub const REJ_GUARD: &str = "publish_clearing_price_guard";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublishClearingPriceInput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub clearing_price_seen: bool,
    pub clearing_price_epoch: i128,
    pub clearing_price_e8: i128,
    pub oracle_last_update_epoch: i128,
    pub price_e8: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublishClearingPriceOutput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub clearing_price_seen: bool,
    pub clearing_price_epoch: i128,
    pub clearing_price_e8: i128,
}

#[inline]
fn in_closed(x: i128, lo: i128, hi: i128) -> bool {
    lo <= x && x <= hi
}

#[inline]
fn valid_phase(x: i128) -> bool {
    matches!(x, PHASE_OPEN | PHASE_PRICE_PUBLISHED | PHASE_SETTLED)
}

/// `PerpMarketState._validate_isolated_state_consistency` (`src/core/perps.py`),
/// over the fields this surface carries. The authority can never hold a state
/// violating this.
///
/// * clearing-price fields are zero when unseen
/// * `Open`            => not (`cps && cpe==now`); and (`now==0` or `oracle != now`)
/// * `PricePublished`  => `cps && cpe==now`; and `oracle != now`
/// * `Settled`         => `cps && cpe==now`; and `oracle == now`
#[inline]
fn state_consistent(
    phase: i128,
    now: i128,
    cps: bool,
    cpe: i128,
    cp_e8: i128,
    oracle_last: i128,
) -> bool {
    if !cps && (cpe != 0 || cp_e8 != 0) {
        return false;
    }
    match phase {
        PHASE_OPEN => !(cps && cpe == now || now > 0 && oracle_last == now),
        PHASE_PRICE_PUBLISHED => (cps && cpe == now) && oracle_last != now,
        PHASE_SETTLED => (cps && cpe == now) && oracle_last == now,
        _ => false,
    }
}

pub fn publish_clearing_price(
    input: &PublishClearingPriceInput,
) -> Result<PublishClearingPriceOutput, &'static str> {
    // (1) Numeric input domain (malformed CLI input).
    if !in_closed(input.now_epoch, 0, MAX_EPOCH)
        || !in_closed(input.clearing_price_epoch, 0, MAX_EPOCH)
        || !in_closed(input.oracle_last_update_epoch, 0, input.now_epoch)
        || !in_closed(input.clearing_price_e8, 0, PRICE_MAX)
        || !valid_phase(input.epoch_phase)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }

    // (2) State-consistency invariant: reject states the authority can never hold.
    if !state_consistent(
        input.epoch_phase,
        input.now_epoch,
        input.clearing_price_seen,
        input.clearing_price_epoch,
        input.clearing_price_e8,
        input.oracle_last_update_epoch,
    ) {
        return Err(REJ_INCONSISTENT_STATE);
    }

    // (3-5) Price checks, in the authority's order (sign -> positivity -> domain),
    //       all of which precede the kernel guard.
    if input.price_e8 < 0 {
        return Err(REJ_PRICE_NEGATIVE);
    }
    if input.price_e8 == 0 {
        return Err(REJ_PRICE_NOT_POSITIVE);
    }
    if input.price_e8 > PRICE_MAX {
        return Err(REJ_PARAM_PRICE);
    }

    // (6) Kernel guard: phase == Open AND clearing_price_epoch < now_epoch.
    if !(input.epoch_phase == PHASE_OPEN && input.clearing_price_epoch < input.now_epoch) {
        return Err(REJ_GUARD);
    }

    // (7) Transition: record the clearing price and move Open -> PricePublished.
    Ok(PublishClearingPriceOutput {
        now_epoch: input.now_epoch,
        epoch_phase: PHASE_PRICE_PUBLISHED,
        clearing_price_seen: true,
        clearing_price_epoch: input.now_epoch,
        clearing_price_e8: input.price_e8,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn open_at(now: i128, oracle_last: i128, price: i128) -> PublishClearingPriceInput {
        // A consistent Open state: clearing price unseen, oracle stale for now>0.
        PublishClearingPriceInput {
            now_epoch: now,
            epoch_phase: PHASE_OPEN,
            clearing_price_seen: false,
            clearing_price_epoch: 0,
            clearing_price_e8: 0,
            oracle_last_update_epoch: oracle_last,
            price_e8: price,
        }
    }

    #[test]
    fn publishes_from_open_and_sets_price_published() {
        let out = publish_clearing_price(&open_at(5, 4, 100_000_000)).unwrap();
        assert_eq!(out.now_epoch, 5);
        assert_eq!(out.epoch_phase, PHASE_PRICE_PUBLISHED);
        assert!(out.clearing_price_seen);
        assert_eq!(out.clearing_price_epoch, 5);
        assert_eq!(out.clearing_price_e8, 100_000_000);
    }

    #[test]
    fn accepts_price_at_domain_bound() {
        let out = publish_clearing_price(&open_at(2, 1, PRICE_MAX)).unwrap();
        assert_eq!(out.clearing_price_e8, PRICE_MAX);
    }

    #[test]
    fn rejects_negative_price_before_guard() {
        // Even from a non-Open state, the price-sign check precedes the guard.
        let mut inp = open_at(5, 4, -1);
        inp.epoch_phase = PHASE_SETTLED;
        inp.clearing_price_seen = true;
        inp.clearing_price_epoch = 5;
        inp.clearing_price_e8 = 100_000_000;
        inp.oracle_last_update_epoch = 5;
        assert_eq!(
            publish_clearing_price(&inp).unwrap_err(),
            REJ_PRICE_NEGATIVE
        );
    }

    #[test]
    fn rejects_zero_price_as_not_positive() {
        assert_eq!(
            publish_clearing_price(&open_at(5, 4, 0)).unwrap_err(),
            REJ_PRICE_NOT_POSITIVE
        );
    }

    #[test]
    fn rejects_price_above_param_max() {
        assert_eq!(
            publish_clearing_price(&open_at(5, 4, PRICE_MAX + 1)).unwrap_err(),
            REJ_PARAM_PRICE
        );
    }

    #[test]
    fn rejects_non_open_phase_as_guard() {
        // Settled at now==oracle with a fresh clearing price: a valid Settled state.
        let inp = PublishClearingPriceInput {
            now_epoch: 5,
            epoch_phase: PHASE_SETTLED,
            clearing_price_seen: true,
            clearing_price_epoch: 5,
            clearing_price_e8: 100_000_000,
            oracle_last_update_epoch: 5,
            price_e8: 100_000_000,
        };
        assert_eq!(publish_clearing_price(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_open_at_epoch_zero_as_guard() {
        // Bootstrap Open at now==0: clearing_price_epoch(0) < now(0) is false.
        assert_eq!(
            publish_clearing_price(&open_at(0, 0, 100_000_000)).unwrap_err(),
            REJ_GUARD
        );
    }

    #[test]
    fn rejects_states_violating_consistency_invariant() {
        // PricePublished with a stale-enough oracle is fine, but cps=false here.
        let mut inp = open_at(5, 4, 100_000_000);
        inp.epoch_phase = PHASE_PRICE_PUBLISHED; // requires cps && cpe==now
        assert_eq!(
            publish_clearing_price(&inp).unwrap_err(),
            REJ_INCONSISTENT_STATE
        );
        // clearing fields nonzero while unseen.
        let mut inp2 = open_at(5, 4, 100_000_000);
        inp2.clearing_price_e8 = 1;
        assert_eq!(
            publish_clearing_price(&inp2).unwrap_err(),
            REJ_INCONSISTENT_STATE
        );
    }

    #[test]
    fn rejects_invalid_numeric_domain() {
        let mut inp = open_at(5, 4, 100_000_000);
        inp.epoch_phase = 99;
        assert_eq!(publish_clearing_price(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
        // oracle ahead of now.
        let inp2 = open_at(3, 4, 100_000_000);
        assert_eq!(
            publish_clearing_price(&inp2).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
    }

    proptest! {
        #[test]
        fn prop_open_accept_shape(
            now in 1i128..=990_000,
            price in 1i128..=PRICE_MAX,
        ) {
            // Open with stale oracle (now-1) and unseen clearing price always publishes.
            let out = publish_clearing_price(&open_at(now, now - 1, price)).unwrap();
            prop_assert_eq!(out.epoch_phase, PHASE_PRICE_PUBLISHED);
            prop_assert!(out.clearing_price_seen);
            prop_assert_eq!(out.clearing_price_epoch, now);
            prop_assert_eq!(out.clearing_price_e8, price);
            prop_assert_eq!(out.now_epoch, now);
        }

        #[test]
        fn prop_total_over_modelled_domain(
            now in 0i128..=MAX_EPOCH,
            phase in 0i128..=2,
            cps in any::<bool>(),
            cpe in 0i128..=MAX_EPOCH,
            oracle in 0i128..=MAX_EPOCH,
            price in -5i128..=(PRICE_MAX + 5),
        ) {
            let inp = PublishClearingPriceInput {
                now_epoch: now,
                epoch_phase: phase,
                clearing_price_seen: cps,
                clearing_price_epoch: cpe,
                clearing_price_e8: 0,
                oracle_last_update_epoch: oracle,
                price_e8: price,
            };
            match publish_clearing_price(&inp) {
                Ok(out) => {
                    prop_assert_eq!(out.epoch_phase, PHASE_PRICE_PUBLISHED);
                    prop_assert_eq!(out.clearing_price_epoch, now);
                    prop_assert_eq!(out.clearing_price_e8, price);
                    prop_assert_eq!(phase, PHASE_OPEN);
                    prop_assert!(cpe < now);
                    prop_assert!((1..=PRICE_MAX).contains(&price));
                }
                Err(code) => {
                    prop_assert!(matches!(
                        code,
                        REJ_OUT_OF_DOMAIN
                            | REJ_INCONSISTENT_STATE
                            | REJ_PRICE_NEGATIVE
                            | REJ_PRICE_NOT_POSITIVE
                            | REJ_PARAM_PRICE
                            | REJ_GUARD
                    ));
                }
            }
        }
    }
}
