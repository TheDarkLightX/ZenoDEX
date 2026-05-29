//! Stateful perps E2 — isolated `advance_epoch` shadow.
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_advance_epoch`.
//! The action is global-only: it does not mutate account state. It advances the
//! epoch and resets the phase to `Open`, after the integration gate confirms the
//! current epoch has been settled (`oracle_last_update_epoch == now_epoch`).
//!
//! Python remains authority. This is a shadow/checker surface only.

pub const MAX_EPOCH: i128 = 1_000_000;
pub const MAX_DELTA: i128 = 10_000;

pub const PHASE_OPEN: i128 = 0;
pub const PHASE_PRICE_PUBLISHED: i128 = 1;
pub const PHASE_SETTLED: i128 = 2;

pub const REJ_OUT_OF_DOMAIN: &str = "advance_epoch_out_of_domain";
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

pub fn advance_epoch(input: &AdvanceEpochInput) -> Result<AdvanceEpochOutput, &'static str> {
    if !in_closed(input.now_epoch, 0, MAX_EPOCH)
        || !in_closed(input.oracle_last_update_epoch, 0, MAX_EPOCH)
        || !valid_phase(input.epoch_phase)
        || input.oracle_last_update_epoch > input.now_epoch
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }

    // Integration gate runs before the kernel's delta-domain check.
    if input.oracle_last_update_epoch != input.now_epoch {
        return Err(REJ_EPOCH_NOT_SETTLED);
    }
    if input.epoch_phase == PHASE_PRICE_PUBLISHED
        || (input.epoch_phase == PHASE_OPEN && input.now_epoch > 0)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }

    if !in_closed(input.delta, 1, MAX_DELTA) {
        return Err(REJ_PARAM_DELTA);
    }

    let next_epoch = input
        .now_epoch
        .checked_add(input.delta)
        .ok_or(REJ_OVERFLOW)?;
    if next_epoch > MAX_EPOCH {
        return Err(REJ_GUARD);
    }

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
        let out = advance_epoch(&input(0, PHASE_OPEN, 0, 1)).unwrap();
        assert_eq!(out.now_epoch, 1);
        assert_eq!(out.epoch_phase, PHASE_OPEN);
    }

    #[test]
    fn rejects_unsettled_epoch_before_delta_domain() {
        assert_eq!(
            advance_epoch(&input(5, PHASE_OPEN, 4, 0)).unwrap_err(),
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
    fn rejects_invalid_state_domain() {
        assert_eq!(
            advance_epoch(&input(1, 99, 1, 1)).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
        assert_eq!(
            advance_epoch(&input(1, PHASE_OPEN, 2, 1)).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
        assert_eq!(
            advance_epoch(&input(1, PHASE_OPEN, 1, 1)).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
        assert_eq!(
            advance_epoch(&input(1, PHASE_PRICE_PUBLISHED, 1, 1)).unwrap_err(),
            REJ_OUT_OF_DOMAIN
        );
    }

    proptest! {
        #[test]
        fn prop_accepted_transition_shape(
            now in 0i128..=990_000,
            delta in 1i128..=10_000,
        ) {
            let inp = input(now, PHASE_SETTLED, now, delta);
            let out = advance_epoch(&inp).unwrap();
            prop_assert_eq!(out.now_epoch, now + delta);
            prop_assert_eq!(out.epoch_phase, PHASE_OPEN);
            prop_assert_eq!(out.oracle_last_update_epoch, now);
        }
    }
}
