//! Stateful perps E2 — isolated `partial_liquidate` shadow.
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_partial_liquidate`.
//! A single-account, mid-`Open` liquidation: it closes the minimum fraction of an
//! underwater position needed to restore maintenance margin (auto-computed by
//! binary search when `fraction_bps == 0`), applies a penalty on the closed
//! portion to `fee_pool/fee_income` (and thus insurance), and leaves the epoch
//! phase unchanged. It evaluates against the **current index price** (not a
//! settlement price) and requires a fresh oracle.
//!
//! ## Faithfulness contract
//!
//! Param domain: `fraction_bps ∈ [0, PERP_RATE_BPS_MAX = 10_000]` (else
//! `param_domain:fraction_bps`); `0` means auto-compute.
//!
//! `guard_partial_liquidate` (`perp_v2/guards.py`) + the eligibility gate
//! (`perp_liquidation_eligibility_gate.py`), with `auth_ok = true` (set by the
//! integration), require:
//!   * `epoch_phase == Open`, `position != 0`, `index_price > 0`, oracle fresh,
//!     and the position is liquidatable at the index price;
//!   * the resolved fraction is in `[1, BPS_SCALE]`;
//!   * `0 ≤ collateral − penalty ≤ MAX_COLLATERAL`;
//!   * `fee_pool + penalty`, `fee_income + penalty`, and the derived insurance
//!     all stay `≤ MAX_COLLATERAL`;
//!   * if a position remains, `collateral − penalty ≥ maint_margin_req(remaining)`.
//!
//! Any failure → `partial_liquidate_guard`.
//!
//! `apply_partial_liquidate` then sets `position = remaining`,
//! `entry_price = 0 if flat else index_price`, `collateral −= penalty`,
//! `fee_pool/fee_income += penalty`, `insurance = initial + fee_income − claims`,
//! `liquidated_this_step = true`.
//!
//! Oracle-adapter/authorization gates are integration-auth concerns out of this
//! transition's scope. Python remains authority; this is a shadow only.

use crate::perp_math::{
    compute_partial_close_fraction, is_liquidatable, is_oracle_fresh, maint_margin_req,
    partial_liq_penalty_capped, remaining_position_signed, MAX_ABS, MAX_BPS,
};

pub const MAX_EPOCH: i128 = 1_000_000;
pub const MAX_COLLATERAL: i128 = 1_000_000_000_000_000;
pub const BPS_SCALE: i128 = 10_000;
/// `PERP_RATE_BPS_MAX`: the kernel param-domain upper bound for `fraction_bps`.
pub const FRACTION_BPS_MAX: i128 = 10_000;

pub const PHASE_OPEN: i128 = 0;
pub const PHASE_PRICE_PUBLISHED: i128 = 1;
pub const PHASE_SETTLED: i128 = 2;

pub const REJ_OUT_OF_DOMAIN: &str = "partial_liquidate_out_of_domain";
pub const REJ_PARAM_FRACTION: &str = "param_domain_fraction_bps";
pub const REJ_GUARD: &str = "partial_liquidate_guard";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialLiquidateInput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub oracle_last_update_epoch: i128,
    pub max_oracle_staleness_epochs: i128,
    pub oracle_seen: bool,
    pub index_price_e8: i128,
    pub position_base: i128,
    pub collateral_quote: i128,
    pub entry_price_e8: i128,
    pub maintenance_margin_bps: i128,
    pub depeg_buffer_bps: i128,
    pub liquidation_penalty_bps: i128,
    pub min_notional_for_bounty: i128,
    pub fee_pool_quote: i128,
    pub fee_income: i128,
    pub initial_insurance: i128,
    pub claims_paid: i128,
    pub fraction_bps: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialLiquidateOutput {
    pub position_base: i128,
    pub entry_price_e8: i128,
    pub collateral_quote: i128,
    pub fee_pool_quote: i128,
    pub fee_income: i128,
    pub insurance_balance: i128,
    pub liquidated_this_step: bool,
}

#[inline]
fn in_closed(x: i128, lo: i128, hi: i128) -> bool {
    lo <= x && x <= hi
}

pub fn partial_liquidate(
    input: &PartialLiquidateInput,
) -> Result<PartialLiquidateOutput, &'static str> {
    // (1) Numeric/param input domain (sound bounds: every valid state passes).
    if !in_closed(input.now_epoch, 0, MAX_EPOCH)
        || !in_closed(input.oracle_last_update_epoch, 0, MAX_EPOCH)
        || !in_closed(input.max_oracle_staleness_epochs, 0, MAX_EPOCH)
        || !matches!(
            input.epoch_phase,
            PHASE_OPEN | PHASE_PRICE_PUBLISHED | PHASE_SETTLED
        )
        || !in_closed(input.index_price_e8, 0, MAX_ABS)
        || !in_closed(input.position_base, -MAX_ABS, MAX_ABS)
        || !in_closed(input.collateral_quote, 0, MAX_COLLATERAL)
        || !in_closed(input.entry_price_e8, 0, MAX_ABS)
        || !in_closed(input.maintenance_margin_bps, 0, MAX_BPS)
        || !in_closed(input.depeg_buffer_bps, 0, MAX_BPS)
        || !in_closed(input.liquidation_penalty_bps, 0, MAX_BPS)
        || !in_closed(input.min_notional_for_bounty, 0, MAX_ABS)
        || !in_closed(input.fee_pool_quote, 0, MAX_COLLATERAL)
        || !in_closed(input.fee_income, 0, MAX_COLLATERAL)
        || !in_closed(input.initial_insurance, 0, MAX_COLLATERAL)
        || !in_closed(input.claims_paid, 0, MAX_COLLATERAL)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }

    // (2) Kernel param-domain: fraction_bps in [0, PERP_RATE_BPS_MAX].
    if !in_closed(input.fraction_bps, 0, FRACTION_BPS_MAX) {
        return Err(REJ_PARAM_FRACTION);
    }

    // (3) Eligibility gate (auth_ok is true: set by the integration).
    let oracle_fresh = is_oracle_fresh(
        input.now_epoch,
        input.oracle_last_update_epoch,
        input.max_oracle_staleness_epochs,
        input.oracle_seen,
    );
    let liquidatable = input.position_base != 0
        && input.index_price_e8 > 0
        && is_liquidatable(
            input.position_base,
            input.collateral_quote,
            input.index_price_e8,
            input.maintenance_margin_bps,
            input.depeg_buffer_bps,
        );
    let allowed = input.epoch_phase == PHASE_OPEN
        && input.position_base != 0
        && input.index_price_e8 > 0
        && oracle_fresh
        && liquidatable;
    if !allowed {
        return Err(REJ_GUARD);
    }

    // (4) Resolve fraction (0 -> auto-compute via binary search).
    let fraction = if input.fraction_bps == 0 {
        compute_partial_close_fraction(
            input.position_base,
            input.collateral_quote,
            input.index_price_e8,
            input.maintenance_margin_bps,
            input.depeg_buffer_bps,
            input.liquidation_penalty_bps,
            input.min_notional_for_bounty,
        )
    } else {
        input.fraction_bps
    };
    if !(1..=BPS_SCALE).contains(&fraction) {
        return Err(REJ_GUARD);
    }

    // (5) Penalty + post-state bounds (mirrors guard_partial_liquidate).
    let penalty = partial_liq_penalty_capped(
        input.collateral_quote,
        input.position_base,
        fraction,
        input.index_price_e8,
        input.liquidation_penalty_bps,
        input.min_notional_for_bounty,
    );
    let new_collateral = input.collateral_quote - penalty;
    if !in_closed(new_collateral, 0, MAX_COLLATERAL) {
        return Err(REJ_GUARD);
    }
    let new_fee_pool = input.fee_pool_quote + penalty;
    if new_fee_pool > MAX_COLLATERAL {
        return Err(REJ_GUARD);
    }
    let new_fee_income = input.fee_income + penalty;
    if new_fee_income > MAX_COLLATERAL {
        return Err(REJ_GUARD);
    }
    let new_insurance = input.initial_insurance + new_fee_income - input.claims_paid;
    if new_insurance > MAX_COLLATERAL {
        return Err(REJ_GUARD);
    }

    let remaining = remaining_position_signed(input.position_base, fraction);
    if remaining != 0 {
        let mreq = maint_margin_req(
            remaining,
            input.index_price_e8,
            input.maintenance_margin_bps,
            input.depeg_buffer_bps,
        );
        if new_collateral < mreq {
            return Err(REJ_GUARD);
        }
    }

    // (6) Transition.
    Ok(PartialLiquidateOutput {
        position_base: remaining,
        entry_price_e8: if remaining == 0 {
            0
        } else {
            input.index_price_e8
        },
        collateral_quote: new_collateral,
        fee_pool_quote: new_fee_pool,
        fee_income: new_fee_income,
        insurance_balance: new_insurance,
        liquidated_this_step: true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn liquidatable_input() -> PartialLiquidateInput {
        // pos 1e6 long opened near 1e8; index drops so it is below maint margin.
        // notional @ 80e6 = 1e6*80e6/1e8 = 800_000; maint(6%) = 48_000 > collateral.
        PartialLiquidateInput {
            now_epoch: 4,
            epoch_phase: PHASE_OPEN,
            oracle_last_update_epoch: 3,
            max_oracle_staleness_epochs: 5,
            oracle_seen: true,
            index_price_e8: 80_000_000,
            position_base: 1_000_000,
            collateral_quote: 40_000,
            entry_price_e8: 100_000_000,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            liquidation_penalty_bps: 50,
            min_notional_for_bounty: 0,
            fee_pool_quote: 0,
            fee_income: 0,
            initial_insurance: 0,
            claims_paid: 0,
            fraction_bps: 0,
        }
    }

    #[test]
    fn auto_fraction_partially_closes_and_restores_margin() {
        let out = partial_liquidate(&liquidatable_input()).unwrap();
        assert!(out.liquidated_this_step);
        // Some position closed (or fully), penalty routed to fee_pool == fee_income.
        assert_eq!(out.fee_pool_quote, out.fee_income);
        assert_eq!(out.insurance_balance, out.fee_income);
        // If a position remains, it must meet maintenance margin.
        if out.position_base != 0 {
            let mreq = maint_margin_req(out.position_base, 80_000_000, 500, 100);
            assert!(out.collateral_quote >= mreq);
            assert_eq!(out.entry_price_e8, 80_000_000);
        } else {
            assert_eq!(out.entry_price_e8, 0);
        }
    }

    #[test]
    fn explicit_full_close_zeroes_position() {
        let mut inp = liquidatable_input();
        inp.fraction_bps = BPS_SCALE; // full close
        let out = partial_liquidate(&inp).unwrap();
        assert_eq!(out.position_base, 0);
        assert_eq!(out.entry_price_e8, 0);
    }

    #[test]
    fn rejects_healthy_position_as_guard() {
        let mut inp = liquidatable_input();
        inp.index_price_e8 = 100_000_000; // back at entry -> not underwater
        inp.collateral_quote = 200_000;
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_non_open_phase_as_guard() {
        let mut inp = liquidatable_input();
        inp.epoch_phase = PHASE_PRICE_PUBLISHED;
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_stale_oracle_as_guard() {
        let mut inp = liquidatable_input();
        inp.oracle_last_update_epoch = 0;
        inp.max_oracle_staleness_epochs = 1; // now=4, last=0 -> stale
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_flat_position_as_guard() {
        let mut inp = liquidatable_input();
        inp.position_base = 0;
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_fraction_above_param_max() {
        let mut inp = liquidatable_input();
        inp.fraction_bps = FRACTION_BPS_MAX + 1;
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_PARAM_FRACTION);
    }

    #[test]
    fn rejects_negative_fraction_as_param() {
        let mut inp = liquidatable_input();
        inp.fraction_bps = -1;
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_PARAM_FRACTION);
    }

    #[test]
    fn rejects_invalid_phase_domain() {
        let mut inp = liquidatable_input();
        inp.epoch_phase = 99;
        assert_eq!(partial_liquidate(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
    }
}

#[cfg(kani)]
mod kani_contracts {
    use super::*;

    fn liquidatable_input() -> PartialLiquidateInput {
        PartialLiquidateInput {
            now_epoch: 4,
            epoch_phase: PHASE_OPEN,
            oracle_last_update_epoch: 3,
            max_oracle_staleness_epochs: 5,
            oracle_seen: true,
            index_price_e8: 80_000_000,
            position_base: 1_000_000,
            collateral_quote: 40_000,
            entry_price_e8: 100_000_000,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            liquidation_penalty_bps: 50,
            min_notional_for_bounty: 0,
            fee_pool_quote: 0,
            fee_income: 0,
            initial_insurance: 0,
            claims_paid: 0,
            fraction_bps: BPS_SCALE,
        }
    }

    #[kani::proof]
    fn negative_fraction_rejects_as_param_domain() {
        let mut inp = liquidatable_input();
        inp.fraction_bps = -1;

        assert_eq!(partial_liquidate(&inp), Err(REJ_PARAM_FRACTION));
    }

    #[kani::proof]
    fn above_max_fraction_rejects_as_param_domain() {
        let mut inp = liquidatable_input();
        inp.fraction_bps = FRACTION_BPS_MAX + 1;

        assert_eq!(partial_liquidate(&inp), Err(REJ_PARAM_FRACTION));
    }

    #[kani::proof]
    fn full_close_accept_shape_is_exact() {
        let inp = liquidatable_input();
        let out = partial_liquidate(&inp).unwrap();

        assert_eq!(out.position_base, 0);
        assert_eq!(out.entry_price_e8, 0);
        assert!(out.liquidated_this_step);
        assert_eq!(out.fee_pool_quote, out.fee_income);
        assert_eq!(out.insurance_balance, out.fee_income);
        assert!(out.collateral_quote <= inp.collateral_quote);
    }

    #[kani::proof]
    fn non_open_phase_rejects_as_guard() {
        let mut inp = liquidatable_input();
        inp.epoch_phase = PHASE_SETTLED;

        assert_eq!(partial_liquidate(&inp), Err(REJ_GUARD));
    }

    #[kani::proof]
    fn partial_liquidate_covers_are_reachable() {
        let ok = liquidatable_input();
        kani::cover!(partial_liquidate(&ok).is_ok());

        let mut param = liquidatable_input();
        param.fraction_bps = FRACTION_BPS_MAX + 1;
        kani::cover!(partial_liquidate(&param) == Err(REJ_PARAM_FRACTION));

        let mut guard = liquidatable_input();
        guard.position_base = 0;
        kani::cover!(partial_liquidate(&guard) == Err(REJ_GUARD));

        let mut domain = liquidatable_input();
        domain.epoch_phase = 99;
        kani::cover!(partial_liquidate(&domain) == Err(REJ_OUT_OF_DOMAIN));
    }
}
