//! Stateful perps E2 — isolated `set_market_params` shadow.
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_market_params`
//! (the body of `_apply_isolated_set_market_params`). Operator-only parameter
//! governance: it overlays a subset of the nine control params onto the current
//! market, validates the merged set, clamps the stored funding rate to the new
//! cap, and fails closed if any open position would be invalidated.
//!
//! Only the params present in the request are updated (overlay); absent params
//! keep their current value. An empty request is a no-op.
//!
//! Reject categories (the authority strings are mapped to these by the harness):
//!   * `set_market_params_param_domain` — a requested value is out of `[lo, hi]`.
//!   * `set_market_params_anti_farming` — raising penalty / lowering bounty
//!     notional while positions are open.
//!   * `set_market_params_ordering`     — margin-ordering invariants
//!     (`depeg > 0`, `max_move ≤ maint+depeg ≤ initial`, `0 < liq < maint+depeg`).
//!   * `set_market_params_min_notional` — bounty notional below the
//!     positive-penalty / policy floor.
//!   * `set_market_params_account_unsafe` — an open position would exceed the new
//!     `max_position_abs` or fall under maintenance margin at the new params.
//!
//! Operator/epoch-settled gates and unknown-key rejection are integration
//! concerns out of this transition's scope. Python remains authority; shadow only.

use crate::perp_math::checked_maint_margin_req;

pub const BPS_SCALE: i128 = 10_000;
pub const MAX_COLLATERAL: i128 = 1_000_000_000_000_000;
pub const MAX_ABS: i128 = 1_000_000_000_000_000_000;

pub const REJ_PARAM_DOMAIN: &str = "set_market_params_param_domain";
pub const REJ_ANTI_FARMING: &str = "set_market_params_anti_farming";
pub const REJ_ORDERING: &str = "set_market_params_ordering";
pub const REJ_MIN_NOTIONAL: &str = "set_market_params_min_notional";
pub const REJ_ACCOUNT_UNSAFE: &str = "set_market_params_account_unsafe";
pub const REJ_OUT_OF_DOMAIN: &str = "set_market_params_out_of_domain";

/// `(lo, hi)` bounds for each control param (`_ISOLATED_CONTROL_PARAM_BOUNDS`).
pub const BOUND_MAX_ORACLE_STALENESS: (i128, i128) = (1, 1_000_000);
pub const BOUND_MAX_ORACLE_MOVE_BPS: (i128, i128) = (0, 10_000);
pub const BOUND_INITIAL_MARGIN_BPS: (i128, i128) = (0, 10_000);
pub const BOUND_MAINTENANCE_MARGIN_BPS: (i128, i128) = (0, 10_000);
pub const BOUND_DEPEG_BUFFER_BPS: (i128, i128) = (0, 5_000);
pub const BOUND_LIQUIDATION_PENALTY_BPS: (i128, i128) = (0, 10_000);
pub const BOUND_MAX_POSITION_ABS: (i128, i128) = (1, 1_000_000);
pub const BOUND_FUNDING_CAP_BPS: (i128, i128) = (1, 10_000);
pub const BOUND_MIN_NOTIONAL_FOR_BOUNTY: (i128, i128) = (0, 1_000_000_000_000);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarketParamsAccount {
    pub position_base: i128,
    pub collateral_quote: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetMarketParamsInput {
    // Current control params (the overlay base).
    pub cur_max_oracle_staleness_epochs: i128,
    pub cur_max_oracle_move_bps: i128,
    pub cur_initial_margin_bps: i128,
    pub cur_maintenance_margin_bps: i128,
    pub cur_depeg_buffer_bps: i128,
    pub cur_liquidation_penalty_bps: i128,
    pub cur_max_position_abs: i128,
    pub cur_funding_cap_bps: i128,
    pub cur_min_notional_for_bounty: i128,
    pub cur_funding_rate_bps: i128,
    pub index_price_e8: i128,
    pub min_collectible_liquidation_penalty_quote: i128,
    // Requested updates (None => keep current).
    pub upd_max_oracle_staleness_epochs: Option<i128>,
    pub upd_max_oracle_move_bps: Option<i128>,
    pub upd_initial_margin_bps: Option<i128>,
    pub upd_maintenance_margin_bps: Option<i128>,
    pub upd_depeg_buffer_bps: Option<i128>,
    pub upd_liquidation_penalty_bps: Option<i128>,
    pub upd_max_position_abs: Option<i128>,
    pub upd_funding_cap_bps: Option<i128>,
    pub upd_min_notional_for_bounty: Option<i128>,
    pub accounts: Vec<MarketParamsAccount>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetMarketParamsOutput {
    pub max_oracle_staleness_epochs: i128,
    pub max_oracle_move_bps: i128,
    pub initial_margin_bps: i128,
    pub maintenance_margin_bps: i128,
    pub depeg_buffer_bps: i128,
    pub liquidation_penalty_bps: i128,
    pub max_position_abs: i128,
    pub funding_cap_bps: i128,
    pub min_notional_for_bounty: i128,
    pub funding_rate_bps: i128,
}

/// `ceil(a / b)` for `a >= 0`, `b > 0`.
#[inline]
fn ceil_div(a: i128, b: i128) -> i128 {
    (a + b - 1) / b
}

/// Validate one requested update against its bound (mirrors `_validated_control_params`:
/// `_require_int(non_negative)` then range). Returns the merged value.
fn merge_checked(cur: i128, upd: Option<i128>, bound: (i128, i128)) -> Result<i128, &'static str> {
    match upd {
        None => Ok(cur),
        Some(v) => {
            // require_int(non_negative=True) then [lo, hi]; lo >= 0 here so a
            // negative value is out of range either way.
            if v < bound.0 || v > bound.1 {
                Err(REJ_PARAM_DOMAIN)
            } else {
                Ok(v)
            }
        }
    }
}

pub fn set_market_params(
    input: &SetMarketParamsInput,
) -> Result<SetMarketParamsOutput, &'static str> {
    // (0) Defensive numeric domain on the current/contextual values.
    if !(0..=MAX_ABS).contains(&input.index_price_e8)
        || !(0..=MAX_COLLATERAL).contains(&input.min_collectible_liquidation_penalty_quote)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }

    let any_update = input.upd_max_oracle_staleness_epochs.is_some()
        || input.upd_max_oracle_move_bps.is_some()
        || input.upd_initial_margin_bps.is_some()
        || input.upd_maintenance_margin_bps.is_some()
        || input.upd_depeg_buffer_bps.is_some()
        || input.upd_liquidation_penalty_bps.is_some()
        || input.upd_max_position_abs.is_some()
        || input.upd_funding_cap_bps.is_some()
        || input.upd_min_notional_for_bounty.is_some();

    // (1) Per-key bound validation + overlay merge.
    let max_oracle_staleness_epochs = merge_checked(
        input.cur_max_oracle_staleness_epochs,
        input.upd_max_oracle_staleness_epochs,
        BOUND_MAX_ORACLE_STALENESS,
    )?;
    let max_oracle_move_bps = merge_checked(
        input.cur_max_oracle_move_bps,
        input.upd_max_oracle_move_bps,
        BOUND_MAX_ORACLE_MOVE_BPS,
    )?;
    let initial_margin_bps = merge_checked(
        input.cur_initial_margin_bps,
        input.upd_initial_margin_bps,
        BOUND_INITIAL_MARGIN_BPS,
    )?;
    let maintenance_margin_bps = merge_checked(
        input.cur_maintenance_margin_bps,
        input.upd_maintenance_margin_bps,
        BOUND_MAINTENANCE_MARGIN_BPS,
    )?;
    let depeg_buffer_bps = merge_checked(
        input.cur_depeg_buffer_bps,
        input.upd_depeg_buffer_bps,
        BOUND_DEPEG_BUFFER_BPS,
    )?;
    let liquidation_penalty_bps = merge_checked(
        input.cur_liquidation_penalty_bps,
        input.upd_liquidation_penalty_bps,
        BOUND_LIQUIDATION_PENALTY_BPS,
    )?;
    let max_position_abs = merge_checked(
        input.cur_max_position_abs,
        input.upd_max_position_abs,
        BOUND_MAX_POSITION_ABS,
    )?;
    let funding_cap_bps = merge_checked(
        input.cur_funding_cap_bps,
        input.upd_funding_cap_bps,
        BOUND_FUNDING_CAP_BPS,
    )?;
    let min_notional_for_bounty = merge_checked(
        input.cur_min_notional_for_bounty,
        input.upd_min_notional_for_bounty,
        BOUND_MIN_NOTIONAL_FOR_BOUNTY,
    )?;

    // (2) Empty request is a no-op (still after bound validation, matching the authority).
    if !any_update {
        return Ok(current_output(input));
    }

    let has_open_positions = input.accounts.iter().any(|a| a.position_base != 0);

    // (3) Anti-farming while positions are open.
    if has_open_positions {
        if liquidation_penalty_bps > input.cur_liquidation_penalty_bps {
            return Err(REJ_ANTI_FARMING);
        }
        if min_notional_for_bounty < input.cur_min_notional_for_bounty {
            return Err(REJ_ANTI_FARMING);
        }
    }

    // (4) Funding-rate clamp to the new cap (mutation, not a reject).
    let cur_funding_rate_abs = input
        .cur_funding_rate_bps
        .checked_abs()
        .ok_or(REJ_OUT_OF_DOMAIN)?;
    let funding_rate_bps = if cur_funding_rate_abs > funding_cap_bps {
        if input.cur_funding_rate_bps >= 0 {
            funding_cap_bps
        } else {
            -funding_cap_bps
        }
    } else {
        input.cur_funding_rate_bps
    };

    // (5) Margin-ordering invariants (authority order).
    let eff_maint_bps = maintenance_margin_bps + depeg_buffer_bps;
    if depeg_buffer_bps <= 0
        || max_oracle_move_bps > eff_maint_bps
        || eff_maint_bps > initial_margin_bps
        || liquidation_penalty_bps >= eff_maint_bps
        || liquidation_penalty_bps <= 0
    {
        return Err(REJ_ORDERING);
    }

    // (6) Bounty-notional floors (liquidation_penalty_bps > 0 here).
    let min_notional_for_positive_penalty = ceil_div(BPS_SCALE, liquidation_penalty_bps);
    if min_notional_for_bounty < min_notional_for_positive_penalty {
        return Err(REJ_MIN_NOTIONAL);
    }
    if input.min_collectible_liquidation_penalty_quote > 0 {
        let policy_floor = ceil_div(
            input.min_collectible_liquidation_penalty_quote * BPS_SCALE,
            liquidation_penalty_bps,
        );
        if min_notional_for_bounty < policy_floor {
            return Err(REJ_MIN_NOTIONAL);
        }
    }

    // (7) Open-position safety at the new params.
    for acct in &input.accounts {
        let position_abs = acct.position_base.checked_abs().ok_or(REJ_OUT_OF_DOMAIN)?;
        if position_abs > max_position_abs {
            return Err(REJ_ACCOUNT_UNSAFE);
        }
        if acct.position_base != 0 {
            let mreq = checked_maint_margin_req(
                acct.position_base,
                input.index_price_e8,
                maintenance_margin_bps,
                depeg_buffer_bps,
            )
            .ok_or(REJ_OUT_OF_DOMAIN)?;
            if acct.collateral_quote < mreq {
                return Err(REJ_ACCOUNT_UNSAFE);
            }
        }
    }

    Ok(SetMarketParamsOutput {
        max_oracle_staleness_epochs,
        max_oracle_move_bps,
        initial_margin_bps,
        maintenance_margin_bps,
        depeg_buffer_bps,
        liquidation_penalty_bps,
        max_position_abs,
        funding_cap_bps,
        min_notional_for_bounty,
        funding_rate_bps,
    })
}

fn current_output(input: &SetMarketParamsInput) -> SetMarketParamsOutput {
    SetMarketParamsOutput {
        max_oracle_staleness_epochs: input.cur_max_oracle_staleness_epochs,
        max_oracle_move_bps: input.cur_max_oracle_move_bps,
        initial_margin_bps: input.cur_initial_margin_bps,
        maintenance_margin_bps: input.cur_maintenance_margin_bps,
        depeg_buffer_bps: input.cur_depeg_buffer_bps,
        liquidation_penalty_bps: input.cur_liquidation_penalty_bps,
        max_position_abs: input.cur_max_position_abs,
        funding_cap_bps: input.cur_funding_cap_bps,
        min_notional_for_bounty: input.cur_min_notional_for_bounty,
        funding_rate_bps: input.cur_funding_rate_bps,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base() -> SetMarketParamsInput {
        // A consistent default param set (matches the market defaults).
        SetMarketParamsInput {
            cur_max_oracle_staleness_epochs: 100,
            cur_max_oracle_move_bps: 500,
            cur_initial_margin_bps: 1000,
            cur_maintenance_margin_bps: 500,
            cur_depeg_buffer_bps: 100,
            cur_liquidation_penalty_bps: 50,
            cur_max_position_abs: 1_000_000,
            cur_funding_cap_bps: 1000,
            cur_min_notional_for_bounty: 100_000_000,
            cur_funding_rate_bps: 0,
            index_price_e8: 100_000_000,
            min_collectible_liquidation_penalty_quote: 0,
            upd_max_oracle_staleness_epochs: None,
            upd_max_oracle_move_bps: None,
            upd_initial_margin_bps: None,
            upd_maintenance_margin_bps: None,
            upd_depeg_buffer_bps: None,
            upd_liquidation_penalty_bps: None,
            upd_max_position_abs: None,
            upd_funding_cap_bps: None,
            upd_min_notional_for_bounty: None,
            accounts: vec![],
        }
    }

    #[test]
    fn empty_request_is_noop() {
        let out = set_market_params(&base()).unwrap();
        assert_eq!(out.maintenance_margin_bps, 500);
        assert_eq!(out.funding_cap_bps, 1000);
    }

    #[test]
    fn valid_update_applies() {
        let mut inp = base();
        inp.upd_maintenance_margin_bps = Some(600);
        let out = set_market_params(&inp).unwrap();
        assert_eq!(out.maintenance_margin_bps, 600);
    }

    #[test]
    fn out_of_range_is_param_domain() {
        let mut inp = base();
        inp.upd_depeg_buffer_bps = Some(6000); // > 5000
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_PARAM_DOMAIN);
    }

    #[test]
    fn negative_update_is_param_domain() {
        let mut inp = base();
        inp.upd_max_oracle_move_bps = Some(-1);
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_PARAM_DOMAIN);
    }

    #[test]
    fn ordering_violation_rejects() {
        let mut inp = base();
        // maint+depeg = 9000+100 > initial 1000 -> ordering.
        inp.upd_maintenance_margin_bps = Some(9000);
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_ORDERING);
    }

    #[test]
    fn liq_penalty_zero_rejects_ordering() {
        let mut inp = base();
        inp.upd_liquidation_penalty_bps = Some(0);
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_ORDERING);
    }

    #[test]
    fn min_notional_below_positive_penalty_floor() {
        let mut inp = base();
        // liq_penalty 50 -> positive-penalty floor = ceil(10000/50) = 200.
        inp.upd_min_notional_for_bounty = Some(100);
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_MIN_NOTIONAL);
    }

    #[test]
    fn anti_farming_increase_penalty_with_open_positions() {
        let mut inp = base();
        inp.accounts = vec![MarketParamsAccount {
            position_base: 500_000,
            collateral_quote: 200_000,
        }];
        inp.upd_liquidation_penalty_bps = Some(80); // > current 50
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_ANTI_FARMING);
    }

    #[test]
    fn account_unsafe_under_maintenance() {
        let mut inp = base();
        inp.accounts = vec![MarketParamsAccount {
            position_base: 1_000_000,
            collateral_quote: 1_000,
        }];
        // Raise maintenance so the open position is under margin (no penalty raise:
        // keep liq_penalty, raise maint to 590 so maint+depeg=690 stays ordered).
        inp.upd_maintenance_margin_bps = Some(590);
        // maint_req(1e6 @ 1e8, 690bps) = 1e6 * 690/1e4 = 69_000 > collateral 1_000.
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_ACCOUNT_UNSAFE);
    }

    #[test]
    fn account_position_exceeds_new_max() {
        let mut inp = base();
        inp.accounts = vec![MarketParamsAccount {
            position_base: 800_000,
            collateral_quote: 200_000,
        }];
        inp.upd_max_position_abs = Some(500_000); // < open 800_000
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_ACCOUNT_UNSAFE);
    }

    #[test]
    fn funding_rate_clamped_to_new_cap() {
        let mut inp = base();
        inp.cur_funding_rate_bps = 900;
        inp.upd_funding_cap_bps = Some(500); // lower cap below stored rate
        let out = set_market_params(&inp).unwrap();
        assert_eq!(out.funding_cap_bps, 500);
        assert_eq!(out.funding_rate_bps, 500); // clamped
    }

    #[test]
    fn funding_rate_i128_min_rejects_without_panic() {
        let mut inp = base();
        inp.cur_funding_rate_bps = i128::MIN;
        inp.upd_funding_cap_bps = Some(500);
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
    }

    #[test]
    fn account_position_i128_min_rejects_without_panic() {
        let mut inp = base();
        inp.accounts = vec![MarketParamsAccount {
            position_base: i128::MIN,
            collateral_quote: 200_000,
        }];
        inp.upd_max_position_abs = Some(500_000);
        assert_eq!(set_market_params(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
    }
}

#[cfg(kani)]
mod kani_contracts {
    use super::*;

    fn base_no_accounts() -> SetMarketParamsInput {
        SetMarketParamsInput {
            cur_max_oracle_staleness_epochs: 100,
            cur_max_oracle_move_bps: 500,
            cur_initial_margin_bps: 1000,
            cur_maintenance_margin_bps: 500,
            cur_depeg_buffer_bps: 100,
            cur_liquidation_penalty_bps: 50,
            cur_max_position_abs: 1_000_000,
            cur_funding_cap_bps: 1000,
            cur_min_notional_for_bounty: 100_000_000,
            cur_funding_rate_bps: 0,
            index_price_e8: 100_000_000,
            min_collectible_liquidation_penalty_quote: 0,
            upd_max_oracle_staleness_epochs: None,
            upd_max_oracle_move_bps: None,
            upd_initial_margin_bps: None,
            upd_maintenance_margin_bps: None,
            upd_depeg_buffer_bps: None,
            upd_liquidation_penalty_bps: None,
            upd_max_position_abs: None,
            upd_funding_cap_bps: None,
            upd_min_notional_for_bounty: None,
            accounts: vec![],
        }
    }

    #[kani::proof]
    fn empty_request_returns_current_params() {
        let mut inp = base_no_accounts();
        inp.cur_funding_rate_bps = kani::any();

        let out = set_market_params(&inp).unwrap();
        assert_eq!(out, current_output(&inp));
    }

    #[kani::proof]
    fn funding_rate_clamps_to_requested_cap_without_accounts() {
        let rate_raw: i32 = kani::any();
        let cap_raw: i32 = kani::any();
        kani::assume((-20_000..=20_000).contains(&rate_raw));
        kani::assume((1..=10_000).contains(&cap_raw));

        let mut inp = base_no_accounts();
        inp.cur_funding_rate_bps = rate_raw as i128;
        inp.upd_funding_cap_bps = Some(cap_raw as i128);

        let out = set_market_params(&inp).unwrap();
        assert_eq!(out.funding_cap_bps, cap_raw as i128);
        assert!(out.funding_rate_bps.checked_abs().unwrap() <= cap_raw as i128);
    }

    #[kani::proof]
    fn set_market_params_covers_are_reachable() {
        let base = base_no_accounts();
        kani::cover!(set_market_params(&base).is_ok());

        let mut param_domain = base_no_accounts();
        param_domain.upd_depeg_buffer_bps = Some(BOUND_DEPEG_BUFFER_BPS.1 + 1);
        kani::cover!(set_market_params(&param_domain) == Err(REJ_PARAM_DOMAIN));

        let mut ordering = base_no_accounts();
        ordering.upd_liquidation_penalty_bps = Some(0);
        kani::cover!(set_market_params(&ordering) == Err(REJ_ORDERING));

        let mut min_notional = base_no_accounts();
        min_notional.upd_min_notional_for_bounty = Some(100);
        kani::cover!(set_market_params(&min_notional) == Err(REJ_MIN_NOTIONAL));

        let mut clamp = base_no_accounts();
        clamp.cur_funding_rate_bps = 900;
        clamp.upd_funding_cap_bps = Some(500);
        kani::cover!(set_market_params(&clamp)
            .map(|out| out.funding_rate_bps == 500)
            .unwrap_or(false));
    }
}
