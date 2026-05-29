//! Stateful perps E2 — isolated account-management ops shadow.
//!
//! Shadows the OPEN-phase account ops in
//! `src/integration/perp_engine.py` (`_apply_isolated_deposit_collateral`,
//! `_apply_isolated_withdraw_collateral`, `_apply_isolated_set_position`,
//! `_apply_isolated_clear_breaker`) over the `perp_v2` guards/updates.
//!
//! * `deposit_collateral` / `withdraw_collateral` / `set_position` are
//!   single-account, sender-bound (`auth_ok = true` is set by the integration).
//! * `clear_breaker` is a global, operator-gated op: the integration rejects
//!   when **any** account holds an open position ("cannot clear breaker while
//!   positions are open"); the kernel then requires the breaker to be active.
//!   The shadow takes `all_positions_flat` (the integration's aggregate).
//!
//! Param domains: `amount ∈ [1, PERP_PARAM_AMOUNT_MAX = 1e12]`,
//! `new_position_base ∈ [-PERP_POSITION_MAX = -1e6, 1e6]`.
//!
//! Python remains authority; this is a shadow only.

use crate::perp_math::{
    abs_val, init_margin_req, is_oracle_fresh, maint_margin_req, MAX_ABS, MAX_BPS,
};

pub const MAX_EPOCH: i128 = 1_000_000;
pub const MAX_COLLATERAL: i128 = 1_000_000_000_000_000;
pub const AMOUNT_MAX: i128 = 1_000_000_000_000;
pub const POSITION_PARAM_MAX: i128 = 1_000_000;

pub const PHASE_OPEN: i128 = 0;
pub const PHASE_PRICE_PUBLISHED: i128 = 1;
pub const PHASE_SETTLED: i128 = 2;

pub const REJ_OUT_OF_DOMAIN: &str = "account_op_out_of_domain";
pub const REJ_UNKNOWN_OP: &str = "account_op_unknown";
pub const REJ_PARAM_AMOUNT: &str = "param_domain_amount";
pub const REJ_PARAM_NEW_POSITION: &str = "param_domain_new_position_base";
pub const REJ_DEPOSIT_GUARD: &str = "deposit_collateral_guard";
pub const REJ_WITHDRAW_GUARD: &str = "withdraw_collateral_guard";
pub const REJ_SET_POSITION_GUARD: &str = "set_position_guard";
pub const REJ_MAINT_MARGIN: &str = "invariant_maint_margin";
pub const REJ_CLEAR_BREAKER_GUARD: &str = "clear_breaker_guard";
pub const REJ_POSITIONS_OPEN: &str = "clear_breaker_positions_open";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountOpInput {
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
    pub initial_margin_bps: i128,
    pub max_position_abs: i128,
    pub breaker_active: bool,
    pub breaker_last_trigger_epoch: i128,
    pub amount: i128,
    pub new_position_base: i128,
    pub all_positions_flat: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountOpOutput {
    pub position_base: i128,
    pub entry_price_e8: i128,
    pub collateral_quote: i128,
    pub breaker_active: bool,
    pub breaker_last_trigger_epoch: i128,
}

#[inline]
fn in_closed(x: i128, lo: i128, hi: i128) -> bool {
    lo <= x && x <= hi
}

fn domain_ok(input: &AccountOpInput) -> bool {
    in_closed(input.now_epoch, 0, MAX_EPOCH)
        && in_closed(input.oracle_last_update_epoch, 0, MAX_EPOCH)
        && in_closed(input.max_oracle_staleness_epochs, 0, MAX_EPOCH)
        && matches!(
            input.epoch_phase,
            PHASE_OPEN | PHASE_PRICE_PUBLISHED | PHASE_SETTLED
        )
        && in_closed(input.index_price_e8, 0, MAX_ABS)
        && in_closed(input.position_base, -MAX_ABS, MAX_ABS)
        && in_closed(input.collateral_quote, 0, MAX_COLLATERAL)
        && in_closed(input.entry_price_e8, 0, MAX_ABS)
        && in_closed(input.maintenance_margin_bps, 0, MAX_BPS)
        && in_closed(input.depeg_buffer_bps, 0, MAX_BPS)
        && in_closed(input.initial_margin_bps, 0, MAX_BPS)
        && in_closed(input.max_position_abs, 0, MAX_ABS)
}

fn unchanged(input: &AccountOpInput) -> AccountOpOutput {
    AccountOpOutput {
        position_base: input.position_base,
        entry_price_e8: input.entry_price_e8,
        collateral_quote: input.collateral_quote,
        breaker_active: input.breaker_active,
        breaker_last_trigger_epoch: input.breaker_last_trigger_epoch,
    }
}

fn deposit_collateral(input: &AccountOpInput) -> Result<AccountOpOutput, &'static str> {
    if !in_closed(input.amount, 1, AMOUNT_MAX) {
        return Err(REJ_PARAM_AMOUNT);
    }
    if input.epoch_phase != PHASE_OPEN || input.collateral_quote + input.amount > MAX_COLLATERAL {
        return Err(REJ_DEPOSIT_GUARD);
    }
    Ok(AccountOpOutput {
        collateral_quote: input.collateral_quote + input.amount,
        ..unchanged(input)
    })
}

fn withdraw_collateral(input: &AccountOpInput) -> Result<AccountOpOutput, &'static str> {
    if !in_closed(input.amount, 1, AMOUNT_MAX) {
        return Err(REJ_PARAM_AMOUNT);
    }
    if input.epoch_phase != PHASE_OPEN || input.amount > input.collateral_quote {
        return Err(REJ_WITHDRAW_GUARD);
    }
    if input.position_base != 0 {
        let oracle_fresh = is_oracle_fresh(
            input.now_epoch,
            input.oracle_last_update_epoch,
            input.max_oracle_staleness_epochs,
            input.oracle_seen,
        );
        let remaining = input.collateral_quote - input.amount;
        let ok = input.index_price_e8 > 0
            && oracle_fresh
            && remaining
                >= maint_margin_req(
                    input.position_base,
                    input.index_price_e8,
                    input.maintenance_margin_bps,
                    input.depeg_buffer_bps,
                );
        if !ok {
            return Err(REJ_WITHDRAW_GUARD);
        }
    }
    Ok(AccountOpOutput {
        collateral_quote: input.collateral_quote - input.amount,
        ..unchanged(input)
    })
}

fn set_position_guard_ok(input: &AccountOpInput) -> bool {
    if input.epoch_phase != PHASE_OPEN || !input.oracle_seen {
        return false;
    }
    if abs_val(input.new_position_base) > input.max_position_abs {
        return false;
    }
    if input.breaker_active {
        // Reduce-only: no opening, no increase, no sign flip.
        if input.position_base == 0 && input.new_position_base != 0 {
            return false;
        }
        if abs_val(input.new_position_base) > abs_val(input.position_base) {
            return false;
        }
        if input.new_position_base != 0
            && ((input.position_base >= 0) != (input.new_position_base >= 0))
        {
            return false;
        }
        return true;
    }
    // Normal: oracle freshness + initial margin for the new position.
    if input.index_price_e8 <= 0
        || !is_oracle_fresh(
            input.now_epoch,
            input.oracle_last_update_epoch,
            input.max_oracle_staleness_epochs,
            input.oracle_seen,
        )
    {
        return false;
    }
    if input.new_position_base == 0 {
        return true;
    }
    input.collateral_quote
        >= init_margin_req(
            input.new_position_base,
            input.index_price_e8,
            input.initial_margin_bps,
        )
}

fn set_position(input: &AccountOpInput) -> Result<AccountOpOutput, &'static str> {
    if !in_closed(
        input.new_position_base,
        -POSITION_PARAM_MAX,
        POSITION_PARAM_MAX,
    ) {
        return Err(REJ_PARAM_NEW_POSITION);
    }
    if !set_position_guard_ok(input) {
        return Err(REJ_SET_POSITION_GUARD);
    }
    // Post-transition invariant `inv_maint_margin_ok`: the engine checks invariants
    // on the post-state. The normal path's initial-margin guard implies this (via
    // `inv_margin_params_ordered`: maint+depeg ≤ initial), but the breaker
    // reduce-only path does not check margin, so a reduction can still leave the
    // remaining position below maintenance -> `invariant:inv_maint_margin_ok`.
    if input.new_position_base != 0
        && input.collateral_quote
            < maint_margin_req(
                input.new_position_base,
                input.index_price_e8,
                input.maintenance_margin_bps,
                input.depeg_buffer_bps,
            )
    {
        return Err(REJ_MAINT_MARGIN);
    }
    Ok(AccountOpOutput {
        position_base: input.new_position_base,
        entry_price_e8: if input.new_position_base == 0 {
            0
        } else {
            input.index_price_e8
        },
        ..unchanged(input)
    })
}

fn clear_breaker(input: &AccountOpInput) -> Result<AccountOpOutput, &'static str> {
    // Integration aggregate gate first, then the kernel guard (breaker active).
    if !input.all_positions_flat {
        return Err(REJ_POSITIONS_OPEN);
    }
    if !input.breaker_active {
        return Err(REJ_CLEAR_BREAKER_GUARD);
    }
    Ok(AccountOpOutput {
        breaker_active: false,
        breaker_last_trigger_epoch: 0,
        ..unchanged(input)
    })
}

/// Dispatch an isolated account-management op.
pub fn account_op(op: &str, input: &AccountOpInput) -> Result<AccountOpOutput, &'static str> {
    if !domain_ok(input) {
        return Err(REJ_OUT_OF_DOMAIN);
    }
    match op {
        "deposit_collateral" => deposit_collateral(input),
        "withdraw_collateral" => withdraw_collateral(input),
        "set_position" => set_position(input),
        "clear_breaker" => clear_breaker(input),
        _ => Err(REJ_UNKNOWN_OP),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn open_input() -> AccountOpInput {
        AccountOpInput {
            now_epoch: 4,
            epoch_phase: PHASE_OPEN,
            oracle_last_update_epoch: 3,
            max_oracle_staleness_epochs: 100,
            oracle_seen: true,
            index_price_e8: 100_000_000,
            position_base: 500_000,
            collateral_quote: 200_000,
            entry_price_e8: 100_000_000,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            initial_margin_bps: 1000,
            max_position_abs: 1_000_000,
            breaker_active: false,
            breaker_last_trigger_epoch: 0,
            amount: 0,
            new_position_base: 0,
            all_positions_flat: false,
        }
    }

    #[test]
    fn deposit_adds_collateral() {
        let mut inp = open_input();
        inp.amount = 50_000;
        let out = account_op("deposit_collateral", &inp).unwrap();
        assert_eq!(out.collateral_quote, 250_000);
        assert_eq!(out.position_base, 500_000);
    }

    #[test]
    fn deposit_zero_amount_is_param_reject() {
        let mut inp = open_input();
        inp.amount = 0;
        assert_eq!(
            account_op("deposit_collateral", &inp).unwrap_err(),
            REJ_PARAM_AMOUNT
        );
    }

    #[test]
    fn deposit_outside_open_is_guard() {
        let mut inp = open_input();
        inp.amount = 50_000;
        inp.epoch_phase = PHASE_PRICE_PUBLISHED;
        assert_eq!(
            account_op("deposit_collateral", &inp).unwrap_err(),
            REJ_DEPOSIT_GUARD
        );
    }

    #[test]
    fn withdraw_within_margin_succeeds() {
        let mut inp = open_input();
        inp.amount = 50_000; // remaining 150_000 >> maint (~30_000 @ 500k pos)
        let out = account_op("withdraw_collateral", &inp).unwrap();
        assert_eq!(out.collateral_quote, 150_000);
    }

    #[test]
    fn withdraw_breaking_margin_is_guard() {
        let mut inp = open_input();
        // maint @ 500k pos, idx 1e8, 6% = 30_000. Withdraw down to 20_000 -> guard.
        inp.amount = 180_000;
        assert_eq!(
            account_op("withdraw_collateral", &inp).unwrap_err(),
            REJ_WITHDRAW_GUARD
        );
    }

    #[test]
    fn withdraw_more_than_collateral_is_guard() {
        let mut inp = open_input();
        inp.amount = 300_000;
        assert_eq!(
            account_op("withdraw_collateral", &inp).unwrap_err(),
            REJ_WITHDRAW_GUARD
        );
    }

    #[test]
    fn set_position_within_margin_sets_entry_to_index() {
        let mut inp = open_input();
        inp.new_position_base = 800_000; // init margin = 80_000 <= 200_000
        let out = account_op("set_position", &inp).unwrap();
        assert_eq!(out.position_base, 800_000);
        assert_eq!(out.entry_price_e8, 100_000_000);
    }

    #[test]
    fn set_position_flat_zeroes_entry() {
        let mut inp = open_input();
        inp.new_position_base = 0;
        let out = account_op("set_position", &inp).unwrap();
        assert_eq!(out.position_base, 0);
        assert_eq!(out.entry_price_e8, 0);
    }

    #[test]
    fn set_position_over_param_max_is_param_reject() {
        let mut inp = open_input();
        inp.new_position_base = POSITION_PARAM_MAX + 1;
        assert_eq!(
            account_op("set_position", &inp).unwrap_err(),
            REJ_PARAM_NEW_POSITION
        );
    }

    #[test]
    fn set_position_insufficient_initial_margin_is_guard() {
        let mut inp = open_input();
        inp.collateral_quote = 10_000;
        inp.new_position_base = 1_000_000; // init margin 100_000 > 10_000
        assert_eq!(
            account_op("set_position", &inp).unwrap_err(),
            REJ_SET_POSITION_GUARD
        );
    }

    #[test]
    fn set_position_reduce_only_under_breaker() {
        let mut inp = open_input();
        inp.breaker_active = true;
        inp.position_base = 500_000;
        // Increase is rejected under breaker.
        inp.new_position_base = 600_000;
        assert_eq!(
            account_op("set_position", &inp).unwrap_err(),
            REJ_SET_POSITION_GUARD
        );
        // Reduction is allowed.
        inp.new_position_base = 200_000;
        let out = account_op("set_position", &inp).unwrap();
        assert_eq!(out.position_base, 200_000);
    }

    #[test]
    fn set_position_reduce_only_below_maint_is_invariant() {
        // Reduce-only passes the guard, but the post-state collateral (10_000) is
        // below maint(200_000 @ 1e8, 6%) = 12_000 -> inv_maint_margin_ok.
        let mut inp = open_input();
        inp.breaker_active = true;
        inp.position_base = 300_000;
        inp.collateral_quote = 10_000;
        inp.new_position_base = 200_000;
        assert_eq!(
            account_op("set_position", &inp).unwrap_err(),
            REJ_MAINT_MARGIN
        );
    }

    #[test]
    fn clear_breaker_requires_flat_and_active() {
        let mut inp = open_input();
        inp.position_base = 0;
        // positions not flat (aggregate) -> positions-open.
        inp.all_positions_flat = false;
        inp.breaker_active = true;
        assert_eq!(
            account_op("clear_breaker", &inp).unwrap_err(),
            REJ_POSITIONS_OPEN
        );
        // flat but breaker inactive -> guard.
        inp.all_positions_flat = true;
        inp.breaker_active = false;
        assert_eq!(
            account_op("clear_breaker", &inp).unwrap_err(),
            REJ_CLEAR_BREAKER_GUARD
        );
        // flat + active -> clears.
        inp.breaker_active = true;
        inp.breaker_last_trigger_epoch = 3;
        let out = account_op("clear_breaker", &inp).unwrap();
        assert!(!out.breaker_active);
        assert_eq!(out.breaker_last_trigger_epoch, 0);
    }

    #[test]
    fn unknown_op_rejects() {
        assert_eq!(
            account_op("nope", &open_input()).unwrap_err(),
            REJ_UNKNOWN_OP
        );
    }
}
