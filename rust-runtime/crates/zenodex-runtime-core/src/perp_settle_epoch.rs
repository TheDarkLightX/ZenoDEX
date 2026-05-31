//! Stateful perps E2 — isolated `settle_epoch` shadow.
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_settle_epoch`.
//! Unlike `advance_epoch` / `publish_clearing_price` this transition mutates
//! **per-account** state (PnL realization + optional liquidation) as well as the
//! global epoch/breaker/fee/insurance fields.
//!
//! ## Faithfulness contract (mirrors the integration orchestration)
//!
//! Phase 1 — global guard via a flat "dummy" account: the kernel
//! `guard_settle_epoch` (`perp_v2/guards.py`) requires
//! `epoch_phase == PricePublished ∧ clearing_price_seen ∧
//! clearing_price_epoch == now_epoch ∧ oracle_last_update_epoch < now_epoch`.
//! If this fails the authority rejects with `settle_epoch rejected` (mapped here
//! to `REJ_GUARD`). The post-epoch global update is computed once and must be
//! identical for every account: `oracle_last = now`, `oracle_seen = true`,
//! `epoch_phase = Settled`, `index_price = sp` (the clamped settlement price),
//! `breaker_active |= move_violated`, `breaker_last_trigger = now if violated`.
//!
//! Phase 2 — each account is settled against the **same pre-global** state:
//!   `sp = settle_price(clearing, index, max_move, oracle_seen)`
//!   `pnl = pnl_quote(pos, sp, index)`; `coll' = collateral + pnl`
//!   guard: `0 ≤ coll' ≤ MAX_COLLATERAL`; if liquidatable, the penalty must not
//!   push `fee_pool / fee_income / insurance` over `MAX_COLLATERAL` (per-account,
//!   against pre-globals). On liquidation: `penalty = liq_penalty_capped(...)`,
//!   `coll' -= penalty`, position/entry → 0; the penalty is added to
//!   `fee_pool / fee_income` (equal deltas). A strictly-flat, in-bounds, stable
//!   account is left untouched (the authority's fast path) and contributes 0.
//!
//! Phase 3 — penalties are summed and the globals reassembled once:
//!   `fee_pool += Σpenalty`, `fee_income += Σpenalty`,
//!   `insurance = initial_insurance + fee_income' - claims_paid`, with a
//!   post-settle overflow bound (`MAX_COLLATERAL`) and non-negativity check.
//!
//! Reject codes map to the authority strings: global/per-account guard →
//! `settle_epoch rejected[...]` → `REJ_GUARD`; `fee/insurance overflow
//! (post-settle)` → `REJ_FEE_OVERFLOW`; `insurance negative (post-settle)` →
//! `REJ_INSURANCE_NEGATIVE`. Oracle-adapter/authorization gates are integration
//! auth concerns (like the operator gate) and are out of this transition's scope.
//!
//! Python remains authority. This is a shadow/checker surface only.

use crate::perp_math::{
    is_liquidatable, liq_penalty_capped, oracle_move_violated, pnl_quote, settle_price, MAX_ABS,
    MAX_BPS,
};

pub const MAX_EPOCH: i128 = 1_000_000;
/// `MAX_COLLATERAL` (`perp_v2`); also the post-settle fee/insurance overflow bound.
pub const MAX_COLLATERAL: i128 = 1_000_000_000_000_000;

pub const PHASE_OPEN: i128 = 0;
pub const PHASE_PRICE_PUBLISHED: i128 = 1;
pub const PHASE_SETTLED: i128 = 2;

pub const REJ_OUT_OF_DOMAIN: &str = "settle_epoch_out_of_domain";
pub const REJ_GUARD: &str = "settle_epoch_guard";
pub const REJ_FEE_OVERFLOW: &str = "settle_epoch_fee_overflow";
pub const REJ_INSURANCE_NEGATIVE: &str = "settle_epoch_insurance_negative";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettleAccount {
    pub key: String,
    pub position_base: i128,
    pub collateral_quote: i128,
    pub entry_price_e8: i128,
    pub liquidated_this_step: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettleEpochInput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub clearing_price_seen: bool,
    pub clearing_price_epoch: i128,
    pub clearing_price_e8: i128,
    pub oracle_last_update_epoch: i128,
    pub oracle_seen: bool,
    pub index_price_e8: i128,
    pub max_oracle_move_bps: i128,
    pub maintenance_margin_bps: i128,
    pub depeg_buffer_bps: i128,
    pub liquidation_penalty_bps: i128,
    pub min_notional_for_bounty: i128,
    pub fee_pool_quote: i128,
    pub fee_income: i128,
    pub initial_insurance: i128,
    pub claims_paid: i128,
    pub breaker_active: bool,
    pub breaker_last_trigger_epoch: i128,
    pub accounts: Vec<SettleAccount>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettleEpochOutput {
    pub now_epoch: i128,
    pub epoch_phase: i128,
    pub oracle_last_update_epoch: i128,
    pub oracle_seen: bool,
    pub index_price_e8: i128,
    pub breaker_active: bool,
    pub breaker_last_trigger_epoch: i128,
    pub fee_pool_quote: i128,
    pub fee_income: i128,
    pub insurance_balance: i128,
    pub accounts: Vec<SettleAccount>,
}

#[inline]
fn in_closed(x: i128, lo: i128, hi: i128) -> bool {
    lo <= x && x <= hi
}

#[inline]
fn valid_phase(phase: i128) -> bool {
    matches!(phase, PHASE_OPEN | PHASE_PRICE_PUBLISHED | PHASE_SETTLED)
}

#[inline]
fn account_domain_ok(position_base: i128, collateral_quote: i128, entry_price_e8: i128) -> bool {
    in_closed(position_base, -MAX_ABS, MAX_ABS)
        && in_closed(collateral_quote, 0, MAX_COLLATERAL)
        && in_closed(entry_price_e8, 0, MAX_ABS)
}

#[inline]
fn flat_fast_path_ok(
    position_base: i128,
    entry_price_e8: i128,
    liquidated_this_step: bool,
    collateral_quote: i128,
) -> bool {
    position_base == 0
        && entry_price_e8 == 0
        && !liquidated_this_step
        && in_closed(collateral_quote, 0, MAX_COLLATERAL)
}

#[inline]
fn settle_global_guard_ok(
    epoch_phase: i128,
    clearing_price_seen: bool,
    clearing_price_epoch: i128,
    now_epoch: i128,
    oracle_last_update_epoch: i128,
) -> bool {
    epoch_phase == PHASE_PRICE_PUBLISHED
        && clearing_price_seen
        && clearing_price_epoch == now_epoch
        && oracle_last_update_epoch < now_epoch
}

/// Per-account settled result + the penalty added to the global fee/insurance.
struct AccountSettlement {
    account: SettleAccount,
    penalty: i128,
}

/// Settle one account against the pre-global state. Mirrors `apply_settle_epoch`
/// plus the kernel guard's per-account bounds (`guard_settle_epoch`).
fn settle_one(
    input: &SettleEpochInput,
    acct: &SettleAccount,
    sp: i128,
) -> Result<AccountSettlement, &'static str> {
    // Authority fast path: a strictly-flat, in-bounds, stable account is untouched.
    if flat_fast_path_ok(
        acct.position_base,
        acct.entry_price_e8,
        acct.liquidated_this_step,
        acct.collateral_quote,
    ) {
        return Ok(AccountSettlement {
            account: acct.clone(),
            penalty: 0,
        });
    }

    let pnl = pnl_quote(acct.position_base, sp, input.index_price_e8);
    let coll_after_pnl = acct
        .collateral_quote
        .checked_add(pnl)
        .ok_or(REJ_OUT_OF_DOMAIN)?;

    // Kernel guard: post-PnL collateral must stay within integer bounds.
    if !in_closed(coll_after_pnl, 0, MAX_COLLATERAL) {
        return Err(REJ_GUARD);
    }

    let liq = acct.position_base != 0
        && is_liquidatable(
            acct.position_base,
            coll_after_pnl,
            sp,
            input.maintenance_margin_bps,
            input.depeg_buffer_bps,
        );

    if liq {
        let penalty = liq_penalty_capped(
            coll_after_pnl,
            acct.position_base,
            sp,
            input.liquidation_penalty_bps,
            input.min_notional_for_bounty,
        );
        // Kernel guard: per-account liquidation overflow checks (against pre-globals).
        if input.fee_pool_quote + penalty > MAX_COLLATERAL {
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
        Ok(AccountSettlement {
            account: SettleAccount {
                key: acct.key.clone(),
                position_base: 0,
                collateral_quote: coll_after_pnl - penalty,
                entry_price_e8: 0,
                liquidated_this_step: true,
            },
            penalty,
        })
    } else {
        // Spec: entry_price_e8 is 0 when flat, else the settled price.
        let new_entry = if acct.position_base == 0 { 0 } else { sp };
        Ok(AccountSettlement {
            account: SettleAccount {
                key: acct.key.clone(),
                position_base: acct.position_base,
                collateral_quote: coll_after_pnl,
                entry_price_e8: new_entry,
                liquidated_this_step: false,
            },
            penalty: 0,
        })
    }
}

pub fn settle_epoch(input: &SettleEpochInput) -> Result<SettleEpochOutput, &'static str> {
    // (1) Numeric/param input domain (sound bounds: every valid state passes).
    if !in_closed(input.now_epoch, 0, MAX_EPOCH)
        || !in_closed(input.clearing_price_epoch, 0, MAX_EPOCH)
        || !in_closed(input.oracle_last_update_epoch, 0, input.now_epoch)
        || !valid_phase(input.epoch_phase)
        || !in_closed(input.index_price_e8, 0, MAX_ABS)
        || !in_closed(input.clearing_price_e8, 0, MAX_ABS)
        || !in_closed(input.max_oracle_move_bps, 0, MAX_BPS)
        || !in_closed(input.maintenance_margin_bps, 0, MAX_BPS)
        || !in_closed(input.depeg_buffer_bps, 0, MAX_BPS)
        || !in_closed(input.liquidation_penalty_bps, 0, MAX_BPS)
        || !in_closed(input.min_notional_for_bounty, 0, MAX_ABS)
        || !in_closed(input.fee_pool_quote, 0, MAX_COLLATERAL)
        || !in_closed(input.fee_income, 0, MAX_COLLATERAL)
        || !in_closed(input.initial_insurance, 0, MAX_COLLATERAL)
        || !in_closed(input.claims_paid, 0, MAX_COLLATERAL)
        || !in_closed(input.breaker_last_trigger_epoch, 0, MAX_EPOCH)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }
    for acct in &input.accounts {
        if !account_domain_ok(
            acct.position_base,
            acct.collateral_quote,
            acct.entry_price_e8,
        ) {
            return Err(REJ_OUT_OF_DOMAIN);
        }
    }

    // (2) Global guard (Phase 1, the flat-dummy guard): the settle preconditions.
    if !settle_global_guard_ok(
        input.epoch_phase,
        input.clearing_price_seen,
        input.clearing_price_epoch,
        input.now_epoch,
        input.oracle_last_update_epoch,
    ) {
        return Err(REJ_GUARD);
    }

    // (3) Global post-epoch update, computed once (account-independent).
    let sp = settle_price(
        input.clearing_price_e8,
        input.index_price_e8,
        input.max_oracle_move_bps,
        input.oracle_seen,
    );
    let move_violated = oracle_move_violated(
        input.clearing_price_e8,
        input.index_price_e8,
        input.max_oracle_move_bps,
        input.oracle_seen,
    );

    // (4) Settle each account against the same pre-global state; sum penalties.
    let mut total_penalty: i128 = 0;
    let mut out_accounts: Vec<SettleAccount> = Vec::with_capacity(input.accounts.len());
    for acct in &input.accounts {
        let settled = settle_one(input, acct, sp)?;
        total_penalty = total_penalty
            .checked_add(settled.penalty)
            .ok_or(REJ_FEE_OVERFLOW)?;
        out_accounts.push(settled.account);
    }

    // (5) Reassemble the global fee/insurance accounting once.
    let next_fee_pool = input.fee_pool_quote + total_penalty;
    let next_fee_income = input.fee_income + total_penalty;
    let next_insurance = input.initial_insurance + next_fee_income - input.claims_paid;
    if next_fee_pool > MAX_COLLATERAL
        || next_fee_income > MAX_COLLATERAL
        || next_insurance > MAX_COLLATERAL
    {
        return Err(REJ_FEE_OVERFLOW);
    }
    if next_insurance < 0 {
        return Err(REJ_INSURANCE_NEGATIVE);
    }

    Ok(SettleEpochOutput {
        now_epoch: input.now_epoch,
        epoch_phase: PHASE_SETTLED,
        oracle_last_update_epoch: input.now_epoch,
        oracle_seen: true,
        index_price_e8: sp,
        breaker_active: input.breaker_active || move_violated,
        breaker_last_trigger_epoch: if move_violated {
            input.now_epoch
        } else {
            input.breaker_last_trigger_epoch
        },
        fee_pool_quote: next_fee_pool,
        fee_income: next_fee_income,
        insurance_balance: next_insurance,
        accounts: out_accounts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base_input() -> SettleEpochInput {
        // A consistent PricePublished global at now=5 (oracle stale at 4),
        // clearing == index so there is no oracle-move clamp/breaker.
        SettleEpochInput {
            now_epoch: 5,
            epoch_phase: PHASE_PRICE_PUBLISHED,
            clearing_price_seen: true,
            clearing_price_epoch: 5,
            clearing_price_e8: 100_000_000,
            oracle_last_update_epoch: 4,
            oracle_seen: true,
            index_price_e8: 100_000_000,
            max_oracle_move_bps: 500,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            liquidation_penalty_bps: 200,
            min_notional_for_bounty: 0,
            fee_pool_quote: 0,
            fee_income: 0,
            initial_insurance: 0,
            claims_paid: 0,
            breaker_active: false,
            breaker_last_trigger_epoch: 0,
            accounts: vec![],
        }
    }

    #[test]
    fn settles_empty_market_to_settled_phase() {
        let out = settle_epoch(&base_input()).unwrap();
        assert_eq!(out.epoch_phase, PHASE_SETTLED);
        assert_eq!(out.oracle_last_update_epoch, 5);
        assert!(out.oracle_seen);
        assert_eq!(out.index_price_e8, 100_000_000);
        assert!(!out.breaker_active);
        assert_eq!(out.fee_pool_quote, 0);
        assert_eq!(out.insurance_balance, 0);
    }

    #[test]
    fn flat_account_is_untouched() {
        let mut inp = base_input();
        inp.accounts = vec![SettleAccount {
            key: "a".into(),
            position_base: 0,
            collateral_quote: 1_000,
            entry_price_e8: 0,
            liquidated_this_step: false,
        }];
        let out = settle_epoch(&inp).unwrap();
        assert_eq!(out.accounts[0].collateral_quote, 1_000);
        assert_eq!(out.accounts[0].position_base, 0);
        assert!(!out.accounts[0].liquidated_this_step);
    }

    #[test]
    fn long_position_profits_when_settle_above_index() {
        // index moves up to 102e6 within the 5% move band; long gains PnL.
        let mut inp = base_input();
        inp.index_price_e8 = 100_000_000;
        inp.clearing_price_e8 = 102_000_000; // +2% < 5% band -> sp = clearing
        inp.accounts = vec![SettleAccount {
            key: "a".into(),
            position_base: 100_000_000, // 1.0 base
            collateral_quote: 50_000_000,
            entry_price_e8: 100_000_000,
            liquidated_this_step: false,
        }];
        let out = settle_epoch(&inp).unwrap();
        // pnl = |1.0| * |102e6-100e6| / 1e8 = 2_000_000, same sign (long & up).
        assert_eq!(out.index_price_e8, 102_000_000);
        assert_eq!(out.accounts[0].collateral_quote, 52_000_000);
        assert_eq!(out.accounts[0].entry_price_e8, 102_000_000);
        assert_eq!(out.accounts[0].position_base, 100_000_000);
    }

    #[test]
    fn undercollateralized_position_is_liquidated_with_penalty() {
        // Big position, tiny collateral, adverse move -> liquidatable.
        let mut inp = base_input();
        inp.min_notional_for_bounty = 0;
        inp.liquidation_penalty_bps = 200;
        inp.index_price_e8 = 100_000_000;
        inp.clearing_price_e8 = 99_000_000; // -1% within band -> sp = 99e6
        inp.accounts = vec![SettleAccount {
            key: "a".into(),
            // pos 10 base; pnl = -10_000_000 keeps coll_after >= 0 (20e6 -> 10e6),
            // but maint margin (notional 990e6 * 6% = 59.4e6) > coll_after -> liquidatable.
            position_base: 1_000_000_000,
            collateral_quote: 20_000_000,
            entry_price_e8: 100_000_000,
            liquidated_this_step: false,
        }];
        let out = settle_epoch(&inp).unwrap();
        assert!(out.accounts[0].liquidated_this_step);
        assert_eq!(out.accounts[0].position_base, 0);
        assert_eq!(out.accounts[0].entry_price_e8, 0);
        // penalty flowed into fee_pool == fee_income; insurance tracks it.
        assert!(out.fee_pool_quote > 0);
        assert_eq!(out.fee_pool_quote, out.fee_income);
        assert_eq!(out.insurance_balance, out.fee_income);
    }

    #[test]
    fn rejects_non_price_published_as_guard() {
        let mut inp = base_input();
        inp.epoch_phase = PHASE_SETTLED;
        inp.oracle_last_update_epoch = 5; // Settled invariant, but settle needs PricePublished
        assert_eq!(settle_epoch(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_pnl_underflow_collateral_as_guard() {
        // Adverse move drives collateral below zero before liquidation accounting.
        let mut inp = base_input();
        inp.index_price_e8 = 100_000_000;
        inp.clearing_price_e8 = 96_000_000; // -4% within 5% band
        inp.accounts = vec![SettleAccount {
            key: "a".into(),
            position_base: 1_000_000_000_000, // huge long
            collateral_quote: 10,
            entry_price_e8: 100_000_000,
            liquidated_this_step: false,
        }];
        // coll_after_pnl = 10 - (huge loss) < 0 -> guard.
        assert_eq!(settle_epoch(&inp).unwrap_err(), REJ_GUARD);
    }

    #[test]
    fn rejects_out_of_domain_phase() {
        let mut inp = base_input();
        inp.epoch_phase = 99;
        assert_eq!(settle_epoch(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
    }

    #[test]
    fn clamps_settle_price_and_trips_breaker_on_big_move() {
        // clearing far above index beyond the 5% band -> clamp + breaker.
        let mut inp = base_input();
        inp.index_price_e8 = 100_000_000;
        inp.max_oracle_move_bps = 500; // 5%
        inp.clearing_price_e8 = 200_000_000; // +100% >> band
        let out = settle_epoch(&inp).unwrap();
        assert!(out.breaker_active);
        assert_eq!(out.breaker_last_trigger_epoch, 5);
        // sp clamped to index + 5% = 105_000_000.
        assert_eq!(out.index_price_e8, 105_000_000);
    }
}

#[cfg(kani)]
mod kani_contracts {
    use super::*;

    #[kani::proof]
    fn phase_classifier_is_exact() {
        let phase: i128 = kani::any();
        let expected =
            phase == PHASE_OPEN || phase == PHASE_PRICE_PUBLISHED || phase == PHASE_SETTLED;

        assert_eq!(valid_phase(phase), expected);
    }

    #[kani::proof]
    fn account_domain_classifier_is_exact() {
        let position: i128 = kani::any();
        let collateral: i128 = kani::any();
        let entry: i128 = kani::any();
        let expected = in_closed(position, -MAX_ABS, MAX_ABS)
            && in_closed(collateral, 0, MAX_COLLATERAL)
            && in_closed(entry, 0, MAX_ABS);

        assert_eq!(account_domain_ok(position, collateral, entry), expected);
    }

    #[kani::proof]
    fn flat_fast_path_classifier_is_exact() {
        let position: i128 = kani::any();
        let entry: i128 = kani::any();
        let liquidated: bool = kani::any();
        let collateral: i128 = kani::any();
        let expected =
            position == 0 && entry == 0 && !liquidated && in_closed(collateral, 0, MAX_COLLATERAL);

        assert_eq!(
            flat_fast_path_ok(position, entry, liquidated, collateral),
            expected
        );
    }

    #[kani::proof]
    fn global_guard_classifier_is_exact() {
        let phase: i128 = kani::any();
        let seen: bool = kani::any();
        let clearing_epoch: i128 = kani::any();
        let now: i128 = kani::any();
        let oracle_last: i128 = kani::any();
        let expected =
            phase == PHASE_PRICE_PUBLISHED && seen && clearing_epoch == now && oracle_last < now;

        assert_eq!(
            settle_global_guard_ok(phase, seen, clearing_epoch, now, oracle_last),
            expected
        );
    }

    #[kani::proof]
    fn settle_helper_covers_are_reachable() {
        kani::cover!(valid_phase(PHASE_PRICE_PUBLISHED));
        kani::cover!(!valid_phase(99));
        kani::cover!(account_domain_ok(0, 0, 0));
        kani::cover!(!account_domain_ok(MAX_ABS + 1, 0, 0));
        kani::cover!(flat_fast_path_ok(0, 0, false, 1));
        kani::cover!(!flat_fast_path_ok(1, 0, false, 1));
        kani::cover!(settle_global_guard_ok(PHASE_PRICE_PUBLISHED, true, 5, 5, 4));
        kani::cover!(!settle_global_guard_ok(PHASE_OPEN, true, 5, 5, 4));
    }
}
