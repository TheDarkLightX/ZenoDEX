//! Stateful perps E2 — `apply_funding_auto` SETTLEMENT shadow (bounded sink).
//!
//! Shadow of `src/integration/perp_engine.py::_apply_isolated_apply_funding_auto`
//! after the bounded-sink funding fix. Each open account receives EXACTLY its
//! formula-derived `funding_payment` (no counterparty residual transfer; no
//! `Σ position_base == 0` requirement). The net of all per-account payments,
//!
//!   `projected_net = Σ funding_payment_i`,
//!
//! is routed into the protocol sink, conserving total value
//! (`Δ(Σ collateral) = -projected_net`, `Δ fee_pool = +projected_net`):
//!
//!   `fee_pool_quote    += projected_net`
//!   `fee_income        += projected_net`
//!   `insurance_balance += projected_net`
//!
//! Bumping all three mirrors by the same delta preserves the persistent
//! identities. The transition mutates exactly the fields the Python authority
//! mutates: each open account's `collateral_quote`, `funding_paid_cumulative`,
//! and `funding_last_applied_epoch` (set to `now_epoch`), and the global
//! `funding_rate_bps`. This lets same-epoch replay/double-apply be checked
//! (the `funding_not_applied` gate: an open account with
//! `funding_last_applied_epoch >= now_epoch` rejects).
//!
//! SCOPE: the funding-auto **settlement** only — NOT full perps authority. The
//! funding-rate derivation (`settle_price` / `compute_funding_rate_bps`) and the
//! oracle/clearing freshness gate are upstream (the stateless E1 `perp_math`
//! slice + the Python auto gate); this transition is given an already-derived
//! `rate_bps`. SHADOW; Python remains authority.
//!
//! Per the crate rule (`#![forbid(unsafe_code)]`, explicit checked transition
//! arithmetic) every `+`/`-` on the transition path uses `checked_*` and
//! fails closed with `REJ_OVERFLOW` rather than wrapping. Reject order mirrors
//! the authority: domain → pre-sink → post-sink (auto gate sink bounds) →
//! already-applied (funding_not_applied) → per-account (collateral /
//! maintenance margin / cumulative bounds). Any rejection is fail-closed
//! (`Err`, no state).

use crate::perp_math::{funding_payment, maint_margin_req, MAX_ABS, MAX_BPS};

/// Collateral / sink finite-domain max (1e15), mirrors `MAX_COLLATERAL` in Python.
pub const MAX_COLLATERAL: i128 = 1_000_000_000_000_000;
/// Cumulative-funding finite-domain bound (1e15), mirrors Python.
pub const MAX_FUNDING_CUMULATIVE: i128 = 1_000_000_000_000_000;

// Stable reject codes (mirror the Python authority's reject categories).
pub const REJ_OUT_OF_DOMAIN: &str = "funding_input_out_of_domain";
pub const REJ_OVERFLOW: &str = "funding_arithmetic_overflow";
pub const REJ_PRE_SINK_OUT_OF_DOMAIN: &str = "pre_sink_out_of_domain";
pub const REJ_SINK_OUT_OF_DOMAIN: &str = "sink_out_of_domain";
pub const REJ_FUNDING_ALREADY_APPLIED: &str = "funding_already_applied";
pub const REJ_COLLATERAL_BOUNDS: &str = "collateral_bounds";
pub const REJ_MAINTENANCE_MARGIN: &str = "maintenance_margin";
pub const REJ_CUMULATIVE_BOUNDS: &str = "cumulative_funding_bounds";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FundingAccount {
    pub key: String,
    pub position_base: i128,
    pub collateral_quote: i128,
    pub funding_paid_cumulative: i128,
    pub funding_last_applied_epoch: i128,
}

#[derive(Clone, Debug)]
pub struct FundingAutoInput {
    pub accounts: Vec<FundingAccount>,
    pub now_epoch: i128,
    pub rate_bps: i128,
    pub index_price_e8: i128,
    pub maintenance_margin_bps: i128,
    pub depeg_buffer_bps: i128,
    pub fee_pool_quote: i128,
    pub fee_income: i128,
    pub insurance_balance: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FundingAutoOutput {
    /// Accounts in deterministic (key-sorted) order; open accounts settled
    /// (collateral / cumulative / funding_last_applied_epoch updated), flat
    /// accounts (`position_base == 0`) carried through unchanged.
    pub accounts: Vec<FundingAccount>,
    pub funding_rate_bps: i128,
    pub fee_pool_quote: i128,
    pub fee_income: i128,
    pub insurance_balance: i128,
    pub projected_net: i128,
}

#[inline]
fn in_closed(x: i128, lo: i128, hi: i128) -> bool {
    lo <= x && x <= hi
}

#[inline]
fn ck_add(a: i128, b: i128) -> Result<i128, &'static str> {
    a.checked_add(b).ok_or(REJ_OVERFLOW)
}

#[inline]
fn ck_sub(a: i128, b: i128) -> Result<i128, &'static str> {
    a.checked_sub(b).ok_or(REJ_OVERFLOW)
}

fn apply_sink_delta(
    fee_pool_quote: i128,
    fee_income: i128,
    insurance_balance: i128,
    projected_net: i128,
) -> Result<(i128, i128, i128), &'static str> {
    let fee_pool_after = ck_add(fee_pool_quote, projected_net)?;
    let fee_income_after = ck_add(fee_income, projected_net)?;
    let insurance_after = ck_add(insurance_balance, projected_net)?;
    for s in [fee_pool_after, fee_income_after, insurance_after] {
        if !in_closed(s, 0, MAX_COLLATERAL) {
            return Err(REJ_SINK_OUT_OF_DOMAIN);
        }
    }
    Ok((fee_pool_after, fee_income_after, insurance_after))
}

fn funding_already_applied(
    position_base: i128,
    funding_last_applied_epoch: i128,
    now_epoch: i128,
) -> bool {
    position_base != 0 && funding_last_applied_epoch >= now_epoch
}

#[allow(clippy::too_many_arguments)]
fn settle_open_account_values(
    position_base: i128,
    collateral_quote: i128,
    funding_paid_cumulative: i128,
    index_price_e8: i128,
    rate_bps: i128,
    maintenance_margin_bps: i128,
    depeg_buffer_bps: i128,
) -> Result<(i128, i128, i128), &'static str> {
    let fp = funding_payment(position_base, index_price_e8, rate_bps);
    let coll_after = ck_sub(collateral_quote, fp)?;
    let cum_after = ck_add(funding_paid_cumulative, fp)?;
    if !in_closed(coll_after, 0, MAX_COLLATERAL) {
        return Err(REJ_COLLATERAL_BOUNDS);
    }
    let maint = maint_margin_req(
        position_base,
        index_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
    );
    if coll_after < maint {
        return Err(REJ_MAINTENANCE_MARGIN);
    }
    if !in_closed(cum_after, -MAX_FUNDING_CUMULATIVE, MAX_FUNDING_CUMULATIVE) {
        return Err(REJ_CUMULATIVE_BOUNDS);
    }
    Ok((fp, coll_after, cum_after))
}

/// Apply the funding-auto settlement. Fail-closed: returns `Err(code)` with NO
/// state on any rejection.
pub fn apply_funding_auto(input: &FundingAutoInput) -> Result<FundingAutoOutput, &'static str> {
    // (0) Input domain guards — keep every intermediate product inside i128 and
    // mirror the authority's per-int domain.
    if !in_closed(input.now_epoch, 0, MAX_ABS)
        || !in_closed(input.rate_bps, -MAX_BPS, MAX_BPS)
        || !in_closed(input.index_price_e8, 0, MAX_ABS)
        || !in_closed(input.maintenance_margin_bps, 0, MAX_BPS)
        || !in_closed(input.depeg_buffer_bps, 0, MAX_BPS)
    {
        return Err(REJ_OUT_OF_DOMAIN);
    }
    for a in &input.accounts {
        if !in_closed(a.position_base, -MAX_ABS, MAX_ABS)
            || !in_closed(a.collateral_quote, 0, MAX_COLLATERAL)
            || !in_closed(
                a.funding_paid_cumulative,
                -MAX_FUNDING_CUMULATIVE,
                MAX_FUNDING_CUMULATIVE,
            )
            || !in_closed(a.funding_last_applied_epoch, 0, MAX_ABS)
        {
            return Err(REJ_OUT_OF_DOMAIN);
        }
    }

    // (1) Pre-sink domain (fail closed before any mutation).
    for s in [
        input.fee_pool_quote,
        input.fee_income,
        input.insurance_balance,
    ] {
        if !in_closed(s, 0, MAX_COLLATERAL) {
            return Err(REJ_PRE_SINK_OUT_OF_DOMAIN);
        }
    }

    // (2) Deterministic account ordering (mirrors Python `sorted(items())`).
    let mut accts = input.accounts.clone();
    accts.sort_by(|a, b| a.key.cmp(&b.key));

    // (3) projected_net = Σ funding_payment_i over OPEN accounts (checked).
    let mut projected_net: i128 = 0;
    for a in &accts {
        if a.position_base == 0 {
            continue;
        }
        let fp = funding_payment(a.position_base, input.index_price_e8, input.rate_bps);
        projected_net = ck_add(projected_net, fp)?;
    }

    // (4) Post-sink domain (the auto gate's sink_bounds_ok — before mutation).
    let (fee_pool_after, fee_income_after, insurance_after) = apply_sink_delta(
        input.fee_pool_quote,
        input.fee_income,
        input.insurance_balance,
        projected_net,
    )?;

    // (5) funding_not_applied gate: no OPEN account may have already received
    // funding this epoch (same-epoch replay / double-apply protection).
    for a in &accts {
        if funding_already_applied(
            a.position_base,
            a.funding_last_applied_epoch,
            input.now_epoch,
        ) {
            return Err(REJ_FUNDING_ALREADY_APPLIED);
        }
    }

    // (6) Per-account settlement checks (mirror evaluate_perp_funding_apply_gate:
    // collateral bounds, maintenance margin, cumulative bounds). Any reject =>
    // fail closed, no mutation.
    let mut settled: Vec<FundingAccount> = Vec::with_capacity(accts.len());
    for a in &accts {
        if a.position_base == 0 {
            settled.push(a.clone());
            continue;
        }
        let (_fp, coll_after, cum_after) = settle_open_account_values(
            a.position_base,
            a.collateral_quote,
            a.funding_paid_cumulative,
            input.index_price_e8,
            input.rate_bps,
            input.maintenance_margin_bps,
            input.depeg_buffer_bps,
        )?;
        settled.push(FundingAccount {
            key: a.key.clone(),
            position_base: a.position_base,
            collateral_quote: coll_after,
            funding_paid_cumulative: cum_after,
            funding_last_applied_epoch: input.now_epoch,
        });
    }

    // (7) Commit: settled accounts + global rate + bumped sinks.
    Ok(FundingAutoOutput {
        accounts: settled,
        funding_rate_bps: input.rate_bps,
        fee_pool_quote: fee_pool_after,
        fee_income: fee_income_after,
        insurance_balance: insurance_after,
        projected_net,
    })
}

/// Total collateral across accounts (helper for conservation assertions).
pub fn sum_collateral(accounts: &[FundingAccount]) -> i128 {
    accounts.iter().map(|a| a.collateral_quote).sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn acct(key: &str, pos: i128, coll: i128) -> FundingAccount {
        FundingAccount {
            key: key.to_string(),
            position_base: pos,
            collateral_quote: coll,
            funding_paid_cumulative: 0,
            funding_last_applied_epoch: 0,
        }
    }

    // now_epoch = 5 (> accounts' funding_last_applied_epoch 0, so not already
    // applied); index = 1e8 so notional == |position|; rate 100 bps.
    fn input(accounts: Vec<FundingAccount>, sink: i128) -> FundingAutoInput {
        FundingAutoInput {
            accounts,
            now_epoch: 5,
            rate_bps: 100,
            index_price_e8: 100_000_000,
            maintenance_margin_bps: 0,
            depeg_buffer_bps: 0,
            fee_pool_quote: sink,
            fee_income: sink,
            insurance_balance: sink,
        }
    }

    #[test]
    fn balanced_book_sink_unchanged() {
        let out = apply_funding_auto(&input(
            vec![
                acct("a", 1_000_000, 200_000),
                acct("b", -1_000_000, 200_000),
            ],
            0,
        ))
        .unwrap();
        assert_eq!(out.projected_net, 0);
        assert_eq!(
            (out.fee_pool_quote, out.fee_income, out.insurance_balance),
            (0, 0, 0)
        );
        assert_eq!(out.funding_rate_bps, 100);
        assert_eq!(sum_collateral(&out.accounts), 400_000);
        // funding_last_applied_epoch advanced to now_epoch on every open account.
        assert!(out
            .accounts
            .iter()
            .all(|a| a.funding_last_applied_epoch == 5));
    }

    #[test]
    fn positive_net_sink_increases() {
        let out = apply_funding_auto(&input(
            vec![acct("a", 2_000, 200_000), acct("b", -1_000, 200_000)],
            0,
        ))
        .unwrap();
        assert_eq!(out.projected_net, 10);
        assert_eq!(
            (out.fee_pool_quote, out.fee_income, out.insurance_balance),
            (10, 10, 10)
        );
        assert_eq!(out.fee_pool_quote, out.fee_income);
        assert_eq!(sum_collateral(&out.accounts), 400_000 - 10);
    }

    #[test]
    fn negative_net_empty_sink_rejects() {
        let err = apply_funding_auto(&input(
            vec![acct("a", 1_000, 200_000), acct("b", -2_000, 200_000)],
            0,
        ))
        .unwrap_err();
        assert_eq!(err, REJ_SINK_OUT_OF_DOMAIN);
    }

    #[test]
    fn negative_net_prefunded_sink_succeeds() {
        let out = apply_funding_auto(&input(
            vec![acct("a", 1_000, 200_000), acct("b", -2_000, 200_000)],
            50,
        ))
        .unwrap();
        assert_eq!(out.projected_net, -10);
        assert_eq!(
            (out.fee_pool_quote, out.fee_income, out.insurance_balance),
            (40, 40, 40)
        );
        assert_eq!(sum_collateral(&out.accounts), 400_000 + 10);
    }

    #[test]
    fn no_artificial_user_residual_transfer() {
        let out = apply_funding_auto(&input(
            vec![acct("a", 2_000, 200_000), acct("b", -1_000, 200_000)],
            0,
        ))
        .unwrap();
        let a = out.accounts.iter().find(|x| x.key == "a").unwrap();
        let b = out.accounts.iter().find(|x| x.key == "b").unwrap();
        assert_eq!(a.collateral_quote, 200_000 - 20);
        assert_eq!(b.collateral_quote, 200_000 + 10);
        assert_eq!(a.funding_paid_cumulative, 20);
        assert_eq!(b.funding_paid_cumulative, -10);
    }

    #[test]
    fn no_op_on_reject() {
        let res = apply_funding_auto(&input(
            vec![acct("a", 1_000, 200_000), acct("b", -2_000, 200_000)],
            0,
        ));
        assert!(res.is_err());
    }

    #[test]
    fn double_apply_same_epoch_rejects() {
        // An open account already funded this epoch (funding_last_applied_epoch
        // == now_epoch) => replay rejected.
        let mut a = acct("a", 1_000_000, 200_000);
        a.funding_last_applied_epoch = 5;
        let err =
            apply_funding_auto(&input(vec![a, acct("b", -1_000_000, 200_000)], 0)).unwrap_err();
        assert_eq!(err, REJ_FUNDING_ALREADY_APPLIED);
    }

    #[test]
    fn maintenance_margin_rejects() {
        let mut inp = input(
            vec![acct("a", 1_000_000, 60_000), acct("b", -1_000_000, 200_000)],
            0,
        );
        inp.maintenance_margin_bps = 600;
        let err = apply_funding_auto(&inp).unwrap_err();
        assert_eq!(err, REJ_MAINTENANCE_MARGIN);
    }

    #[test]
    fn collateral_bounds_rejects() {
        let err = apply_funding_auto(&input(
            vec![acct("a", 1_000_000, 100), acct("b", -1_000_000, 200_000)],
            0,
        ))
        .unwrap_err();
        assert_eq!(err, REJ_COLLATERAL_BOUNDS);
    }

    #[test]
    fn pre_sink_out_of_domain_rejects() {
        let mut inp = input(
            vec![acct("a", 1_000, 200_000), acct("b", -1_000, 200_000)],
            0,
        );
        inp.fee_pool_quote = -1;
        assert_eq!(
            apply_funding_auto(&inp).unwrap_err(),
            REJ_PRE_SINK_OUT_OF_DOMAIN
        );
        let mut inp2 = input(vec![acct("a", 1_000, 200_000)], 0);
        inp2.insurance_balance = MAX_COLLATERAL + 1;
        assert_eq!(
            apply_funding_auto(&inp2).unwrap_err(),
            REJ_PRE_SINK_OUT_OF_DOMAIN
        );
    }

    #[test]
    fn overflow_input_rejects() {
        let mut inp = input(vec![acct("a", MAX_ABS + 1, 200_000)], 0);
        assert_eq!(apply_funding_auto(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
        inp = input(vec![acct("a", 1_000, 200_000)], 0);
        inp.rate_bps = MAX_BPS + 1;
        assert_eq!(apply_funding_auto(&inp).unwrap_err(), REJ_OUT_OF_DOMAIN);
    }

    #[test]
    fn order_independent() {
        let a = apply_funding_auto(&input(
            vec![acct("a", 2_000, 200_000), acct("b", -1_000, 200_000)],
            0,
        ))
        .unwrap();
        let b = apply_funding_auto(&input(
            vec![acct("b", -1_000, 200_000), acct("a", 2_000, 200_000)],
            0,
        ))
        .unwrap();
        assert_eq!(a, b);
    }

    proptest! {
        // CONSERVATION property: for any accepted settlement over random in-domain
        // books, Δ(Σ collateral) == -projected_net, each sink moved by
        // projected_net, and funding_last_applied advanced on every open account.
        #[test]
        fn prop_conservation_and_state(
            positions in prop::collection::vec(-5_000i128..=5_000, 1..6),
            rate in -300i128..=300,
            sink in 0i128..=2_000_000,
        ) {
            let accounts: Vec<FundingAccount> = positions
                .iter()
                .enumerate()
                .map(|(i, &p)| acct(&format!("k{i:02}"), p, 1_000_000))
                .collect();
            let pre_sum = sum_collateral(&accounts);
            let mut inp = input(accounts, sink);
            inp.rate_bps = rate;
            if let Ok(out) = apply_funding_auto(&inp) {
                // exact conservation: Δ(Σ collateral + fee_pool) == 0
                prop_assert_eq!(sum_collateral(&out.accounts), pre_sum - out.projected_net);
                prop_assert_eq!(out.fee_pool_quote, sink + out.projected_net);
                prop_assert_eq!(out.fee_income, sink + out.projected_net);
                prop_assert_eq!(out.insurance_balance, sink + out.projected_net);
                prop_assert_eq!(out.fee_pool_quote, out.fee_income);
                // every open account advanced funding_last_applied_epoch to now_epoch
                for a in &out.accounts {
                    if a.position_base != 0 {
                        prop_assert_eq!(a.funding_last_applied_epoch, inp.now_epoch);
                    }
                }
            }
        }
    }
}

// CBC_CORE_V0 — Kani contracts on the ACTUAL bounded-sink funding arithmetic.
//
// The public transition uses Vec/String sorting, which is too expensive for CBMC.
// These harnesses target heap-free helpers that the running transition calls:
// per-account settlement, sink delta application, and the same-epoch replay
// predicate. This proves the value-conservation arithmetic without treating the
// heap/map wrapper as proven. The wrapper remains covered by differential tests.
//
// Run exact harnesses, for example:
// `cargo kani -p zenodex-runtime-core --harness perp_funding_auto::kani_contracts::two_account_conservation`
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    const POS_BOUND: i128 = 1_000_000;
    const MONEY_BOUND: i128 = 1_000_000_000_000;
    const CUM_BOUND: i128 = 1_000_000_000_000;
    const PRICE_E8: i128 = 100_000_000;

    fn bounded_i128(lo: i128, hi: i128) -> i128 {
        let value: i128 = kani::any();
        kani::assume(lo <= value && value <= hi);
        value
    }

    fn settled(
        position: i128,
        collateral: i128,
        cumulative: i128,
        rate_bps: i128,
    ) -> Result<(i128, i128, i128), &'static str> {
        settle_open_account_values(position, collateral, cumulative, PRICE_E8, rate_bps, 0, 0)
    }

    #[kani::proof]
    fn sink_delta_moves_all_mirrors_exactly() {
        let fee_pool = bounded_i128(0, MONEY_BOUND);
        let fee_income = bounded_i128(0, MONEY_BOUND);
        let insurance = bounded_i128(0, MONEY_BOUND);
        let projected_net = bounded_i128(-MONEY_BOUND, MONEY_BOUND);
        if let Ok((fee_pool_after, fee_income_after, insurance_after)) =
            apply_sink_delta(fee_pool, fee_income, insurance, projected_net)
        {
            assert_eq!(fee_pool_after, fee_pool + projected_net);
            assert_eq!(fee_income_after, fee_income + projected_net);
            assert_eq!(insurance_after, insurance + projected_net);
            assert!(0 <= fee_pool_after && fee_pool_after <= MAX_COLLATERAL);
            assert!(0 <= fee_income_after && fee_income_after <= MAX_COLLATERAL);
            assert!(0 <= insurance_after && insurance_after <= MAX_COLLATERAL);
        }
    }

    #[kani::proof]
    fn account_collateral_delta_is_negative_payment() {
        let position = bounded_i128(-POS_BOUND, POS_BOUND);
        kani::assume(position != 0);
        let collateral = bounded_i128(0, MONEY_BOUND);
        let cumulative = bounded_i128(-CUM_BOUND, CUM_BOUND);
        let rate_bps = bounded_i128(-10_000, 10_000);
        if let Ok((payment, collateral_after, cumulative_after)) =
            settled(position, collateral, cumulative, rate_bps)
        {
            assert_eq!(collateral_after + payment, collateral);
            assert_eq!(cumulative_after, cumulative + payment);
        }
    }

    #[kani::proof]
    fn two_account_conservation() {
        let p0 = bounded_i128(-POS_BOUND, POS_BOUND);
        let p1 = bounded_i128(-POS_BOUND, POS_BOUND);
        kani::assume(p0 != 0 && p1 != 0);
        let c0 = bounded_i128(0, MONEY_BOUND);
        let c1 = bounded_i128(0, MONEY_BOUND);
        let u0 = bounded_i128(-CUM_BOUND, CUM_BOUND);
        let u1 = bounded_i128(-CUM_BOUND, CUM_BOUND);
        let rate_bps = bounded_i128(-10_000, 10_000);
        let fee_pool = bounded_i128(0, MONEY_BOUND);
        let fee_income = bounded_i128(0, MONEY_BOUND);
        let insurance = bounded_i128(0, MONEY_BOUND);

        if let (Ok((fp0, c0_after, _)), Ok((fp1, c1_after, _))) =
            (settled(p0, c0, u0, rate_bps), settled(p1, c1, u1, rate_bps))
        {
            let projected_net = fp0 + fp1;
            if let Ok((fee_pool_after, _, _)) =
                apply_sink_delta(fee_pool, fee_income, insurance, projected_net)
            {
                assert_eq!(c0_after + c1_after + fee_pool_after, c0 + c1 + fee_pool);
            }
        }
    }

    #[kani::proof]
    fn replay_predicate_matches_open_same_epoch() {
        let position = bounded_i128(-POS_BOUND, POS_BOUND);
        let last = bounded_i128(0, 1_000_000);
        let now = bounded_i128(0, 1_000_000);
        let expected = position != 0 && last >= now;
        assert_eq!(funding_already_applied(position, last, now), expected);
    }

    #[kani::proof]
    fn covers_are_reachable() {
        kani::cover!(settled(1_000, 1_000_000, 0, 10).is_ok());
        kani::cover!(settled(1_000, 0, 0, 10) == Err(REJ_COLLATERAL_BOUNDS));
        kani::cover!(apply_sink_delta(0, 0, 0, -1) == Err(REJ_SINK_OUT_OF_DOMAIN));
        kani::cover!(funding_already_applied(1, 1, 1));
    }
}
