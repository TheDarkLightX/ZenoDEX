//! Stateless perp risk arithmetic — shadow of `src/core/perp_v2/math.py`.
//!
//! These are pure integer functions (oracle freshness, price clamp, margin,
//! PnL, liquidation eligibility, funding). They are the smallest self-contained
//! perps slice: no state, no epoch lifecycle. The stateful engine
//! (`perp_v2/engine.py`, `updates.py`) is a later, larger slice.
//!
//! Signedness & rounding (the parity-critical part):
//! * Values are **signed** (`i128`): `position_base` (long>0/short<0),
//!   `rate_bps`, price differences, `collateral_after_pnl`, and the PnL/funding
//!   outputs. So this module uses `i128`, unlike the unsigned kernels.
//! * The Python authority computes every floor-division on **non-negative
//!   magnitudes** (`abs_val` first, sign applied afterwards), so Rust's
//!   truncating `/` equals Python's flooring `//` at every division site — there
//!   is no toward-zero-vs-toward-−∞ divergence here. This is mirrored exactly.
//! * Inputs are domain-bounded by the caller (the CLI bridge rejects magnitude
//!   args outside ±[`MAX_ABS`] and bps args outside ±[`MAX_BPS`]). Within those
//!   bounds the worst intermediate product is
//!   `(MAX_ABS·MAX_ABS / PRICE_SCALE)·MAX_BPS = 1e35 < i128::MAX (≈1.7e38)`, so
//!   no multiplication can overflow.

/// Price fixed-point scale (1e8), matching `PRICE_SCALE` in Python.
pub const PRICE_SCALE: i128 = 100_000_000;
/// Basis-point scale (1e4), matching `BPS_SCALE` in Python.
pub const BPS_SCALE: i128 = 10_000;

/// Conservative magnitude bound for price/position/collateral/epoch inputs.
/// Real perp domain values (collateral ≤ 1e15, prices/positions far smaller)
/// sit well inside this.
pub const MAX_ABS: i128 = 1_000_000_000_000_000_000; // 1e18
/// Bound for basis-point inputs. Real rates/margins are ≤ a few ×1e4; this
/// keeps `notional·bps` (≤ 1e28·1e7 = 1e35) safely inside `i128`.
pub const MAX_BPS: i128 = 10_000_000; // 1e7

#[inline]
pub fn abs_val(x: i128) -> i128 {
    if x >= 0 {
        x
    } else {
        -x
    }
}

// -- Oracle helpers ----------------------------------------------------------

pub fn is_oracle_fresh(
    now_epoch: i128,
    oracle_last_update_epoch: i128,
    max_oracle_staleness_epochs: i128,
    oracle_seen: bool,
) -> bool {
    if !oracle_seen {
        return false;
    }
    if now_epoch < oracle_last_update_epoch {
        return false;
    }
    (now_epoch - oracle_last_update_epoch) <= max_oracle_staleness_epochs
}

pub fn oracle_move_violated(
    clearing_price_e8: i128,
    index_price_e8: i128,
    max_oracle_move_bps: i128,
    oracle_seen: bool,
) -> bool {
    if !oracle_seen {
        return false;
    }
    let diff = abs_val(clearing_price_e8 - index_price_e8);
    diff * BPS_SCALE > max_oracle_move_bps * index_price_e8
}

pub fn settle_price(
    clearing_price_e8: i128,
    index_price_e8: i128,
    max_oracle_move_bps: i128,
    oracle_seen: bool,
) -> i128 {
    if !oracle_move_violated(
        clearing_price_e8,
        index_price_e8,
        max_oracle_move_bps,
        oracle_seen,
    ) {
        return clearing_price_e8;
    }
    // Ceil-div clamp band so a non-zero intended move cannot collapse to width 0.
    let max_delta = ((index_price_e8 * max_oracle_move_bps) + (BPS_SCALE - 1)) / BPS_SCALE;
    if clearing_price_e8 >= index_price_e8 {
        index_price_e8 + max_delta
    } else {
        index_price_e8 - max_delta
    }
}

// -- Position / margin helpers -----------------------------------------------

pub fn notional_quote(position_base: i128, price_e8: i128) -> i128 {
    (abs_val(position_base) * price_e8) / PRICE_SCALE
}

pub fn margin_requirement(notional: i128, margin_bps: i128) -> i128 {
    (notional * margin_bps) / BPS_SCALE
}

pub fn maint_margin_req(
    position_base: i128,
    price_e8: i128,
    maint_bps: i128,
    depeg_bps: i128,
) -> i128 {
    margin_requirement(
        notional_quote(position_base, price_e8),
        maint_bps + depeg_bps,
    )
}

pub fn init_margin_req(position_base: i128, price_e8: i128, init_bps: i128) -> i128 {
    margin_requirement(notional_quote(position_base, price_e8), init_bps)
}

// -- PnL helpers (symmetric) -------------------------------------------------

pub fn pnl_magnitude(position_base: i128, settle_price_e8: i128, index_price_e8: i128) -> i128 {
    (abs_val(position_base) * abs_val(settle_price_e8 - index_price_e8)) / PRICE_SCALE
}

pub fn pnl_same_sign(position_base: i128, settle_price_e8: i128, index_price_e8: i128) -> bool {
    (position_base >= 0) == (settle_price_e8 >= index_price_e8)
}

pub fn pnl_quote(position_base: i128, settle_price_e8: i128, index_price_e8: i128) -> i128 {
    let mag = pnl_magnitude(position_base, settle_price_e8, index_price_e8);
    if pnl_same_sign(position_base, settle_price_e8, index_price_e8) {
        mag
    } else {
        -mag
    }
}

// -- Liquidation helpers -----------------------------------------------------

pub fn is_liquidatable(
    position_base: i128,
    collateral_after_pnl: i128,
    settle_price_e8: i128,
    maintenance_margin_bps: i128,
    depeg_buffer_bps: i128,
) -> bool {
    if position_base == 0 {
        return false;
    }
    collateral_after_pnl
        < maint_margin_req(
            position_base,
            settle_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
        )
}

/// Liquidation penalty in quote; `0` below the anti-bounty-farming notional floor.
pub fn liq_penalty(
    position_base: i128,
    settle_price_e8: i128,
    liquidation_penalty_bps: i128,
    min_notional_for_bounty: i128,
) -> i128 {
    let notional = notional_quote(position_base, settle_price_e8);
    if notional < min_notional_for_bounty {
        return 0;
    }
    margin_requirement(notional, liquidation_penalty_bps)
}

/// Liquidation penalty capped at the remaining collateral after PnL.
pub fn liq_penalty_capped(
    collateral_after_pnl: i128,
    position_base: i128,
    settle_price_e8: i128,
    liquidation_penalty_bps: i128,
    min_notional_for_bounty: i128,
) -> i128 {
    let raw = liq_penalty(
        position_base,
        settle_price_e8,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    );
    collateral_after_pnl.min(raw)
}

// -- Partial-liquidation helpers ---------------------------------------------

/// Unsigned base units closed by `fraction_bps/10000` of `|position|`.
pub fn partial_close_base(position_abs: i128, fraction_bps: i128) -> i128 {
    (position_abs * fraction_bps) / BPS_SCALE
}

/// Remaining (signed) position after closing `fraction_bps/10000`.
pub fn remaining_position_signed(position_base: i128, fraction_bps: i128) -> i128 {
    if fraction_bps >= BPS_SCALE {
        return 0;
    }
    if fraction_bps <= 0 {
        return position_base;
    }
    let pos_abs = abs_val(position_base);
    let remaining_abs = pos_abs - partial_close_base(pos_abs, fraction_bps);
    if position_base >= 0 {
        remaining_abs
    } else {
        -remaining_abs
    }
}

/// Liquidation penalty for the closed portion of the position.
pub fn partial_liq_penalty(
    position_base: i128,
    fraction_bps: i128,
    settle_price_e8: i128,
    liquidation_penalty_bps: i128,
    min_notional_for_bounty: i128,
) -> i128 {
    if fraction_bps >= BPS_SCALE {
        return liq_penalty(
            position_base,
            settle_price_e8,
            liquidation_penalty_bps,
            min_notional_for_bounty,
        );
    }
    let closed = partial_close_base(abs_val(position_base), fraction_bps);
    if closed == 0 {
        return 0;
    }
    liq_penalty(
        closed,
        settle_price_e8,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    )
}

/// Partial-close penalty capped at remaining collateral (clamped non-negative).
pub fn partial_liq_penalty_capped(
    collateral_after_pnl: i128,
    position_base: i128,
    fraction_bps: i128,
    settle_price_e8: i128,
    liquidation_penalty_bps: i128,
    min_notional_for_bounty: i128,
) -> i128 {
    let raw = partial_liq_penalty(
        position_base,
        fraction_bps,
        settle_price_e8,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    );
    collateral_after_pnl.max(0).min(raw)
}

/// True if closing `fraction_bps/10000` restores the remaining position to maint margin.
#[allow(clippy::too_many_arguments)]
fn is_partial_fraction_sufficient(
    position_base: i128,
    collateral_after_pnl: i128,
    fraction_bps: i128,
    settle_price_e8: i128,
    maintenance_margin_bps: i128,
    depeg_buffer_bps: i128,
    liquidation_penalty_bps: i128,
    min_notional_for_bounty: i128,
) -> bool {
    let remaining = remaining_position_signed(position_base, fraction_bps);
    let penalty = partial_liq_penalty_capped(
        collateral_after_pnl,
        position_base,
        fraction_bps,
        settle_price_e8,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    );
    let coll_after = collateral_after_pnl - penalty;
    if remaining == 0 {
        return true;
    }
    coll_after
        >= maint_margin_req(
            remaining,
            settle_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
        )
}

/// Minimum fraction in `[1, BPS_SCALE]` to close to restore maint margin; `0` if
/// not liquidatable, `BPS_SCALE` if a full close is needed. Binary search.
#[allow(clippy::too_many_arguments)]
pub fn compute_partial_close_fraction(
    position_base: i128,
    collateral_after_pnl: i128,
    settle_price_e8: i128,
    maintenance_margin_bps: i128,
    depeg_buffer_bps: i128,
    liquidation_penalty_bps: i128,
    min_notional_for_bounty: i128,
) -> i128 {
    if position_base == 0 {
        return 0;
    }
    if !is_liquidatable(
        position_base,
        collateral_after_pnl,
        settle_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
    ) {
        return 0;
    }
    if !is_partial_fraction_sufficient(
        position_base,
        collateral_after_pnl,
        BPS_SCALE - 1,
        settle_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    ) {
        return BPS_SCALE;
    }
    let (mut lo, mut hi) = (1i128, BPS_SCALE);
    while lo < hi {
        let mid = (lo + hi) / 2;
        if is_partial_fraction_sufficient(
            position_base,
            collateral_after_pnl,
            mid,
            settle_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
            liquidation_penalty_bps,
            min_notional_for_bounty,
        ) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

// -- Funding helpers (symmetric) ---------------------------------------------

pub fn funding_magnitude(position_base: i128, index_price_e8: i128, rate_bps: i128) -> i128 {
    (notional_quote(position_base, index_price_e8) * abs_val(rate_bps)) / BPS_SCALE
}

pub fn funding_same_sign(position_base: i128, rate_bps: i128) -> bool {
    (position_base >= 0) == (rate_bps >= 0)
}

pub fn funding_payment(position_base: i128, index_price_e8: i128, rate_bps: i128) -> i128 {
    let mag = funding_magnitude(position_base, index_price_e8, rate_bps);
    if funding_same_sign(position_base, rate_bps) {
        mag
    } else {
        -mag
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn oracle_freshness_fail_closed() {
        assert!(!is_oracle_fresh(5, 0, 10, false)); // not seen
        assert!(!is_oracle_fresh(3, 5, 10, true)); // update in the future
        assert!(is_oracle_fresh(5, 0, 10, true));
        assert!(!is_oracle_fresh(20, 0, 10, true)); // stale
    }

    #[test]
    fn settle_price_clamp_band_never_zero() {
        // index=100, move=1bps -> raw delta floor = 0, ceil-div keeps band >=1.
        let p = settle_price(1_000_000, 100, 1, true);
        // clearing 1e6 far above index 100 -> violated -> clamp to index+delta.
        assert!(p > 100);
        // No violation -> raw clearing returned.
        assert_eq!(settle_price(100, 100, 50, true), 100);
    }

    #[test]
    fn pnl_sign_symmetry() {
        // Long, price up -> profit (+).
        assert!(pnl_quote(1_000_000_000, 110 * PRICE_SCALE, 100 * PRICE_SCALE) > 0);
        // Long, price down -> loss (-).
        assert!(pnl_quote(1_000_000_000, 90 * PRICE_SCALE, 100 * PRICE_SCALE) < 0);
        // Short mirrors long.
        let long = pnl_quote(1_000, 110 * PRICE_SCALE, 100 * PRICE_SCALE);
        let short = pnl_quote(-1_000, 110 * PRICE_SCALE, 100 * PRICE_SCALE);
        assert_eq!(long, -short);
    }

    #[test]
    fn funding_sign_symmetry() {
        let long_pos_pos_rate = funding_payment(1_000, 100 * PRICE_SCALE, 50);
        let short_pos_rate = funding_payment(-1_000, 100 * PRICE_SCALE, 50);
        // Long pays when rate>0; short receives -> opposite signs, equal magnitude.
        assert_eq!(long_pos_pos_rate, -short_pos_rate);
        assert!(long_pos_pos_rate > 0);
    }

    #[test]
    fn liquidatable_flat_is_false() {
        assert!(!is_liquidatable(0, -100, 100 * PRICE_SCALE, 500, 0));
        // Tiny collateral, real position -> liquidatable.
        assert!(is_liquidatable(1_000_000, 0, 100 * PRICE_SCALE, 500, 0));
    }
}
