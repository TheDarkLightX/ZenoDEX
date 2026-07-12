"""Pure arithmetic for the versioned `perp_epoch_isolated_v4` risk engine.

Every function is stateless and operates on plain Python `int`s.

Design goals:
- **Deterministic integer math** (consensus-friendly).
- **Explicit rounding**: Python `//` is floor-division (toward -∞), which matters
  for negative values.
- **No hidden floats**: comparisons use cross-multiplication when possible.

Conventions (see `types.py` for full units):
- `*_e8` prices are quote-per-base scaled by 1e8.
- `*_bps` rates are basis points (1/10_000).
"""

from __future__ import annotations

# Domain constants (from YAML type bounds)
PRICE_SCALE: int = 100_000_000  # 1e8
BPS_SCALE: int = 10_000
MAX_EPOCH: int = 1_000_000
MAX_COLLATERAL: int = 1_000_000_000_000_000
MAX_FUNDING_CUMULATIVE: int = 1_000_000_000_000_000


# -- Basic helpers -----------------------------------------------------------


def abs_val(x: int) -> int:
    """Absolute value of *x*."""
    return x if x >= 0 else -x


# -- Oracle helpers ----------------------------------------------------------


def is_oracle_fresh(
    now_epoch: int,
    oracle_last_update_epoch: int,
    max_oracle_staleness_epochs: int,
    oracle_seen: bool,
) -> bool:
    """True when the oracle has been seen and is not stale."""
    if not oracle_seen:
        return False
    # Fail-closed on malformed states that claim oracle updates in the future.
    if now_epoch < oracle_last_update_epoch:
        return False
    return (now_epoch - oracle_last_update_epoch) <= max_oracle_staleness_epochs


def is_settle_oracle_usable(
    now_epoch: int,
    oracle_last_update_epoch: int,
    max_oracle_staleness_epochs: int,
    oracle_seen: bool,
    index_price_e8: int,
) -> bool:
    """True when settlement can safely rely on oracle/index state."""
    if index_price_e8 <= 0:
        return False
    return is_oracle_fresh(
        now_epoch,
        oracle_last_update_epoch,
        max_oracle_staleness_epochs,
        oracle_seen,
    )


def oracle_move_violated(
    clearing_price_e8: int,
    index_price_e8: int,
    max_oracle_move_bps: int,
    oracle_seen: bool,
) -> bool:
    """True when the clearing-to-index price move exceeds the bound.

    Uses cross-multiplication to avoid division:
    ``|clearing - index| * 10000 > max_move_bps * index``.

    Note the strict `>`: a move exactly on the boundary is allowed.
    """
    if not oracle_seen:
        return False
    diff = abs_val(clearing_price_e8 - index_price_e8)
    return diff * BPS_SCALE > max_oracle_move_bps * index_price_e8


def settle_price(
    clearing_price_e8: int,
    index_price_e8: int,
    max_oracle_move_bps: int,
    oracle_seen: bool,
) -> int:
    """Settlement price used for mark-to-market in `settle_epoch`.

    - If the oracle bound is not violated, this is the raw `clearing_price_e8`.
    - If the bound is violated, clamp to `index_price_e8 ± δ`.

    Quantization safety:
    - Prices are discrete in 1e-8 ticks.
    - We compute `δ` using ceil-division so the clamp band cannot collapse to
      width 0 when the intended percent move is non-zero but < 1 tick.
    """
    if not oracle_move_violated(
        clearing_price_e8, index_price_e8, max_oracle_move_bps, oracle_seen
    ):
        return clearing_price_e8
    # Quantization-safe clamp: use a ceil-div to avoid a zero-width band when
    # `index_price_e8 * max_oracle_move_bps < 10000`. This preserves the intended
    # percent bound up to rounding to the 1e-8 price tick.
    max_delta = ((index_price_e8 * max_oracle_move_bps) + (BPS_SCALE - 1)) // BPS_SCALE
    if clearing_price_e8 >= index_price_e8:
        return index_price_e8 + max_delta
    return index_price_e8 - max_delta


# -- Position / margin helpers -----------------------------------------------


def notional_quote(position_base: int, price_e8: int) -> int:
    """Absolute notional in quote: ``floor(|pos| * price_e8 / 1e8)``."""
    return (abs_val(position_base) * price_e8) // PRICE_SCALE


def margin_requirement(notional: int, margin_bps: int) -> int:
    """Margin in quote: ``floor(notional * margin_bps / 10_000)``."""
    return (notional * margin_bps) // BPS_SCALE


def risk_margin_requirement(
    position_base: int, price_e8: int, margin_bps: int
) -> int:
    """Least quote unit covering the full scaled risk product.

    v4 performs one ceiling division over
    ``|position| * price_e8 * margin_bps / (1e8 * 10_000)``. Fee, funding,
    bounty, and penalty helpers continue using their existing floor policies.
    """
    numerator = abs_val(position_base) * price_e8 * margin_bps
    denominator = PRICE_SCALE * BPS_SCALE
    return (numerator + denominator - 1) // denominator


def maint_margin_req(
    position_base: int, price_e8: int, maint_bps: int, depeg_bps: int
) -> int:
    """Ceiling maintenance margin in quote, including the depeg buffer."""
    return risk_margin_requirement(
        position_base, price_e8, maint_bps + depeg_bps
    )


def init_margin_req(position_base: int, price_e8: int, init_bps: int) -> int:
    """Ceiling initial margin in quote."""
    return risk_margin_requirement(position_base, price_e8, init_bps)


# -- PnL helpers (symmetric — magnitude from abs values) ---------------------


def pnl_magnitude(position_base: int, settle_price_e8: int, index_price_e8: int) -> int:
    """Unsigned PnL: ``floor(|pos| * |settle-index| / 1e8)``."""
    return (
        abs_val(position_base) * abs_val(settle_price_e8 - index_price_e8)
    ) // PRICE_SCALE


def pnl_same_sign(
    position_base: int, settle_price_e8: int, index_price_e8: int
) -> bool:
    """True when position direction matches price-change direction (profit)."""
    return (position_base >= 0) == (settle_price_e8 >= index_price_e8)


def pnl_quote(position_base: int, settle_price_e8: int, index_price_e8: int) -> int:
    """Signed PnL: +magnitude when profitable, -magnitude when losing."""
    mag = pnl_magnitude(position_base, settle_price_e8, index_price_e8)
    return (
        mag if pnl_same_sign(position_base, settle_price_e8, index_price_e8) else -mag
    )


# -- Liquidation helpers -----------------------------------------------------


def liq_penalty(
    position_base: int,
    settle_price_e8: int,
    liquidation_penalty_bps: int,
    min_notional_for_bounty: int,
) -> int:
    """Liquidation penalty (0 when notional < anti-bounty-farming threshold)."""
    notional = notional_quote(position_base, settle_price_e8)
    if notional < min_notional_for_bounty:
        return 0
    return margin_requirement(notional, liquidation_penalty_bps)


def liq_penalty_capped(
    collateral_after_pnl: int,
    position_base: int,
    settle_price_e8: int,
    liquidation_penalty_bps: int,
    min_notional_for_bounty: int,
) -> int:
    """Liquidation penalty capped at remaining collateral after PnL."""
    raw = liq_penalty(
        position_base, settle_price_e8, liquidation_penalty_bps, min_notional_for_bounty
    )
    return min(collateral_after_pnl, raw)


def is_liquidatable(
    position_base: int,
    collateral_after_pnl: int,
    settle_price_e8: int,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
) -> bool:
    """True when collateral < effective maintenance requirement."""
    if position_base == 0:
        return False
    return collateral_after_pnl < maint_margin_req(
        position_base,
        settle_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
    )


# -- Funding helpers (symmetric) ---------------------------------------------


def funding_magnitude(position_base: int, index_price_e8: int, rate_bps: int) -> int:
    """Unsigned funding: ``floor(notional * |rate_bps| / 10_000)``."""
    return (
        notional_quote(position_base, index_price_e8) * abs_val(rate_bps)
    ) // BPS_SCALE


def funding_same_sign(position_base: int, rate_bps: int) -> bool:
    """True when position and rate have same sign (account is payer)."""
    return (position_base >= 0) == (rate_bps >= 0)


def funding_payment(position_base: int, index_price_e8: int, rate_bps: int) -> int:
    """Signed funding: +magnitude for payer, -magnitude for payee."""
    mag = funding_magnitude(position_base, index_price_e8, rate_bps)
    return mag if funding_same_sign(position_base, rate_bps) else -mag


# -- Liquidation price estimate ---------------------------------------------


# -- Partial liquidation helpers ---------------------------------------------


def partial_close_base(position_abs: int, fraction_bps: int) -> int:
    """Number of base units to close (unsigned), given fraction in bps."""
    return (position_abs * fraction_bps) // BPS_SCALE


def remaining_position_signed(position_base: int, fraction_bps: int) -> int:
    """Remaining position (signed) after closing fraction_bps/10000."""
    if fraction_bps >= BPS_SCALE:
        return 0
    if fraction_bps <= 0:
        return position_base
    pos_abs = abs_val(position_base)
    closed = partial_close_base(pos_abs, fraction_bps)
    remaining_abs = pos_abs - closed
    return remaining_abs if position_base >= 0 else -remaining_abs


def partial_liq_penalty(
    position_base: int,
    fraction_bps: int,
    settle_price_e8: int,
    liquidation_penalty_bps: int,
    min_notional_for_bounty: int,
) -> int:
    """Liquidation penalty for the closed portion of the position."""
    if fraction_bps >= BPS_SCALE:
        return liq_penalty(
            position_base, settle_price_e8,
            liquidation_penalty_bps, min_notional_for_bounty,
        )
    closed = partial_close_base(abs_val(position_base), fraction_bps)
    if closed == 0:
        return 0
    return liq_penalty(
        closed, settle_price_e8,
        liquidation_penalty_bps, min_notional_for_bounty,
    )


def partial_liq_penalty_capped(
    collateral_after_pnl: int,
    position_base: int,
    fraction_bps: int,
    settle_price_e8: int,
    liquidation_penalty_bps: int,
    min_notional_for_bounty: int,
) -> int:
    """Penalty for partial close, capped at remaining collateral (non-negative)."""
    raw = partial_liq_penalty(
        position_base, fraction_bps, settle_price_e8,
        liquidation_penalty_bps, min_notional_for_bounty,
    )
    return min(max(collateral_after_pnl, 0), raw)


def _is_partial_fraction_sufficient(
    position_base: int,
    collateral_after_pnl: int,
    fraction_bps: int,
    settle_price_e8: int,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    liquidation_penalty_bps: int,
    min_notional_for_bounty: int,
) -> bool:
    """True if closing fraction_bps/10000 of position restores maint margin."""
    remaining = remaining_position_signed(position_base, fraction_bps)
    penalty = partial_liq_penalty_capped(
        collateral_after_pnl, position_base, fraction_bps,
        settle_price_e8, liquidation_penalty_bps, min_notional_for_bounty,
    )
    coll_after = collateral_after_pnl - penalty
    if remaining == 0:
        return True
    mreq = maint_margin_req(remaining, settle_price_e8,
                            maintenance_margin_bps, depeg_buffer_bps)
    return coll_after >= mreq


def compute_partial_close_fraction(
    position_base: int,
    collateral_after_pnl: int,
    settle_price_e8: int,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    liquidation_penalty_bps: int,
    min_notional_for_bounty: int,
) -> int:
    """Compute minimum fraction [1, BPS_SCALE] to close to restore maint margin.

    Returns BPS_SCALE if full close is needed (or account is deeply underwater).
    Returns 0 if the position is not actually liquidatable (defensive).

    The sufficiency predicate is not monotone in the close fraction: crossing
    `min_notional_for_bounty` can activate a liquidation penalty, and integer
    rounding can create additional local reversals. The bounded basis-point
    domain is therefore scanned in canonical ascending order so the returned
    fraction is the true minimum under the runtime arithmetic. The loop keeps
    the exact predicate arithmetic inline to bound dispatch overhead on the
    worst-case 9,999-candidate path.
    """
    if position_base == 0:
        return 0

    if not is_liquidatable(
        position_base, collateral_after_pnl, settle_price_e8,
        maintenance_margin_bps, depeg_buffer_bps,
    ):
        return 0

    position_abs = abs_val(position_base)
    effective_maintenance_bps = maintenance_margin_bps + depeg_buffer_bps
    penalty_cap = max(collateral_after_pnl, 0)
    for fraction_bps in range(1, BPS_SCALE):
        closed_base = (position_abs * fraction_bps) // BPS_SCALE
        remaining_abs = position_abs - closed_base
        if remaining_abs == 0:
            return int(fraction_bps)
        closed_notional = (closed_base * settle_price_e8) // PRICE_SCALE
        if closed_notional < min_notional_for_bounty:
            penalty = 0
        else:
            penalty = min(
                penalty_cap,
                (closed_notional * liquidation_penalty_bps) // BPS_SCALE,
            )
        maintenance_requirement = risk_margin_requirement(
            remaining_abs,
            settle_price_e8,
            effective_maintenance_bps,
        )
        if collateral_after_pnl - penalty >= maintenance_requirement:
            return int(fraction_bps)

    return BPS_SCALE


def liquidation_price_e8(
    position_base: int,
    collateral: int,
    index_price_e8: int,
    maint_bps: int,
    depeg_bps: int,
) -> int | None:
    """Estimate the index price at which position becomes liquidatable.

    Returns the price (in e8) at which collateral == maintenance margin,
    or None if the position is flat.

    This is a *UI display estimate*, not a safety-critical computation.
    The actual liquidation decision uses ``is_liquidatable()`` which includes
    PnL. This estimate answers: "at roughly what mark price does
    collateral == maintenance margin?", ignoring direction-dependent PnL.

    Integer approximation via cross-multiplication:
    At liquidation: collateral = floor(floor(abs_pos * liq_price / 1e8) * eff_maint / 10000)
    Upper bound: abs_pos * liq_price * eff_maint / (1e8 * 10000)
    Solving: liq_price = collateral * 1e8 * 10000 / (abs_pos * eff_maint)
    """
    if position_base == 0:
        return None

    abs_pos = abs_val(position_base)
    eff_maint_bps = maint_bps + depeg_bps
    if eff_maint_bps == 0:
        return None

    liq = (collateral * PRICE_SCALE * BPS_SCALE) // (abs_pos * eff_maint_bps)
    if liq <= 0:
        return None
    return liq
