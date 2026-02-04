"""Pure arithmetic for the `perp_v2` risk engine.

Every function is stateless and operates on plain Python ints.

This module is intentionally explicit about rounding: it uses Python's `//`
for integer division (floor toward -∞). This matches the kernel interpreter and
the generated reference models used by parity tests.
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
    return oracle_seen and (now_epoch - oracle_last_update_epoch) <= max_oracle_staleness_epochs


def oracle_move_violated(
    clearing_price_e8: int,
    index_price_e8: int,
    max_oracle_move_bps: int,
    oracle_seen: bool,
) -> bool:
    """True when the clearing-to-index price move exceeds the bound.

    Uses cross-multiplication to avoid division:
    ``|clearing - index| * 10000 > max_move_bps * index``.
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
    """Settlement price: clearing price clamped to max allowed move."""
    if not oracle_move_violated(clearing_price_e8, index_price_e8, max_oracle_move_bps, oracle_seen):
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
    """Absolute notional in quote: ``|pos| * price / 1e8``."""
    return (abs_val(position_base) * price_e8) // PRICE_SCALE


def margin_requirement(notional: int, margin_bps: int) -> int:
    """Margin in quote: ``notional * margin_bps / 10000``."""
    return (notional * margin_bps) // BPS_SCALE


def maint_margin_req(position_base: int, price_e8: int, maint_bps: int, depeg_bps: int) -> int:
    """Maintenance margin in quote (includes depeg buffer)."""
    return margin_requirement(notional_quote(position_base, price_e8), maint_bps + depeg_bps)


def init_margin_req(position_base: int, price_e8: int, init_bps: int) -> int:
    """Initial margin in quote."""
    return margin_requirement(notional_quote(position_base, price_e8), init_bps)


# -- PnL helpers (symmetric — magnitude from abs values) ---------------------

def pnl_magnitude(position_base: int, settle_price_e8: int, index_price_e8: int) -> int:
    """Unsigned PnL: ``|pos| * |settle - index| / 1e8``."""
    return (abs_val(position_base) * abs_val(settle_price_e8 - index_price_e8)) // PRICE_SCALE


def pnl_same_sign(position_base: int, settle_price_e8: int, index_price_e8: int) -> bool:
    """True when position direction matches price-change direction (profit)."""
    return (position_base >= 0) == (settle_price_e8 >= index_price_e8)


def pnl_quote(position_base: int, settle_price_e8: int, index_price_e8: int) -> int:
    """Signed PnL: +magnitude when profitable, -magnitude when losing."""
    mag = pnl_magnitude(position_base, settle_price_e8, index_price_e8)
    return mag if pnl_same_sign(position_base, settle_price_e8, index_price_e8) else -mag


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
    raw = liq_penalty(position_base, settle_price_e8, liquidation_penalty_bps, min_notional_for_bounty)
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
        position_base, settle_price_e8, maintenance_margin_bps, depeg_buffer_bps,
    )


# -- Funding helpers (symmetric) ---------------------------------------------

def funding_magnitude(position_base: int, index_price_e8: int, rate_bps: int) -> int:
    """Unsigned funding: ``floor(notional * |rate| / 10000)``."""
    return (notional_quote(position_base, index_price_e8) * abs_val(rate_bps)) // BPS_SCALE


def funding_same_sign(position_base: int, rate_bps: int) -> bool:
    """True when position and rate have same sign (account is payer)."""
    return (position_base >= 0) == (rate_bps >= 0)


def funding_payment(position_base: int, index_price_e8: int, rate_bps: int) -> int:
    """Signed funding: +magnitude for payer, -magnitude for payee."""
    mag = funding_magnitude(position_base, index_price_e8, rate_bps)
    return mag if funding_same_sign(position_base, rate_bps) else -mag
