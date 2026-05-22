"""Multi-cycle wash-trade models (internal).

This extends the single-cycle analysis in `tools/tokenomics/wash_trade.py` by
allowing an attacker to perform N consecutive wash trades, updating reserves
each cycle.

Key design choice:
- We value and convert everything at the *initial* spot price p0.
  This avoids letting the attacker game the conversion by moving p0 mid-sequence.

This is analysis-only code and is intentionally bounded/deterministic.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from src.kernels.python.cpmm_swap_v8 import swap_exact_in

E8 = 100_000_000
BPS_DENOM = 10_000


def _require_int(name: str, v: int) -> None:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int")


def _spot_price_e8(*, reserve_base: int, reserve_quote: int) -> int:
    if reserve_base <= 0 or reserve_quote <= 0:
        raise ValueError("empty reserves")
    return (int(reserve_quote) * E8) // int(reserve_base)


@dataclass(frozen=True)
class WashTradeSequenceResult:
    cycles: int
    trade_in_quote_per_cycle: int

    reserve_base_before: int
    reserve_quote_before: int
    reserve_base_after: int
    reserve_quote_after: int

    price0_e8: int

    # Totals across all cycles.
    total_quote_in: int
    total_quote_back: int
    wallet_delta_quote: int

    protocol_fee_total_quote_at_p0: int

    pool_value_before_quote_at_p0: int
    pool_value_after_quote_at_p0: int
    delta_pool_value_quote_at_p0: int

    attacker_cost_quote_at_p0: Fraction


def wash_trade_sequence(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    trade_in_quote_per_cycle: int,
    cycles: int,
    attacker_lp_share_bps: int,
) -> WashTradeSequenceResult:
    for name, v in (
        ("reserve_base", reserve_base),
        ("reserve_quote", reserve_quote),
        ("fee_bps", fee_bps),
        ("protocol_fee_share_bps", protocol_fee_share_bps),
        ("trade_in_quote_per_cycle", trade_in_quote_per_cycle),
        ("cycles", cycles),
        ("attacker_lp_share_bps", attacker_lp_share_bps),
    ):
        _require_int(name, v)

    if reserve_base <= 0 or reserve_quote <= 0:
        raise ValueError("reserves must be positive")
    if trade_in_quote_per_cycle <= 0:
        raise ValueError("trade_in_quote_per_cycle must be positive")
    if cycles <= 0:
        raise ValueError("cycles must be positive")
    if not (0 <= fee_bps <= BPS_DENOM):
        raise ValueError("fee_bps out of range")
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError("protocol_fee_share_bps out of range")
    if not (0 <= attacker_lp_share_bps <= BPS_DENOM):
        raise ValueError("attacker_lp_share_bps out of range")

    price0_e8 = _spot_price_e8(reserve_base=int(reserve_base), reserve_quote=int(reserve_quote))
    value_before = int(reserve_quote) + int((int(reserve_base) * price0_e8) // E8)

    b = int(reserve_base)
    q = int(reserve_quote)

    total_quote_in = 0
    total_quote_back = 0
    protocol_fee_total_q = 0

    for _ in range(int(cycles)):
        total_quote_in += int(trade_in_quote_per_cycle)

        leg1 = swap_exact_in(
            reserve_in=int(q),
            reserve_out=int(b),
            amount_in=int(trade_in_quote_per_cycle),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        base_out = int(leg1.amount_out)
        q = int(leg1.new_reserve_in)
        b = int(leg1.new_reserve_out)
        pf1_quote = int(leg1.protocol_fee)

        leg2 = swap_exact_in(
            reserve_in=int(b),
            reserve_out=int(q),
            amount_in=int(base_out),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        quote_back = int(leg2.amount_out)
        pf2_base = int(leg2.protocol_fee)

        # Convert base-denominated protocol fee to quote at initial p0 (floor).
        pf2_quote = int((pf2_base * price0_e8) // E8)

        total_quote_back += int(quote_back)
        protocol_fee_total_q += int(pf1_quote + pf2_quote)

        # Update reserves after leg2.
        b = int(leg2.new_reserve_in)
        q = int(leg2.new_reserve_out)

    wallet_delta_q = int(total_quote_back - total_quote_in)
    value_after = int(q) + int((int(b) * price0_e8) // E8)
    delta_pool_value_q = int(value_after - value_before)

    lp_share = Fraction(int(attacker_lp_share_bps), BPS_DENOM)
    attacker_delta = Fraction(int(wallet_delta_q), 1) + lp_share * Fraction(int(delta_pool_value_q), 1)
    cost = Fraction(0, 1) if attacker_delta >= 0 else -attacker_delta

    return WashTradeSequenceResult(
        cycles=int(cycles),
        trade_in_quote_per_cycle=int(trade_in_quote_per_cycle),
        reserve_base_before=int(reserve_base),
        reserve_quote_before=int(reserve_quote),
        reserve_base_after=int(b),
        reserve_quote_after=int(q),
        price0_e8=int(price0_e8),
        total_quote_in=int(total_quote_in),
        total_quote_back=int(total_quote_back),
        wallet_delta_quote=int(wallet_delta_q),
        protocol_fee_total_quote_at_p0=int(protocol_fee_total_q),
        pool_value_before_quote_at_p0=int(value_before),
        pool_value_after_quote_at_p0=int(value_after),
        delta_pool_value_quote_at_p0=int(delta_pool_value_q),
        attacker_cost_quote_at_p0=cost,
    )

