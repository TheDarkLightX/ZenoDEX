"""Kernel-backed settlement helpers for ``funding_rate_market_v1_1``.

This module isolates the deterministic settlement arithmetic from
``src.core.funding_rate_market`` so the market runtime and witness shells can
share one implementation.
"""

from __future__ import annotations

from dataclasses import dataclass


BPS_DENOM = 10_000
MAX_AMOUNT = 1_000_000_000_000
MAX_RATE_BPS = 10_000


@dataclass(frozen=True)
class FundingRateSettlementQuote:
    realized_rate_bps: int
    protocol_fee: int
    distributable_pool: int
    winning_long: bool
    long_payout: int
    short_payout: int


def _require_int_range(
    name: str,
    value: object,
    *,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    value_int = int(value)
    if minimum is not None and value_int < minimum:
        raise ValueError(f"{name} must be >= {minimum}: {value_int}")
    if maximum is not None and value_int > maximum:
        raise ValueError(f"{name} exceeds max {maximum}: {value_int}")
    return value_int


def _clamp_rate(raw_rate_bps: int, funding_cap_bps: int) -> int:
    return max(-funding_cap_bps, min(funding_cap_bps, raw_rate_bps))


def compute_funding_rate_settlement(
    *,
    rate_long_exposure: int,
    rate_short_exposure: int,
    premium_pool: int,
    implied_rate_bps: int,
    funding_cap_bps: int,
    protocol_fee_bps: int,
    mark_price_e8: int,
    index_price_e8: int,
) -> FundingRateSettlementQuote:
    """Return the deterministic settlement values for one funding-rate epoch."""

    rate_long_exposure = _require_int_range(
        "rate_long_exposure",
        rate_long_exposure,
        minimum=0,
        maximum=MAX_AMOUNT,
    )
    rate_short_exposure = _require_int_range(
        "rate_short_exposure",
        rate_short_exposure,
        minimum=0,
        maximum=MAX_AMOUNT,
    )
    premium_pool = _require_int_range(
        "premium_pool",
        premium_pool,
        minimum=0,
        maximum=MAX_AMOUNT,
    )
    implied_rate_bps = _require_int_range(
        "implied_rate_bps",
        implied_rate_bps,
        minimum=-MAX_RATE_BPS,
        maximum=MAX_RATE_BPS,
    )
    funding_cap_bps = _require_int_range(
        "funding_cap_bps",
        funding_cap_bps,
        minimum=1,
        maximum=MAX_RATE_BPS,
    )
    protocol_fee_bps = _require_int_range(
        "protocol_fee_bps",
        protocol_fee_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )
    mark_price_e8 = _require_int_range(
        "mark_price_e8",
        mark_price_e8,
        minimum=1,
        maximum=MAX_AMOUNT,
    )
    index_price_e8 = _require_int_range(
        "index_price_e8",
        index_price_e8,
        minimum=1,
        maximum=MAX_AMOUNT,
    )

    total_exposure = rate_long_exposure + rate_short_exposure
    if total_exposure <= 0:
        raise ValueError("total exposure must be > 0")
    if total_exposure > MAX_AMOUNT:
        raise ValueError(f"total exposure exceeds max {MAX_AMOUNT}: {total_exposure}")

    realized_raw = ((mark_price_e8 - index_price_e8) * BPS_DENOM) // index_price_e8
    realized_rate_bps = _clamp_rate(realized_raw, funding_cap_bps)

    protocol_fee = (premium_pool * protocol_fee_bps) // BPS_DENOM
    distributable_pool = premium_pool - protocol_fee
    winning_long = realized_rate_bps >= implied_rate_bps
    winning_exposure = rate_long_exposure if winning_long else rate_short_exposure

    long_payout = (distributable_pool * winning_exposure) // total_exposure
    short_payout = distributable_pool - long_payout

    return FundingRateSettlementQuote(
        realized_rate_bps=int(realized_rate_bps),
        protocol_fee=int(protocol_fee),
        distributable_pool=int(distributable_pool),
        winning_long=bool(winning_long),
        long_payout=int(long_payout),
        short_payout=int(short_payout),
    )
