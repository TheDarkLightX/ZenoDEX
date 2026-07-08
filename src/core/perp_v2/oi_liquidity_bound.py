"""Open-interest liquidity bounds for funding manipulation resistance.

The funding-rate rule can only be as safe as its reference price. This module
adds a small integer guard for the TWAP funding lane:

    max_open_interest <= spot_depth * arbitrage_absorb_factor

It does not compute TWAPs. It checks the capacity relation that makes a TWAP
manipulation uneconomic in the linear funding-vs-arbitrage-cost model.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..domain_limits import require_int_range
from .math import BPS_SCALE


@dataclass(frozen=True)
class OILiquidityBound:
    """Result of evaluating an open-interest liquidity guard."""

    open_interest_quote: int
    spot_depth_quote: int
    arbitrage_absorb_bps: int
    max_open_interest_quote: int
    bound_ok: bool

    def __post_init__(self) -> None:
        require_int_range("open_interest_quote", self.open_interest_quote, minimum=0)
        require_int_range("spot_depth_quote", self.spot_depth_quote, minimum=0)
        require_int_range(
            "arbitrage_absorb_bps",
            self.arbitrage_absorb_bps,
            minimum=0,
            maximum=BPS_SCALE,
        )
        require_int_range("max_open_interest_quote", self.max_open_interest_quote, minimum=0)
        if not isinstance(self.bound_ok, bool):
            raise TypeError("bound_ok must be a bool")


def max_open_interest_from_spot_depth(
    *,
    spot_depth_quote: int,
    arbitrage_absorb_bps: int,
) -> int:
    """Return the max OI supported by spot depth and absorb factor."""

    depth = require_int_range("spot_depth_quote", spot_depth_quote, minimum=0)
    absorb = require_int_range(
        "arbitrage_absorb_bps",
        arbitrage_absorb_bps,
        minimum=0,
        maximum=BPS_SCALE,
    )
    return (depth * absorb) // BPS_SCALE


def evaluate_oi_liquidity_bound(
    *,
    open_interest_quote: int,
    spot_depth_quote: int,
    arbitrage_absorb_bps: int,
) -> OILiquidityBound:
    """Evaluate the TWAP funding OI/depth admission guard."""

    oi = require_int_range("open_interest_quote", open_interest_quote, minimum=0)
    max_oi = max_open_interest_from_spot_depth(
        spot_depth_quote=spot_depth_quote,
        arbitrage_absorb_bps=arbitrage_absorb_bps,
    )
    depth = require_int_range("spot_depth_quote", spot_depth_quote, minimum=0)
    absorb = require_int_range(
        "arbitrage_absorb_bps",
        arbitrage_absorb_bps,
        minimum=0,
        maximum=BPS_SCALE,
    )
    return OILiquidityBound(
        open_interest_quote=oi,
        spot_depth_quote=depth,
        arbitrage_absorb_bps=absorb,
        max_open_interest_quote=max_oi,
        bound_ok=oi <= max_oi,
    )


def funding_extraction_upper_bound_quote(
    *,
    open_interest_quote: int,
    twap_deviation_bps: int,
) -> int:
    """Upper-bound funding extraction under a TWAP deviation."""

    oi = require_int_range("open_interest_quote", open_interest_quote, minimum=0)
    deviation = require_int_range(
        "twap_deviation_bps",
        twap_deviation_bps,
        minimum=0,
        maximum=BPS_SCALE,
    )
    return (oi * deviation) // BPS_SCALE


def twap_arbitrage_bleed_floor_quote(
    *,
    spot_depth_quote: int,
    arbitrage_absorb_bps: int,
    twap_deviation_bps: int,
) -> int:
    """Lower-bound manipulation bleed in the linear TWAP cost model."""

    max_oi = max_open_interest_from_spot_depth(
        spot_depth_quote=spot_depth_quote,
        arbitrage_absorb_bps=arbitrage_absorb_bps,
    )
    deviation = require_int_range(
        "twap_deviation_bps",
        twap_deviation_bps,
        minimum=0,
        maximum=BPS_SCALE,
    )
    return (max_oi * deviation) // BPS_SCALE

