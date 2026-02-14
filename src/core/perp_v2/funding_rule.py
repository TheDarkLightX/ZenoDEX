"""Deterministic funding-rate rule (protocol-side) for isolated perps.

The `perp_v2` kernel treats `new_rate_bps` as an environment input. This module
provides a small, auditable rule for deriving a funding rate from two prices:
- `index_price_e8`: the current index price (quote-per-base scaled by 1e8)
- `mark_price_e8`: an external mark/clearing price for the next settlement

The rule is intentionally simple:
    basis_bps := floor(|mark-index| / index * 10_000)
    rate_bps  := sign(mark-index) * min(basis_bps, funding_cap_bps)

Positive funding means longs pay shorts (mark > index), matching the kernel's
sign convention.
"""

from __future__ import annotations

from .math import BPS_SCALE, abs_val


def compute_funding_rate_bps(*, index_price_e8: int, mark_price_e8: int, funding_cap_bps: int) -> int:
    if not isinstance(index_price_e8, int) or isinstance(index_price_e8, bool):
        raise TypeError("index_price_e8 must be an int")
    if not isinstance(mark_price_e8, int) or isinstance(mark_price_e8, bool):
        raise TypeError("mark_price_e8 must be an int")
    if not isinstance(funding_cap_bps, int) or isinstance(funding_cap_bps, bool):
        raise TypeError("funding_cap_bps must be an int")
    if index_price_e8 <= 0:
        raise ValueError("index_price_e8 must be positive")
    if funding_cap_bps < 0:
        raise ValueError("funding_cap_bps must be non-negative")

    diff = int(mark_price_e8) - int(index_price_e8)
    mag = (abs_val(diff) * BPS_SCALE) // int(index_price_e8)
    mag = min(int(funding_cap_bps), int(mag))
    if diff >= 0:
        return int(mag)
    return -int(mag)

