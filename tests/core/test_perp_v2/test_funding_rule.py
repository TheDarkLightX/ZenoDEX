from __future__ import annotations

import pytest

from src.core.perp_v2.funding_rule import compute_funding_rate_bps


def test_compute_funding_rate_bps_sign_and_cap() -> None:
    index = 100_000_000

    # +2% basis => 200 bps, capped to 100.
    assert compute_funding_rate_bps(index_price_e8=index, mark_price_e8=102_000_000, funding_cap_bps=100) == 100

    # -1% basis => -100 bps (uncapped).
    assert compute_funding_rate_bps(index_price_e8=index, mark_price_e8=99_000_000, funding_cap_bps=200) == -100

    # No basis => 0.
    assert compute_funding_rate_bps(index_price_e8=index, mark_price_e8=index, funding_cap_bps=100) == 0


def test_compute_funding_rate_bps_rejects_nonpositive_index() -> None:
    with pytest.raises(ValueError):
        compute_funding_rate_bps(index_price_e8=0, mark_price_e8=1, funding_cap_bps=100)
