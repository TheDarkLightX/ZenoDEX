from __future__ import annotations

import pytest

from src.core.perp_v2.oi_liquidity_bound import (
    evaluate_oi_liquidity_bound,
    funding_extraction_upper_bound_quote,
    max_open_interest_from_spot_depth,
    twap_arbitrage_bleed_floor_quote,
)


def test_max_open_interest_from_spot_depth() -> None:
    assert (
        max_open_interest_from_spot_depth(
            spot_depth_quote=1_000_000,
            arbitrage_absorb_bps=5_000,
        )
        == 500_000
    )


def test_oi_liquidity_bound_accepts_supported_open_interest() -> None:
    outcome = evaluate_oi_liquidity_bound(
        open_interest_quote=500_000,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
    )

    assert outcome.bound_ok is True
    assert outcome.max_open_interest_quote == 500_000


def test_oi_liquidity_bound_rejects_unsupported_open_interest() -> None:
    outcome = evaluate_oi_liquidity_bound(
        open_interest_quote=500_001,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
    )

    assert outcome.bound_ok is False


def test_bound_implies_funding_extraction_no_more_than_arbitrage_bleed() -> None:
    for deviation_bps in [0, 1, 100, 1_000, 10_000]:
        extraction = funding_extraction_upper_bound_quote(
            open_interest_quote=500_000,
            twap_deviation_bps=deviation_bps,
        )
        bleed = twap_arbitrage_bleed_floor_quote(
            spot_depth_quote=1_000_000,
            arbitrage_absorb_bps=5_000,
            twap_deviation_bps=deviation_bps,
        )
        assert extraction <= bleed


def test_exceeding_bound_has_positive_extraction_gap_witness() -> None:
    extraction = funding_extraction_upper_bound_quote(
        open_interest_quote=600_000,
        twap_deviation_bps=1_000,
    )
    bleed = twap_arbitrage_bleed_floor_quote(
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        twap_deviation_bps=1_000,
    )

    assert extraction == 60_000
    assert bleed == 50_000
    assert extraction > bleed


def test_oi_liquidity_bound_rejects_invalid_types() -> None:
    with pytest.raises(TypeError):
        evaluate_oi_liquidity_bound(
            open_interest_quote=True,
            spot_depth_quote=1_000_000,
            arbitrage_absorb_bps=5_000,
        )

    with pytest.raises(ValueError):
        evaluate_oi_liquidity_bound(
            open_interest_quote=1,
            spot_depth_quote=1_000_000,
            arbitrage_absorb_bps=10_001,
        )
