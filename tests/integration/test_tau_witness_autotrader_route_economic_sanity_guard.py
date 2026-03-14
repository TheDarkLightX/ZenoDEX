from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1,
    build_autotrader_route_economic_sanity_guard_v1_step,
)


def test_build_autotrader_route_economic_sanity_guard_v1_step() -> None:
    step = build_autotrader_route_economic_sanity_guard_v1_step(
        receipt_verified=1,
        route_kind_supported=1,
        body_pair_valid=1,
        legs_present=1,
        all_legs_single_hop=1,
        all_legs_match_body_pair=1,
        multi_hop_present=0,
        max_hop_input_vs_reserve_bps=2500,
        max_hop_output_vs_reserve_bps=2000,
        max_hop_price_impact_bps=800,
        input_stress_extreme_bps=10000,
        output_depletion_extreme_bps=9000,
        price_impact_extreme_bps=5000,
    )
    assert AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.spec_id == "autotrader_route_economic_sanity_guard_v1"
    assert step == {
        "i1": 1,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 0,
        "i8": 2500,
        "i9": 2000,
        "i10": 800,
        "i11": 10000,
        "i12": 9000,
        "i13": 5000,
    }


def test_build_autotrader_route_economic_sanity_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="receipt_verified must be 0 or 1"):
        build_autotrader_route_economic_sanity_guard_v1_step(
            receipt_verified=2,
            route_kind_supported=1,
            body_pair_valid=1,
            legs_present=1,
            all_legs_single_hop=1,
            all_legs_match_body_pair=1,
            multi_hop_present=0,
            max_hop_input_vs_reserve_bps=2500,
            max_hop_output_vs_reserve_bps=2000,
            max_hop_price_impact_bps=800,
            input_stress_extreme_bps=10000,
            output_depletion_extreme_bps=9000,
            price_impact_extreme_bps=5000,
        )
