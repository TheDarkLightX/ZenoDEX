from __future__ import annotations

import pytest

from src.kernels.python.strategy_route_economic_sanity_guard_v1_adapter import (
    StrategyRouteEconomicSanityInputs,
    StrategyRouteEconomicSanityPolicy,
    check_strategy_route_economic_sanity,
)


def _policy() -> StrategyRouteEconomicSanityPolicy:
    return StrategyRouteEconomicSanityPolicy(
        input_stress_extreme_bps=10_000,
        output_depletion_extreme_bps=9_000,
        price_impact_extreme_bps=5_000,
    )


def _inputs(**overrides: object) -> StrategyRouteEconomicSanityInputs:
    data = {
        "receipt_verified": True,
        "route_kind_supported": True,
        "body_pair_valid": True,
        "legs_present": True,
        "all_legs_single_hop": True,
        "all_legs_match_body_pair": True,
        "multi_hop_present": False,
        "max_hop_input_vs_reserve_bps": 2_500,
        "max_hop_output_vs_reserve_bps": 2_000,
        "max_hop_price_impact_bps": 800,
    }
    data.update(overrides)
    return StrategyRouteEconomicSanityInputs(**data)


def test_check_strategy_route_economic_sanity_accepts_supported_sane_route() -> None:
    result = check_strategy_route_economic_sanity(
        inputs=_inputs(),
        policy=_policy(),
    )
    assert result.ok is True
    assert result.route_shape_supported_for_intents is True
    assert result.extreme_input_stress_present is False
    assert result.extreme_output_depletion_present is False
    assert result.extreme_price_impact_present is False
    assert result.error is None


def test_check_strategy_route_economic_sanity_rejects_multi_hop_route_shape() -> None:
    result = check_strategy_route_economic_sanity(
        inputs=_inputs(all_legs_single_hop=False, multi_hop_present=True),
        policy=_policy(),
    )
    assert result.ok is False
    assert result.route_shape_supported_for_intents is False
    assert result.error == "route_multi_hop_unsupported"


def test_check_strategy_route_economic_sanity_rejects_extreme_input_stress() -> None:
    result = check_strategy_route_economic_sanity(
        inputs=_inputs(max_hop_input_vs_reserve_bps=10_000),
        policy=_policy(),
    )
    assert result.ok is False
    assert result.route_shape_supported_for_intents is True
    assert result.extreme_input_stress_present is True
    assert result.error == "route_extreme_input_stress:max=10000,threshold=10000"


def test_check_strategy_route_economic_sanity_rejects_mixed_asset_pairs() -> None:
    result = check_strategy_route_economic_sanity(
        inputs=_inputs(all_legs_match_body_pair=False),
        policy=_policy(),
    )
    assert result.ok is False
    assert result.route_shape_supported_for_intents is False
    assert result.error == "route_mixed_asset_pairs"


def test_check_strategy_route_economic_sanity_rejects_invalid_types_and_ranges() -> None:
    with pytest.raises(TypeError, match="receipt_verified must be a bool"):
        StrategyRouteEconomicSanityInputs(
            receipt_verified=1,
            route_kind_supported=True,
            body_pair_valid=True,
            legs_present=True,
            all_legs_single_hop=True,
            all_legs_match_body_pair=True,
            multi_hop_present=False,
            max_hop_input_vs_reserve_bps=1,
            max_hop_output_vs_reserve_bps=1,
            max_hop_price_impact_bps=1,
        )
    with pytest.raises(ValueError, match="max_hop_input_vs_reserve_bps out of u32 range"):
        StrategyRouteEconomicSanityInputs(
            receipt_verified=True,
            route_kind_supported=True,
            body_pair_valid=True,
            legs_present=True,
            all_legs_single_hop=True,
            all_legs_match_body_pair=True,
            multi_hop_present=False,
            max_hop_input_vs_reserve_bps=-1,
            max_hop_output_vs_reserve_bps=1,
            max_hop_price_impact_bps=1,
        )
    with pytest.raises(ValueError, match="input_stress_extreme_bps out of u32 range"):
        StrategyRouteEconomicSanityPolicy(
            input_stress_extreme_bps=0,
            output_depletion_extreme_bps=1,
            price_impact_extreme_bps=1,
        )
    with pytest.raises(TypeError, match="inputs must be a StrategyRouteEconomicSanityInputs"):
        check_strategy_route_economic_sanity(inputs="bad", policy=_policy())
    with pytest.raises(TypeError, match="policy must be a StrategyRouteEconomicSanityPolicy"):
        check_strategy_route_economic_sanity(inputs=_inputs(), policy="bad")
