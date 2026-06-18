from __future__ import annotations

from fractions import Fraction

import pytest

from experiments.zusd_hybrid_economics_v1.pool_depth_oracle import (
    ZUSDBuybackDepthGate,
    evaluate_zusd_buyback_depth_gate,
    recommended_min_pool_depth_quote,
    sigma_fee_rule_ok,
    twap_consecutive_control_gain_cost_ratio,
)


@pytest.mark.parametrize(
    "budget,fee_bps,expected_depth",
    [
        (500, 5, 2_000_000),
        (1_000, 25, 800_000),
        (2_400, 30, 1_600_000),
        (5_000, 100, 1_000_000),
    ],
)
def test_recommended_min_pool_depth_matches_stage_c_table(
    budget: int,
    fee_bps: int,
    expected_depth: int,
) -> None:
    assert (
        recommended_min_pool_depth_quote(
            buyback_budget_cap_quote=budget,
            fee_bps=fee_bps,
        )
        == expected_depth
    )


def test_recommended_min_pool_depth_uses_integer_ceiling() -> None:
    assert recommended_min_pool_depth_quote(buyback_budget_cap_quote=2_401, fee_bps=30) == 1_600_668


def test_zero_fee_pool_has_no_finite_depth_gate() -> None:
    result = evaluate_zusd_buyback_depth_gate(
        ZUSDBuybackDepthGate(
            buyback_budget_cap_quote=2_400,
            fee_bps=0,
            sigma_bps=0,
            observed_pool_depth_quote=10**18,
        )
    )

    assert result.required_min_pool_depth_quote is None
    assert result.sigma_fee_rule_ok is True
    assert result.depth_gate_ok is False
    assert result.eligible is False


@pytest.mark.parametrize(
    "sigma_bps,fee_bps,expected",
    [
        (59, 30, True),
        (60, 30, False),
        (50, 30, True),
        (10, 5, False),
        (9, 5, True),
    ],
)
def test_sigma_fee_rule_is_fee_padded_at_boundary(
    sigma_bps: int,
    fee_bps: int,
    expected: bool,
) -> None:
    assert sigma_fee_rule_ok(sigma_bps=sigma_bps, fee_bps=fee_bps) is expected


def test_depth_gate_requires_depth_and_sigma_rule() -> None:
    passing = evaluate_zusd_buyback_depth_gate(
        ZUSDBuybackDepthGate(
            buyback_budget_cap_quote=2_400,
            fee_bps=30,
            sigma_bps=50,
            observed_pool_depth_quote=1_600_000,
        )
    )
    shallow = evaluate_zusd_buyback_depth_gate(
        ZUSDBuybackDepthGate(
            buyback_budget_cap_quote=2_400,
            fee_bps=30,
            sigma_bps=50,
            observed_pool_depth_quote=1_599_999,
        )
    )
    sigma_bad = evaluate_zusd_buyback_depth_gate(
        ZUSDBuybackDepthGate(
            buyback_budget_cap_quote=2_400,
            fee_bps=30,
            sigma_bps=60,
            observed_pool_depth_quote=1_600_000,
        )
    )

    assert passing.eligible is True
    assert shallow.depth_gate_ok is False
    assert shallow.eligible is False
    assert sigma_bad.sigma_fee_rule_ok is False
    assert sigma_bad.eligible is False


def test_twap_consecutive_control_ratio_is_window_independent() -> None:
    ratios = {
        twap_consecutive_control_gain_cost_ratio(
            buyback_budget_per_epoch_quote=2_400,
            pool_depth_quote=1_600_000,
            bias_bps=100,
            window_epochs=window_epochs,
        )
        for window_epochs in (1, 6, 12, 48)
    }

    assert ratios == {Fraction(3, 10)}


def test_twap_consecutive_control_ratio_decreases_with_depth_and_bias() -> None:
    baseline = twap_consecutive_control_gain_cost_ratio(
        buyback_budget_per_epoch_quote=2_400,
        pool_depth_quote=800_000,
        bias_bps=100,
        window_epochs=12,
    )
    deeper = twap_consecutive_control_gain_cost_ratio(
        buyback_budget_per_epoch_quote=2_400,
        pool_depth_quote=1_600_000,
        bias_bps=100,
        window_epochs=12,
    )
    wider_bias = twap_consecutive_control_gain_cost_ratio(
        buyback_budget_per_epoch_quote=2_400,
        pool_depth_quote=800_000,
        bias_bps=200,
        window_epochs=12,
    )

    assert baseline == Fraction(3, 5)
    assert deeper == Fraction(3, 10)
    assert wider_bias == Fraction(3, 10)


@pytest.mark.parametrize(
    "kwargs",
    [
        {"buyback_budget_cap_quote": True},
        {"fee_bps": True},
        {"sigma_bps": True},
        {"observed_pool_depth_quote": True},
        {"safety_multiplier": True},
    ],
)
def test_depth_gate_rejects_bool_numeric_fields(kwargs: dict[str, object]) -> None:
    base: dict[str, object] = {
        "buyback_budget_cap_quote": 2_400,
        "fee_bps": 30,
        "sigma_bps": 50,
        "observed_pool_depth_quote": 1_600_000,
        "safety_multiplier": 2,
    }
    base.update(kwargs)

    with pytest.raises(TypeError):
        evaluate_zusd_buyback_depth_gate(
            ZUSDBuybackDepthGate(**base)  # type: ignore[arg-type]
        )


def test_twap_ratio_rejects_bool_window() -> None:
    with pytest.raises(TypeError):
        twap_consecutive_control_gain_cost_ratio(
            buyback_budget_per_epoch_quote=2_400,
            pool_depth_quote=1_600_000,
            bias_bps=100,
            window_epochs=True,
        )
