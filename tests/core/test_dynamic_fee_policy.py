import pytest

from src.core.dynamic_fee_policy import StressFeePolicy, fee_bps_from_stress_policy


def test_stress_fee_policy_rejects_bool_fields() -> None:
    with pytest.raises(TypeError, match="base_fee_bps must be an int"):
        StressFeePolicy(base_fee_bps=True, slope_bps=100)


def test_fee_bps_from_stress_policy_rejects_bool_inputs() -> None:
    policy = StressFeePolicy(base_fee_bps=30, slope_bps=1000)

    with pytest.raises(TypeError, match="reserve_in must be an int"):
        fee_bps_from_stress_policy(policy, reserve_in=True, amount_in=10)

    with pytest.raises(TypeError, match="amount_in must be an int"):
        fee_bps_from_stress_policy(policy, reserve_in=100, amount_in=False)


def test_fee_bps_from_stress_policy_valid_integer_behavior() -> None:
    policy = StressFeePolicy(base_fee_bps=30, slope_bps=1000, min_fee_bps=20, max_fee_bps=500)

    assert fee_bps_from_stress_policy(policy, reserve_in=1000, amount_in=100) == 130
    assert fee_bps_from_stress_policy(policy, reserve_in=1000, amount_in=10_000) == 500
