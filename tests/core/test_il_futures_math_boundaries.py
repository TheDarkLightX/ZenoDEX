import pytest

from src.core.il_futures_math import compute_il_bps, compute_payout


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"reserve_x_before": True, "reserve_y_before": 1, "reserve_x_after": 1, "reserve_y_after": 1}, "reserve_x_before"),
        ({"reserve_x_before": 1, "reserve_y_before": False, "reserve_x_after": 1, "reserve_y_after": 1}, "reserve_y_before"),
        ({"reserve_x_before": 1, "reserve_y_before": 1, "reserve_x_after": True, "reserve_y_after": 1}, "reserve_x_after"),
        ({"reserve_x_before": 1, "reserve_y_before": 1, "reserve_x_after": 1, "reserve_y_after": False}, "reserve_y_after"),
    ],
)
def test_compute_il_bps_rejects_bool_reserves(kwargs: dict[str, int], message: str) -> None:
    with pytest.raises(TypeError, match=rf"{message} must be an int"):
        compute_il_bps(**kwargs)


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"il_bps": True, "position_value": 100, "coverage_ratio_bps": 100}, "il_bps"),
        ({"il_bps": 100, "position_value": False, "coverage_ratio_bps": 100}, "position_value"),
        ({"il_bps": 100, "position_value": 100, "coverage_ratio_bps": True}, "coverage_ratio_bps"),
    ],
)
def test_compute_payout_rejects_bool_inputs(kwargs: dict[str, int], message: str) -> None:
    with pytest.raises(TypeError, match=rf"{message} must be an int"):
        compute_payout(**kwargs)


def test_il_math_valid_integer_fail_safe_behavior_is_unchanged() -> None:
    assert compute_il_bps(0, 1000, 1000, 1000) == 0
    assert compute_il_bps(1000, 1000, 1000, 1000) == 0
    assert compute_payout(0, 1_000_000, 8_000) == 0
    assert compute_payout(500, 1_000_000, 8_000) == 40_000
