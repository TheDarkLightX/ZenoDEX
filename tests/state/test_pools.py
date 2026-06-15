from __future__ import annotations

from typing import cast

import pytest

from src.state.pools import PoolState, PoolStatus, compute_pool_id


def test_compute_pool_id_rejects_non_strict_fee_bps() -> None:
    for bad_fee_bps in (True, False, 30.0, "30"):
        with pytest.raises(TypeError, match="fee_bps must be an int"):
            compute_pool_id("A", "B", cast(int, bad_fee_bps))


@pytest.mark.parametrize(
    ("field_name", "bad_value"),
    [
        ("reserve0", True),
        ("reserve1", False),
        ("fee_bps", True),
        ("lp_supply", 1.0),
        ("created_at", "0"),
    ],
)
def test_pool_state_rejects_non_strict_integer_fields(field_name: str, bad_value: object) -> None:
    kwargs = {
        "pool_id": "pool",
        "asset0": "A",
        "asset1": "B",
        "reserve0": 100,
        "reserve1": 200,
        "fee_bps": 30,
        "lp_supply": 1_000,
        "status": PoolStatus.ACTIVE,
        "created_at": 0,
    }
    kwargs[field_name] = bad_value

    with pytest.raises(TypeError, match=f"{field_name} must be an int"):
        PoolState(**kwargs)  # type: ignore[arg-type]
