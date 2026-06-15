from __future__ import annotations

from typing import cast

import pytest

from src.state.pools import PoolState, PoolStatus, compute_pool_id


def test_compute_pool_id_rejects_non_strict_fee_bps() -> None:
    for bad_fee_bps in (True, False, 30.0, "30"):
        with pytest.raises(TypeError, match="fee_bps must be an int"):
            compute_pool_id("A", "B", cast(int, bad_fee_bps))


def test_compute_pool_id_rejects_non_string_assets() -> None:
    with pytest.raises(TypeError, match="asset ids must be strings"):
        compute_pool_id(cast(str, 1), "B", 30)
    with pytest.raises(TypeError, match="asset ids must be strings"):
        compute_pool_id("A", cast(str, 2), 30)


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


def test_pool_state_rejects_invalid_identity_and_created_at_fields() -> None:
    base_kwargs = {
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

    with pytest.raises(TypeError, match="pool_id must be a non-empty string"):
        PoolState(**{**base_kwargs, "pool_id": ""})  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="asset ids must be strings"):
        PoolState(**{**base_kwargs, "asset0": 1})  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="asset ids must be strings"):
        PoolState(**{**base_kwargs, "asset1": 2})  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="created_at must be non-negative"):
        PoolState(**{**base_kwargs, "created_at": -1})  # type: ignore[arg-type]
