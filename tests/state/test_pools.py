from __future__ import annotations

import pytest

from src.state.pools import PoolState, PoolStatus, compute_pool_id


ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "ab" * 32


def _pool(**overrides: object) -> PoolState:
    fields: dict[str, object] = {
        "pool_id": POOL_ID,
        "asset0": ASSET0,
        "asset1": ASSET1,
        "reserve0": 1_000,
        "reserve1": 2_000,
        "fee_bps": 30,
        "lp_supply": 3_000,
        "status": PoolStatus.ACTIVE,
        "created_at": 0,
    }
    fields.update(overrides)
    return PoolState(**fields)  # type: ignore[arg-type]


@pytest.mark.parametrize("field", ["reserve0", "reserve1", "fee_bps", "lp_supply", "created_at"])
def test_pool_state_rejects_bool_scalars(field: str) -> None:
    # REVIEW [B- -> B+]: bool is an int subclass in Python, but it is not a
    # valid pool scalar. PoolState now rejects it at construction instead of
    # letting invalid state survive until state-root serialization.
    with pytest.raises(TypeError, match=f"{field} must be an int"):
        _pool(**{field: True})


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("reserve0", "1"),
        ("reserve1", 1.5),
        ("fee_bps", None),
        ("lp_supply", "3"),
        ("created_at", 0.0),
    ],
)
def test_pool_state_rejects_non_int_scalars(field: str, value: object) -> None:
    with pytest.raises(TypeError, match=f"{field} must be an int"):
        _pool(**{field: value})


def test_compute_pool_id_rejects_bool_fee_bps() -> None:
    with pytest.raises(TypeError, match="fee_bps must be an int"):
        compute_pool_id(ASSET0, ASSET1, True)


@pytest.mark.parametrize("status", ["ACTIVE", True, object()])
def test_pool_state_rejects_non_enum_status(status: object) -> None:
    # REVIEW [B+ -> A-]: pool status is consensus-relevant and state-root maps
    # only PoolStatus enum values to committed codes. Keep strings and other
    # primitives out of live PoolState; parsers should convert before entry.
    with pytest.raises(TypeError, match="status must be a PoolStatus"):
        _pool(status=status)
