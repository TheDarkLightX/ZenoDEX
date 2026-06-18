from __future__ import annotations

import pytest

from src.integration.api_server import _canonical_routing_pool_snapshots


def _pool_snapshot() -> dict[str, object]:
    return {
        "pool_id": "pool_a",
        "asset0": "A",
        "asset1": "B",
        "reserve0": 1000,
        "reserve1": 1001,
        "fee_bps": 0,
        "lp_supply": 1,
        "status": "ACTIVE",
        "created_at": 0,
    }


@pytest.mark.parametrize("field", ("reserve0", "reserve1", "fee_bps", "lp_supply", "created_at"))
def test_canonical_routing_pool_snapshots_reject_numeric_string_fields(field: str) -> None:
    row = _pool_snapshot()
    row[field] = "1"

    with pytest.raises(ValueError, match=f"{field}_must_be_int"):
        _canonical_routing_pool_snapshots([row])


@pytest.mark.parametrize("field", ("reserve0", "reserve1", "fee_bps", "lp_supply", "created_at"))
def test_canonical_routing_pool_snapshots_reject_bool_fields(field: str) -> None:
    row = _pool_snapshot()
    row[field] = True

    with pytest.raises(ValueError, match=f"{field}_must_be_int"):
        _canonical_routing_pool_snapshots([row])
