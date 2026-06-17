from __future__ import annotations

import pytest

from src.integration.api_server import _canonical_routing_pool_snapshots


def _pool() -> dict[str, object]:
    return {
        "pool_id": "pool-a",
        "asset0": "A",
        "asset1": "B",
        "reserve0": 1_000,
        "reserve1": 2_000,
        "fee_bps": 30,
        "lp_supply": 100,
        "status": "active",
        "created_at": 0,
        "curve_tag": "CPMM",
        "curve_params": "",
    }


@pytest.mark.parametrize("field", ("reserve0", "reserve1", "fee_bps", "lp_supply", "created_at"))
def test_canonical_routing_pool_snapshots_reject_bool_numeric_fields(field: str) -> None:
    pool = _pool()
    pool[field] = True

    with pytest.raises(ValueError, match=f"{field}_must_be_int"):
        _canonical_routing_pool_snapshots([pool])
