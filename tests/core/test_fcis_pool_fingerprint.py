from __future__ import annotations

import pytest

from src.core.fcis_pool_fingerprint import pool_state_fingerprint_committed_v1
from src.core.quote_receipts import pool_state_fingerprint
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshot_values import CommittedPoolStateV1
from src.state.state_snapshots import snapshot_pool


def _legacy_pool() -> PoolState:
    return PoolState(
        pool_id=compute_pool_id("asset-a", "asset-b", 30),
        asset0="asset-a",
        asset1="asset-b",
        reserve0=100,
        reserve1=200,
        fee_bps=30,
        lp_supply=50,
        status=PoolStatus.ACTIVE,
        created_at=7,
    )


def test_exact_pool_fingerprint_matches_the_preserved_legacy_digest() -> None:
    legacy = _legacy_pool()
    committed = snapshot_pool(legacy)

    assert pool_state_fingerprint_committed_v1(committed) == pool_state_fingerprint(legacy)


def test_exact_pool_fingerprint_rejects_wrong_root_type() -> None:
    with pytest.raises(TypeError, match="exact committed pool"):
        pool_state_fingerprint_committed_v1(_legacy_pool())  # type: ignore[arg-type]


def test_exact_pool_fingerprint_revalidates_hostile_nested_mutation() -> None:
    committed = snapshot_pool(_legacy_pool())
    assert type(committed) is CommittedPoolStateV1
    object.__setattr__(committed, "reserve0", -1)

    with pytest.raises((TypeError, ValueError)):
        pool_state_fingerprint_committed_v1(committed)
