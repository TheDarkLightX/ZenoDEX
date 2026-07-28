from __future__ import annotations

from src.core.fcis_create_pool_event import (
    ExactCreatePoolEventV1,
    create_pool_event_matches_owned_v1,
    exact_create_pool_event_v1,
)
from src.state.owned_json import snapshot_owned_json_object
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshots import snapshot_pool


def _committed_pool():
    legacy = PoolState(
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
    return snapshot_pool(legacy)


def _source_event(event: ExactCreatePoolEventV1) -> dict[str, str | int]:
    return {
        "type": "CREATE_POOL",
        "pool_id": event.pool_id,
        "asset0": event.asset0,
        "asset1": event.asset1,
        "fee_bps": event.fee_bps,
        "curve_tag": event.curve_tag,
        "curve_params": event.curve_params,
        "status": event.status,
        "created_at": event.created_at,
    }


def test_exact_create_pool_event_matches_the_admitted_protocol_event() -> None:
    expected = exact_create_pool_event_v1(_committed_pool())
    supplied = snapshot_owned_json_object(_source_event(expected))

    assert create_pool_event_matches_owned_v1(expected, supplied)


def test_exact_create_pool_event_rejects_field_substitution() -> None:
    expected = exact_create_pool_event_v1(_committed_pool())
    source = _source_event(expected)
    source["fee_bps"] = 31

    assert not create_pool_event_matches_owned_v1(
        expected,
        snapshot_owned_json_object(source),
    )


def test_exact_create_pool_event_rejects_extra_or_missing_fields() -> None:
    expected = exact_create_pool_event_v1(_committed_pool())
    extra = _source_event(expected)
    extra["attacker"] = 1
    missing = _source_event(expected)
    del missing["status"]

    assert not create_pool_event_matches_owned_v1(
        expected,
        snapshot_owned_json_object(extra),
    )
    assert not create_pool_event_matches_owned_v1(
        expected,
        snapshot_owned_json_object(missing),
    )
