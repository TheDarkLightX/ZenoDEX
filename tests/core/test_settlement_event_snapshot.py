"""Settlement event snapshots own supported JSON metadata without wire drift."""

from __future__ import annotations

import json

import pytest

from src.core.settlement import Settlement, SettlementEventSnapshot, snapshot_settlement


def _settlement_with_events(events: list[dict[str, object]]) -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch-1",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=events,
    )


def _nested_event() -> dict[str, object]:
    return {
        "type": "ROUTE_METADATA",
        "metadata": {
            "route": [
                {"pool_id": "pool-a", "hops": [0, 1]},
                {"pool_id": "pool-b", "hops": [2]},
            ],
            "labels": ["fast", "stable"],
            "flags": {"active": True, "memo": None},
        },
        "sequence": [1, {"name": "second", "values": [2, 3]}],
    }


def test_settlement_event_snapshot_round_trips_nested_json_in_original_order() -> None:
    expected_event = _nested_event()
    snapshot = snapshot_settlement(_settlement_with_events([_nested_event()]))

    assert snapshot.events is not None
    event = snapshot.events[0]
    assert type(event["metadata"]) is SettlementEventSnapshot
    assert type(event["metadata"]["route"]) is tuple  # type: ignore[index]
    assert event.to_dict() == expected_event
    assert list(event.to_dict()) == list(expected_event)

    rebuilt = snapshot.to_settlement()
    assert rebuilt.events == [expected_event]
    assert type(rebuilt.events[0]) is dict  # type: ignore[index]
    assert snapshot_settlement(rebuilt) == snapshot
    assert json.dumps(rebuilt.events, separators=(",", ":")) == json.dumps(
        [expected_event], separators=(",", ":")
    )


def test_settlement_event_snapshot_is_stable_after_nested_builder_mutation() -> None:
    builder_event = _nested_event()
    snapshot = snapshot_settlement(_settlement_with_events([builder_event]))

    builder_event["metadata"]["route"][0]["pool_id"] = "rewritten"  # type: ignore[index]
    builder_event["metadata"]["labels"].append("late")  # type: ignore[index]
    builder_event["sequence"][1]["values"].append(4)  # type: ignore[index]

    assert snapshot.events is not None
    assert snapshot.events[0].to_dict() == _nested_event()


def test_settlement_event_snapshot_returns_detached_nested_json_values() -> None:
    snapshot = snapshot_settlement(_settlement_with_events([_nested_event()]))

    assert snapshot.events is not None
    output_event = snapshot.events[0].to_dict()
    assert type(output_event["metadata"]) is dict
    assert type(output_event["metadata"]["route"]) is list  # type: ignore[index]
    output_event["metadata"]["route"][0]["pool_id"] = "rewritten"  # type: ignore[index]
    output_event["metadata"]["labels"].append("late")  # type: ignore[index]

    rebuilt = snapshot.to_settlement()
    assert rebuilt.events is not None
    rebuilt.events[0]["sequence"][1]["values"].append(4)  # type: ignore[index]

    assert snapshot.events[0].to_dict() == _nested_event()


@pytest.mark.parametrize(
    "event",
    [
        {"type": "ROUTE_METADATA", "value": 1.5},
        {"type": "ROUTE_METADATA", "value": object()},
        {"type": "ROUTE_METADATA", "value": ("unsupported",)},
        {"type": "ROUTE_METADATA", "metadata": [1, 2.5]},
        {"type": "ROUTE_METADATA", "metadata": {"value": object()}},
    ],
    ids=("float", "foreign_object", "tuple", "nested_float", "nested_foreign_object"),
)
def test_settlement_event_snapshot_rejects_values_outside_closed_json_algebra(event: dict[str, object]) -> None:
    with pytest.raises(TypeError):
        SettlementEventSnapshot(event)


def test_event_snapshot_equality_matches_mapping_semantics_without_reordering_output() -> None:
    left = SettlementEventSnapshot({"type": "META", "data": {"a": 1, "b": 2}})
    right = SettlementEventSnapshot({"data": {"b": 2, "a": 1}, "type": "META"})
    assert left == right
    assert list(left.to_dict()) == ["type", "data"]
    assert list(right.to_dict()) == ["data", "type"]


def test_settlement_event_snapshot_preserves_flat_create_pool_compatibility() -> None:
    create_pool_event = {
        "type": "CREATE_POOL",
        "pool_id": "pool-ab",
        "asset0": "asset-a",
        "asset1": "asset-b",
        "fee_bps": 30,
        "curve_tag": "CPMM",
        "curve_params": "",
        "status": "ACTIVE",
        "created_at": 0,
    }
    snapshot = snapshot_settlement(_settlement_with_events([create_pool_event]))

    assert snapshot.events is not None
    assert snapshot.events[0].to_dict() == create_pool_event
    assert snapshot.to_settlement().events == [create_pool_event]
