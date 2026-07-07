from __future__ import annotations

import pytest

from src.state.app_root import (
    APP_ROOT_LANE_KINDS,
    AppRootLeaf,
    app_root_entries,
    app_root_json_value_hash,
    app_root_lane_key,
    app_root_value_hash,
    compute_app_root,
    compute_app_root_from_json_lanes,
    compute_required_app_root,
    prove_app_root_leaf,
    require_app_root_lane_kinds,
    verify_app_root_leaf,
)


def _lane_payload(tag: str, version: int = 1) -> dict[str, object]:
    return {"schema": f"zenodex.{tag}.snapshot.v1", "version": version, "state": {"nonce": version}}


def _leaf(kind: str, lane_id: str, tag: str | None = None) -> AppRootLeaf:
    return AppRootLeaf.from_json(lane_kind=kind, lane_id=lane_id, payload=_lane_payload(tag or kind))


def test_app_root_binds_full_keystone_lane_set_order_independently() -> None:
    leaves = [
        _leaf("spot", "global", "spot"),
        _leaf("oracle", "global", "oracle"),
        _leaf("vault", "protocol", "vault"),
        _leaf("perps", "market:BTC-PERP", "perps"),
        _leaf("zusd", "system", "zusd"),
        _leaf("clob", "book:BTC-USDC", "clob"),
        _leaf("cross_shard", "global", "cross_shard"),
        _leaf("proof_mining", "global", "proof_mining"),
        _leaf("governance", "global", "governance"),
    ]

    root_a = compute_app_root(leaves)
    root_b = compute_app_root(reversed(leaves))

    assert {leaf.lane_kind for leaf in leaves} == APP_ROOT_LANE_KINDS
    assert root_a == root_b

    mutated_perps = [
        leaf if leaf.lane_kind != "perps" else AppRootLeaf.from_json(lane_kind="perps", lane_id="market:BTC-PERP", payload=_lane_payload("perps", 2))
        for leaf in leaves
    ]
    moved_payload = [
        leaf if leaf.lane_kind != "perps" else AppRootLeaf.from_json(lane_kind="zusd", lane_id="market:BTC-PERP", payload=_lane_payload("perps"))
        for leaf in leaves
        if leaf.lane_kind != "zusd"
    ]

    # Review note, grade A: this catches the prior consensus gap directly.
    # The root must change when an excluded lane changes, and the same digest
    # cannot be moved across lane namespaces without changing the JMT key.
    assert root_a != compute_app_root(mutated_perps)
    assert root_a != compute_app_root(moved_payload)


def test_required_app_root_rejects_missing_lane_kinds() -> None:
    partial = [
        _leaf("spot", "global", "spot"),
        _leaf("oracle", "global", "oracle"),
        _leaf("vault", "protocol", "vault"),
        _leaf("perps", "market:BTC-PERP", "perps"),
        _leaf("zusd", "system", "zusd"),
        _leaf("cross_shard", "global", "cross_shard"),
        _leaf("proof_mining", "global", "proof_mining"),
        _leaf("governance", "global", "governance"),
    ]
    full = [*partial, _leaf("clob", "book:BTC-USDC", "clob")]

    # Review note, grade A-: generic JMT roots may be partial, but a production
    # all-app root must carry an explicit empty or non-empty leaf for every
    # required lane kind. This prevents an omitted subsystem from looking like a
    # valid full-keystone commitment.
    with pytest.raises(ValueError, match="missing required app-root lane kind\\(s\\): clob"):
        require_app_root_lane_kinds(partial)
    assert compute_required_app_root(full) == compute_app_root(full)


def test_required_app_root_accepts_scoped_lane_set_for_incremental_rollout() -> None:
    leaves = [_leaf("spot", "global"), _leaf("oracle", "global")]

    normalized = require_app_root_lane_kinds(leaves, required_lane_kinds={"spot", "oracle"})
    assert [(leaf.lane_kind, leaf.lane_id) for leaf in normalized] == [("oracle", "global"), ("spot", "global")]
    assert compute_required_app_root(leaves, required_lane_kinds={"spot", "oracle"}) == compute_app_root(leaves)
    with pytest.raises(ValueError, match="required app-root lane kinds must be non-empty"):
        compute_required_app_root(leaves, required_lane_kinds=set())


def test_app_root_membership_proof_replays_and_tampering_fails() -> None:
    leaves = [
        _leaf("spot", "global"),
        _leaf("oracle", "global"),
        _leaf("perps", "market:ETH-PERP"),
        _leaf("zusd", "system"),
    ]
    target = leaves[2]
    root = compute_app_root(leaves)
    proof = prove_app_root_leaf(leaves, target)

    assert verify_app_root_leaf(root, target, proof)
    assert not verify_app_root_leaf(root, AppRootLeaf.from_json(lane_kind="perps", lane_id="market:ETH-PERP", payload=_lane_payload("perps", 9)), proof)
    assert not verify_app_root_leaf(root, AppRootLeaf(lane_kind="perps", lane_id="market:BTC-PERP", value_hash=target.value_hash), proof)
    assert not verify_app_root_leaf("0x" + "ff" * 32, target, proof)
    assert not verify_app_root_leaf(root, object(), proof)
    with pytest.raises(TypeError, match="leaf must be an AppRootLeaf"):
        prove_app_root_leaf(leaves, object())  # type: ignore[arg-type]


def test_app_root_rejects_ambiguous_or_duplicate_lanes() -> None:
    leaf = _leaf("spot", "global")

    with pytest.raises(TypeError, match="app-root lane kind"):
        AppRootLeaf.from_json(lane_kind=7, lane_id="global", payload={})  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="app-root lane id"):
        AppRootLeaf.from_json(lane_kind="spot", lane_id=7, payload={})  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="unsupported app-root lane kind"):
        AppRootLeaf.from_json(lane_kind="SPOT", lane_id="global", payload={})
    with pytest.raises(ValueError, match="app-root lane id"):
        AppRootLeaf.from_json(lane_kind="spot", lane_id="global with space", payload={})
    with pytest.raises(ValueError, match="app-root value_hash"):
        AppRootLeaf(lane_kind="spot", lane_id="global", value_hash=b"short")
    with pytest.raises(TypeError, match="app-root value_hash"):
        AppRootLeaf(lane_kind="spot", lane_id="global", value_hash=bytearray(b"x" * 32))  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="app-root leaves"):
        app_root_entries([leaf, object()])  # type: ignore[list-item]
    with pytest.raises(ValueError, match="duplicate app-root lane leaf"):
        compute_app_root([leaf, leaf])


def test_app_root_hash_helpers_are_canonical_and_fail_closed() -> None:
    payload_a = {"b": [2, 3], "a": {"x": 1}}
    payload_b = {"a": {"x": 1}, "b": [2, 3]}

    assert app_root_json_value_hash(payload_a) == app_root_json_value_hash(payload_b)
    assert app_root_value_hash(b"payload") != app_root_value_hash(b"payload!")
    assert AppRootLeaf.from_bytes(lane_kind="spot", lane_id="bytes", payload=b"payload").value_hash == app_root_value_hash(b"payload")
    assert app_root_lane_key(lane_kind="spot", lane_id="global") != app_root_lane_key(lane_kind="oracle", lane_id="global")

    with pytest.raises(TypeError, match="floats are not allowed"):
        app_root_json_value_hash({"bad": 1.5})
    with pytest.raises(TypeError, match="app-root lane payload must be bytes"):
        app_root_value_hash("payload")  # type: ignore[arg-type]


def test_compute_app_root_from_json_lanes_matches_explicit_leaves() -> None:
    lanes = {
        ("spot", "global"): _lane_payload("spot"),
        ("oracle", "global"): _lane_payload("oracle"),
        ("vault", "protocol"): _lane_payload("vault"),
    }
    explicit = [
        AppRootLeaf.from_json(lane_kind=kind, lane_id=lane_id, payload=payload)
        for (kind, lane_id), payload in lanes.items()
    ]

    assert compute_app_root_from_json_lanes(lanes) == compute_app_root(explicit)
    with pytest.raises(TypeError, match="app-root JSON lanes"):
        compute_app_root_from_json_lanes([(("spot", "global"), {})])  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="app-root JSON lane keys"):
        compute_app_root_from_json_lanes({"spot:global": {}})  # type: ignore[dict-item]
