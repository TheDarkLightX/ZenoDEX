"""Node-anchored committed-surface registry and apply-path tests (WS5)."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from src.integration.autonomous_governance_live_registry import (
    ANCHOR_SOURCE_V1,
    apply_autonomous_governance_update_from_node_state_v1,
    committed_governance_surface_v1,
)
from src.integration.autonomous_governance_session_store_file import (
    current_session_store_file_head_v1,
)
from tests.integration.test_autonomous_governance_live_apply import _init_file
from tests.integration.test_autonomous_governance_session_store import _continue


def test_committed_surface_reads_store_head(tmp_path: Path) -> None:
    path = tmp_path / "autogov-store.json"
    policy, genesis, init = _init_file(path)
    surface = committed_governance_surface_v1(store_path=path)
    assert surface["ok"] is True, surface["errors"]
    assert surface["anchor_source"] == ANCHOR_SOURCE_V1
    assert surface["surface_state"] == genesis["final_state"]
    assert surface["store_hash"] == init["store_hash"]
    assert surface["committed_surface_hash"]


def test_committed_surface_fail_closed_without_store(tmp_path: Path) -> None:
    surface = committed_governance_surface_v1(store_path=tmp_path / "missing.json")
    assert surface["ok"] is False
    assert surface["surface_state"] == {}


def test_node_apply_admits_verified_continuation(tmp_path: Path) -> None:
    path = tmp_path / "autogov-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)

    result = apply_autonomous_governance_update_from_node_state_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert result["admitted"] is True, result["errors"]
    assert result["anchor_source"] == ANCHOR_SOURCE_V1
    assert result["applied_state"] == receipt["final_state"]
    assert result["store_hash_before"] == init["store_hash"]
    assert result["store_hash_after"] != init["store_hash"]

    head = current_session_store_file_head_v1(path=path)
    assert head["surface_state"] == receipt["final_state"]


def test_node_apply_ignores_caller_anchor_entirely(tmp_path: Path) -> None:
    """The node derives the committed state itself; there is no parameter a
    caller could use to substitute `curr` — the signature does not accept one.
    A receipt built against a DIFFERENT anchor than the node's head refuses."""
    path = tmp_path / "autogov-store.json"
    policy, genesis, _init = _init_file(path)
    receipt = _continue(policy, genesis, 103)

    # Advance the node's store once so its head moves past genesis.
    first = apply_autonomous_governance_update_from_node_state_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert first["admitted"] is True, first["errors"]

    # Replaying the same receipt now anchors against a stale state: refused,
    # and the store does not move.
    head_before = current_session_store_file_head_v1(path=path)
    replay = apply_autonomous_governance_update_from_node_state_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert replay["admitted"] is False
    head_after = current_session_store_file_head_v1(path=path)
    assert head_after["store_hash"] == head_before["store_hash"]


def test_node_apply_refuses_forged_receipt_total_noop(tmp_path: Path) -> None:
    path = tmp_path / "autogov-store.json"
    policy, genesis, init = _init_file(path)
    receipt: dict[str, Any] = dict(_continue(policy, genesis, 103))
    receipt["final_state"] = {**receipt["final_state"], "fee_bps": 999}

    result = apply_autonomous_governance_update_from_node_state_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert result["admitted"] is False
    assert result["applied_state"] == result["committed_state"]
    assert current_session_store_file_head_v1(path=path)["store_hash"] == init["store_hash"]


def test_node_apply_requires_policy_pin(tmp_path: Path) -> None:
    path = tmp_path / "autogov-store.json"
    policy, genesis, _init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    result = apply_autonomous_governance_update_from_node_state_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        expected_policy_hash=None,
    )
    assert result["admitted"] is False
    assert "node_apply_expected_policy_hash_required" in result["errors"]
