"""HTTP-free autogov live-apply API handler tests (WS5 routing)."""

from __future__ import annotations

import json
from pathlib import Path

from src.integration.autogov_live_apply_api import handle_autogov_request
from tests.integration.test_autonomous_governance_live_apply import _init_file
from tests.integration.test_autonomous_governance_session_store import _continue


def _apply_body(policy: dict, receipt: dict, pin: str) -> bytes:
    return json.dumps(
        {
            "policy": policy,
            "trajectory_receipt": receipt,
            "expected_policy_hash": pin,
        }
    ).encode("utf-8")


def test_fail_closed_without_store_path() -> None:
    status, resp = handle_autogov_request(
        "GET", "/api/autogov/surface", None, store_path="", pinned_policy_hash=""
    )
    assert status == 503
    assert resp["error"] == "autogov_store_path_not_configured"


def test_surface_read(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    _policy, genesis, _init = _init_file(path)
    status, resp = handle_autogov_request(
        "GET", "/api/autogov/surface", None, store_path=str(path), pinned_policy_hash=""
    )
    assert status == 200
    assert resp["surface_state"] == genesis["final_state"]


def test_apply_requires_node_policy_pin(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    policy, genesis, _init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    status, resp = handle_autogov_request(
        "POST",
        "/api/autogov/apply",
        _apply_body(policy, receipt, str(policy["policy_hash"])),
        store_path=str(path),
        pinned_policy_hash="",
    )
    assert status == 503
    assert resp["error"] == "autogov_policy_pin_not_configured"


def test_apply_refuses_non_pinned_policy_hash(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    policy, genesis, _init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    status, resp = handle_autogov_request(
        "POST",
        "/api/autogov/apply",
        _apply_body(policy, receipt, "0x" + "ab" * 32),
        store_path=str(path),
        pinned_policy_hash=str(policy["policy_hash"]),
    )
    assert status == 403
    assert resp["error"] == "autogov_policy_hash_not_node_pinned"


def test_apply_happy_path_advances_head(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    pin = str(policy["policy_hash"])
    status, resp = handle_autogov_request(
        "POST",
        "/api/autogov/apply",
        _apply_body(policy, receipt, pin),
        store_path=str(path),
        pinned_policy_hash=pin,
    )
    assert status == 200, resp
    assert resp["admitted"] is True
    assert resp["applied_state"] == receipt["final_state"]
    assert resp["store_hash_before"] == init["store_hash"]


def test_apply_refusal_returns_409_and_noop(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    policy, genesis, init = _init_file(path)
    receipt = dict(_continue(policy, genesis, 103))
    receipt["final_state"] = {**receipt["final_state"], "fee_bps": 999}
    pin = str(policy["policy_hash"])
    status, resp = handle_autogov_request(
        "POST",
        "/api/autogov/apply",
        _apply_body(policy, receipt, pin),
        store_path=str(path),
        pinned_policy_hash=pin,
    )
    assert status == 409
    assert resp["admitted"] is False
    assert resp["applied_state"] == resp["committed_state"]
    assert resp["store_hash_before"] == init["store_hash"]


def test_malformed_body_rejected(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    _init_file(path)
    status, resp = handle_autogov_request(
        "POST",
        "/api/autogov/apply",
        b"not json",
        store_path=str(path),
        pinned_policy_hash="deadbeef",
    )
    assert status == 400
    assert resp["error"] == "autogov_body_invalid_json"


def test_unknown_route_404(tmp_path: Path) -> None:
    path = tmp_path / "store.json"
    _init_file(path)
    status, _resp = handle_autogov_request(
        "GET", "/api/autogov/unknown", None, store_path=str(path), pinned_policy_hash=""
    )
    assert status == 404
