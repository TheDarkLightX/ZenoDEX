"""Node wiring for the autonomous-governance live proposer endpoints.

The deployed apply path is `/api/governance/propose-step`: it loads the pinned
policy artifact, runs the production proposer, and only the live admission
guard can advance the store head. These tests pin the flag gating (default
off), the write-auth requirement, the pinned-policy refusal, and the
end-to-end admitted update through a real HTTP round-trip.
"""

from __future__ import annotations

import json
import threading
from http import HTTPStatus
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.integration.autonomous_governance_session_store_file import (
    initialize_autonomous_governance_session_store_file_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from tools.zeno_ledger_node import NODE_STATUS_SCHEMA, make_node_http_server_v0
from tests.integration.test_autonomous_governance_session_store import (
    _genesis_pin,
    _genesis_receipt,
    _policy,
)

AUTH_TOKEN = "test-governance-auth-token-v0"


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _write_node_status(data_dir: Path) -> None:
    body: dict[str, object] = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": "node-governance",
        "node_role": "follower_watcher",
        "network_id": "zeno-ledger-governance-testnet-0",
        "chain_id": "zeno-ledger-governance-testnet-0",
        "bundle_root": str(data_dir / "bundle"),
        "data_dir": str(data_dir),
        "latest_height": 1,
        "last_header_hash": _root("header-1"),
        "last_app_hash": _root("app-1"),
        "operator_attestation_path": "",
        "operator_attestation_hash": _root("attestation"),
        "combined_testnet_status_path": "",
        "combined_testnet_status_hash": _root("testnet-status"),
        "combined_watcher_count": 1,
        "sequencer_set_hash": _root("validator-set"),
        "mirror_index_hash": _root("mirror"),
        "feature_suite_hash": _root("features"),
        "covered_feature_count": 0,
        "covered_features": [],
        "required_features": [],
        "token_symbol": "tZENO",
        "token_posture": {},
        "test_token_catalog": [],
        "testnet_faucet_posture": {},
        "testnet_token_support": {},
    }
    status_body = {key: value for key, value in body.items()}
    status = {**body, "node_status_hash": hash_v0("node_status_v0", status_body)}
    data_dir.mkdir(parents=True, exist_ok=True)
    (data_dir / "node_status.json").write_text(
        json.dumps(status, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def _request_json(
    url: str,
    *,
    token: str | None = None,
    method: str = "GET",
    payload: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], int]:
    headers = {"Authorization": f"Bearer {token}"} if token is not None else {}
    data = None
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    request = Request(url, headers=headers, method=method, data=data)
    try:
        with urlopen(request, timeout=10) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
            status = int(response.status)
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
        status = int(exc.code)
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj, status


def _observation(**overrides: int) -> dict[str, int]:
    base = {
        "observed_price_bps": 10_400,
        "target_price_bps": 10_000,
        "volatility_bps": 100,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
    }
    return {**base, **overrides}


@pytest.fixture()
def governance_node(tmp_path: Path) -> Any:
    """A served node with the governance feature enabled and one live store."""

    data_dir = tmp_path / "node"
    _write_node_status(data_dir)

    policy = _policy()
    store_path = tmp_path / "governance" / "session_store.json"
    genesis = _genesis_receipt(policy)
    init = initialize_autonomous_governance_session_store_file_v1(
        path=store_path,
        genesis_pin=_genesis_pin(policy, genesis),
        genesis_receipt=genesis,
        policy=policy,
    )
    assert init["ok"] is True, init["errors"]
    policy_path = tmp_path / "governance" / "policy.json"
    policy_path.write_text(json.dumps(policy), encoding="utf-8")

    server = make_node_http_server_v0(
        data_dir=data_dir,
        host="127.0.0.1",
        port=0,
        write_auth_token=AUTH_TOKEN,
        autonomous_governance_store=store_path,
        autonomous_governance_policy=policy_path,
        autonomous_governance_expected_policy_hash=str(policy["policy_hash"]),
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address[0], server.server_address[1]
    try:
        yield {
            "url": f"http://{host}:{port}",
            "policy": policy,
            "policy_path": policy_path,
            "store_path": store_path,
        }
    finally:
        server.shutdown()
        server.server_close()


def test_partial_governance_config_refuses_to_start(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    _write_node_status(data_dir)
    with pytest.raises(ValueError, match="autonomous governance requires"):
        make_node_http_server_v0(
            data_dir=data_dir,
            host="127.0.0.1",
            port=0,
            autonomous_governance_store=tmp_path / "store.json",
        )


def test_governance_endpoints_disabled_by_default(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    _write_node_status(data_dir)
    server = make_node_http_server_v0(data_dir=data_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address[0], server.server_address[1]
    url = f"http://{host}:{port}"
    try:
        surface, surface_status = _request_json(f"{url}/api/governance/surface")
        propose, propose_status = _request_json(
            f"{url}/api/governance/propose-step",
            method="POST",
            payload={"observation": _observation(), "current_epoch": 103, "proposal_epoch": 79},
        )
    finally:
        server.shutdown()
        server.server_close()
    assert surface_status == HTTPStatus.FORBIDDEN
    assert surface["error"] == "autonomous_governance_disabled"
    assert propose_status == HTTPStatus.FORBIDDEN
    assert propose["error"] == "autonomous_governance_disabled"


def test_propose_step_requires_write_auth(governance_node: dict[str, Any]) -> None:
    url = governance_node["url"]
    payload = {"observation": _observation(), "current_epoch": 103, "proposal_epoch": 79}
    unauth, unauth_status = _request_json(
        f"{url}/api/governance/propose-step", method="POST", payload=payload
    )
    assert unauth_status == HTTPStatus.UNAUTHORIZED
    bad_token, bad_status = _request_json(
        f"{url}/api/governance/propose-step",
        method="POST",
        payload=payload,
        token="wrong-token",
    )
    assert bad_status == HTTPStatus.UNAUTHORIZED
    assert unauth.get("ok") is not True and bad_token.get("ok") is not True


def test_surface_read_then_admitted_propose_step_round_trip(
    governance_node: dict[str, Any]
) -> None:
    url = governance_node["url"]
    policy = governance_node["policy"]

    surface, surface_status = _request_json(f"{url}/api/governance/surface")
    assert surface_status == HTTPStatus.OK
    assert surface["ok"] is True
    assert surface["surface_state"]["fee_bps"] == 60
    assert surface["policy_hash"] == policy["policy_hash"]
    assert surface["expected_policy_hash"] == policy["policy_hash"]
    assert surface["segment_count"] == 1

    receipt, receipt_status = _request_json(
        f"{url}/api/governance/propose-step",
        method="POST",
        payload={"observation": _observation(), "current_epoch": 103, "proposal_epoch": 79},
        token=AUTH_TOKEN,
    )
    assert receipt_status == HTTPStatus.OK
    assert receipt["ok"] is True and receipt["admitted"] is True
    assert receipt["step_action_id"] == "raise_fee_10"
    assert receipt["applied_state"]["fee_bps"] == 70

    after, after_status = _request_json(f"{url}/api/governance/surface")
    assert after_status == HTTPStatus.OK
    assert after["surface_state"]["fee_bps"] == 70
    assert after["segment_count"] == 2
    assert after["store_hash"] == receipt["store_hash_after"]


def test_propose_step_no_op_and_refusals_leave_surface_unchanged(
    governance_node: dict[str, Any]
) -> None:
    url = governance_node["url"]
    before, _ = _request_json(f"{url}/api/governance/surface")

    stale, stale_status = _request_json(
        f"{url}/api/governance/propose-step",
        method="POST",
        payload={
            "observation": _observation(freshness_lag_epochs=9),
            "current_epoch": 103,
            "proposal_epoch": 79,
        },
        token=AUTH_TOKEN,
    )
    assert stale_status == HTTPStatus.OK
    assert stale["ok"] is True and stale["admitted"] is False and stale["no_op"] is True

    bad_epoch, bad_epoch_status = _request_json(
        f"{url}/api/governance/propose-step",
        method="POST",
        payload={"observation": _observation(), "current_epoch": True, "proposal_epoch": 79},
        token=AUTH_TOKEN,
    )
    assert bad_epoch_status == HTTPStatus.BAD_REQUEST
    assert bad_epoch["ok"] is False

    bad_observation, bad_observation_status = _request_json(
        f"{url}/api/governance/propose-step",
        method="POST",
        payload={"observation": "not-an-object", "current_epoch": 103, "proposal_epoch": 79},
        token=AUTH_TOKEN,
    )
    assert bad_observation_status == HTTPStatus.BAD_REQUEST
    assert bad_observation["error"] == "observation_must_be_object"

    after, _ = _request_json(f"{url}/api/governance/surface")
    assert after["surface_state"] == before["surface_state"]
    assert after["store_hash"] == before["store_hash"]


def test_propose_step_refuses_tampered_policy_file(
    governance_node: dict[str, Any]
) -> None:
    url = governance_node["url"]
    policy = governance_node["policy"]
    policy_path: Path = governance_node["policy_path"]
    before, before_status = _request_json(f"{url}/api/governance/surface")
    assert before_status == HTTPStatus.OK
    policy_path.write_text(json.dumps({**policy, "version": 2}), encoding="utf-8")

    receipt, status = _request_json(
        f"{url}/api/governance/propose-step",
        method="POST",
        payload={"observation": _observation(), "current_epoch": 103, "proposal_epoch": 79},
        token=AUTH_TOKEN,
    )
    assert status == HTTPStatus.BAD_REQUEST
    assert receipt["ok"] is False
    assert receipt["error"] == "autonomous_governance_policy_rejected"
    assert "pinned_policy_content_hash_mismatch" in receipt["policy_load_errors"]

    after, after_status = _request_json(f"{url}/api/governance/surface")
    assert after_status == HTTPStatus.OK
    assert after["surface_state"] == before["surface_state"]
    assert after["store_hash"] == before["store_hash"]
    assert after["surface_state"]["fee_bps"] == 60


def test_governance_enabled_without_write_auth_token_refuses_to_start(
    tmp_path: Path,
) -> None:
    """The unauthenticated-testnet-writes loophole must not reach governance."""

    data_dir = tmp_path / "node"
    _write_node_status(data_dir)
    policy = _policy()
    policy_path = tmp_path / "policy.json"
    policy_path.write_text(json.dumps(policy), encoding="utf-8")
    for token in (None, ""):
        with pytest.raises(ValueError, match="write auth token"):
            make_node_http_server_v0(
                data_dir=data_dir,
                host="127.0.0.1",
                port=0,
                allow_unauthenticated_testnet_writes=True,
                write_auth_token=token,
                autonomous_governance_store=tmp_path / "store.json",
                autonomous_governance_policy=policy_path,
                autonomous_governance_expected_policy_hash=str(policy["policy_hash"]),
            )
