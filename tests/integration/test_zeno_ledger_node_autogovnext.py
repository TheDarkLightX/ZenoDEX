from __future__ import annotations

import json
import subprocess
import sys
import threading
from http.server import ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.integration.autonomous_governance_q_policy import (
    policy_content_hash_v1,
)
from src.integration.zeno_ledger_feature_suite import build_feature_suite_manifest_v0
from src.integration.zeno_ledger_v0 import canonical_header_hash_v0
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_next_policy_v1,
)
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_TIME_MS, build_testnet_bundle_v0
from tools.zeno_ledger_node import (
    AUTOGOVNEXT_ADMISSION_KIND,
    _autogovnext_governance_state_from_state_file_obj_v1,
    _body_for_tx_v0,
    _build_autogovnext_block_from_body_v1,
    append_autogovnext_admission_v1,
    load_node_status_v0,
    make_node_http_server_v0,
    pull_live_from_peer_v0,
    run_node_once_v0,
)


def _surface_state(**overrides: int) -> dict[str, int]:
    state = {
        "fee_bps": 300,
        "buyburn_bps": 6_000,
        "stakers_bps": 0,
        "reserve_bps": 2_000,
        "hosts_bps": 2_000,
        "mcr_bps": 11_000,
        "ccr_bps": 15_000,
        "staker_bps": 5_000,
        "funding_cap_bps": 150,
    }
    state.update(overrides)
    return state


def _observation(**overrides: int) -> dict[str, int]:
    obs = {
        "observed_price_bps": 10_000,
        "target_price_bps": 10_000,
        "volatility_bps": 25,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
        "oracle_confidence_bps": 9_900,
        "liquidity_concentration_bps": 2_000,
        "recent_governance_churn_bps": 0,
        "proof_market_health_bps": 9_900,
        "validator_stress_bps": 100,
        "network_stress_bps": 100,
    }
    obs.update(overrides)
    return obs


def _autogovnext_request(*, tx_id: str, **observation_overrides: int) -> dict[str, object]:
    policy = sample_autonomous_governance_next_policy_v1()
    return {
        "schema": "zenodex.autonomous_governance.q_surface_policy_eval_bundle.v1",
        "tx_id": tx_id,
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "surface_state": _surface_state(),
        "observation": _observation(**observation_overrides),
        "current_epoch": 50,
        "proposal_epoch": 10,
        "last_update_epoch": 48,
    }


def _load_json(path: Path) -> dict[str, object]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _make_light_public_bundle_v0(
    *,
    out_dir: Path,
    network_id: str,
    chain_id: str,
    sequencer_id: str,
) -> None:
    """Build a real node bundle without the heavyweight release feature suite.

    The node requires a public manifest and a feature-suite manifest. For this
    focused AutoGovNEXT path, one bootstrap replay lane is enough to exercise
    the normal operator rehearsal, header verification, attestation, live append,
    and follower replay code.
    """

    bootstrap_dir = out_dir / "bootstrap"
    bootstrap_report = build_testnet_bundle_v0(
        out_dir=bootstrap_dir,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
        proof_required=False,
    )
    assert bootstrap_report["ok"] is True
    bootstrap_manifest_path = Path(str(bootstrap_report["manifest_path"]))
    bootstrap_manifest = _load_json(bootstrap_manifest_path)
    token_distribution_path = bootstrap_dir / str(bootstrap_manifest["token_distribution_path"])
    token_distribution = _load_json(token_distribution_path)

    feature_suite = build_feature_suite_manifest_v0(
        suite_name=f"{network_id}_autogovnext_minimal",
        lanes=[("bootstrap_replay", bootstrap_manifest_path)],
        required_features=["bootstrap_replay"],
        base_dir=out_dir,
    )
    _write_json(out_dir / "feature_suite.json", feature_suite)

    _write_json(
        out_dir / "public_testnet_manifest.json",
        {
            "schema": "zenodex.zeno_ledger.public_testnet_bundle.v0",
            "network_id": network_id,
            "chain_id": chain_id,
            "sequencer_id": sequencer_id,
            "token_symbol": "tZENO",
            "token_distribution": token_distribution,
            "token_distribution_path": "bootstrap/token_distribution.json",
            "token_distribution_hash": token_distribution["distribution_hash"],
            "bootstrap_manifest_path": "bootstrap/manifest.json",
            "core_suite_path": "feature_suite.json",
            "covered_features": ["bootstrap_replay"],
            "token_posture": {
                "testnet_scope": "autogovnext_node_fixture",
                "production_value": False,
            },
            "tokenomics_posture": {
                "enabled": True,
                "production_security_claim": False,
            },
            "test_token_catalog": [],
            "testnet_faucet_posture": {
                "scope": "testnet_only",
                "production_value": False,
            },
        },
    )


def _make_bundle_and_writer(tmp_path: Path, *, slug: str) -> tuple[Path, Path]:
    bundle_root = tmp_path / f"bundle-{slug}"
    _make_light_public_bundle_v0(
        out_dir=bundle_root,
        network_id=f"zeno-ledger-autogovnext-{slug}",
        chain_id=f"zeno-ledger-autogovnext-{slug}",
        sequencer_id=f"sequencer-autogovnext-{slug}",
    )
    writer_dir = tmp_path / f"writer-{slug}"
    assert run_node_once_v0(bundle_root=bundle_root, node_id=f"writer-{slug}", data_dir=writer_dir)["ok"] is True
    return bundle_root, writer_dir


def _make_bundle_and_nodes(tmp_path: Path, *, slug: str) -> tuple[Path, Path, Path]:
    bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug=slug)
    follower_dir = tmp_path / f"follower-{slug}"
    assert run_node_once_v0(bundle_root=bundle_root, node_id=f"follower-{slug}", data_dir=follower_dir)["ok"] is True
    return bundle_root, writer_dir, follower_dir


def _post_json_status(url: str, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    request = Request(
        url,
        data=json.dumps(payload, sort_keys=True).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
            status = response.status
            body = response.read().decode("utf-8")
    except HTTPError as exc:
        status = exc.code
        body = exc.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return status, obj


def _post_node_tx_status(writer_dir: Path, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        return _post_json_status(f"http://{host}:{port}/tx", payload)
    finally:
        server.shutdown()
        server.server_close()


def test_autogovnext_append_commits_request_and_replays_to_follower(tmp_path: Path) -> None:
    _bundle_root, writer_dir, follower_dir = _make_bundle_and_nodes(tmp_path, slug="valid")
    request = _autogovnext_request(tx_id="autogovnext-node-valid-1")

    append_report = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=request,
        time_ms=DEFAULT_TIME_MS + 2_000_000,
    )

    assert append_report["ok"] is True
    assert append_report["append_kind"] == "autogovnext_admission"
    assert append_report["autogovnext_admission"]["admitted"] is True
    assert append_report["receipt"]["accepted"] is True
    assert append_report["receipt"]["state_changed"] is True
    assert append_report["production_security_claim"] is False

    header = _load_json(Path(str(append_report["header_path"])))
    assert header["pre_state_root"] != header["post_state_root"]
    post_snapshot = _load_json(Path(str(append_report["post_snapshot_path"])))
    governance_state = post_snapshot["governance"]
    assert governance_state["schema"] == "zenodex.zeno_ledger.autogovnext_governance_state.v1"
    assert governance_state["trajectory_reset_policy"] == "no_auto_reset_governance_authority_only_v1"
    assert governance_state["trajectory_window_policy"] == "lifetime_until_governance_authority_reset_v1"
    assert governance_state["surface_state"] == append_report["autogovnext_admission"]["applied_state"]
    assert governance_state["previous_approved_deltas"] == {"fee_bps": -10, "funding_cap_bps": 5}
    assert governance_state["trajectory_used"] == {"fee_bps": 10, "funding_cap_bps": 5}

    server = make_node_http_server_v0(data_dir=writer_dir, host="127.0.0.1", port=0)
    assert isinstance(server, ThreadingHTTPServer)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        pull_report = pull_live_from_peer_v0(data_dir=follower_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()

    assert pull_report["ok"] is True
    assert pull_report["pulled_count"] == 1
    assert pull_report["pulled"][0]["header_hash"] == append_report["header_hash"]
    follower_header = _load_json(follower_dir / "live_ledger" / "headers" / f"{append_report['height']}.json")
    assert canonical_header_hash_v0(follower_header) == append_report["header_hash"]
    follower_body = _load_json(follower_dir / "live_ledger" / "bodies" / f"{append_report['height']}.json")
    assert follower_body["transactions"][0]["kind"] == "ZENODEX_AUTOGOVNEXT_ADMISSION"
    assert follower_body["transactions"][0]["request"]["tx_id"] == "autogovnext-node-valid-1"
    follower_snapshot = _load_json(follower_dir / "live_ledger" / "snapshots" / f"{append_report['height']}.json")
    assert follower_snapshot["governance"] == governance_state


def test_autogovnext_cli_append_commits_real_node_update(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="cli")
    request = _autogovnext_request(tx_id="autogovnext-node-cli-1")
    request_path = tmp_path / "autogovnext-request.json"
    _write_json(request_path, request)

    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_ledger_node.py",
            "append-autogov-next",
            "--data-dir",
            str(writer_dir),
            "--request",
            str(request_path),
            "--time-ms",
            str(DEFAULT_TIME_MS + 2_005_000),
        ],
        cwd=Path(__file__).resolve().parents[2],
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["append_kind"] == "autogovnext_admission"
    assert report["autogovnext_admission"]["admitted"] is True
    assert report["receipt"]["accepted"] is True
    assert report["production_security_claim"] is False
    header = _load_json(Path(str(report["header_path"])))
    assert header["pre_state_root"] != header["post_state_root"]
    post_snapshot = _load_json(Path(str(report["post_snapshot_path"])))
    assert post_snapshot["governance"]["last_tx_id"] == "autogovnext-node-cli-1"
    live_state = _load_json(writer_dir / "live_state.json")
    assert live_state["latest_height"] == report["height"]
    assert live_state["latest_header_hash"] == report["header_hash"]


def test_autogovnext_append_uses_node_owned_governance_state_for_next_update(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="stateful")
    first_request = _autogovnext_request(tx_id="autogovnext-node-stateful-1")
    first = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=first_request,
        time_ms=DEFAULT_TIME_MS + 2_010_000,
    )
    first_governance = _load_json(Path(str(first["post_snapshot_path"])))["governance"]

    stale_request = _autogovnext_request(tx_id="autogovnext-node-stateful-stale")
    before_status = load_node_status_v0(writer_dir)
    with pytest.raises(ValueError, match="autogovnext request not bound to node governance state: surface_state"):
        append_autogovnext_admission_v1(
            data_dir=writer_dir,
            request=stale_request,
            time_ms=DEFAULT_TIME_MS + 2_011_000,
        )
    assert load_node_status_v0(writer_dir)["latest_height"] == before_status["latest_height"]

    second_request = _autogovnext_request(tx_id="autogovnext-node-stateful-2")
    second_request["surface_state"] = first_governance["surface_state"]
    second_request["previous_approved_deltas"] = first_governance["previous_approved_deltas"]
    second_request["trajectory_used"] = first_governance["trajectory_used"]
    second_request["last_update_epoch"] = first_governance["last_update_epoch"]
    second_request["current_epoch"] = int(first_governance["last_update_epoch"]) + 2

    second = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=second_request,
        time_ms=DEFAULT_TIME_MS + 2_012_000,
    )
    second_governance = _load_json(Path(str(second["post_snapshot_path"])))["governance"]

    assert second["autogovnext_admission"]["admitted"] is True
    assert second["receipt"]["state_changed"] is True
    assert second_governance["surface_state"]["fee_bps"] == first_governance["surface_state"]["fee_bps"] - 10
    assert second_governance["trajectory_used"]["fee_bps"] == first_governance["trajectory_used"]["fee_bps"] + 10
    assert second_governance["trajectory_reset_policy"] == "no_auto_reset_governance_authority_only_v1"
    assert second_governance["trajectory_window_policy"] == "lifetime_until_governance_authority_reset_v1"


def test_autogovnext_append_rejects_automatic_trajectory_reset_policy(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="reset-policy")
    first_request = _autogovnext_request(tx_id="autogovnext-node-reset-policy-1")
    first = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=first_request,
        time_ms=DEFAULT_TIME_MS + 2_015_000,
    )
    first_governance = _load_json(Path(str(first["post_snapshot_path"])))["governance"]
    tampered_snapshot_path = Path(str(first["post_snapshot_path"]))
    tampered_snapshot = _load_json(tampered_snapshot_path)
    tampered_snapshot["governance"]["trajectory_reset_policy"] = "automatic_epoch_reset_v1"
    _write_json(tampered_snapshot_path, tampered_snapshot)

    second_request = _autogovnext_request(tx_id="autogovnext-node-reset-policy-2")
    second_request["surface_state"] = first_governance["surface_state"]
    second_request["previous_approved_deltas"] = first_governance["previous_approved_deltas"]
    second_request["trajectory_used"] = first_governance["trajectory_used"]
    second_request["last_update_epoch"] = first_governance["last_update_epoch"]
    second_request["current_epoch"] = int(first_governance["last_update_epoch"]) + 2

    before_status = load_node_status_v0(writer_dir)
    with pytest.raises(ValueError, match="live_state_invalid"):
        append_autogovnext_admission_v1(
            data_dir=writer_dir,
            request=second_request,
            time_ms=DEFAULT_TIME_MS + 2_016_000,
        )
    assert load_node_status_v0(writer_dir)["latest_height"] == before_status["latest_height"]


def test_autogovnext_governance_state_parser_rejects_automatic_trajectory_reset_policy() -> None:
    state_file = {
        "governance": {
            "schema": "zenodex.zeno_ledger.autogovnext_governance_state.v1",
            "version": 1,
            "trajectory_reset_policy": "automatic_epoch_reset_v1",
            "trajectory_window_policy": "lifetime_until_governance_authority_reset_v1",
            "surface_state": _surface_state(),
            "previous_approved_deltas": {"fee_bps": -10},
            "trajectory_used": {"fee_bps": 10},
            "last_update_epoch": 50,
            "accepted_update_count": 1,
        }
    }

    with pytest.raises(ValueError, match="trajectory reset policy mismatch"):
        _autogovnext_governance_state_from_state_file_obj_v1(state_file)


def test_autogovnext_append_duplicate_tx_id_returns_existing_report(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="duplicate")
    request = _autogovnext_request(tx_id="autogovnext-node-duplicate-1")

    first = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=request,
        time_ms=DEFAULT_TIME_MS + 2_025_000,
    )
    second = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=request,
        time_ms=DEFAULT_TIME_MS + 2_026_000,
    )

    assert first["ok"] is True
    assert second["ok"] is True
    assert second["height"] == first["height"]
    assert second["header_hash"] == first["header_hash"]
    assert second["append_report_path"] == first["append_report_path"]
    assert _load_json(writer_dir / "live_state.json")["latest_height"] == first["height"]


def test_autogovnext_pull_rejects_tampered_live_body_without_tip_mutation(tmp_path: Path) -> None:
    _bundle_root, writer_dir, follower_dir = _make_bundle_and_nodes(tmp_path, slug="tampered")
    request = _autogovnext_request(tx_id="autogovnext-node-tampered-1")
    append_report = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=request,
        time_ms=DEFAULT_TIME_MS + 2_050_000,
    )
    height = int(append_report["height"])
    before_status = load_node_status_v0(follower_dir)
    assert not (follower_dir / "live_state.json").exists()

    body_path = Path(str(append_report["body_path"]))
    body = _load_json(body_path)
    body["transactions"][0]["request"]["expected_policy_hash"] = "0x" + "00" * 32
    _write_json(body_path, body)

    server = make_node_http_server_v0(data_dir=writer_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        with pytest.raises(ValueError, match=f"peer header mismatch at height {height}"):
            pull_live_from_peer_v0(data_dir=follower_dir, peer_url=f"http://{host}:{port}")
    finally:
        server.shutdown()
        server.server_close()

    after_status = load_node_status_v0(follower_dir)
    assert after_status["latest_height"] == before_status["latest_height"]
    assert not (follower_dir / "live_state.json").exists()


def test_autogovnext_append_includes_gate_rejected_noop_without_state_mutation(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="rejected")
    request = _autogovnext_request(
        tx_id="autogovnext-node-low-confidence-1",
        oracle_confidence_bps=6_999,
    )

    append_report = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=request,
        time_ms=DEFAULT_TIME_MS + 2_100_000,
    )

    assert append_report["ok"] is True
    assert append_report["autogovnext_admission"]["admitted"] is False
    assert append_report["autogovnext_admission"]["reason"] == "receipt_rejected_noop"
    assert append_report["receipt"]["accepted"] is False
    assert append_report["receipt"]["error_code"] == "receipt_rejected_noop"
    assert append_report["receipt"]["state_changed"] is False
    header = _load_json(Path(str(append_report["header_path"])))
    assert header["pre_state_root"] == header["post_state_root"]


def test_autogovnext_append_commits_authority_parameter_attempt_as_noop(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="authority-noop")
    request = _autogovnext_request(tx_id="autogovnext-node-authority-noop-1")
    policy = json.loads(json.dumps(request["policy"]))
    policy["actions"].append(
        {
            "id": "rotate_verifier_keys",
            "deltas": {
                "verifier_image_id": 1,
                "signer_set_hash": 1,
            },
        }
    )
    policy["policy_hash"] = policy_content_hash_v1(policy)
    request["policy"] = policy
    request["expected_policy_hash"] = policy["policy_hash"]

    append_report = append_autogovnext_admission_v1(
        data_dir=writer_dir,
        request=request,
        time_ms=DEFAULT_TIME_MS + 2_150_000,
    )

    assert append_report["ok"] is True
    assert append_report["autogovnext_admission"]["admitted"] is False
    assert append_report["autogovnext_admission"]["reason"] == "receipt_rejected_noop"
    assert "authority_action_delta_forbidden:verifier_image_id" in append_report["autogovnext_admission"]["receipt"]["errors"]
    assert "authority_action_delta_forbidden:signer_set_hash" in append_report["autogovnext_admission"]["receipt"]["errors"]
    assert append_report["receipt"]["accepted"] is False
    assert append_report["receipt"]["state_changed"] is False
    header = _load_json(Path(str(append_report["header_path"])))
    assert header["pre_state_root"] == header["post_state_root"]


def test_autogovnext_append_rejects_direct_result_field_without_tip_mutation(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="bypass")
    before_status = load_node_status_v0(writer_dir)
    request = _autogovnext_request(tx_id="autogovnext-node-bypass-1")
    request["proposed_state"] = {**_surface_state(), "fee_bps": 1_000}

    with pytest.raises(ValueError, match="autogovnext admission request invalid"):
        append_autogovnext_admission_v1(
            data_dir=writer_dir,
            request=request,
            time_ms=DEFAULT_TIME_MS + 2_200_000,
        )

    after_status = load_node_status_v0(writer_dir)
    assert after_status["latest_height"] == before_status["latest_height"]
    assert not (writer_dir / "live_state.json").exists()


def test_autogovnext_http_endpoint_accepts_valid_request(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http")
    request = _autogovnext_request(tx_id="autogovnext-node-http-1")
    request["time_ms"] = DEFAULT_TIME_MS + 2_300_000

    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, report = _post_json_status(f"http://{host}:{port}/api/governance/autogov-next", request)
    finally:
        server.shutdown()
        server.server_close()

    assert status == 200
    assert report["ok"] is True
    assert report["autogovnext_admitted"] is True
    assert report["autogovnext_admission"]["admitted"] is True


def test_autogovnext_tx_endpoint_routes_through_governance_admission(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http-tx")
    request = _autogovnext_request(tx_id="autogovnext-node-http-tx-1")

    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, report = _post_json_status(
            f"http://{host}:{port}/tx",
            {
                "time_ms": DEFAULT_TIME_MS + 2_320_000,
                "tx": {
                    "tx_id": request["tx_id"],
                    "kind": AUTOGOVNEXT_ADMISSION_KIND,
                    "request": request,
                },
            },
        )
    finally:
        server.shutdown()
        server.server_close()

    assert status == 200
    assert report["ok"] is True
    assert report["append_kind"] == "autogovnext_admission"
    assert report["autogovnext_admitted"] is True
    assert report["autogovnext_admission"]["admitted"] is True


def test_autogovnext_tx_endpoint_rejects_mismatched_tx_id_without_tip_mutation(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http-tx-mismatch")
    before_status = load_node_status_v0(writer_dir)
    request = _autogovnext_request(tx_id="autogovnext-node-http-tx-mismatch-1")

    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, report = _post_json_status(
            f"http://{host}:{port}/tx",
            {
                "time_ms": DEFAULT_TIME_MS + 2_330_000,
                "tx": {
                    "tx_id": "autogovnext-node-http-tx-mismatch-other",
                    "kind": AUTOGOVNEXT_ADMISSION_KIND,
                    "request": request,
                },
            },
        )
    finally:
        server.shutdown()
        server.server_close()

    after_status = load_node_status_v0(writer_dir)
    assert status == 400
    assert report["ok"] is False
    assert report["error"] == "autogovnext tx_id/request tx_id mismatch"
    assert after_status["latest_height"] == before_status["latest_height"]
    assert not (writer_dir / "live_state.json").exists()


def test_autogovnext_tx_endpoint_rejects_missing_outer_tx_id_without_tip_mutation(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http-tx-missing-id")
    before_status = load_node_status_v0(writer_dir)
    request = _autogovnext_request(tx_id="autogovnext-node-http-tx-missing-id-1")

    status, report = _post_node_tx_status(
        writer_dir,
        {
            "time_ms": DEFAULT_TIME_MS + 2_340_000,
            "tx": {
                "kind": AUTOGOVNEXT_ADMISSION_KIND,
                "request": request,
            },
        },
    )

    after_status = load_node_status_v0(writer_dir)
    assert status == 400
    assert report["ok"] is False
    assert report["error"] == "autogovnext tx_id invalid"
    assert after_status["latest_height"] == before_status["latest_height"]
    assert not (writer_dir / "live_state.json").exists()


def test_autogovnext_tx_endpoint_rejects_non_string_outer_tx_id_without_tip_mutation(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http-tx-int-id")
    before_status = load_node_status_v0(writer_dir)
    request = _autogovnext_request(tx_id="123")

    status, report = _post_node_tx_status(
        writer_dir,
        {
            "time_ms": DEFAULT_TIME_MS + 2_345_000,
            "tx": {
                "tx_id": 123,
                "kind": AUTOGOVNEXT_ADMISSION_KIND,
                "request": request,
            },
        },
    )

    after_status = load_node_status_v0(writer_dir)
    assert status == 400
    assert report["ok"] is False
    assert report["error"] == "autogovnext tx_id invalid"
    assert after_status["latest_height"] == before_status["latest_height"]
    assert not (writer_dir / "live_state.json").exists()


@pytest.mark.parametrize(
    ("tx_overrides", "expected_error"),
    [
        ({"tx_id": 123}, "autogovnext tx_id invalid"),
        ({"debug_receipt": {}}, "autogovnext tx keys mismatch"),
    ],
)
def test_autogovnext_block_replay_rejects_malformed_tx_envelope_before_writing(
    tmp_path: Path,
    tx_overrides: dict[str, object],
    expected_error: str,
) -> None:
    bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="replay-envelope")
    node_status = load_node_status_v0(writer_dir)
    bootstrap_manifest = _load_json(bundle_root / "bootstrap" / "manifest.json")
    latest_height = int(node_status["latest_height"])
    request = _autogovnext_request(tx_id="123")
    tx = {
        "tx_id": request["tx_id"],
        "kind": AUTOGOVNEXT_ADMISSION_KIND,
        "request": request,
        **tx_overrides,
    }
    body = _body_for_tx_v0(
        chain_id=str(node_status["chain_id"]),
        height=latest_height + 1,
        time_ms=DEFAULT_TIME_MS + 2_347_000,
        sequencer_id=str(bootstrap_manifest["sequencer_id"]),
        tx=tx,
    )

    with pytest.raises(ValueError, match=expected_error):
        _build_autogovnext_block_from_body_v1(
            data_dir=writer_dir,
            body=body,
            time_ms=DEFAULT_TIME_MS + 2_347_000,
            prev_header_path=bundle_root / "bootstrap" / "ledger" / "headers" / f"{latest_height}.json",
            pre_snapshot_path=bundle_root / "bootstrap" / "ledger" / "snapshots" / f"{latest_height}.json",
            sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
            config_digest=str(bootstrap_manifest["config_digest"]),
            module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        )

    assert not (writer_dir / "live_ledger" / "headers" / f"{latest_height + 1}.json").exists()
    assert not (writer_dir / "live_ledger" / "bodies" / f"{latest_height + 1}.json").exists()


def test_autogovnext_http_endpoint_requires_write_auth(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http-auth")
    request = _autogovnext_request(tx_id="autogovnext-node-http-auth-1")
    request["time_ms"] = DEFAULT_TIME_MS + 2_350_000

    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=False,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, report = _post_json_status(f"http://{host}:{port}/api/governance/autogov-next", request)
    finally:
        server.shutdown()
        server.server_close()

    assert status == 401
    assert report["ok"] is False
    assert report["error"] == "write_auth_required"


def test_autogovnext_http_endpoint_commits_policy_rejection_receipt(tmp_path: Path) -> None:
    _bundle_root, writer_dir = _make_bundle_and_writer(tmp_path, slug="http-rejected")
    request = _autogovnext_request(
        tx_id="autogovnext-node-http-rejected-1",
        oracle_confidence_bps=6_999,
    )
    request["time_ms"] = DEFAULT_TIME_MS + 2_400_000

    server = make_node_http_server_v0(
        data_dir=writer_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        status, report = _post_json_status(f"http://{host}:{port}/api/governance/autogov-next", request)
    finally:
        server.shutdown()
        server.server_close()

    assert status == 200
    assert report["ok"] is True
    assert report["autogovnext_admitted"] is False
    assert report["autogovnext_admission"]["reason"] == "receipt_rejected_noop"
    assert report["receipt"]["accepted"] is False
    assert report["receipt"]["state_changed"] is False
