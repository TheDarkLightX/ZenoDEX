from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.integration.zeno_ledger_v0 import canonical_header_hash_v0, hash_v0
from tools.build_zeno_ledger_node_evidence_input import build_node_evidence_input_v0, main
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_ASSET0,
    DEFAULT_BOOTSTRAP_SENDER,
    DEFAULT_ASSET1,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
    build_testnet_bundle_v0,
)
from tools.zeno_ledger_node import (
    NODE_STATUS_SCHEMA,
    _node_status_hash,
    _public_network_config_hash_v0,
    append_testnet_faucet_v0,
)
from tools.zeno_ledger_run_manifest import run_manifest_v0

COMMIT = "a" * 40


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@pytest.fixture(scope="module")
def node_evidence_fixture(tmp_path_factory: pytest.TempPathFactory) -> tuple[Path, Path, dict[str, object]]:
    root = tmp_path_factory.mktemp("zeno-ledger-node-evidence")
    bundle_root = root / "bundle"
    bootstrap_root = bundle_root / "bootstrap"
    build_report = build_testnet_bundle_v0(
        out_dir=bootstrap_root,
        chain_id="zeno-ledger-node-evidence-testnet-0",
        sequencer_id=DEFAULT_SEQUENCER_ID,
        time_ms=DEFAULT_TIME_MS,
        token_symbol="tZENO",
        proof_required=False,
    )
    assert build_report["ok"] is True
    run_report = run_manifest_v0(manifest_path=Path(str(build_report["manifest_path"])), cwd=Path.cwd())
    assert run_report["ok"] is True
    bootstrap_manifest = json.loads((bootstrap_root / "manifest.json").read_text(encoding="utf-8"))
    public_manifest = {
        "schema": "zenodex.zeno_ledger.public_testnet_bundle.v0",
        "network_id": "zeno-ledger-node-evidence-testnet-0",
        "chain_id": "zeno-ledger-node-evidence-testnet-0",
        "sequencer_id": DEFAULT_SEQUENCER_ID,
        "token_symbol": "tZENO",
        "bootstrap_manifest_path": "bootstrap/manifest.json",
        "token_posture": {
            "testnet_scope": "zeno_ledger_testnet",
            "release_scope": "tau_net_exclusive",
            "external_minting_allowed": False,
        },
        "test_token_catalog": [
            {"symbol": "tZENO", "asset_id": bootstrap_manifest["token_asset_id"]},
            {"symbol": "tASSET0", "asset_id": DEFAULT_ASSET0},
            {"symbol": "tASSET1", "asset_id": DEFAULT_ASSET1},
        ],
        "testnet_faucet_posture": {
            "scope": "testnet_only",
            "operation_key": "7",
            "supports_fixture_mint": True,
            "supports_token_ops": True,
        },
    }
    _write_json(bundle_root / "public_testnet_manifest.json", public_manifest)
    feature_suite_hash = hash_v0("test_feature_suite", {"fixture": "node_evidence"})
    network_config_body = {
        "schema": "zenodex.zeno_ledger.public_network_config.v0",
        "ok": True,
        "status": "accepted",
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "token_symbol": "tZENO",
        "mirror_base_url": "http://127.0.0.1:8000/",
        "writer_urls": ["http://127.0.0.1:8787"],
        "peer_urls": ["http://127.0.0.1:8787"],
        "feature_suite_hash": feature_suite_hash,
        "feature_count": 1,
        "test_token_catalog": public_manifest["test_token_catalog"],
        "testnet_faucet_posture": public_manifest["testnet_faucet_posture"],
        "recommended_node": {
            "host": "0.0.0.0",
            "port": 8788,
            "poll_seconds": 5,
            "enable_testnet_intake": True,
            "enable_testnet_faucet": True,
            "submit_peer_url": "http://127.0.0.1:8787",
        },
    }
    network_config = {
        **network_config_body,
        "network_config_hash": _public_network_config_hash_v0(network_config_body),
    }
    network_config_path = bundle_root / "public_network_config.json"
    _write_json(network_config_path, network_config)

    node_dir = root / "node-a"
    node_dir.mkdir()
    header_5 = json.loads((bootstrap_root / "ledger" / "headers" / "5.json").read_text(encoding="utf-8"))
    status_body = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": "machine-a",
        "node_role": "follower_watcher",
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "bundle_root": str(bundle_root),
        "data_dir": str(node_dir),
        "latest_height": 5,
        "last_header_hash": canonical_header_hash_v0(header_5),
        "last_app_hash": header_5["app_hash"],
        "feature_suite_hash": feature_suite_hash,
    }
    _write_json(node_dir / "node_status.json", {**status_body, "node_status_hash": _node_status_hash(status_body)})
    faucet_report = append_testnet_faucet_v0(
        data_dir=node_dir,
        to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset=DEFAULT_ASSET0,
        amount=1234,
        time_ms=1_778_731_123_000,
        tx_id="node-evidence-faucet-v0",
    )
    assert faucet_report["ok"] is True
    return node_dir, network_config_path, faucet_report


def test_build_node_evidence_input_binds_live_tip(
    tmp_path: Path,
    node_evidence_fixture: tuple[Path, Path, dict[str, object]],
) -> None:
    node_dir, network_config_path, faucet_report = node_evidence_fixture
    machine_out = tmp_path / "machine-a.json"
    attestation_out = tmp_path / "machine-a-watcher.json"

    report = build_node_evidence_input_v0(
        data_dir=node_dir,
        network_config_path=network_config_path,
        machine_out=machine_out,
        attestation_out=attestation_out,
        commit_sha=COMMIT,
        observed_time_ms=1_778_731_124_000,
    )
    machine = json.loads(machine_out.read_text(encoding="utf-8"))
    attestation = json.loads(attestation_out.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["height"] == 6
    assert report["header_hash"] == faucet_report["header_hash"]
    assert report["checked_heights"] == [1, 2, 3, 4, 5, 6]
    assert machine["schema"] == "zenodex.zeno_ledger.node_evidence_input.v0"
    assert machine["machine_id"] == "machine-a"
    assert machine["commit_sha"] == COMMIT
    assert machine["header_hash"] == faucet_report["header_hash"]
    assert attestation["watcher_id"] == "machine-a"
    assert attestation["last_header_hash"] == faucet_report["header_hash"]
    assert attestation["checked_heights"] == [1, 2, 3, 4, 5, 6]


def test_build_node_evidence_input_rejects_tampered_network_config(
    tmp_path: Path,
    node_evidence_fixture: tuple[Path, Path, dict[str, object]],
) -> None:
    node_dir, network_config_path, _ = node_evidence_fixture
    config = json.loads(network_config_path.read_text(encoding="utf-8"))
    config["network_id"] = "tampered-network"
    tampered_config_path = tmp_path / "tampered-public-network-config.json"
    _write_json(tampered_config_path, config)

    report = build_node_evidence_input_v0(
        data_dir=node_dir,
        network_config_path=tampered_config_path,
        machine_out=tmp_path / "machine-a.json",
        attestation_out=tmp_path / "machine-a-watcher.json",
        commit_sha=COMMIT,
        observed_time_ms=1_778_731_124_000,
    )

    assert report["ok"] is False
    assert "public network config hash mismatch" in report["errors"]


def test_build_node_evidence_input_cli(
    tmp_path: Path,
    capsys,
    node_evidence_fixture: tuple[Path, Path, dict[str, object]],
) -> None:
    node_dir, network_config_path, _ = node_evidence_fixture
    code = main(
        [
            "--data-dir",
            str(node_dir),
            "--network-config",
            str(network_config_path),
            "--machine-out",
            str(tmp_path / "machine-a.json"),
            "--attestation-out",
            str(tmp_path / "machine-a-watcher.json"),
            "--commit-sha",
            COMMIT,
            "--observed-time-ms",
            "1778731124000",
        ]
    )
    report = json.loads(capsys.readouterr().out)

    assert code == 0
    assert report["schema"] == "zenodex.zeno_ledger.node_evidence_input_report.v0"
    assert report["status"] == "accepted"
