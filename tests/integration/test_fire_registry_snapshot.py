from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.registry.deployment_contract_v1 import check_fire_registry_deployment_receipt
from src.fire.registry.release_v1 import verify_fire_registry_release


REPO_ROOT = Path(__file__).resolve().parents[2]
SNAPSHOT_CLI = REPO_ROOT / "tools" / "build_fire_registry_snapshot.py"
SNAPSHOT_CHECK_CLI = REPO_ROOT / "tools" / "check_fire_registry_snapshot.py"
PINNED_INDEX = REPO_ROOT / "docs" / "fire_registry" / "devnet_v1" / "fire_registry_index.json"
PINNED_METADATA = REPO_ROOT / "docs" / "fire_registry" / "devnet_v1" / "release_metadata.json"
PINNED_DEPLOYMENT_RECEIPT = REPO_ROOT / "docs" / "fire_registry" / "devnet_v1" / "deployment_receipt.json"


def test_build_fire_registry_snapshot_cli_roundtrip(tmp_path: Path) -> None:
    out_dir = tmp_path / "snapshot"
    proc = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_CLI),
            "--output-dir",
            str(out_dir),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-registry-snapshot-build-report/v1"
    assert report["ok"] is True
    assert report["compile_receipt_emitted"] is True
    assert report["kernel_receipt_emitted"] is True
    assert report["kernel_eval_receipt_emitted"] is True
    assert report["kernel_replay_receipt_emitted"] is True
    assert report["kernel_settlement_receipt_emitted"] is True
    assert report["proof_tree_cert_emitted"] is False
    assert report["signature_present"] is True
    assert report["snapshot_name"] == "devnet_v1"
    assert report["contract_count"] == 4
    assert report["instance_gate_summary"] == {
        "entry_count": 3,
        "all_ok": True,
        "param_ok_count": 3,
        "authorization_ok_count": 3,
        "nonce_ok_count": 3,
        "maturity_ok_count": 3,
        "window_ok_count": 3,
    }
    assert report["certificate_instance_gate_summary"] == {
        "entry_count": 3,
        "param_ok": "implemented",
        "authorization_ok": "implemented",
        "nonce_ok": "implemented",
        "maturity_ok": "implemented",
        "window_ok": "implemented",
    }
    assert [row["name"] for row in report["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]

    ok, err, metadata = verify_fire_registry_release(
        out_dir / "release_metadata.json",
        expected_snapshot_name=report["snapshot_name"],
        expected_metadata_file_sha256=report["release_metadata_file_sha256"],
    )
    assert ok is True, err
    assert metadata is not None
    assert metadata.index_hash == report["index_hash"]
    assert metadata.index_file_sha256 == report["index_file_sha256"]
    assert len(metadata.contract_receipts) == 4
    assert metadata.instance_gate_summary.to_dict() == report["instance_gate_summary"]
    assert metadata.certificate_instance_gate_summary.to_dict() == report["certificate_instance_gate_summary"]

    check = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_CHECK_CLI),
            "--metadata-file",
            str(out_dir / "release_metadata.json"),
            "--expected-snapshot-name",
            report["snapshot_name"],
            "--expected-metadata-file-sha256",
            report["release_metadata_file_sha256"],
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check.returncode == 0, check.stderr
    check_payload = json.loads(check.stdout)
    assert check_payload["schema"] == "zenodex/fire-registry-snapshot-check-report/v1"
    assert check_payload["ok"] is True
    assert check_payload["snapshot_name"] == report["snapshot_name"]
    assert check_payload["contract_count"] == 4
    assert check_payload["instance_gate_summary"] == report["instance_gate_summary"]
    assert check_payload["certificate_instance_gate_summary"] == report["certificate_instance_gate_summary"]
    assert [row["name"] for row in check_payload["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]


def test_build_fire_registry_snapshot_cli_can_emit_proof_tree_sidecars(tmp_path: Path) -> None:
    out_dir = tmp_path / "snapshot"
    proc = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_CLI),
            "--output-dir",
            str(out_dir),
            "--emit-proof-tree-cert",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["proof_tree_cert_emitted"] is True
    assert report["compile_receipt_emitted"] is True
    assert report["kernel_receipt_emitted"] is True
    assert report["kernel_eval_receipt_emitted"] is True
    assert report["kernel_replay_receipt_emitted"] is True
    assert report["kernel_settlement_receipt_emitted"] is True
    assert all(bundle["compile_receipt_present"] is True for bundle in report["bundles"].values())
    assert all(bundle["kernel_receipt_present"] is True for bundle in report["bundles"].values())
    assert all(bundle["kernel_eval_receipt_present"] is True for bundle in report["bundles"].values())
    assert all(bundle["kernel_replay_receipt_present"] is True for bundle in report["bundles"].values())
    assert all(bundle["kernel_settlement_receipt_present"] is True for bundle in report["bundles"].values())
    assert all(bundle["proof_tree_cert_present"] is True for bundle in report["bundles"].values())


def test_pinned_fire_registry_snapshot_verifies() -> None:
    ok, err, metadata = verify_fire_registry_release(
        PINNED_METADATA,
        expected_snapshot_name="devnet_v1",
    )
    assert ok is True, err
    assert metadata is not None
    assert metadata.index_path == "fire_registry_index.json"
    assert metadata.require_signature is True
    assert metadata.instance_gate_summary.to_dict() == {
        "entry_count": 3,
        "all_ok": True,
        "param_ok_count": 3,
        "authorization_ok_count": 3,
        "nonce_ok_count": 3,
        "maturity_ok_count": 3,
        "window_ok_count": 3,
    }
    assert metadata.certificate_instance_gate_summary.to_dict() == {
        "entry_count": 3,
        "param_ok": "implemented",
        "authorization_ok": "implemented",
        "nonce_ok": "implemented",
        "maturity_ok": "implemented",
        "window_ok": "implemented",
    }
    assert [row.name for row in metadata.contract_receipts] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]
    assert (PINNED_METADATA.parent / metadata.index_path) == PINNED_INDEX

    deployment_report = check_fire_registry_deployment_receipt(
        PINNED_DEPLOYMENT_RECEIPT,
        require_current=True,
    )
    assert deployment_report["accepted"] is True
    assert deployment_report["violated_checks"] == []
