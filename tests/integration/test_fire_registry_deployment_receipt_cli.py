from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.fire.registry.deployment_contract_v1 import FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA


REPO_ROOT = Path(__file__).resolve().parents[2]
SNAPSHOT_BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_snapshot.py"
DEPLOY_BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_deployment_receipt.py"
DEPLOY_CHECK_CLI = REPO_ROOT / "tools" / "check_fire_registry_deployment_receipt.py"


def test_fire_registry_deployment_receipt_cli_roundtrip(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    build_snapshot = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_BUILD_CLI),
            "--output-dir",
            str(snapshot_dir),
            "--snapshot-name",
            "receipt_cli_v1",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build_snapshot.returncode == 0, build_snapshot.stderr
    snapshot_report = json.loads(build_snapshot.stdout)

    contract_path = snapshot_dir / "deployment_contract.json"
    contract_path.write_text(
        json.dumps(
            {
                "schema": FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
                "contract_id": "fire.registry.deploy.receipt_cli_v1.v1",
                "snapshot_name": "receipt_cli_v1",
                "required_signer_pubkey": snapshot_report["signer_pubkey"],
                "require_signature": True,
                "description": "CLI test contract.",
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    receipt_path = snapshot_dir / "deployment_receipt.json"
    build_receipt = subprocess.run(
        [
            sys.executable,
            str(DEPLOY_BUILD_CLI),
            "--contract-file",
            str(contract_path),
            "--release-metadata-file",
            str(snapshot_dir / "release_metadata.json"),
            "--output",
            str(receipt_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build_receipt.returncode == 0, build_receipt.stderr
    build_payload = json.loads(build_receipt.stdout)
    assert build_payload["schema"] == "zenodex/fire-registry-deployment-receipt-build-report/v1"
    assert build_payload["ok"] is True
    assert build_payload["contract_count"] == 4
    assert [row["name"] for row in build_payload["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]

    check_receipt = subprocess.run(
        [
            sys.executable,
            str(DEPLOY_CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
            "--require-current",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_receipt.returncode == 0, check_receipt.stderr
    check_payload = json.loads(check_receipt.stdout)
    assert check_payload["schema"] == "zenodex/fire-registry-deployment-receipt-check-report/v1"
    assert check_payload["ok"] is True
    assert check_payload["contract_count"] == 4
    assert [row["name"] for row in check_payload["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]

    receipt_payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt_payload["contract_path"] == "deployment_contract.json"
    assert receipt_payload["release_metadata_path"] == "release_metadata.json"
    assert [row["name"] for row in receipt_payload["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]


def test_fire_registry_deployment_receipt_cli_rejects_tampered_receipt(tmp_path: Path) -> None:
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(74)
    contract_path = tmp_path / "deployment_contract.json"
    contract_path.write_text(
        json.dumps(
            {
                "schema": FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
                "contract_id": "fire.registry.deploy.tamper.v1",
                "snapshot_name": "tamper_v1",
                "required_signer_pubkey": signer_pubkey,
                "require_signature": True,
                "description": "Tamper test contract.",
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    receipt_path = tmp_path / "deployment_receipt.json"
    receipt_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/fire-registry-deployment-receipt/v1",
                "contract_path": "deployment_contract.json",
                "release_metadata_path": "release_metadata.json",
                "receipt_sha256": "bad",
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    check_receipt = subprocess.run(
        [
            sys.executable,
            str(DEPLOY_CHECK_CLI),
            "--receipt-file",
            str(receipt_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_receipt.returncode == 1
    check_payload = json.loads(check_receipt.stderr)
    assert check_payload["schema"] == "zenodex/fire-registry-deployment-receipt-check-report/v1"
    assert check_payload["ok"] is False
