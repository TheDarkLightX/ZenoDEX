from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_deployment_contract.py"
SNAPSHOT_BUILD_CLI = REPO_ROOT / "tools" / "build_fire_registry_snapshot.py"


def test_fire_registry_deployment_contract_cli_roundtrip(tmp_path: Path) -> None:
    contract_path = tmp_path / "deployment_contract.json"
    signer_pubkey = "0x" + ("12" * 48)
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--output",
            str(contract_path),
            "--snapshot-name",
            "release_v1",
            "--required-signer-pubkey",
            signer_pubkey,
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-registry-deployment-contract-build-report/v1"
    assert report["ok"] is True
    assert report["snapshot_name"] == "release_v1"
    assert report["required_signer_pubkey"] == signer_pubkey

    payload = json.loads(contract_path.read_text(encoding="utf-8"))
    assert payload["snapshot_name"] == "release_v1"
    assert payload["required_signer_pubkey"] == signer_pubkey
    assert payload["contract_id"] == "fire.registry.deploy.release_v1.v1"
    assert report["contract_count"] == 0
    assert payload.get("contracts") is None


def test_fire_registry_deployment_contract_cli_can_pin_release_contracts(tmp_path: Path) -> None:
    snapshot_dir = tmp_path / "snapshot"
    build_snapshot = subprocess.run(
        [
            sys.executable,
            str(SNAPSHOT_BUILD_CLI),
            "--output-dir",
            str(snapshot_dir),
            "--snapshot-name",
            "release_v1",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert build_snapshot.returncode == 0, build_snapshot.stderr
    snapshot_report = json.loads(build_snapshot.stdout)

    contract_path = tmp_path / "deployment_contract.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--output",
            str(contract_path),
            "--snapshot-name",
            "release_v1",
            "--required-signer-pubkey",
            snapshot_report["signer_pubkey"],
            "--release-metadata-file",
            str(snapshot_dir / "release_metadata.json"),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["contract_count"] == 4
    assert [row["name"] for row in report["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]

    payload = json.loads(contract_path.read_text(encoding="utf-8"))
    assert [row["name"] for row in payload["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]


def test_fire_registry_deployment_contract_cli_rejects_missing_signer_pubkey(tmp_path: Path) -> None:
    contract_path = tmp_path / "deployment_contract.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD_CLI),
            "--output",
            str(contract_path),
            "--snapshot-name",
            "release_v1",
            "--required-signer-pubkey",
            "",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
