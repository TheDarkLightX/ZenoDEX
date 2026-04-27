from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.fire.registry.deployment_contract_v1 import FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA


REPO_ROOT = Path(__file__).resolve().parents[2]
PUBLISH_CLI = REPO_ROOT / "tools" / "publish_fire_registry_snapshot.py"
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_registry_snapshot.py"


def _canonical_contracts() -> list[dict[str, object]]:
    return [
        {
            "name": "burn_contract",
            "roles": [
                "import:burn_index_v1.burn_final",
                "witness:BurnCertificate[TDEX]",
            ],
            "object_refs": ["BurnBoostCall@v1"],
            "use_sites": [
                "BurnBoostCall@v1:import:burn_final",
                "BurnBoostCall@v1:witness:BurnCertificate[TDEX]",
            ],
        },
        {
            "name": "fee_contract",
            "roles": [
                "import:fee_index_v1.fee_final",
                "witness:FeeIndexPacket",
            ],
            "object_refs": ["FeeNote@v1"],
            "use_sites": [
                "FeeNote@v1:import:fee_final",
                "FeeNote@v1:witness:FeeIndexPacket",
            ],
        },
        {
            "name": "hodl_contract",
            "roles": [
                "import:hodl_value_v1.hodl_final",
                "witness:HODLValuePacket",
            ],
            "object_refs": ["LPLossCover@v1"],
            "use_sites": [
                "LPLossCover@v1:import:hodl_final",
                "LPLossCover@v1:witness:HODLValuePacket",
            ],
        },
        {
            "name": "lpv_contract",
            "roles": [
                "import:lp_value_v1.lpv_final",
                "witness:LPValuePacket",
            ],
            "object_refs": ["LPLossCover@v1"],
            "use_sites": [
                "LPLossCover@v1:import:lpv_final",
                "LPLossCover@v1:witness:LPValuePacket",
            ],
        },
    ]


def _write_deployment_contract(path: Path, *, snapshot_name: str, signer_pubkey: str) -> None:
    payload = {
        "schema": FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
        "contract_id": f"fire.registry.deploy.{snapshot_name}.v1",
        "snapshot_name": snapshot_name,
        "required_signer_pubkey": signer_pubkey,
        "require_signature": True,
        "description": "Test FIRE registry deployment contract.",
    }
    path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")


def test_publish_fire_registry_snapshot_cli_roundtrip(tmp_path: Path, monkeypatch) -> None:
    signer_privkey = "74"
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", signer_privkey)
    expected_signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(int(signer_privkey))
    monkeypatch.setenv("FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY", expected_signer_pubkey)
    out_dir = tmp_path / "release_snapshot"

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v1",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-registry-snapshot-publish-report/v1"
    assert report["ok"] is True
    assert report["snapshot_name"] == "release_candidate_v1"
    assert report["compile_receipt_emitted"] is True
    assert report["kernel_receipt_emitted"] is True
    assert report["kernel_eval_receipt_emitted"] is True
    assert report["kernel_replay_receipt_emitted"] is True
    assert report["kernel_settlement_receipt_emitted"] is True
    assert report["proof_tree_cert_emitted"] is False
    assert report["signer_pubkey"] == expected_signer_pubkey
    assert report["expected_signer_pubkey"] == expected_signer_pubkey
    assert report["signer_pubkey_matches_expected"] is True
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

    check = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--metadata-file",
            report["release_metadata_path"],
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
    assert check_payload["ok"] is True
    assert check_payload["signer_pubkey"] == report["signer_pubkey"]
    assert check_payload["instance_gate_summary"] == report["instance_gate_summary"]
    assert check_payload["certificate_instance_gate_summary"] == report["certificate_instance_gate_summary"]


def test_publish_fire_registry_snapshot_cli_can_emit_proof_tree_sidecars(tmp_path: Path, monkeypatch) -> None:
    signer_privkey = "74"
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", signer_privkey)
    expected_signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(int(signer_privkey))
    monkeypatch.setenv("FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY", expected_signer_pubkey)
    out_dir = tmp_path / "release_snapshot"

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_with_proof_tree_v1",
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
    assert report["ok"] is True
    assert report["compile_receipt_emitted"] is True
    assert report["kernel_receipt_emitted"] is True
    assert report["kernel_eval_receipt_emitted"] is True
    assert report["kernel_replay_receipt_emitted"] is True
    assert report["kernel_settlement_receipt_emitted"] is True
    assert report["proof_tree_cert_emitted"] is True


def test_publish_fire_registry_snapshot_cli_rejects_missing_env(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.delenv("FIRE_REGISTRY_SIGNER_PRIVKEY", raising=False)
    out_dir = tmp_path / "release_snapshot"

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v1",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "missing required signer env var" in proc.stderr


def test_publish_fire_registry_snapshot_cli_rejects_demo_signer_by_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", "73")
    out_dir = tmp_path / "release_snapshot"

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v1",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "demo signer key rejected" in proc.stderr


def test_publish_fire_registry_snapshot_cli_rejects_unexpected_signer_pubkey(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", "74")
    monkeypatch.setenv("FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY", "0x" + ("00" * 48))
    out_dir = tmp_path / "release_snapshot"

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v1",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "expected signer pubkey mismatch" in proc.stderr


def test_publish_fire_registry_snapshot_cli_allows_demo_signer_when_explicit(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", "73")
    out_dir = tmp_path / "release_snapshot"

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "dev_release_candidate_v1",
            "--allow-demo-signer",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["demo_signer_allowed"] is True


def test_publish_fire_registry_snapshot_cli_enforces_deployment_contract(tmp_path: Path, monkeypatch) -> None:
    signer_privkey = "74"
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(int(signer_privkey))
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", signer_privkey)
    monkeypatch.setenv("FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY", signer_pubkey)
    out_dir = tmp_path / "release_snapshot"
    contract_path = tmp_path / "deployment_contract.json"
    _write_deployment_contract(contract_path, snapshot_name="release_candidate_v3", signer_pubkey=signer_pubkey)
    payload = json.loads(contract_path.read_text(encoding="utf-8"))
    payload["contracts"] = _canonical_contracts()
    contract_path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v3",
            "--deployment-contract-file",
            str(contract_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["deployment_contract_enforced"] is True
    assert report["deployment_contract_id"] == "fire.registry.deploy.release_candidate_v3.v1"
    assert report["deployment_contract_expected_contract_count"] == 4
    assert [row["name"] for row in report["deployment_contract_expected_contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]
    assert [row["name"] for row in report["contracts"]] == [
        "burn_contract",
        "fee_contract",
        "hodl_contract",
        "lpv_contract",
    ]
    assert report["deployment_receipt_path"] is not None
    assert Path(report["deployment_receipt_path"]).exists()


def test_publish_fire_registry_snapshot_cli_rejects_deployment_contract_mismatch(tmp_path: Path, monkeypatch) -> None:
    signer_privkey = "74"
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(int(signer_privkey))
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", signer_privkey)
    monkeypatch.setenv("FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY", signer_pubkey)
    out_dir = tmp_path / "release_snapshot"
    contract_path = tmp_path / "deployment_contract.json"
    _write_deployment_contract(contract_path, snapshot_name="other_snapshot", signer_pubkey=signer_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v3",
            "--deployment-contract-file",
            str(contract_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "deployment_contract_snapshot_name_mismatch" in proc.stderr


def test_publish_fire_registry_snapshot_cli_rejects_deployment_contract_contract_mismatch(tmp_path: Path, monkeypatch) -> None:
    signer_privkey = "74"
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(int(signer_privkey))
    monkeypatch.setenv("FIRE_REGISTRY_SIGNER_PRIVKEY", signer_privkey)
    monkeypatch.setenv("FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY", signer_pubkey)
    out_dir = tmp_path / "release_snapshot"
    contract_path = tmp_path / "deployment_contract.json"
    _write_deployment_contract(contract_path, snapshot_name="release_candidate_v4", signer_pubkey=signer_pubkey)
    payload = json.loads(contract_path.read_text(encoding="utf-8"))
    payload["contracts"] = [
        {
            "name": "wrong_contract",
            "roles": ["import:burn_index_v1.burn_final"],
            "object_refs": ["BurnBoostCall@v1"],
            "use_sites": ["BurnBoostCall@v1:import:burn_final"],
        }
    ]
    contract_path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(PUBLISH_CLI),
            "--output-dir",
            str(out_dir),
            "--snapshot-name",
            "release_candidate_v4",
            "--deployment-contract-file",
            str(contract_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "release contracts do not match deployment contract" in proc.stderr
