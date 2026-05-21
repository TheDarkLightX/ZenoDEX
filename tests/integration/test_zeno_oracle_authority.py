from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.zeno_key_manager import KeyRef, ZenoKeyManager
from src.integration.zeno_ledger_signature import infer_artifact_hash_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_oracle_authority import (
    ORACLE_AUTHORITY_PAYLOAD_KIND,
    build_oracle_authority_profile_v1,
    evaluate_oracle_authority_profile_v1,
)


ROOT = Path(__file__).resolve().parents[2]
ORACLE_CLI = ROOT / "tools" / "zenodex_oracle.py"
PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
PUBKEY_C = "0x" + "33" * 48


def _key_manager(*, second_pubkey: str = PUBKEY_B) -> dict[str, object]:
    return ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=PUBKEY_A),
            KeyRef(key_id="oracle-authority-b", public_key=second_pubkey),
        )
    ).public_dict()


def _signer_registry(*, second_pubkey: str = PUBKEY_B, threshold: int = 2) -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="zenooracle-prod-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=threshold,
        signers=(
            {
                "signer_id": "operator-a",
                "key_id": "oracle-authority-a",
                "public_key": PUBKEY_A,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "operator-b",
                "key_id": "oracle-authority-b",
                "public_key": second_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )


def _profile(**overrides: object) -> dict[str, object]:
    base = {
        "authority_id": "zenooracle-mainnet-authority-v1",
        "chain_id": "zeno-ledger-mainnet",
        "stage": "production",
        "enabled": True,
        "key_manager": _key_manager(),
        "signer_registry": _signer_registry(),
        "wallet_ux": {
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
        },
        "proof_profile": {
            "zk_or_proof_required": True,
            "oracle_receipt_replay_required": True,
            "runtime_proof_profile": "zenooracle-o3-replay-zk-profile-v1",
        },
    }
    base.update(overrides)
    return build_oracle_authority_profile_v1(**base)


def test_oracle_authority_missing_profile_is_blocked() -> None:
    status = evaluate_oracle_authority_profile_v1(None)

    assert status["ok"] is False
    assert status["production_authority"] is False
    assert status["status"] == "blocked"
    assert status["readiness_gaps"] == ["oracle production authority profile is missing"]


def test_oracle_authority_complete_profile_is_ready() -> None:
    profile = _profile()
    status = evaluate_oracle_authority_profile_v1(profile)

    assert status["ok"] is True
    assert status["production_authority"] is True
    assert status["status"] == "ready"
    assert status["readiness_gaps"] == []
    assert status["threshold"] == 2
    assert status["active_signer_count"] == 2
    assert status["key_ref_count"] == 2
    assert infer_artifact_hash_v0(
        artifact=profile,
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
    ) == profile["authority_hash"]


def test_oracle_authority_blocks_devnet_and_missing_required_controls() -> None:
    profile = _profile(
        stage="devnet",
        enabled=False,
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": False,
            "device_approval_required": True,
        },
        proof_profile={
            "zk_or_proof_required": False,
            "oracle_receipt_replay_required": True,
            "runtime_proof_profile": "",
        },
    )

    status = evaluate_oracle_authority_profile_v1(profile)
    gaps = set(status["readiness_gaps"])

    assert status["production_authority"] is False
    assert "oracle production authority profile is not enabled" in gaps
    assert "oracle production authority profile stage must be production" in gaps
    assert "wallet_ux.key_manager_required must be true" in gaps
    assert "proof_profile.zk_or_proof_required must be true" in gaps
    assert "proof_profile.runtime_proof_profile must be a non-empty string" in gaps


def test_oracle_authority_blocks_signer_key_manager_public_key_mismatch() -> None:
    profile = _profile(
        key_manager=_key_manager(second_pubkey=PUBKEY_C),
        signer_registry=_signer_registry(second_pubkey=PUBKEY_B),
    )

    status = evaluate_oracle_authority_profile_v1(profile)

    assert status["production_authority"] is False
    assert "active signer key_id oracle-authority-b public key mismatch" in status["readiness_gaps"]


def test_oracle_authority_status_is_secret_free() -> None:
    profile = _profile()
    encoded = json.dumps(evaluate_oracle_authority_profile_v1(profile), sort_keys=True)

    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_oracle_authority_endpoint_reports_missing_profile(tmp_path: Path) -> None:
    from tools.zenodex_oracle import _dashboard_endpoint_payload

    status_code, payload = _dashboard_endpoint_payload(
        tmp_path / "oracle",
        "/api/oracle/authority",
        now_epoch=1,
    )

    assert status_code == 200
    assert payload["production_authority"] is False
    assert payload["status"] == "blocked"
    assert payload["readiness_gaps"] == ["oracle production authority profile is missing"]


def test_oracle_dashboard_snapshot_loads_ready_authority_profile(tmp_path: Path) -> None:
    from tools.zenodex_oracle import _dashboard_endpoint_payload

    home = tmp_path / "oracle"
    authority_dir = home / "authority"
    authority_dir.mkdir(parents=True)
    (authority_dir / "production_authority_profile.json").write_text(
        json.dumps(_profile(), sort_keys=True),
        encoding="utf-8",
    )

    status_code, payload = _dashboard_endpoint_payload(home, "/api/oracle/dashboard", now_epoch=1)

    assert status_code == 200
    assert payload["production_authority"] is True
    assert payload["authority_status"]["status"] == "ready"


def test_oracle_authority_cli_provisions_profile_and_status(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    key_manager_path = tmp_path / "key_manager.json"
    signer_registry_path = tmp_path / "signer_registry.json"
    key_manager_path.write_text(json.dumps(_key_manager(), sort_keys=True), encoding="utf-8")
    signer_registry_path.write_text(json.dumps(_signer_registry(), sort_keys=True), encoding="utf-8")

    provision = subprocess.run(
        [
            sys.executable,
            str(ORACLE_CLI),
            "--json",
            "authority",
            "provision-profile",
            "--home",
            str(home),
            "--authority-id",
            "zenooracle-mainnet-authority-v1",
            "--chain-id",
            "zeno-ledger-mainnet",
            "--key-manager",
            str(key_manager_path),
            "--signer-registry",
            str(signer_registry_path),
            "--runtime-proof-profile",
            "zenooracle-o3-replay-zk-profile-v1",
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    status = subprocess.run(
        [
            sys.executable,
            str(ORACLE_CLI),
            "--json",
            "authority",
            "status",
            "--home",
            str(home),
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )

    provision_payload = json.loads(provision.stdout)
    status_payload = json.loads(status.stdout)
    profile_path = home / "authority" / "production_authority_profile.json"

    assert provision.returncode == 0, provision.stderr
    assert provision_payload["production_authority"] is True
    assert provision_payload["authority_status"]["status"] == "ready"
    assert profile_path.exists()
    assert status.returncode == 0, status.stderr
    assert status_payload["production_authority"] is True
    assert status_payload["profile_path"] == str(profile_path)
