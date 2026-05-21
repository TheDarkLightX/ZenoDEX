from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.zeno_key_manager import KeyRef, ZenoKeyManager
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
    infer_artifact_hash_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_oracle_authority import (
    ORACLE_AUTHORITY_PAYLOAD_KIND,
    build_oracle_authority_exercise_v1,
    build_oracle_authority_profile_v1,
    evaluate_oracle_authority_exercise_v1,
    evaluate_oracle_authority_profile_v1,
)


ROOT = Path(__file__).resolve().parents[2]
ORACLE_CLI = ROOT / "tools" / "zenodex_oracle.py"
def _privkey_hex(value: int) -> str:
    return "0x" + int(value).to_bytes(32, byteorder="big", signed=False).hex()


PRIVKEY_A = _privkey_hex(101)
PRIVKEY_B = _privkey_hex(102)
PRIVKEY_C = _privkey_hex(103)
PUBKEY_A = bls_public_key_hex_from_private_key_v0(PRIVKEY_A)
PUBKEY_B = bls_public_key_hex_from_private_key_v0(PRIVKEY_B)
PUBKEY_C = bls_public_key_hex_from_private_key_v0(PRIVKEY_C)


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


def _signature_envelopes(profile: dict[str, object]) -> list[dict[str, object]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="operator-a",
            key_id="oracle-authority-a",
            private_key_hex=PRIVKEY_A,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="operator-b",
            key_id="oracle-authority-b",
            private_key_hex=PRIVKEY_B,
        ),
    ]


def _profile(*, signed: bool = True, **overrides: object) -> dict[str, object]:
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
    profile = build_oracle_authority_profile_v1(**base)
    if signed:
        profile["signature_envelopes"] = _signature_envelopes(profile)
    return profile


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
    assert status["signature_count"] == 2
    assert status["signature_quorum"]["accepted_weight"] == 2
    assert status["signature_quorum"]["threshold"] == 2
    assert [entry["key_id"] for entry in status["key_refs"]] == [
        "oracle-authority-a",
        "oracle-authority-b",
    ]
    assert [entry["signer_id"] for entry in status["active_signers"]] == ["operator-a", "operator-b"]
    assert status["wallet_ux"] == {
        "external_signer_required": True,
        "key_manager_required": True,
        "device_approval_required": True,
    }
    assert status["proof_profile"]["oracle_receipt_replay_required"] is True
    assert status["proof_profile"]["runtime_proof_profile"] == "zenooracle-o3-replay-zk-profile-v1"
    assert infer_artifact_hash_v0(
        artifact=profile,
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
    ) == profile["authority_hash"]


def test_oracle_authority_blocks_unsigned_profile() -> None:
    profile = _profile(signed=False)
    status = evaluate_oracle_authority_profile_v1(profile)

    assert status["production_authority"] is False
    assert status["signature_count"] == 0
    assert "oracle production authority signature_envelopes must be a non-empty list" in status["readiness_gaps"]


def test_oracle_authority_blocks_bad_signature_quorum() -> None:
    profile = _profile()
    profile["signature_envelopes"] = list(profile["signature_envelopes"])  # type: ignore[arg-type]
    profile["signature_envelopes"][0] = {  # type: ignore[index]
        **profile["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status = evaluate_oracle_authority_profile_v1(profile)

    assert status["production_authority"] is False
    assert any("signature quorum invalid" in gap for gap in status["readiness_gaps"])


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


def test_oracle_authority_local_exercise_is_ready() -> None:
    profile = _profile()
    exercise = build_oracle_authority_exercise_v1(
        chain_id="zeno-ledger-mainnet",
        authority_id="zenooracle-mainnet-authority-v1",
        target_network="local",
        current_epoch=12,
        operator_service_url="http://127.0.0.1:8787/api/oracle/dashboard",
        query_id="query:oracle-local",
        report_id="report:oracle-local",
        aggregate_id="aggregate:oracle-local",
        read_id="read:oracle-local",
        authorization_id="authorization:oracle-local",
        reward_receipt_id="reward:oracle-local",
    )

    status = evaluate_oracle_authority_exercise_v1(
        profile,
        exercise,
        expected_chain_id="zeno-ledger-mainnet",
    )

    assert status["ok"] is True
    assert status["authority_exercised"] is True
    assert status["public_testnet_evidence_present"] is False
    assert status["public_testnet_exercised"] is False
    assert status["exercise_hash"].startswith("0x")
    assert status["status_hash"].startswith("0x")


def test_oracle_authority_public_testnet_exercise_requires_broadcast_refs() -> None:
    profile = _profile()
    exercise = build_oracle_authority_exercise_v1(
        chain_id="zeno-ledger-mainnet",
        authority_id="zenooracle-mainnet-authority-v1",
        target_network="public_testnet",
        current_epoch=12,
        operator_service_url="http://127.0.0.1:8787/api/oracle/dashboard",
        query_id="query:oracle-public",
        report_id="report:oracle-public",
        aggregate_id="aggregate:oracle-public",
        read_id="read:oracle-public",
        authorization_id="authorization:oracle-public",
        reward_receipt_id="reward:oracle-public",
    )

    status = evaluate_oracle_authority_exercise_v1(
        profile,
        exercise,
        expected_chain_id="zeno-ledger-mainnet",
    )

    assert status["ok"] is False
    assert status["authority_exercised"] is False
    assert "public testnet exercise requires public_broadcast_reference and public_settlement_reference" in status["errors"]


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


def test_oracle_authority_exercise_endpoint_reports_ready_local_exercise(tmp_path: Path) -> None:
    from tools.zenodex_oracle import _write_endpoint_payload

    home = tmp_path / "oracle-exercise"
    authority_dir = home / "authority"
    authority_dir.mkdir(parents=True)
    (authority_dir / "production_authority_profile.json").write_text(
        json.dumps(_profile(), sort_keys=True),
        encoding="utf-8",
    )

    status_code, payload = _write_endpoint_payload(
        home,
        "/api/oracle/authority/exercise/evaluate",
        {
            "target_network": "local",
            "current_epoch": 12,
            "operator_service_url": "http://127.0.0.1:8787/api/oracle/dashboard",
            "query_id": "query:oracle-local",
            "report_id": "report:oracle-local",
            "aggregate_id": "aggregate:oracle-local",
            "read_id": "read:oracle-local",
            "authorization_id": "authorization:oracle-local",
            "reward_receipt_id": "reward:oracle-local",
        },
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["authority_exercise_status"]["authority_exercised"] is True
    assert payload["authority_exercise_status"]["public_testnet_exercised"] is False


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
            "--signer-private-key",
            f"operator-a:oracle-authority-a:{PRIVKEY_A}",
            "--signer-private-key",
            f"operator-b:oracle-authority-b:{PRIVKEY_B}",
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
