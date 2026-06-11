from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration.production_promotion_evidence import (
    attach_production_hardware_wallet_hash_v1,
    evaluate_production_hardware_wallet_evidence_v1,
    production_hardware_wallet_approval_message_v1,
    production_hardware_wallet_attestation_challenge_v1,
    production_hardware_wallet_attestation_message_v1,
)
from tools import build_hardware_wallet_evidence as builder

NOW = 1747878000
DEVICE_PRIVATE_KEY = Ed25519PrivateKey.from_private_bytes(bytes([7]) * 32)
DEVICE_PUBKEY = DEVICE_PRIVATE_KEY.public_key().public_bytes(
    encoding=serialization.Encoding.Raw,
    format=serialization.PublicFormat.Raw,
).hex()


def _sign_attestation(challenge: str) -> str:
    return DEVICE_PRIVATE_KEY.sign(production_hardware_wallet_attestation_message_v1(challenge)).hex()


def _sign_approval(tx_payload_hash: str) -> str:
    return DEVICE_PRIVATE_KEY.sign(production_hardware_wallet_approval_message_v1(tx_payload_hash)).hex()


def _expected_challenge(
    *,
    prompt_captured_at: int = NOW - 120,
    approval_captured_at: int = NOW - 60,
    prompt_hash: str = "ff" * 32,
    tx_payload_hash: str = "10" * 32,
) -> str:
    return production_hardware_wallet_attestation_challenge_v1(
        {
            "schema": "zenodex/production-hardware-wallet-evidence/v1",
            "device_id": "ledger-x-prod-01",
            "device_model": "ledger-nano-x",
            "device_firmware_version": "2.4.0",
            "device_attestation": {
                "pubkey": DEVICE_PUBKEY,
                "challenge": "00" * 32,
                "signature": "ee" * 64,
            },
            "os_prompt_capture": {
                "kind": "screenshot_hash",
                "hash": prompt_hash,
                "captured_at": prompt_captured_at,
            },
            "device_approval_tx": {
                "tx_payload_hash": tx_payload_hash,
                "approval_signature": "20" * 64,
                "captured_at": approval_captured_at,
            },
            "profile_wallet_authority_hash": "wallet-auth-hash",
            "issued_at": NOW,
        }
    )


def _base_args(
    out: Path,
    *,
    prompt_captured_at: int = NOW - 120,
    approval_captured_at: int = NOW - 60,
    prompt_hash: str = "ff" * 32,
    tx_payload_hash: str = "10" * 32,
) -> list[str]:
    challenge = _expected_challenge(
        prompt_captured_at=prompt_captured_at,
        approval_captured_at=approval_captured_at,
        prompt_hash=prompt_hash,
        tx_payload_hash=tx_payload_hash,
    )
    return [
        "--out",
        str(out),
        "--device-id",
        "ledger-x-prod-01",
        "--device-model",
        "ledger-nano-x",
        "--device-firmware-version",
        "2.4.0",
        "--device-pubkey",
        DEVICE_PUBKEY,
        "--attestation-challenge",
        challenge,
        "--attestation-signature",
        _sign_attestation(challenge),
        "--prompt-kind",
        "screenshot_hash",
        "--prompt-hash",
        prompt_hash,
        "--prompt-captured-at",
        str(prompt_captured_at),
        "--approval-tx-payload-hash",
        tx_payload_hash,
        "--approval-signature",
        _sign_approval(tx_payload_hash),
        "--approval-captured-at",
        str(approval_captured_at),
        "--wallet-authority-profile-hash",
        "wallet-auth-hash",
        "--expected-device-pubkey",
        DEVICE_PUBKEY,
        "--issued-at",
        str(NOW),
        "--check-now",
        str(NOW),
    ]


def test_hardware_builder_writes_lane_ready_evidence(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"

    assert builder.main([*_base_args(out), "--check"]) == 0

    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    lane = evaluate_production_hardware_wallet_evidence_v1(
        evidence,
        wallet_authority_profile_hash="wallet-auth-hash",
        expected_device_pubkey=DEVICE_PUBKEY,
        now=NOW,
    )
    assert lane["production_ready"] is True
    assert lane["gaps"] == []
    assert evidence["device_attestation"]["pubkey"] == DEVICE_PUBKEY
    assert len(evidence["evidence_hash"]) == 64


def test_hardware_builder_rejects_unsupported_model_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--device-model") + 1] = "browser-extension-hot-wallet"

    assert builder.main(args) == 2

    err = json.loads(capsys.readouterr().out)
    assert err["error"] == "hardware_wallet_evidence_build_failed"
    assert "device model" in err["detail"]
    assert "not allowed" in err["detail"]
    assert not out.exists()


def test_hardware_builder_rejects_malformed_pubkey(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--device-pubkey") + 1] = "not-hex"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "device pubkey" in payload["detail"]
    assert not out.exists()


def test_hardware_builder_rejects_expected_device_pubkey_mismatch(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--expected-device-pubkey") + 1] = "ab" * 32

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "does not match expected device pubkey" in payload["detail"]
    assert not out.exists()


def test_hardware_builder_rejects_challenge_for_different_payload(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out, tx_payload_hash="11" * 32)
    args[args.index("--attestation-challenge") + 1] = _expected_challenge(tx_payload_hash="10" * 32)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "canonical hardware approval challenge" in payload["detail"]
    assert not out.exists()


def test_hardware_builder_rejects_capture_window_before_writing(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--approval-captured-at") + 1] = str(NOW + 4_000)

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "within the same hour" in payload["detail"]
    assert not out.exists()


def test_hardware_builder_rejects_reused_attestation_and_approval_signature(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--approval-signature") + 1] = args[args.index("--attestation-signature") + 1]

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "signature must differ" in payload["detail"]
    assert not out.exists()


def test_hardware_builder_rejects_invalid_attestation_signature_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--attestation-signature") + 1] = "ee" * 64

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "attestation signature is invalid" in payload["detail"]
    assert not out.exists()


def test_hardware_builder_check_rejects_stale_issued_at(capsys, tmp_path: Path) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--issued-at") + 1] = str(NOW - 31 * 24 * 3600)

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("freshness" in gap for gap in err["gaps"])
    assert not out.exists()


def test_hardware_evaluator_rejects_rehashed_stale_device_approval(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "hardware_wallet.json"
    stale_prompt = NOW - 7 * 24 * 3600
    args = _base_args(
        out,
        prompt_captured_at=stale_prompt,
        approval_captured_at=stale_prompt + 60,
    )

    assert builder.main(args) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))

    lane = evaluate_production_hardware_wallet_evidence_v1(
        evidence,
        wallet_authority_profile_hash="wallet-auth-hash",
        expected_device_pubkey=DEVICE_PUBKEY,
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "device_approval_tx.captured_at is too old for evidence issued_at" in lane["gaps"]


def test_hardware_evaluator_rejects_rehashed_payload_without_new_challenge(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "hardware_wallet.json"

    assert builder.main(_base_args(out)) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    evidence["device_approval_tx"]["tx_payload_hash"] = "11" * 32
    evidence = attach_production_hardware_wallet_hash_v1(evidence)

    lane = evaluate_production_hardware_wallet_evidence_v1(
        evidence,
        wallet_authority_profile_hash="wallet-auth-hash",
        expected_device_pubkey=DEVICE_PUBKEY,
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "device_attestation.challenge must equal canonical hardware approval challenge" in lane["gaps"]


def test_hardware_evaluator_rejects_rehashed_fake_approval_signature(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "hardware_wallet.json"

    assert builder.main(_base_args(out)) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))
    evidence["device_approval_tx"]["approval_signature"] = "20" * 64
    evidence = attach_production_hardware_wallet_hash_v1(evidence)

    lane = evaluate_production_hardware_wallet_evidence_v1(
        evidence,
        wallet_authority_profile_hash="wallet-auth-hash",
        expected_device_pubkey=DEVICE_PUBKEY,
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "device_approval_tx.approval_signature is invalid" in lane["gaps"]


def test_hardware_builder_rejects_non_positive_issued_at_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    out = tmp_path / "hardware_wallet.json"
    args = _base_args(out)
    args[args.index("--issued-at") + 1] = "0"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "issued_at must be a positive integer" in payload["detail"]
    assert not out.exists()
