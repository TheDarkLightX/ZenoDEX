from __future__ import annotations

import json
from pathlib import Path

from src.integration.production_promotion_evidence import (
    evaluate_production_hardware_wallet_evidence_v1,
)
from tools import build_hardware_wallet_evidence as builder

NOW = 1747878000


def _base_args(out: Path) -> list[str]:
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
        "cc" * 32,
        "--attestation-challenge",
        "dd" * 32,
        "--attestation-signature",
        "ee" * 64,
        "--prompt-kind",
        "screenshot_hash",
        "--prompt-hash",
        "ff" * 32,
        "--prompt-captured-at",
        str(NOW - 120),
        "--approval-tx-payload-hash",
        "10" * 32,
        "--approval-signature",
        "20" * 64,
        "--approval-captured-at",
        str(NOW - 60),
        "--wallet-authority-profile-hash",
        "wallet-auth-hash",
        "--expected-device-pubkey",
        "cc" * 32,
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
        expected_device_pubkey="cc" * 32,
        now=NOW,
    )
    assert lane["production_ready"] is True
    assert lane["gaps"] == []
    assert evidence["device_attestation"]["pubkey"] == "cc" * 32
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
    args[args.index("--approval-signature") + 1] = "ee" * 64

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "hardware_wallet_evidence_build_failed"
    assert "signature must differ" in payload["detail"]
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
    args = _base_args(out)
    stale_prompt = NOW - 7 * 24 * 3600
    args[args.index("--prompt-captured-at") + 1] = str(stale_prompt)
    args[args.index("--approval-captured-at") + 1] = str(stale_prompt + 60)

    assert builder.main(args) == 0
    capsys.readouterr()
    evidence = json.loads(out.read_text(encoding="utf-8"))

    lane = evaluate_production_hardware_wallet_evidence_v1(
        evidence,
        wallet_authority_profile_hash="wallet-auth-hash",
        expected_device_pubkey="cc" * 32,
        now=NOW,
    )

    assert lane["production_ready"] is False
    assert "device_approval_tx.captured_at is too old for evidence issued_at" in lane["gaps"]


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
