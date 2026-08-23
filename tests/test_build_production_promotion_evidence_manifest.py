from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration.production_promotion_evidence import (
    ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
    _oracle_authority_attestation_message,
)
from tools import build_production_promotion_evidence_manifest as builder
from tools.build_app_root_jmt_evidence import build_evidence as build_app_root_evidence

NOW = 1747878000
_ORACLE_AUTHORITY_PRIVATE_KEY = Ed25519PrivateKey.from_private_bytes(bytes.fromhex("45" * 32))


def _oracle_pubkey_hex() -> str:
    return _ORACLE_AUTHORITY_PRIVATE_KEY.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()


def _bounded_oracle_exercise() -> dict[str, object]:
    return {
        "authority_exercised": True,
        "public_testnet_exercised": True,
        "exercise_hash": "exhash",
        "authority_hash": "authhash",
        "chain_id": "tau-test-prod",
        "public_broadcast_height": 100,
        "public_settlement_height": 105,
    }


def _oracle_evidence_body() -> dict[str, object]:
    issued_at = NOW - 60
    signature = _ORACLE_AUTHORITY_PRIVATE_KEY.sign(
        _oracle_authority_attestation_message(
            authority_id="zeno-oracle-prod",
            chain_id="tau-test-prod",
            target_network="public_testnet",
            exercise_hash="exhash",
            profile_authority_hash="authhash",
            public_broadcast_height=100,
            public_settlement_height=105,
            public_broadcast_block_hash="11" * 32,
            public_settlement_block_hash="22" * 32,
            public_broadcast_explorer_url="https://explorer.public-testnet/block/100",
            public_settlement_explorer_url="https://explorer.public-testnet/block/105",
            issued_at=issued_at,
        )
    )
    return {
        "schema": ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
        "authority_id": "zeno-oracle-prod",
        "chain_id": "tau-test-prod",
        "target_network": "public_testnet",
        "exercise_hash": "exhash",
        "profile_authority_hash": "authhash",
        "public_broadcast_height": 100,
        "public_settlement_height": 105,
        "public_broadcast_block_hash": "11" * 32,
        "public_settlement_block_hash": "22" * 32,
        "public_broadcast_explorer_url": "https://explorer.public-testnet/block/100",
        "public_settlement_explorer_url": "https://explorer.public-testnet/block/105",
        "authority_attestation_signature": signature.hex(),
        "authority_attestation_signer_pubkey": _oracle_pubkey_hex(),
        "issued_at": issued_at,
    }


def _app_root_jmt_evidence_body() -> dict[str, object]:
    evidence = build_app_root_evidence(now=NOW)
    evidence.pop("evidence_hash")
    return evidence


def test_builder_hashes_oracle_lane_and_lane_check_passes(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    evidence_path = tmp_path / "oracle.json"
    evidence_path.write_text(json.dumps(_oracle_evidence_body()), encoding="utf-8")
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--oracle-authority",
                str(evidence_path),
                "--bounded-oracle-exercise-status",
                str(bounded_path),
                "--expected-chain-id",
                "tau-test-prod",
                "--expected-oracle-authority-signer-pubkey",
                _oracle_pubkey_hex(),
                "--now",
                str(NOW),
                "--check-lane",
                "oracle_authority",
            ]
        )
        == 0
    )

    checker_out = json.loads(capsys.readouterr().out)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    oracle = manifest["bundle"]["oracle_authority"]
    assert manifest["config"]["bounded_oracle_exercise_status_path"] == "bounded.json"
    assert manifest["config"]["expected_oracle_authority_signer_pubkey"] == _oracle_pubkey_hex()
    assert checker_out["promotion_ready"] is True
    assert checker_out["selected_lane"] == "oracle_authority"
    assert oracle["evidence_hash"] != _oracle_evidence_body().get("evidence_hash")
    assert len(oracle["evidence_hash"]) == 64


def test_builder_hashes_app_root_jmt_lane_and_lane_check_passes(capsys, tmp_path: Path) -> None:
    evidence_path = tmp_path / "app-root.json"
    evidence_path.write_text(json.dumps(_app_root_jmt_evidence_body()), encoding="utf-8")
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--app-root-jmt",
                str(evidence_path),
                "--now",
                str(NOW),
                "--check-lane",
                "app_root_jmt",
            ]
        )
        == 0
    )

    checker_out = json.loads(capsys.readouterr().out)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    app_root = manifest["bundle"]["app_root_jmt"]
    assert checker_out["promotion_ready"] is True
    assert checker_out["selected_lane"] == "app_root_jmt"
    assert app_root["evidence_hash"] != _app_root_jmt_evidence_body().get("evidence_hash")
    assert len(app_root["evidence_hash"]) == 64


def test_builder_writes_autotrader_expected_approver_config(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--expected-autotrader-approval-signer-pubkey",
                "11" * 32,
                "--expected-autotrader-approval-signer-pubkey",
                "22" * 32,
            ]
        )
        == 0
    )

    assert json.loads(capsys.readouterr().out)["ok"] is True
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["config"]["expected_autotrader_approval_signer_pubkeys"] == [
        "11" * 32,
        "22" * 32,
    ]


def test_builder_full_check_stays_blocked_when_other_lanes_missing(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    evidence_path = tmp_path / "oracle.json"
    evidence_path.write_text(json.dumps(_oracle_evidence_body()), encoding="utf-8")
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--oracle-authority",
                str(evidence_path),
                "--bounded-oracle-exercise-status",
                str(bounded_path),
                "--expected-chain-id",
                "tau-test-prod",
                "--expected-oracle-authority-signer-pubkey",
                _oracle_pubkey_hex(),
                "--now",
                str(NOW),
                "--check",
                "--explain-missing",
            ]
        )
        == 1
    )

    checker_out = json.loads(capsys.readouterr().out)
    assert checker_out["promotion_ready"] is False
    assert "hardware_wallet" in checker_out["blocked_lanes"]
    assert "requirements" in checker_out
    assert checker_out["lanes"]["oracle_authority"]["production_ready"] is True


def test_builder_rejects_non_object_lane_json(capsys, tmp_path: Path) -> None:
    evidence_path = tmp_path / "oracle.json"
    evidence_path.write_text("[]", encoding="utf-8")
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--oracle-authority",
                str(evidence_path),
            ]
        )
        == 2
    )

    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_build_failed"
    assert "must contain a JSON object" in out["detail"]
    assert not manifest_path.exists()


def test_builder_rejects_explain_missing_without_checker_run(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--explain-missing",
            ]
        )
        == 2
    )

    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "explain_missing_requires_check"
    assert "--check or --check-lane" in out["detail"]
    assert not manifest_path.exists()


def test_builder_rejects_sidecar_path_outside_manifest_directory(capsys, tmp_path: Path) -> None:
    evidence_dir = tmp_path / "evidence"
    evidence_dir.mkdir()
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    evidence_path = evidence_dir / "oracle.json"
    evidence_path.write_text(json.dumps(_oracle_evidence_body()), encoding="utf-8")
    manifest_path = evidence_dir / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--oracle-authority",
                str(evidence_path),
                "--bounded-oracle-exercise-status",
                str(bounded_path),
                "--expected-chain-id",
                "tau-test-prod",
                "--expected-oracle-authority-signer-pubkey",
                _oracle_pubkey_hex(),
            ]
        )
        == 2
    )

    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_build_failed"
    assert "must be under the manifest directory" in out["detail"]
    assert not manifest_path.exists()


def test_builder_rejects_missing_sidecar_inside_manifest_directory(capsys, tmp_path: Path) -> None:
    evidence_path = tmp_path / "oracle.json"
    evidence_path.write_text(json.dumps(_oracle_evidence_body()), encoding="utf-8")
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--oracle-authority",
                str(evidence_path),
                "--bounded-oracle-exercise-status",
                str(tmp_path / "missing-bounded.json"),
                "--expected-chain-id",
                "tau-test-prod",
                "--expected-oracle-authority-signer-pubkey",
                _oracle_pubkey_hex(),
            ]
        )
        == 2
    )

    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_build_failed"
    assert "must point to a JSON file" in out["detail"]
    assert not manifest_path.exists()


def test_builder_rejects_directory_sidecar_inside_manifest_directory(capsys, tmp_path: Path) -> None:
    evidence_path = tmp_path / "oracle.json"
    evidence_path.write_text(json.dumps(_oracle_evidence_body()), encoding="utf-8")
    sidecar_dir = tmp_path / "sidecar-dir"
    sidecar_dir.mkdir()
    manifest_path = tmp_path / "manifest.json"

    assert (
        builder.main(
            [
                "--out",
                str(manifest_path),
                "--oracle-authority",
                str(evidence_path),
                "--bounded-oracle-exercise-status",
                str(sidecar_dir),
                "--expected-chain-id",
                "tau-test-prod",
                "--expected-oracle-authority-signer-pubkey",
                _oracle_pubkey_hex(),
            ]
        )
        == 2
    )

    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_build_failed"
    assert "must point to a JSON file" in out["detail"]
    assert not manifest_path.exists()
