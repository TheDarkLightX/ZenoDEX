from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration.production_promotion_evidence import (
    _oracle_authority_attestation_message,
    evaluate_production_oracle_authority_evidence_v1,
)
from tools import build_oracle_authority_evidence as builder

NOW = 1747878000
_ORACLE_AUTHORITY_PRIVATE_KEY = Ed25519PrivateKey.from_private_bytes(bytes.fromhex("42" * 32))


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


def _base_args(tmp_path: Path, bounded_path: Path, out: Path) -> list[str]:
    bounded = _bounded_oracle_exercise()
    pubkey = _ORACLE_AUTHORITY_PRIVATE_KEY.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    signature = _ORACLE_AUTHORITY_PRIVATE_KEY.sign(
        _oracle_authority_attestation_message(
            authority_id="zeno-oracle-prod",
            chain_id=str(bounded["chain_id"]),
            target_network="public_testnet",
            exercise_hash=str(bounded["exercise_hash"]),
            profile_authority_hash=str(bounded["authority_hash"]),
            public_broadcast_height=int(bounded["public_broadcast_height"]),
            public_settlement_height=int(bounded["public_settlement_height"]),
            public_broadcast_block_hash="11" * 32,
            public_settlement_block_hash="22" * 32,
            public_broadcast_explorer_url="https://explorer.public-testnet/block/100",
            public_settlement_explorer_url="https://explorer.public-testnet/block/105",
            issued_at=NOW,
        )
    )
    return [
        "--bounded-oracle-exercise-status",
        str(bounded_path),
        "--out",
        str(out),
        "--authority-id",
        "zeno-oracle-prod",
        "--public-broadcast-block-hash",
        "11" * 32,
        "--public-settlement-block-hash",
        "22" * 32,
        "--public-broadcast-explorer-url",
        "https://explorer.public-testnet/block/100",
        "--public-settlement-explorer-url",
        "https://explorer.public-testnet/block/105",
        "--authority-attestation-signature",
        signature.hex(),
        "--authority-attestation-signer-pubkey",
        pubkey.hex(),
        "--issued-at",
        str(NOW),
        "--check-now",
        str(NOW),
        "--expected-chain-id",
        "tau-test-prod",
    ]


def test_oracle_builder_writes_lane_ready_evidence(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    out = tmp_path / "oracle_authority.json"

    assert builder.main([*_base_args(tmp_path, bounded_path, out), "--check"]) == 0

    assert json.loads(capsys.readouterr().out)["ok"] is True
    evidence = json.loads(out.read_text(encoding="utf-8"))
    lane = evaluate_production_oracle_authority_evidence_v1(
        evidence,
        bounded_exercise_status=_bounded_oracle_exercise(),
        expected_chain_id="tau-test-prod",
        now=NOW,
    )
    assert lane["production_ready"] is True
    assert lane["gaps"] == []
    assert evidence["exercise_hash"] == "exhash"
    assert len(evidence["evidence_hash"]) == 64


def test_oracle_builder_rejects_non_public_testnet_exercise_before_writing(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(
        json.dumps(dict(_bounded_oracle_exercise(), public_testnet_exercised=False)),
        encoding="utf-8",
    )
    out = tmp_path / "oracle_authority.json"

    assert builder.main(_base_args(tmp_path, bounded_path, out)) == 2

    err = json.loads(capsys.readouterr().out)
    assert err["error"] == "oracle_authority_evidence_build_failed"
    assert "public_testnet_exercised must be true" in err["detail"]
    assert not out.exists()


def test_oracle_builder_rejects_unexercised_authority_before_writing(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(
        json.dumps(dict(_bounded_oracle_exercise(), authority_exercised=False)),
        encoding="utf-8",
    )
    out = tmp_path / "oracle_authority.json"

    assert builder.main(_base_args(tmp_path, bounded_path, out)) == 2

    err = json.loads(capsys.readouterr().out)
    assert err["error"] == "oracle_authority_evidence_build_failed"
    assert "authority_exercised must be true" in err["detail"]
    assert not out.exists()


def test_oracle_builder_rejects_reversed_public_heights_before_writing(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(
        json.dumps(
            dict(
                _bounded_oracle_exercise(),
                public_broadcast_height=105,
                public_settlement_height=100,
            )
        ),
        encoding="utf-8",
    )
    out = tmp_path / "oracle_authority.json"

    assert builder.main(_base_args(tmp_path, bounded_path, out)) == 2

    err = json.loads(capsys.readouterr().out)
    assert err["error"] == "oracle_authority_evidence_build_failed"
    assert "public_settlement_height must be >= public_broadcast_height" in err["detail"]
    assert not out.exists()


def test_oracle_builder_rejects_malformed_public_block_hash(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    out = tmp_path / "oracle_authority.json"
    args = _base_args(tmp_path, bounded_path, out)
    index = args.index("--public-broadcast-block-hash") + 1
    args[index] = "not-hex"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "oracle_authority_evidence_build_failed"
    assert "public broadcast block hash" in payload["detail"]
    assert not out.exists()


def test_oracle_builder_check_rejects_local_explorer_url(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    out = tmp_path / "oracle_authority.json"
    args = _base_args(tmp_path, bounded_path, out)
    index = args.index("--public-settlement-explorer-url") + 1
    args[index] = "https://localhost/block/105"

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("local explorer host" in gap for gap in err["gaps"])
    assert not out.exists()


def test_oracle_builder_check_rejects_invalid_authority_attestation_signature(
    capsys,
    tmp_path: Path,
) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    out = tmp_path / "oracle_authority.json"
    args = _base_args(tmp_path, bounded_path, out)
    args[args.index("--authority-attestation-signature") + 1] = "aa" * 64

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert "oracle authority attestation signature is invalid" in err["gaps"]
    assert not out.exists()


def test_oracle_builder_check_rejects_stale_issued_at(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    out = tmp_path / "oracle_authority.json"
    args = _base_args(tmp_path, bounded_path, out)
    args[args.index("--issued-at") + 1] = str(NOW - 31 * 24 * 3600)

    assert builder.main([*args, "--check"]) == 1

    err = json.loads(capsys.readouterr().err)
    assert err["production_ready"] is False
    assert any("freshness" in gap for gap in err["gaps"])
    assert not out.exists()


def test_oracle_builder_rejects_non_positive_issued_at_before_writing(
    capsys,
    tmp_path: Path,
) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise()), encoding="utf-8")
    out = tmp_path / "oracle_authority.json"
    args = _base_args(tmp_path, bounded_path, out)
    args[args.index("--issued-at") + 1] = "0"

    assert builder.main(args) == 2

    payload = json.loads(capsys.readouterr().out)
    assert payload["error"] == "oracle_authority_evidence_build_failed"
    assert "issued_at must be a positive integer" in payload["detail"]
    assert not out.exists()
