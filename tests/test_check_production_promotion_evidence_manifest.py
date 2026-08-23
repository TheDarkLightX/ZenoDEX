from __future__ import annotations

import json
import subprocess
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration import production_promotion_evidence as promotion_evidence
from src.integration.production_promotion_evidence import (
    AUTOTRADER_EVIDENCE_SCHEMA_V1,
    ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
    _oracle_authority_attestation_message,
    attach_production_app_root_jmt_hash_v2,
    attach_production_autotrader_hash_v1,
    attach_production_oracle_authority_hash_v1,
    production_autotrader_run_approval_hash_v1,
    production_autotrader_run_approval_message_v1,
)
from tools import check_production_promotion_evidence_manifest as checker
from tools.build_app_root_jmt_evidence import build_evidence as build_app_root_evidence
from tools.check_production_promotion_evidence_manifest import main

NOW = 1747878000
MANIFEST_SCHEMA = "zenodex/production-promotion-evidence-manifest/v1"
ROOT = Path(__file__).resolve().parents[1]
_ORACLE_AUTHORITY_PRIVATE_KEY = Ed25519PrivateKey.from_private_bytes(bytes.fromhex("43" * 32))
_AUTOTRADER_APPROVER_KEYS = (
    Ed25519PrivateKey.from_private_bytes(bytes.fromhex("51" * 32)),
    Ed25519PrivateKey.from_private_bytes(bytes.fromhex("52" * 32)),
)
_AUTOTRADER_UNAPPROVED_KEYS = (
    Ed25519PrivateKey.from_private_bytes(bytes.fromhex("61" * 32)),
    Ed25519PrivateKey.from_private_bytes(bytes.fromhex("62" * 32)),
)


def _oracle_pubkey_hex() -> str:
    return _ORACLE_AUTHORITY_PRIVATE_KEY.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()


def _pubkey_hex(private_key: Ed25519PrivateKey) -> str:
    return private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()


def _autotrader_expected_approvers() -> list[str]:
    return [_pubkey_hex(key) for key in _AUTOTRADER_APPROVER_KEYS]


def _autotrader_evidence(
    *,
    signing_keys: tuple[Ed25519PrivateKey, Ed25519PrivateKey] = _AUTOTRADER_APPROVER_KEYS,
) -> dict[str, object]:
    started = NOW - 25 * 3600 - 60
    last_heartbeat = started + 25 * 3600
    heartbeats = list(range(started, last_heartbeat + 1, 5 * 60))
    if heartbeats[-1] != last_heartbeat:
        heartbeats.append(last_heartbeat)
    evidence: dict[str, object] = {
        "schema": AUTOTRADER_EVIDENCE_SCHEMA_V1,
        "supervisor_id": "autotrader-prod-1",
        "chain_id": "tau-test-prod",
        "profile_supervisor_hash": "sup-hash",
        "run_window": {
            "started_at": started,
            "last_heartbeat_at": last_heartbeat,
            "duration_seconds": 25 * 3600,
            "ticks_executed": 500,
            "ticks_failed": 3,
            "ticks_throttled": 20,
            "heartbeat_timestamps": heartbeats,
        },
        "crash_recovery": [
            {"crash_at": started + 3600, "recovery_at": started + 3620, "checkpoint_hash": "aa" * 32},
        ],
        "budget_compliance": {
            "max_actions_per_tick_observed": 3,
            "max_runs_per_process_observed": 100,
            "config_max_actions_per_tick": 4,
            "config_max_runs_per_process": 200,
        },
        "issued_at": NOW - 30,
    }
    approval_hash = production_autotrader_run_approval_hash_v1(evidence)
    message = production_autotrader_run_approval_message_v1(approval_hash)
    evidence["multi_signer_approvals"] = [
        {
            "signer_pubkey": _pubkey_hex(key),
            "approval_hash": approval_hash,
            "signature": key.sign(message).hex(),
        }
        for key in signing_keys
    ]
    return attach_production_autotrader_hash_v1(evidence)


def _bounded_oracle_exercise(*, chain_id: str = "tau-test-prod") -> dict[str, object]:
    return {
        "authority_exercised": True,
        "public_testnet_exercised": True,
        "exercise_hash": "exhash",
        "authority_hash": "authhash",
        "chain_id": chain_id,
        "public_broadcast_height": 100,
        "public_settlement_height": 105,
    }


def _oracle_evidence(*, chain_id: str = "tau-test-prod") -> dict[str, object]:
    issued_at = NOW - 60
    signature = _ORACLE_AUTHORITY_PRIVATE_KEY.sign(
        _oracle_authority_attestation_message(
            authority_id="zeno-oracle-prod",
            chain_id=chain_id,
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
    return attach_production_oracle_authority_hash_v1(
        {
            "schema": ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
            "authority_id": "zeno-oracle-prod",
            "chain_id": chain_id,
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
    )


def _app_root_evidence(*, evidence_kind: str = "live_replay") -> dict[str, object]:
    evidence = build_app_root_evidence(now=NOW)
    if evidence_kind == "live_replay":
        return evidence
    evidence.pop("evidence_hash")
    evidence["evidence_kind"] = evidence_kind
    return attach_production_app_root_jmt_hash_v2(evidence)


def test_manifest_checker_lane_output_matches_selected_lane_exit(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise(), sort_keys=True))
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "bounded_oracle_exercise_status_path": "bounded.json",
                    "expected_chain_id": "tau-test-prod",
                    "expected_oracle_authority_signer_pubkey": _oracle_pubkey_hex(),
                },
                "bundle": {"oracle_authority": _oracle_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is True
    assert out["selected_lane"] == "oracle_authority"
    assert out["blocked_lanes"] == []
    assert out["gaps"] == []
    assert list(out["lanes"]) == ["oracle_authority"]


def test_manifest_checker_resolves_config_paths_relative_to_manifest_file(
    capsys,
    tmp_path: Path,
) -> None:
    evidence_dir = tmp_path / "evidence"
    evidence_dir.mkdir()
    bounded_path = evidence_dir / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise(), sort_keys=True))
    manifest_path = evidence_dir / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "bounded_oracle_exercise_status_path": "bounded.json",
                    "expected_chain_id": "tau-test-prod",
                    "expected_oracle_authority_signer_pubkey": _oracle_pubkey_hex(),
                },
                "bundle": {"oracle_authority": _oracle_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["selected_lane"] == "oracle_authority"
    assert out["promotion_ready"] is True


def test_manifest_checker_required_config_value_blocks_selected_lane(
    capsys,
    tmp_path: Path,
) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise(), sort_keys=True))
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"bounded_oracle_exercise_status_path": "bounded.json"},
                "bundle": {"oracle_authority": _oracle_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert out["blocked_lanes"] == ["oracle_authority"]
    assert any("config.expected_chain_id is required" in gap for gap in out["gaps"])
    assert any("config.expected_oracle_authority_signer_pubkey is required" in gap for gap in out["gaps"])
    assert out["lanes"]["oracle_authority"]["production_ready"] is False


def test_manifest_checker_rejects_oracle_authority_signer_config_mismatch(
    capsys,
    tmp_path: Path,
) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise(), sort_keys=True))
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "bounded_oracle_exercise_status_path": "bounded.json",
                    "expected_chain_id": "tau-test-prod",
                    "expected_oracle_authority_signer_pubkey": "99" * 32,
                },
                "bundle": {"oracle_authority": _oracle_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert out["blocked_lanes"] == ["oracle_authority"]
    assert any("oracle authority attestation signer pubkey mismatch" in gap for gap in out["gaps"])
    assert out["lanes"]["oracle_authority"]["production_ready"] is False


def test_manifest_checker_rejects_runbook_placeholder_values_even_when_self_consistent(
    capsys,
    tmp_path: Path,
) -> None:
    placeholder_chain_id = "EXPECTED_CHAIN_ID"
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(
        json.dumps(_bounded_oracle_exercise(chain_id=placeholder_chain_id), sort_keys=True)
    )
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "bounded_oracle_exercise_status_path": "bounded.json",
                    "expected_chain_id": placeholder_chain_id,
                    "expected_oracle_authority_signer_pubkey": "EXPECTED_ORACLE_AUTHORITY_SIGNER_PUBKEY",
                },
                "bundle": {
                    "oracle_authority": _oracle_evidence(chain_id=placeholder_chain_id),
                },
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert out["blocked_lanes"] == ["oracle_authority"]
    assert any("placeholder value 'EXPECTED_CHAIN_ID'" in gap for gap in out["gaps"])
    assert out["lanes"]["oracle_authority"]["production_ready"] is False


def test_manifest_checker_placeholder_scan_is_lane_scoped(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"expected_chain_id": "EXPECTED_CHAIN_ID"},
                "bundle": {"app_root_jmt": _app_root_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "app_root_jmt", "--now", str(NOW)]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is True
    assert out["selected_lane"] == "app_root_jmt"


def test_manifest_checker_reports_missing_config_path(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"live_proof_wrapper_status_path": "missing-wrapper.json"},
                "bundle": {},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path)]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_config_invalid"
    assert "live_proof_wrapper_status_path not found" in out["detail"]


def test_manifest_checker_selected_lane_ignores_unrelated_missing_sidecar(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"live_proof_wrapper_status_path": "missing-wrapper.json"},
                "bundle": {},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "autotrader", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["selected_lane"] == "autotrader"
    assert "error" not in out
    assert out["blocked_lanes"] == ["autotrader"]
    assert any("autotrader evidence is missing" in gap for gap in out["gaps"])


def test_manifest_checker_accepts_autotrader_expected_approver_set(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "supervisor_profile_hash": "sup-hash",
                    "config_max_actions_per_tick": 4,
                    "config_max_runs_per_process": 200,
                    "expected_chain_id": "tau-test-prod",
                    "expected_autotrader_approval_signer_pubkeys": _autotrader_expected_approvers(),
                },
                "bundle": {"autotrader": _autotrader_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "autotrader", "--now", str(NOW)]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is True
    assert out["selected_lane"] == "autotrader"
    assert out["blocked_lanes"] == []


def test_manifest_checker_rejects_autotrader_missing_approver_set(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "supervisor_profile_hash": "sup-hash",
                    "config_max_actions_per_tick": 4,
                    "config_max_runs_per_process": 200,
                    "expected_chain_id": "tau-test-prod",
                },
                "bundle": {"autotrader": _autotrader_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "autotrader", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert out["blocked_lanes"] == ["autotrader"]
    assert any("config.expected_autotrader_approval_signer_pubkeys is required" in gap for gap in out["gaps"])


def test_manifest_checker_rejects_autotrader_unapproved_signer_set(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "supervisor_profile_hash": "sup-hash",
                    "config_max_actions_per_tick": 4,
                    "config_max_runs_per_process": 200,
                    "expected_chain_id": "tau-test-prod",
                    "expected_autotrader_approval_signer_pubkeys": _autotrader_expected_approvers(),
                },
                "bundle": {"autotrader": _autotrader_evidence(signing_keys=_AUTOTRADER_UNAPPROVED_KEYS)},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "autotrader", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert out["blocked_lanes"] == ["autotrader"]
    assert any("not in expected approver set" in gap for gap in out["gaps"])


def test_manifest_checker_selected_lane_loads_relevant_missing_sidecar(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"live_proof_wrapper_status_path": "missing-wrapper.json"},
                "bundle": {},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "zk_wrapping", "--now", str(NOW)]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_config_invalid"
    assert "live_proof_wrapper_status_path not found" in out["detail"]


def test_manifest_checker_rejects_absolute_config_sidecar_path(capsys, tmp_path: Path) -> None:
    bounded_path = tmp_path / "bounded.json"
    bounded_path.write_text(json.dumps(_bounded_oracle_exercise(), sort_keys=True))
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "bounded_oracle_exercise_status_path": str(bounded_path),
                    "expected_chain_id": "tau-test-prod",
                    "expected_oracle_authority_signer_pubkey": _oracle_pubkey_hex(),
                },
                "bundle": {"oracle_authority": _oracle_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_config_invalid"
    assert "must be relative to the manifest file" in out["detail"]


def test_manifest_checker_rejects_config_sidecar_escape(capsys, tmp_path: Path) -> None:
    outside = tmp_path / "bounded.json"
    outside.write_text(json.dumps(_bounded_oracle_exercise(), sort_keys=True))
    evidence_dir = tmp_path / "evidence"
    evidence_dir.mkdir()
    manifest_path = evidence_dir / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {
                    "bounded_oracle_exercise_status_path": "../bounded.json",
                    "expected_chain_id": "tau-test-prod",
                    "expected_oracle_authority_signer_pubkey": _oracle_pubkey_hex(),
                },
                "bundle": {"oracle_authority": _oracle_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "oracle_authority", "--now", str(NOW)]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_config_invalid"
    assert "must stay under the manifest directory" in out["detail"]


def test_manifest_checker_explains_missing_lane_requirements(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {
                    "oracle_authority": None,
                    "hardware_wallet": None,
                    "zk_wrapping": None,
                    "autotrader": None,
                    "confidential_runtime": None,
                    "app_root_jmt": None,
                },
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--explain-missing"]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert set(out["requirements"]) == {
        "oracle_authority",
        "hardware_wallet",
        "zk_wrapping",
        "autotrader",
        "confidential_runtime",
        "app_root_jmt",
    }
    assert "bounded_oracle_exercise_status_path" in out["requirements"]["oracle_authority"]["required_config_paths"]
    assert (
        "expected_oracle_authority_signer_pubkey"
        in out["requirements"]["oracle_authority"]["required_config_values"]
    )
    assert "live_proof_wrapper_status_path" in out["requirements"]["zk_wrapping"]["required_config_paths"]
    assert "device_attestation" in out["requirements"]["hardware_wallet"]["required_evidence_fields"]
    assert "approved_measurements" in out["requirements"]["confidential_runtime"]["required_config_values"]
    confidential_fields = out["requirements"]["confidential_runtime"]["required_evidence_fields"]
    assert "provider_id" in confidential_fields
    assert "approved_measurements_hash" in confidential_fields
    assert "private_execution_receipt" in confidential_fields
    assert "receipt_policy" not in confidential_fields
    assert "live_root_checks" in out["requirements"]["app_root_jmt"]["required_evidence_fields"]
    assert "lane-tamper negative check" in " ".join(out["requirements"]["app_root_jmt"]["external_artifacts"])
    assert out["requirements"]["oracle_authority"]["producer_tool"] == "tools/build_oracle_authority_evidence.py"
    assert out["requirements"]["hardware_wallet"]["producer_tool"] == "tools/build_hardware_wallet_evidence.py"
    assert (
        out["requirements"]["zk_wrapping"]["producer_tool"]
        == "tools/build_zk_wrapping_evidence_from_risc0_bundle.py"
    )
    assert out["requirements"]["autotrader"]["producer_tool"] == "tools/build_autotrader_evidence.py"
    assert (
        "expected_autotrader_approval_signer_pubkeys"
        in out["requirements"]["autotrader"]["required_config_values"]
    )
    assert (
        out["requirements"]["confidential_runtime"]["producer_tool"]
        == "tools/build_confidential_runtime_evidence.py"
    )
    assert out["requirements"]["app_root_jmt"]["producer_tool"] == "tools/build_app_root_jmt_evidence.py"


def test_manifest_checker_explains_only_selected_lane(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps({"schema": MANIFEST_SCHEMA, "config": {}, "bundle": {}}, sort_keys=True)
    )

    assert main([str(manifest_path), "--lane", "zk_wrapping", "--explain-missing"]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["selected_lane"] == "zk_wrapping"
    assert list(out["requirements"]) == ["zk_wrapping"]
    assert out["requirements"]["zk_wrapping"]["validator"] == "evaluate_production_zk_wrapping_evidence_v1"
    assert (
        out["requirements"]["zk_wrapping"]["producer_tool"]
        == "tools/build_zk_wrapping_evidence_from_risc0_bundle.py"
    )


def test_manifest_checker_can_attach_collection_runbook_for_all_lanes(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {
                    "oracle_authority": None,
                    "hardware_wallet": None,
                    "zk_wrapping": None,
                    "autotrader": None,
                    "confidential_runtime": None,
                    "app_root_jmt": None,
                },
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--explain-missing", "--include-runbook"]) == 1
    out = json.loads(capsys.readouterr().out)
    runbook = out["collection_runbook"]
    assert runbook["schema"] == "zenodex/production-promotion-evidence-collection-runbook/v1"
    assert set(runbook["lanes"]) == {
        "oracle_authority",
        "hardware_wallet",
        "zk_wrapping",
        "autotrader",
        "confidential_runtime",
        "app_root_jmt",
    }
    assert (
        runbook["lanes"]["oracle_authority"]["producer_command_template"][1]
        == "tools/build_oracle_authority_evidence.py"
    )
    assert (
        runbook["lanes"]["zk_wrapping"]["producer_command_template"][1]
        == "tools/build_zk_wrapping_evidence_from_risc0_bundle.py"
    )
    assert "runs/production_promotion/input/live_proof_wrapper_status.json" in (
        runbook["lanes"]["zk_wrapping"]["producer_command_template"]
    )
    assert "--expected-surface" in runbook["lanes"]["zk_wrapping"]["producer_command_template"]
    for lane in [
        "oracle_authority",
        "hardware_wallet",
        "zk_wrapping",
        "autotrader",
        "confidential_runtime",
    ]:
        command = runbook["lanes"][lane]["producer_command_template"]
        assert "--issued-at" in command
        assert "ISSUED_AT" in command
        assert "--check-now" in command
        assert "CHECK_NOW" in command
    assert "--accepted-at" in runbook["lanes"]["zk_wrapping"]["producer_command_template"]
    assert "ACCEPTED_AT" in runbook["lanes"]["zk_wrapping"]["producer_command_template"]
    assert "--now" in runbook["lanes"]["app_root_jmt"]["producer_command_template"]
    assert "APP_ROOT_CHECKED_AT" in runbook["lanes"]["app_root_jmt"]["producer_command_template"]
    assert "--now" in runbook["manifest_command_template"]
    assert "CHECK_NOW" in runbook["manifest_command_template"]
    assert "tools/build_production_promotion_evidence_manifest.py" in runbook["manifest_command_template"]
    assert "tools/run_production_promotion_evidence_gate.sh" in runbook["final_gate_command_template"]
    assert "--include-runbook" in runbook["final_gate_command_template"]
    assert out["promotion_ready"] is False


def test_production_promotion_requirements_doc_matches_external_lane_arguments() -> None:
    docs = (ROOT / "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md").read_text(
        encoding="utf-8"
    )

    for token in [
        "--expected-surface",
        "expected_autotrader_approval_signer_pubkeys",
        "--expected-approval-signer-pubkeys-file",
        "--issued-at",
        "--check-now",
        "--accepted-at",
        "--now",
        "--live-wrapper-out",
        "--runtime-receipt-hash",
        "--attestation-receipt-hash",
        "--request-id",
        "--attestation-epoch",
        "--current-epoch",
        "--units-charged",
    ]:
        assert token in docs


def test_manifest_checker_can_attach_compact_readiness_plan(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {
                    "oracle_authority": None,
                    "hardware_wallet": None,
                    "zk_wrapping": None,
                    "autotrader": None,
                    "confidential_runtime": None,
                    "app_root_jmt": None,
                },
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--readiness-plan"]) == 1
    out = json.loads(capsys.readouterr().out)
    plan = out["readiness_plan"]
    assert plan["schema"] == "zenodex/production-promotion-readiness-plan/v1"
    assert plan["promotion_ready"] is False
    assert set(plan["blocked_lanes"]) == {
        "oracle_authority",
        "hardware_wallet",
        "zk_wrapping",
        "autotrader",
        "confidential_runtime",
        "app_root_jmt",
    }
    oracle = plan["lanes"]["oracle_authority"]
    assert oracle["status"] == "blocked"
    assert oracle["missing_artifact"] is True
    assert oracle["missing_config"] == [
        "bounded_oracle_exercise_status_path",
        "expected_chain_id",
        "expected_oracle_authority_signer_pubkey",
    ]
    assert oracle["categories"] == [
        "missing_artifact",
        "missing_config",
        "external_required",
    ]
    assert oracle["producer_tool"] == "tools/build_oracle_authority_evidence.py"


def test_manifest_checker_readiness_plan_marks_ready_lane(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {"app_root_jmt": _app_root_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "app_root_jmt", "--now", str(NOW), "--readiness-plan"]) == 0
    out = json.loads(capsys.readouterr().out)
    lane_plan = out["readiness_plan"]["lanes"]["app_root_jmt"]
    assert lane_plan["status"] == "ready"
    assert lane_plan["categories"] == ["ready"]
    assert lane_plan["missing_artifact"] is False
    assert lane_plan["missing_config"] == []
    assert lane_plan["missing_sidecars"] == []


def test_manifest_checker_readiness_plan_reports_missing_sidecar(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"live_proof_wrapper_status_path": "missing-wrapper.json"},
                "bundle": {"zk_wrapping": None},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "zk_wrapping", "--readiness-plan"]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_config_invalid"
    lane_plan = out["readiness_plan"]["lanes"]["zk_wrapping"]
    assert lane_plan["status"] == "blocked"
    assert lane_plan["missing_sidecars"] == [
        {
            "field": "live_proof_wrapper_status_path",
            "path": "missing-wrapper.json",
            "reason": "sidecar file not found",
        }
    ]
    assert lane_plan["categories"] == [
        "missing_artifact",
        "missing_config",
        "missing_sidecar",
        "external_required",
    ]


def test_manifest_checker_collection_runbook_scopes_to_selected_lane(
    capsys,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps({"schema": MANIFEST_SCHEMA, "config": {}, "bundle": {}}, sort_keys=True)
    )

    assert main([str(manifest_path), "--lane", "autotrader", "--include-runbook"]) == 1
    out = json.loads(capsys.readouterr().out)
    runbook = out["collection_runbook"]
    assert list(runbook["lanes"]) == ["autotrader"]
    command = runbook["lanes"]["autotrader"]["producer_command_template"]
    assert command[1] == "tools/build_autotrader_evidence.py"
    assert "--expected-approval-signer-pubkeys-file" in command
    assert "MAX_RUNS_PER_PROCESS_OBSERVED" in command
    assert "MAX_RUNS_PER_PROCESS_OBERVED" not in command
    assert "--include-runbook" in runbook["final_gate_command_template"]
    assert out["blocked_lanes"] == ["autotrader"]


def test_manifest_runbook_placeholders_match_lane_verifier_policy() -> None:
    # The manifest checker derives placeholders from operator command
    # templates; the lane verifier rejects the same values during producer
    # --check. Keep the two gates synchronized so a runbook edit cannot create a
    # checker-only or producer-only false-green path.
    assert checker._RUNBOOK_PLACEHOLDER_TOKENS == promotion_evidence._RUNBOOK_PLACEHOLDER_VALUES
    assert all(
        promotion_evidence._is_template_placeholder(value)
        for value in checker._RUNBOOK_PLACEHOLDER_TOKENS
    )


def test_manifest_checker_app_root_jmt_selected_lane_passes(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {"app_root_jmt": _app_root_evidence()},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "app_root_jmt", "--now", str(NOW)]) == 0
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is True
    assert out["selected_lane"] == "app_root_jmt"
    assert list(out["lanes"]) == ["app_root_jmt"]


def test_manifest_checker_rejects_fixture_app_root_jmt_evidence(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {},
                "bundle": {"app_root_jmt": _app_root_evidence(evidence_kind="fixture")},
            },
            sort_keys=True,
        )
    )

    assert main([str(manifest_path), "--lane", "app_root_jmt", "--now", str(NOW)]) == 1
    out = json.loads(capsys.readouterr().out)
    assert out["promotion_ready"] is False
    assert any("fixture or synthetic" in gap for gap in out["gaps"])


def test_manifest_checker_rejects_null_config(capsys, tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps({"schema": MANIFEST_SCHEMA, "config": None, "bundle": {}}, sort_keys=True))

    assert main([str(manifest_path)]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "config_or_bundle_not_object"
    assert "config must be a JSON object" in out["detail"]


def test_shell_wrapper_allows_default_manifest_with_lane_flag() -> None:
    result = subprocess.run(
        ["bash", "tools/run_production_promotion_evidence_gate.sh", "--lane", "oracle_authority"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )
    assert result.returncode != 2
    output = result.stdout or result.stderr
    assert '"path": "--lane"' not in output
