from __future__ import annotations

import json
import subprocess
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from src.integration.production_promotion_evidence import (
    APP_ROOT_JMT_EVIDENCE_SCHEMA_V1,
    ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
    _oracle_authority_attestation_message,
    attach_production_app_root_jmt_hash_v1,
    attach_production_oracle_authority_hash_v1,
)
from src.state.app_root import APP_ROOT_LANE_KINDS
from tools.check_production_promotion_evidence_manifest import main

NOW = 1747878000
MANIFEST_SCHEMA = "zenodex/production-promotion-evidence-manifest/v1"
ROOT = Path(__file__).resolve().parents[1]
_ORACLE_AUTHORITY_PRIVATE_KEY = Ed25519PrivateKey.from_private_bytes(bytes.fromhex("43" * 32))


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


def _oracle_evidence() -> dict[str, object]:
    issued_at = NOW - 60
    pubkey = _ORACLE_AUTHORITY_PRIVATE_KEY.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
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
    return attach_production_oracle_authority_hash_v1(
        {
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
            "authority_attestation_signer_pubkey": pubkey.hex(),
            "issued_at": issued_at,
        }
    )


def _app_root_evidence(*, evidence_kind: str = "live_replay") -> dict[str, object]:
    lane_kinds = sorted(APP_ROOT_LANE_KINDS)
    return attach_production_app_root_jmt_hash_v1(
        {
            "schema": APP_ROOT_JMT_EVIDENCE_SCHEMA_V1,
            "evidence_kind": evidence_kind,
            "root_system": "typed_app_root_jmt_v1",
            "required_lane_kinds": lane_kinds,
            "live_root_checks": [
                {
                    "check_id": "plain-dex-snapshot",
                    "mode": "plain_dex_snapshot_live_root",
                    "source_kind": "live_local_replay",
                    "observed_root": "11" * 32,
                    "recomputed_root": "11" * 32,
                    "source_state_hash": "21" * 32,
                    "required_lane_kinds": lane_kinds,
                    "live_path": "tools/zeno_ledger_node.py:_state_root_for_state_file_obj_v0",
                    "checked_at": NOW - 30,
                },
                {
                    "check_id": "tau-wrapper",
                    "mode": "tau_app_state_wrapper_live_root",
                    "source_kind": "live_node",
                    "observed_root": "12" * 32,
                    "recomputed_root": "12" * 32,
                    "source_state_hash": "22" * 32,
                    "required_lane_kinds": lane_kinds,
                    "live_path": "src/integration/tau_testnet_dex_plugin.py:_canonical_state_and_hash",
                    "checked_at": NOW - 30,
                },
                {
                    "check_id": "pre-snapshot-header",
                    "mode": "local_block_pre_snapshot_header",
                    "source_kind": "release_replay",
                    "observed_root": "13" * 32,
                    "recomputed_root": "13" * 32,
                    "source_state_hash": "23" * 32,
                    "required_lane_kinds": lane_kinds,
                    "live_path": "tools/zeno_ledger_run_local.py:pre_snapshot_path",
                    "checked_at": NOW - 30,
                },
            ],
            "negative_checks": [
                {
                    "check_id": "lane-tamper",
                    "mutation": "lane_tamper_rejected",
                    "source_kind": "release_replay",
                    "rejected": True,
                    "checked_at": NOW - 30,
                }
            ],
            "issued_at": NOW - 20,
        }
    )


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
    assert out["lanes"]["oracle_authority"]["production_ready"] is False


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
    assert "tools/build_production_promotion_evidence_manifest.py" in runbook["manifest_command_template"]
    assert "tools/run_production_promotion_evidence_gate.sh" in runbook["final_gate_command_template"]
    assert "--include-runbook" in runbook["final_gate_command_template"]
    assert out["promotion_ready"] is False


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
    assert "MAX_RUNS_PER_PROCESS_OBSERVED" in command
    assert "MAX_RUNS_PER_PROCESS_OBERVED" not in command
    assert "--include-runbook" in runbook["final_gate_command_template"]
    assert out["blocked_lanes"] == ["autotrader"]


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
