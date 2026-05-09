from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_production_network_config import (
    check_config,
    receipt_content_hash,
    sample_config,
    sample_receipt_bundle,
)

ROOT = Path(__file__).resolve().parents[1]


def test_production_network_config_accepts_sample_candidate() -> None:
    config = sample_config()
    result = check_config(config, sample_receipt_bundle(config))

    assert result["schema"] == "zenodex.oracle.production_network_config_check.v1"
    assert result["status"] == "accepted"
    assert result["error_count"] == 0
    assert result["receipt_bundle_status"] == "accepted"
    assert result["receipt_bundle_kind_count"] == 7
    assert config["runtime_controls"]["require_oracle_authorization_for_isolated_settle_epoch"] is True
    assert "live_token_settlement_disabled" in result["go_live_blockers"]
    assert "does_not_claim_live_token_settlement" in result["not_claimed"]


def test_production_network_config_rejects_devnet_chain_id() -> None:
    config = sample_config()
    config["chain_id"] = "zenodex.oracle.local"

    result = check_config(config, sample_receipt_bundle(config))

    assert result["status"] == "rejected"
    assert "chain_id_must_be_production_candidate" in result["errors"]
    assert "config_id_mismatch" in result["errors"]


def test_production_network_config_rejects_weak_reporter_quorum_and_operator_concentration() -> None:
    config = sample_config()
    registry = config["reporter_registry"]
    registry["quorum"] = 4
    registry["registered_reporters"] = registry["registered_reporters"][:3]
    for reporter in registry["registered_reporters"]:
        reporter["operator_id"] = "operator.cartel"

    result = check_config(config, sample_receipt_bundle(config))

    assert result["status"] == "rejected"
    assert "registered_reporter_count_below_min" in result["errors"]
    assert "active_reporter_count_below_quorum" in result["errors"]
    assert "distinct_operator_count_below_quorum" in result["errors"]
    assert "operator_share_exceeds_policy:operator.cartel" in result["errors"]


def test_production_network_config_rejects_missing_signing_and_runtime_controls() -> None:
    config = sample_config()
    config["code_signing"]["required"] = False
    config["signing"]["receipt_signature_required"] = False
    del config["runtime_controls"]["DEX_ROUTING_ORACLE_ADAPTER_REQUIRED"]
    del config["runtime_controls"]["require_oracle_authorization_for_isolated_settle_epoch"]
    config["runtime_controls"]["ZUSD_ORACLE_ADAPTER_REQUIRED"] = False

    result = check_config(config, sample_receipt_bundle(config))

    assert result["status"] == "rejected"
    assert "required_must_be_true" in result["errors"]
    assert "receipt_signature_required_must_be_true" in result["errors"]
    assert "missing_runtime_control:DEX_ROUTING_ORACLE_ADAPTER_REQUIRED" in result["errors"]
    assert "missing_runtime_control:require_oracle_authorization_for_isolated_settle_epoch" in result["errors"]
    assert "runtime_control_not_enabled:ZUSD_ORACLE_ADAPTER_REQUIRED" in result["errors"]


def test_production_network_config_rejects_missing_explicit_non_claims() -> None:
    config = sample_config()
    config["not_claimed"] = ["does_not_claim_network_deployed"]

    result = check_config(config, sample_receipt_bundle(config))

    assert result["status"] == "rejected"
    assert "missing_not_claim:does_not_claim_live_token_settlement" in result["errors"]
    assert "missing_not_claim:does_not_claim_reporter_honesty" in result["errors"]


def test_production_network_config_rejects_missing_receipt_bundle() -> None:
    result = check_config(sample_config(), None)

    assert result["status"] == "rejected"
    assert result["receipt_bundle_status"] == "rejected"
    assert "receipt_bundle_rejected" in result["errors"]
    assert "receipt:receipt_bundle_required" in result["errors"]


def test_production_network_config_rejects_signed_release_artifact_drift() -> None:
    config = sample_config()
    bundle = sample_receipt_bundle(config)
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    release = next(receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "signed_release_artifact")
    payload = release["payload"]
    assert isinstance(payload, dict)
    payload["release_artifact_digest"] = "sha256:" + "0" * 64
    release["receipt_id"] = receipt_content_hash(release)

    result = check_config(config, bundle)

    assert result["status"] == "rejected"
    assert "receipt:signed_release_release_artifact_digest_mismatch" in result["errors"]


def test_production_network_config_rejects_release_transparency_log_root_drift() -> None:
    config = sample_config()
    bundle = sample_receipt_bundle(config)
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    release_log = next(
        receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "signed_release_transparency_log"
    )
    payload = release_log["payload"]
    assert isinstance(payload, dict)
    payload["release_transparency_log_root"] = "sha256:" + "9" * 64
    release_log["receipt_id"] = receipt_content_hash(release_log)

    result = check_config(config, bundle)

    assert result["status"] == "rejected"
    assert "receipt:signed_release_transparency_log_root_mismatch" in result["errors"]


def test_production_network_config_rejects_release_receipt_order_drift() -> None:
    config = sample_config()
    bundle = sample_receipt_bundle(config)
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    release = next(receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "signed_release_artifact")
    release_log = next(
        receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "signed_release_transparency_log"
    )
    release_log["block_number"] = int(release["block_number"]) - 1
    release_log["receipt_id"] = receipt_content_hash(release_log)

    result = check_config(config, bundle)

    assert result["status"] == "rejected"
    assert "receipt:receipt_order_invalid:signed_release_artifact->signed_release_transparency_log" in result["errors"]


def test_production_network_config_rejects_receipt_dependency_drift() -> None:
    cases = [
        (
            "feed_governance_deployment",
            "reporter_registry_deployment_receipt",
            "feed_governance_deployment_reporter_registry_receipt_mismatch",
        ),
        (
            "feed_governance_approval",
            "feed_governance_deployment_receipt",
            "feed_governance_approval_deployment_receipt_mismatch",
        ),
        (
            "feed_governance_execution",
            "feed_governance_approval_receipt",
            "feed_governance_execution_approval_receipt_mismatch",
        ),
        (
            "signed_release_artifact",
            "feed_governance_execution_receipt",
            "signed_release_feed_governance_execution_receipt_mismatch",
        ),
        (
            "signed_release_transparency_log",
            "signed_release_artifact_receipt",
            "signed_release_transparency_log_artifact_receipt_mismatch",
        ),
        (
            "runtime_controls_attestation",
            "signed_release_transparency_log_receipt",
            "runtime_controls_transparency_log_receipt_mismatch",
        ),
    ]
    for kind, payload_key, expected_error in cases:
        config = sample_config()
        bundle = sample_receipt_bundle(config)
        receipts = bundle["receipts"]
        assert isinstance(receipts, list)
        receipt = next(
            receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == kind
        )
        payload = receipt["payload"]
        assert isinstance(payload, dict)
        payload[payload_key] = "sha256:" + "8" * 64
        receipt["receipt_id"] = receipt_content_hash(receipt)

        result = check_config(config, bundle)

        assert result["status"] == "rejected"
        assert f"receipt:{expected_error}" in result["errors"]


def test_production_network_config_rejects_runtime_controls_receipt_drift() -> None:
    config = sample_config()
    bundle = sample_receipt_bundle(config)
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    runtime = next(receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "runtime_controls_attestation")
    payload = runtime["payload"]
    assert isinstance(payload, dict)
    payload["runtime_controls_hash"] = "sha256:" + "1" * 64
    runtime["receipt_id"] = receipt_content_hash(runtime)

    result = check_config(config, bundle)

    assert result["status"] == "rejected"
    assert "receipt:runtime_controls_hash_mismatch" in result["errors"]


def test_production_network_config_rejects_early_feed_governance_execution() -> None:
    config = sample_config()
    bundle = sample_receipt_bundle(config)
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    execution = next(
        receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "feed_governance_execution"
    )
    payload = execution["payload"]
    assert isinstance(payload, dict)
    payload["executed_at_timestamp"] = int(payload["executable_after_timestamp"]) - 1
    execution["receipt_id"] = receipt_content_hash(execution)

    result = check_config(config, bundle)

    assert result["status"] == "rejected"
    assert "receipt:feed_governance_execution_before_timelock" in result["errors"]


def test_production_network_config_rejects_feed_governance_proposal_drift() -> None:
    config = sample_config()
    bundle = sample_receipt_bundle(config)
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    approval = next(receipt for receipt in receipts if isinstance(receipt, dict) and receipt["kind"] == "feed_governance_approval")
    payload = approval["payload"]
    assert isinstance(payload, dict)
    payload["proposal_id"] = "sha256:" + "2" * 64
    approval["receipt_id"] = receipt_content_hash(approval)

    result = check_config(config, bundle)

    assert result["status"] == "rejected"
    assert "receipt:feed_governance_approval_proposal_id_mismatch" in result["errors"]


def test_production_network_config_cli_sample_and_require_live(tmp_path: Path) -> None:
    sample = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--sample",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0
    config_path = tmp_path / "production-network-config.json"
    config_path.write_text(sample.stdout, encoding="utf-8")
    sample_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--input",
            str(config_path),
            "--sample-receipts",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample_receipts.returncode == 0
    receipts_path = tmp_path / "production-network-receipts.json"
    receipts_path.write_text(sample_receipts.stdout, encoding="utf-8")

    missing_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--input",
            str(config_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert missing_receipts.returncode == 1
    missing_receipt = json.loads(missing_receipts.stdout)
    assert "receipt:receipt_bundle_required" in missing_receipt["errors"]

    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--input",
            str(config_path),
            "--receipts",
            str(receipts_path),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted.returncode == 0, accepted.stdout + accepted.stderr
    assert "status = accepted" in accepted.stdout
    assert "receipt_bundle_status = accepted" in accepted.stdout

    require_live = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_production_network_config.py",
            "--input",
            str(config_path),
            "--receipts",
            str(receipts_path),
            "--require-live",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert require_live.returncode == 1
    receipt = json.loads(require_live.stdout)
    assert receipt["status"] == "rejected"
    assert "go_live_blockers_present" in receipt["errors"]
