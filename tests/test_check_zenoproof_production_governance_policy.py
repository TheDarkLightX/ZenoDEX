from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_zenoproof_production_governance_policy import (
    check_policy,
    policy_content_hash,
    receipt_content_hash,
    sample_policy,
    sample_receipt_bundle,
)

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "tools" / "zenoproof_registry_manifest.json"
ACCEPTED_REWARD_STATUS = {"status": "accepted", "errors": []}


def _registry() -> dict[str, object]:
    return json.loads(REGISTRY.read_text(encoding="utf-8"))


def _refresh(policy: dict[str, object]) -> None:
    policy["policy_id"] = policy_content_hash(policy)


def _receipt(bundle: dict[str, object], kind: str) -> dict[str, object]:
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    for receipt in receipts:
        assert isinstance(receipt, dict)
        if receipt.get("kind") == kind:
            return receipt
    raise AssertionError(f"missing receipt: {kind}")


def _check(policy: dict[str, object], registry: dict[str, object]) -> dict[str, object]:
    return check_policy(policy, registry, ACCEPTED_REWARD_STATUS, sample_receipt_bundle(policy, registry))


def test_zenoproof_production_governance_policy_accepts_sample_candidate() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, sample_receipt_bundle(policy, registry))

    assert result["schema"] == "zenodex.zenoproof.production_governance_policy_check.v1"
    assert result["status"] == "accepted"
    assert result["error_count"] == 0
    assert result["registry_error_count"] == 0
    assert result["reward_payout_status"] == "accepted"
    assert result["receipt_bundle_status"] == "accepted"
    assert result["receipt_bundle_kind_count"] == 7
    assert result["production_enabled_verifier_count"] == 8
    assert result["verifier_release_entry_count"] == 8
    assert result["devnet_only_verifier_count"] == 2
    assert result["production_verifier_path_lookup_count"] == 0
    assert "production_verifier_release_transparency_log_not_verified" not in result["go_live_blockers"]
    assert "live_proof_mining_token_settlement_not_enabled" in result["go_live_blockers"]
    assert "public_replay_verifiers_still_allow_path_lookup" not in result["go_live_blockers"]
    assert "does_not_claim_live_proof_network" in result["not_claimed"]


def test_zenoproof_production_governance_policy_rejects_policy_lowered_production_coverage() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    verifier_id = policy["verifier_policy"]["production_enabled_verifier_ids"][0]
    policy["verifier_policy"]["production_enabled_verifier_ids"] = [verifier_id]
    policy["verifier_policy"]["min_production_verifiers"] = 1
    policy["verifier_policy"]["min_distinct_proof_kinds"] = 1
    _refresh(policy)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert result["production_enabled_verifier_count"] == 1
    assert "min_production_verifiers_below_min:6" in result["errors"]
    assert "min_distinct_proof_kinds_below_min:6" in result["errors"]
    assert "production_verifier_count_below_required" in result["errors"]
    assert "distinct_proof_kind_count_below_required" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_duplicate_production_verifiers() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    verifier_id = policy["verifier_policy"]["production_enabled_verifier_ids"][0]
    policy["verifier_policy"]["production_enabled_verifier_ids"] = [verifier_id] * 6
    policy["verifier_policy"]["min_distinct_proof_kinds"] = 1
    _refresh(policy)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert result["production_enabled_verifier_count"] == 1
    assert f"production_verifier_duplicate:{verifier_id}" in result["errors"]
    assert "distinct_proof_kind_count_below_required" in result["errors"]

def test_zenoproof_production_governance_policy_rejects_static_verifier_not_quarantined() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    policy["verifier_policy"]["devnet_only_verifier_ids"] = []
    _refresh(policy)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert any(error.startswith("static_verifier_not_marked_devnet_only:") for error in result["errors"])


def test_zenoproof_production_governance_policy_rejects_devnet_verifier_enabled_for_production() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    devnet_id = policy["verifier_policy"]["devnet_only_verifier_ids"][0]
    policy["verifier_policy"]["production_enabled_verifier_ids"].append(devnet_id)
    _refresh(policy)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert "devnet_only_verifier_enabled_for_production" in result["errors"]
    assert f"production_verifier_execution_mode_invalid:{devnet_id}" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_production_path_lookup() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    verifier_id = policy["verifier_policy"]["production_enabled_verifier_ids"][0]
    for verifier in registry["verifiers"]:
        if verifier["verifier_id"] == verifier_id:
            verifier["allow_path_lookup"] = True
            break
    else:
        raise AssertionError(f"missing production verifier: {verifier_id}")
    policy = sample_policy(registry)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert result["production_verifier_path_lookup_count"] == 1
    assert f"production_verifier_path_lookup_enabled:{verifier_id}" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_weak_bridge_and_sandbox_controls() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    policy["oracle_bridge_policy"]["o3_receipt_required"] = False
    policy["oracle_bridge_policy"]["min_o5_distinct_verifier_count"] = 1
    policy["sandbox"]["network_disabled"] = False
    policy["sandbox"]["max_timeout_ms"] = 120_001
    _refresh(policy)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert "o3_receipt_required_must_be_true" in result["errors"]
    assert "min_o5_distinct_verifier_count_below_min:2" in result["errors"]
    assert "network_disabled_must_be_true" in result["errors"]
    assert "max_timeout_ms_above_max:120000" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_bad_governance_and_reward_controls() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    policy["governance"]["timelock_seconds"] = 1
    policy["code_signing"]["required"] = False
    policy["code_signing"]["verifier_release_manifest_digest"] = "sha256:" + "8" * 64
    policy["reward_settlement"]["bounded_pool_required"] = False
    policy["not_claimed"] = ["does_not_claim_live_proof_network"]
    _refresh(policy)

    result = _check(policy, registry)

    assert result["status"] == "rejected"
    assert "timelock_seconds_below_min:86400" in result["errors"]
    assert "required_must_be_true" in result["errors"]
    assert "verifier_release_manifest_digest_mismatch" in result["errors"]
    assert "bounded_pool_required_must_be_true" in result["errors"]
    assert "missing_not_claim:does_not_claim_live_proof_mining_payouts" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_reward_replay_failure() -> None:
    registry = _registry()
    result = check_policy(
        sample_policy(registry),
        registry,
        {"status": "rejected", "errors": ["proof_mining_payout_mismatch"]},
        sample_receipt_bundle(sample_policy(registry), registry),
    )

    assert result["status"] == "rejected"
    assert "reward_payout_replay_rejected" in result["errors"]
    assert "reward_payout:proof_mining_payout_mismatch" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_missing_receipt_bundle() -> None:
    registry = _registry()
    result = check_policy(sample_policy(registry), registry, ACCEPTED_REWARD_STATUS, None)

    assert result["status"] == "rejected"
    assert result["receipt_bundle_status"] == "rejected"
    assert "receipt_bundle_rejected" in result["errors"]
    assert "receipt:receipt_bundle_required" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_early_governance_execution_receipt() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    execution = _receipt(bundle, "governance_execution")
    payload = execution["payload"]
    assert isinstance(payload, dict)
    payload["executed_at_timestamp"] = int(payload["executable_after_timestamp"]) - 1
    execution["receipt_id"] = receipt_content_hash(execution)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:governance_execution_before_timelock" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_governance_execution_dependency_drift() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    execution = _receipt(bundle, "governance_execution")
    payload = execution["payload"]
    assert isinstance(payload, dict)
    payload["governance_approval_receipt"] = "sha256:" + "7" * 64
    execution["receipt_id"] = receipt_content_hash(execution)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:governance_execution_approval_receipt_mismatch" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_receipt_dependency_drift() -> None:
    registry = _registry()
    cases = [
        (
            "revocation_list",
            "governance_execution_receipt",
            "revocation_list_governance_execution_receipt_mismatch",
        ),
        (
            "revocation_drill",
            "governance_execution_receipt",
            "revocation_drill_governance_execution_receipt_mismatch",
        ),
        (
            "code_signing_attestation",
            "governance_execution_receipt",
            "code_signing_attestation_governance_execution_receipt_mismatch",
        ),
        (
            "verifier_release_transparency_log",
            "code_signing_attestation_receipt",
            "verifier_release_transparency_log_code_signing_receipt_mismatch",
        ),
        (
            "sandbox_attestation",
            "verifier_release_transparency_log_receipt",
            "sandbox_attestation_transparency_log_receipt_mismatch",
        ),
    ]
    for kind, payload_key, expected_error in cases:
        policy = sample_policy(registry)
        bundle = sample_receipt_bundle(policy, registry)
        receipt = _receipt(bundle, kind)
        payload = receipt["payload"]
        assert isinstance(payload, dict)
        payload[payload_key] = "sha256:" + "8" * 64
        receipt["receipt_id"] = receipt_content_hash(receipt)

        result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

        assert result["status"] == "rejected"
        assert f"receipt:{expected_error}" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_sandbox_attestation_drift() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    sandbox = _receipt(bundle, "sandbox_attestation")
    payload = sandbox["payload"]
    assert isinstance(payload, dict)
    payload["network_disabled"] = False
    sandbox["receipt_id"] = receipt_content_hash(sandbox)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:sandbox_attestation_network_disabled_mismatch" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_verifier_release_entry_drift() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    code_signing = _receipt(bundle, "code_signing_attestation")
    payload = code_signing["payload"]
    assert isinstance(payload, dict)
    entries = payload["verifier_release_entries"]
    assert isinstance(entries, list)
    first = entries[0]
    assert isinstance(first, dict)
    first["artifact_digest"] = "sha256:" + "9" * 64
    code_signing["receipt_id"] = receipt_content_hash(code_signing)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:code_signing_attestation_verifier_release_entries_mismatch" in result["errors"]


def test_zenoproof_production_governance_policy_binds_release_entries_to_sandbox_digests() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    code_signing = _receipt(bundle, "code_signing_attestation")
    payload = code_signing["payload"]
    assert isinstance(payload, dict)
    entries = payload["verifier_release_entries"]
    assert isinstance(entries, list)
    first = entries[0]
    assert isinstance(first, dict)
    sandbox = policy["sandbox"]
    assert isinstance(sandbox, dict)
    assert first["deterministic_worker_image_digest"] == sandbox["deterministic_worker_image_digest"]
    assert first["seccomp_profile_digest"] == sandbox["seccomp_profile_digest"]

    first["seccomp_profile_digest"] = "sha256:" + "1" * 64
    code_signing["receipt_id"] = receipt_content_hash(code_signing)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:code_signing_attestation_verifier_release_entries_mismatch" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_missing_transparency_log_observation() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    code_signing = _receipt(bundle, "code_signing_attestation")
    payload = code_signing["payload"]
    assert isinstance(payload, dict)
    payload["transparency_log_observed"] = False
    code_signing["receipt_id"] = receipt_content_hash(code_signing)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:code_signing_attestation_transparency_log_not_observed" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_transparency_log_root_drift() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    transparency_log = _receipt(bundle, "verifier_release_transparency_log")
    payload = transparency_log["payload"]
    assert isinstance(payload, dict)
    payload["transparency_log_root"] = "sha256:" + "9" * 64
    transparency_log["receipt_id"] = receipt_content_hash(transparency_log)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:verifier_release_transparency_log_root_mismatch" in result["errors"]


def test_zenoproof_production_governance_policy_rejects_receipt_order_drift() -> None:
    registry = _registry()
    policy = sample_policy(registry)
    bundle = sample_receipt_bundle(policy, registry)
    code_signing = _receipt(bundle, "code_signing_attestation")
    transparency_log = _receipt(bundle, "verifier_release_transparency_log")
    transparency_log["block_number"] = int(code_signing["block_number"]) - 1
    transparency_log["receipt_id"] = receipt_content_hash(transparency_log)

    result = check_policy(policy, registry, ACCEPTED_REWARD_STATUS, bundle)

    assert result["status"] == "rejected"
    assert "receipt:receipt_order_invalid:code_signing_attestation->verifier_release_transparency_log" in result["errors"]


def test_zenoproof_production_governance_policy_cli_sample_and_require_live(tmp_path: Path) -> None:
    sample = subprocess.run(
        [
            sys.executable,
            "tools/check_zenoproof_production_governance_policy.py",
            "--sample-policy",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0
    policy_path = tmp_path / "zenoproof-production-governance-policy.json"
    policy_path.write_text(sample.stdout, encoding="utf-8")
    sample_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zenoproof_production_governance_policy.py",
            "--sample-receipts",
            "--policy",
            str(policy_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample_receipts.returncode == 0
    receipts_path = tmp_path / "zenoproof-production-governance-receipts.json"
    receipts_path.write_text(sample_receipts.stdout, encoding="utf-8")

    missing_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zenoproof_production_governance_policy.py",
            "--policy",
            str(policy_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert missing_receipts.returncode == 1
    missing_receipts_obj = json.loads(missing_receipts.stdout)
    assert "receipt:receipt_bundle_required" in missing_receipts_obj["errors"]

    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zenoproof_production_governance_policy.py",
            "--policy",
            str(policy_path),
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
            "tools/check_zenoproof_production_governance_policy.py",
            "--policy",
            str(policy_path),
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
