from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

from tools import zenoproof_verify as zv


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "tools" / "zenoproof_registry_manifest.json"


def _manifest() -> dict[str, Any]:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def _rehash(artifact: dict[str, Any]) -> dict[str, Any]:
    artifact["proof_id"] = zv.artifact_content_hash(artifact)
    return artifact


LOCAL_TOOLCHAIN_REPLAY_FAILURE_PREFIXES = {
    zv.TLA_REPLAY_PROFILE: ("pytest_replay_skipped:",),
    zv.ESSO_REPLAY_PROFILE: ("pytest_replay_failed:",),
}


def test_manifest_accepts_sample_artifact_and_oracle_bridge() -> None:
    registry = _manifest()

    assert zv.verify_registry_manifest(registry) == []

    artifact_result = zv.verify_zenoproof_artifact(
        zv.sample_artifact(),
        registry,
        now_epoch=150,
    )
    assert artifact_result.status == "accepted"

    bridge_result = zv.verify_oracle_o4_bridge(
        zv.sample_oracle_o4_bridge(),
        registry,
        now_epoch=150,
    )
    assert bridge_result.status == "accepted"

    o5_bridge_result = zv.verify_oracle_o4_bridge(
        zv.sample_oracle_o5_bridge(),
        registry,
        now_epoch=150,
    )
    assert o5_bridge_result.status == "accepted"
    assert o5_bridge_result.o5_witness_status == "accepted"

    reward_result = zv.verify_reward_gate(
        zv.sample_reward_gate(),
        registry,
        now_epoch=150,
    )
    assert reward_result.status == "accepted"
    assert reward_result.checks["proof_ok"] is True
    assert reward_result.checks["binding_ok"] is True
    assert reward_result.checks["policy_ok"] is True
    assert reward_result.checks["unique_claim"] is True
    assert reward_result.checks["reward_pool_has_budget"] is True

    for profile in zv.PUBLIC_REPLAY_PROFILE_CONFIGS:
        try:
            public_replay_artifact = zv.sample_public_replay_artifact(profile)
        except ValueError as exc:
            assert profile in LOCAL_TOOLCHAIN_REPLAY_FAILURE_PREFIXES
            assert str(exc).startswith(LOCAL_TOOLCHAIN_REPLAY_FAILURE_PREFIXES[profile])
            failed_replay_result = zv._public_replay_failed_result(profile, exc)
            assert failed_replay_result.status == "rejected"
            assert failed_replay_result.proof_ok is False
            assert failed_replay_result.errors == [
                "public_replay_sample_failed:"
                f"{profile}:ValueError:{exc}"
            ]
            continue
        public_replay_result = zv.verify_zenoproof_artifact(
            public_replay_artifact,
            registry,
            now_epoch=150,
        )
        assert public_replay_result.status == "accepted"
        assert public_replay_result.proof_ok is True
        assert public_replay_result.binding_ok is True


def test_unknown_artifact_field_rejects_fail_closed() -> None:
    artifact = zv.sample_artifact()
    artifact["unexpected"] = "extra"
    _rehash(artifact)

    result = zv.verify_zenoproof_artifact(artifact, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "unknown_artifact_field:unexpected" in result.errors
    assert not result.proof_ok


def test_stale_verifier_policy_rejects() -> None:
    artifact = zv.sample_artifact()
    artifact["verifier_policy_root"] = zv.sample_hash("stale.policy")
    _rehash(artifact)

    result = zv.verify_zenoproof_artifact(artifact, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "verifier_policy_root_stale" in result.errors
    assert not result.policy_ok


def test_wrong_claim_binding_rejects() -> None:
    result = zv.verify_zenoproof_artifact(
        zv.sample_artifact(),
        _manifest(),
        now_epoch=150,
        expected_claim_id=zv.sample_hash("wrong.claim"),
    )

    assert result.status == "rejected"
    assert "expected_claim_id_mismatch" in result.errors
    assert not result.binding_ok


def test_unknown_proof_kind_rejects() -> None:
    artifact = zv.sample_artifact()
    artifact["proof_kind"] = "unknown_kind"
    _rehash(artifact)

    result = zv.verify_zenoproof_artifact(artifact, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "proof_kind_invalid" in result.errors
    assert "proof_kind_not_allowed" in result.errors


def test_external_verifier_timeout_rejects_even_if_child_would_print_ok() -> None:
    registry = zv.sample_registry()
    verifier = registry["verifiers"][0]
    verifier["verifier_id"] = zv.sample_hash("slow.verifier")
    verifier["current_policy_root"] = zv.sample_hash("slow.policy")
    verifier["toolchain_ids"] = [zv.sample_hash("slow.toolchain")]
    verifier["execution_mode"] = "subprocess_json"
    verifier["verifier_command"] = [
        sys.executable,
        "-c",
        "import time; time.sleep(1); print('{\"ok\": true}')",
    ]
    verifier["allow_path_lookup"] = False
    verifier["timeout_ms"] = 10

    artifact = zv.sample_artifact()
    artifact["verifier_id"] = verifier["verifier_id"]
    artifact["verifier_policy_root"] = verifier["current_policy_root"]
    artifact["toolchain_id"] = verifier["toolchain_ids"][0]
    _rehash(artifact)

    result = zv.verify_zenoproof_artifact(artifact, registry, now_epoch=150)

    assert result.status == "rejected"
    assert "external_verifier_failed:proof verification timed out" in result.errors
    assert not result.proof_ok


def test_public_replay_verifier_rejects_wrong_output_root() -> None:
    artifact = zv.sample_public_replay_artifact()
    artifact["output_commitment_root"] = zv.sample_hash("wrong.public.replay.output")
    _rehash(artifact)

    result = zv.verify_zenoproof_artifact(artifact, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "external_verifier_failed:output_commitment_root_mismatch" in result.errors
    assert not result.proof_ok


def test_oracle_o4_bridge_rejects_wrong_proof_input_binding() -> None:
    bridge = zv.sample_oracle_o4_bridge()
    bridge["proof_artifact"] = zv.sample_artifact(
        input_commitment_root=zv.sample_hash("wrong.oracle.input")
    )
    bridge["bridge_id"] = zv.oracle_o4_bridge_content_hash(bridge)

    result = zv.verify_oracle_o4_bridge(bridge, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "proof:expected_input_commitment_root_mismatch" in result.errors


def test_oracle_o5_bridge_rejects_missing_independence_witness() -> None:
    bridge = zv.sample_oracle_o5_bridge()
    del bridge["o5_independence_witness"]
    bridge["bridge_id"] = zv.oracle_o4_bridge_content_hash(bridge)

    result = zv.verify_oracle_o4_bridge(bridge, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "o5_independence_witness_required" in result.errors


def test_oracle_o5_bridge_rejects_weak_independence_witness() -> None:
    bridge = zv.sample_oracle_o5_bridge()
    witness = bridge["o5_independence_witness"]
    witness["required_distinct_verifier_count"] = 3
    witness["witness_id"] = zv.o5_independence_witness_content_hash(witness)
    bridge["bridge_id"] = zv.oracle_o4_bridge_content_hash(bridge)

    result = zv.verify_oracle_o4_bridge(bridge, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert "o5_independence_witness_not_accepted" in result.errors
    assert "o5_witness:distinct_verifier_count_below_required" in result.errors


def test_registry_rejects_missing_dependency_and_claim_cycle() -> None:
    registry = _manifest()
    registry["claims"][0]["dependency_claim_ids"] = [zv.sample_hash("missing.dependency")]

    missing_errors = zv.verify_registry_manifest(registry)

    assert any(error.startswith("claim_dependency_missing:") for error in missing_errors)

    registry = _manifest()
    registry["claims"][0]["dependency_claim_ids"] = [registry["claims"][1]["claim_id"]]
    registry["claims"][1]["dependency_claim_ids"] = [registry["claims"][0]["claim_id"]]

    cycle_errors = zv.verify_registry_manifest(registry)

    assert any(error.startswith("claim_dependency_cycle:") for error in cycle_errors)


def test_reward_gate_rejects_duplicate_claim() -> None:
    gate = zv.sample_reward_gate()
    gate["previously_rewarded_claim_ids"] = [gate["proof_artifact"]["claim_id"]]

    result = zv.verify_reward_gate(gate, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert result.checks["unique_claim"] is False
    assert "claim_already_rewarded" in result.errors


def test_reward_gate_rejects_budget_mismatch() -> None:
    gate = zv.sample_reward_gate()
    gate["reward_pool_after_e8"] = gate["reward_pool_before_e8"]

    result = zv.verify_reward_gate(gate, _manifest(), now_epoch=150)

    assert result.status == "rejected"
    assert result.checks["reward_pool_has_budget"] is False
    assert "reward_amount_mismatch" in result.errors


def test_reward_gate_rejects_failed_policy_or_binding() -> None:
    gate = zv.sample_reward_gate()
    gate["proof_artifact"]["verifier_policy_root"] = zv.sample_hash("stale.policy")
    gate["proof_artifact"] = _rehash(gate["proof_artifact"])

    policy_result = zv.verify_reward_gate(gate, _manifest(), now_epoch=150)

    assert policy_result.status == "rejected"
    assert policy_result.checks["policy_ok"] is False
    assert "proof:verifier_policy_root_stale" in policy_result.errors

    binding_gate = zv.sample_reward_gate()
    binding_gate["expected_input_commitment_root"] = zv.sample_hash("wrong.reward.input")

    binding_result = zv.verify_reward_gate(binding_gate, _manifest(), now_epoch=150)

    assert binding_result.status == "rejected"
    assert binding_result.checks["binding_ok"] is False
    assert "proof:expected_input_commitment_root_mismatch" in binding_result.errors
