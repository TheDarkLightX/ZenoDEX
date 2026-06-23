from __future__ import annotations

from tools.zeno_ledger_chaos_harness import (
    run_chaos_harness,
    scenario_block_rejection_cross_product,
    scenario_canonical_hash_validation,
    scenario_checkpoint_byzantine_cross_product,
    scenario_equivocation,
    scenario_gossip_flood,
    scenario_invalid_recovery_certificate,
    scenario_malformed_blocks,
    scenario_malformed_checkpoints,
    scenario_partition_healing,
    scenario_partition_height_divergence,
    scenario_recovery_certificate_binding,
    scenario_risk_profile_shape,
    scenario_risk_vector_recovery_budget,
    scenario_state_transition_risk,
    scenario_sybil_peers,
    scenario_tau_rule_drift,
)
from tools.zeno_ledger_network_scenario import ChaosNetworkModel


def test_chaos_harness_runs_all_named_scenarios() -> None:
    report = run_chaos_harness()

    assert report["ok"] is True
    assert report["scenario_count"] == 22
    assert {item["scenario"] for item in report["scenarios"]} == {
        "auth_failures",
        "block_rejection_cross_product",
        "canonical_hash_validation",
        "checkpoint_byzantine_cross_product",
        "degraded_network",
        "equivocation",
        "fork_choice",
        "gossip_flood",
        "invalid_recovery_certificate",
        "live_quorum",
        "malformed_blocks",
        "malformed_checkpoints",
        "partition_healing",
        "partition_height_divergence",
        "peer_churn",
        "recovery_certificate_binding",
        "risk_profile_shape",
        "risk_vector_recovery_budget",
        "state_transition_risk",
        "sybil_peers",
        "tau_rule_drift",
        "validator_schedule",
    }


def test_gossip_flood_rejects_duplicate_envelope() -> None:
    report = scenario_gossip_flood()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["block_rejected:duplicate_gossip_envelope"] == 1
    assert metrics["block_rejected:gossip_oversized_tx_count"] == 1


def test_equivocation_emits_slashing_receipt() -> None:
    report = scenario_equivocation()
    node = report["model_report"]["nodes"]["node-a"]

    assert report["ok"] is True
    assert node["equivocation_event_count"] == 1
    assert node["slashing_receipt_count"] == 1


def test_network_model_rejects_wrong_chain_peer() -> None:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    result = model.admit_peer(node_id="node-a", peer_id="node-b", peer_chain_id="wrong")

    assert result["ok"] is False
    assert result["errors"] == ["peer_chain_id_mismatch"]


def test_network_model_rejects_wrong_network_peer() -> None:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    result = model.admit_peer(node_id="node-a", peer_id="node-b", peer_network_id="wrong")

    assert result["ok"] is False
    assert result["errors"] == ["peer_network_id_mismatch"]


def test_state_transition_risk() -> None:
    report = scenario_state_transition_risk()
    metrics = report["model_report"]["metrics"]
    node_a = report["model_report"]["nodes"]["node-a"]

    assert report["ok"] is True
    assert metrics["risk_transition_rejected:risk_increased_without_certificate"] == 1
    assert metrics["risk_transition_accepted"] == 1
    assert node_a["risk_profile"]["value_loss"] == 5


def test_partition_healing() -> None:
    report = scenario_partition_healing()
    metrics = report["model_report"]["metrics"]
    node_a = report["model_report"]["nodes"]["node-a"]
    node_b = report["model_report"]["nodes"]["node-b"]

    assert report["ok"] is True
    assert metrics["network_partitioned"] == 1
    assert metrics["network_healed"] == 1
    assert metrics["network_reconciled:fork_evidence"] == 1
    assert node_a["height"] == 1
    assert node_b["height"] == 1
    assert node_a["equivocation_event_count"] == 1
    assert node_b["equivocation_event_count"] == 1


def test_partition_height_divergence() -> None:
    report = scenario_partition_height_divergence()
    metrics = report["model_report"]["metrics"]
    node_a = report["model_report"]["nodes"]["node-a"]
    node_b = report["model_report"]["nodes"]["node-b"]

    assert report["ok"] is True
    assert metrics["network_partitioned"] == 1
    assert metrics["network_healed"] == 1
    assert metrics["network_reconciled:height_divergence"] == 1
    assert node_a["height"] == 2
    assert node_b["height"] == 1


def test_invalid_recovery_certificate() -> None:
    report = scenario_invalid_recovery_certificate()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["risk_transition_rejected:certificate_expired"] == 1
    assert metrics["risk_transition_rejected:recovery_cap_exceeded"] == 1
    assert metrics["risk_transition_rejected:invalid_certificate_schema"] == 1
    assert metrics["risk_transition_rejected:invalid_certificate_signature"] >= 1
    assert metrics["risk_transition_rejected:certificate_risk_mismatch"] == 1
    assert metrics["risk_transition_accepted"] == 1


def test_recovery_certificate_is_bound_to_node_chain_and_risk() -> None:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    model.add_node("node-b")
    next_risk = {"value_loss": 5}
    cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )

    wrong_node = model.validate_risk_transition(
        node_id="node-b",
        next_risk=next_risk,
        certificate=cert,
    )
    wrong_risk = model.validate_risk_transition(
        node_id="node-a",
        next_risk={"value_loss": 6},
        certificate=cert,
    )
    tampered_chain = dict(cert)
    tampered_chain["chain_id"] = "wrong-chain"
    wrong_chain = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=tampered_chain,
    )

    assert wrong_node["ok"] is False
    assert "certificate_node_mismatch" in wrong_node["errors"]
    assert wrong_risk["ok"] is False
    assert "certificate_risk_mismatch" in wrong_risk["errors"]
    assert wrong_chain["ok"] is False
    assert "certificate_chain_mismatch" in wrong_chain["errors"]


def test_recovery_certificate_binding_scenario() -> None:
    report = scenario_recovery_certificate_binding()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["risk_transition_rejected:certificate_node_mismatch"] == 1
    assert metrics["risk_transition_rejected:certificate_network_mismatch"] == 1
    assert metrics["risk_transition_rejected:certificate_chain_mismatch"] == 1
    assert metrics["risk_transition_rejected:recovery_amount_insufficient"] == 1
    assert metrics["risk_transition_rejected:certificate_replay"] == 1
    assert metrics["risk_transition_accepted"] == 1


def test_risk_vector_recovery_budget() -> None:
    report = scenario_risk_vector_recovery_budget()
    metrics = report["model_report"]["metrics"]
    node_a = report["model_report"]["nodes"]["node-a"]

    assert report["ok"] is True
    assert metrics["risk_transition_rejected:recovery_amount_insufficient"] == 1
    assert metrics["risk_transition_accepted"] == 2
    assert node_a["risk_profile"]["value_loss"] == 2
    assert node_a["risk_profile"]["replay_exposure"] == 1
    assert node_a["risk_profile"]["authority_drift"] == 0


def test_risk_profile_shape_rejects_unknown_and_invalid_values() -> None:
    report = scenario_risk_profile_shape()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["risk_transition_rejected:risk_component_unknown"] == 1
    assert metrics["risk_transition_rejected:risk_value_invalid"] == 2
    assert metrics["risk_transition_accepted"] == 1


def test_canonical_hash_validation_rejects_noncanonical_roots() -> None:
    report = scenario_canonical_hash_validation()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["block_rejected:wrong_body_root"] == 1
    assert metrics["block_rejected:wrong_checkpoint"] == 1
    assert metrics["block_accepted"] == 2


def test_block_rejection_cross_product_aggregates_errors_and_recovers() -> None:
    report = scenario_block_rejection_cross_product()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    for reason in (
        "duplicate_gossip_envelope",
        "auth_failed",
        "gossip_oversized_tx_count",
        "wrong_proposer",
        "wrong_previous_hash",
        "wrong_body_root",
        "wrong_checkpoint",
    ):
        assert metrics[f"block_rejected:{reason}"] == 1
    assert metrics["block_accepted"] == 2


def test_sybil_peers_rejects_peer_cap_exhaustion() -> None:
    report = scenario_sybil_peers()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["peer_admitted"] == 4
    assert metrics["peer_rejected:peer_cap_exceeded"] == 1


def test_malformed_blocks_rejects_bad_block_fields() -> None:
    report = scenario_malformed_blocks()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["block_rejected:invalid_height"] == 1
    assert metrics["block_rejected:wrong_body_root"] == 1
    assert metrics["block_rejected:wrong_checkpoint"] == 1


def test_malformed_checkpoints_rejects_bad_quorum_inputs() -> None:
    report = scenario_malformed_checkpoints()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["checkpoint_rejected:duplicate_checkpoint_signer"] == 1
    assert metrics["checkpoint_rejected:unknown_checkpoint_signer"] == 1
    assert metrics["checkpoint_rejected:checkpoint_payload_hash_invalid"] == 1


def test_checkpoint_byzantine_cross_product_aggregates_errors() -> None:
    report = scenario_checkpoint_byzantine_cross_product()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["checkpoint_rejected:duplicate_checkpoint_signer"] == 1
    assert metrics["checkpoint_rejected:unknown_checkpoint_signer"] == 1
    assert metrics["checkpoint_rejected:checkpoint_quorum_missing"] == 1
    assert metrics["checkpoint_rejected:checkpoint_payload_hash_invalid"] == 1
    assert metrics["checkpoint_accepted"] == 1


def test_tau_rule_drift_rejects_semantic_network_and_tamper_changes() -> None:
    report = scenario_tau_rule_drift()
    metrics = report["model_report"]["metrics"]

    assert report["ok"] is True
    assert metrics["tau_rule_accepted"] == 1
    assert metrics["tau_rule_rejected:tau_rule_commitment_hash_mismatch"] == 2
    assert metrics["tau_rule_rejected:tau_rule_commitment_tau_network_id_mismatch"] == 1
