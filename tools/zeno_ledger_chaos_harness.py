#!/usr/bin/env python3
"""Run deterministic ZenoLedger adversarial chaos scenarios."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_network_scenario import BlockEnvelope, ChaosNetworkModel, VALID_AUTH_TOKEN
from src.integration.zeno_ledger_tau_export import build_tau_rule_commitment_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.chaos_harness_report.v0"


def _base_model() -> ChaosNetworkModel:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    model.add_node("node-b")
    return model


def scenario_peer_churn() -> dict[str, Any]:
    model = _base_model()
    accepted = model.admit_peer(node_id="node-a", peer_id="node-b")
    duplicate = model.admit_peer(node_id="node-a", peer_id="node-b")
    wrong_chain = model.admit_peer(node_id="node-a", peer_id="node-c", peer_chain_id="wrong")
    wrong_network = model.admit_peer(node_id="node-a", peer_id="node-d", peer_network_id="wrong")
    return _scenario_report("peer_churn", model, [accepted, duplicate, wrong_chain, wrong_network])


def scenario_gossip_flood() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    first = model.submit_block(node_id="node-a", envelope=block)
    duplicate = model.submit_block(node_id="node-a", envelope=block)
    oversize = BlockEnvelope(
        **{**block.__dict__, "envelope_id": "oversize", "height": model.node("node-a").height + 1, "previous_hash": model.node("node-a").tip_hash, "tx_count": 101}
    )
    oversized = model.submit_block(node_id="node-a", envelope=oversize)
    return _scenario_report("gossip_flood", model, [first, duplicate, oversized])


def scenario_equivocation() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    first = model.submit_block(node_id="node-a", envelope=block)
    conflict = BlockEnvelope(
        envelope_id="conflict",
        height=block.height,
        previous_hash=block.previous_hash,
        block_hash="0x" + "12" * 32,
        proposer_id=block.proposer_id,
        body_root=block.body_root,
        checkpoint_hash=block.checkpoint_hash,
    )
    second = model.submit_block(node_id="node-a", envelope=conflict)
    return _scenario_report("equivocation", model, [first, second])


def scenario_fork_choice() -> dict[str, Any]:
    model = _base_model()
    block1 = model.make_block(node_id="node-a")
    accepted = model.submit_block(node_id="node-a", envelope=block1)
    stale = model.make_block(node_id="node-a", height=1, salt="stale")
    stale_result = model.submit_block(node_id="node-a", envelope=stale)
    extending = model.make_block(node_id="node-a", salt="extend")
    extend_result = model.submit_block(node_id="node-a", envelope=extending)
    return _scenario_report("fork_choice", model, [accepted, stale_result, extend_result])


def scenario_auth_failures() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    bad_auth = BlockEnvelope(**{**block.__dict__, "auth_token": "bad"})
    rejected = model.submit_block(node_id="node-a", envelope=bad_auth)
    accepted_block = BlockEnvelope(**{**block.__dict__, "envelope_id": "auth-valid-retry"})
    accepted = model.submit_block(node_id="node-a", envelope=accepted_block)
    return _scenario_report("auth_failures", model, [rejected, accepted])


def scenario_validator_schedule() -> dict[str, Any]:
    model = _base_model()
    wrong = model.make_block(node_id="node-a", proposer_id="validator-c")
    wrong_result = model.submit_block(node_id="node-a", envelope=wrong)
    right = model.make_block(node_id="node-a", proposer_id=model.scheduled_proposer(1), salt="right")
    right_result = model.submit_block(node_id="node-a", envelope=right)
    return _scenario_report("validator_schedule", model, [wrong_result, right_result])


def scenario_live_quorum() -> dict[str, Any]:
    model = _base_model()
    missing = model.checkpoint_quorum_check(node_id="node-a", payload_hash="0x" + "01" * 32, signers=["validator-a"])
    duplicate = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-a"],
    )
    good = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-b"],
    )
    return _scenario_report("live_quorum", model, [missing, duplicate, good])


def scenario_degraded_network() -> dict[str, Any]:
    model = _base_model()
    a1 = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a"))
    delayed = model.make_block(node_id="node-b", height=1, salt="delayed")
    delayed_result = model.submit_block(node_id="node-b", envelope=delayed)
    b2 = model.submit_block(node_id="node-b", envelope=model.make_block(node_id="node-b", salt="heal"))
    return _scenario_report("degraded_network", model, [a1, delayed_result, b2])


def scenario_state_transition_risk() -> dict[str, Any]:
    model = _base_model()
    next_risk = {"value_loss": 5}
    bad_attempt = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
    )
    cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )
    good_attempt = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=cert,
    )
    return _scenario_report("state_transition_risk", model, [bad_attempt, good_attempt])


def scenario_partition_healing() -> dict[str, Any]:
    model = _base_model()
    model.partition_node(node_id="node-a", peer_id="node-b")

    a1 = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a", salt="fork-a"))
    b1 = model.submit_block(node_id="node-b", envelope=model.make_block(node_id="node-b", salt="fork-b"))

    model.heal_partition(node_id="node-a", peer_id="node-b")
    reconcile = model.reconcile_after_heal(node_id="node-a", peer_id="node-b")

    return _scenario_report("partition_healing", model, [a1, b1, reconcile])


def scenario_partition_height_divergence() -> dict[str, Any]:
    model = _base_model()
    model.partition_node(node_id="node-a", peer_id="node-b")

    a1 = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a", salt="a1"))
    a2 = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a", salt="a2"))
    b1 = model.submit_block(node_id="node-b", envelope=model.make_block(node_id="node-b", salt="b1"))

    model.heal_partition(node_id="node-a", peer_id="node-b")
    reconcile = model.reconcile_after_heal(node_id="node-a", peer_id="node-b")

    return _scenario_report("partition_height_divergence", model, [a1, a2, b1, reconcile])


def scenario_invalid_recovery_certificate() -> dict[str, Any]:
    model = _base_model()
    next_risk = {"value_loss": 5}
    expired_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=-1,
        recovery_amount=5,
    )
    expired_result = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=expired_cert,
    )

    overcap_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=15,
    )
    overcap_result = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=overcap_cert,
    )

    schema_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )
    schema_cert["schema"] = "wrong"
    schema_result = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=schema_cert,
    )

    sig_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )
    sig_cert["signature"] = "invalid"
    sig_result = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=sig_cert,
    )

    risk_mismatch_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk={"value_loss": 4},
        expiration_epoch=10,
        recovery_amount=5,
    )
    risk_mismatch_result = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=risk_mismatch_cert,
    )

    good_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )
    good_result = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=good_cert,
    )

    return _scenario_report(
        "invalid_recovery_certificate",
        model,
        [expired_result, overcap_result, schema_result, sig_result, risk_mismatch_result, good_result],
    )


def scenario_recovery_certificate_binding() -> dict[str, Any]:
    model = _base_model()
    next_risk = {"value_loss": 5}
    valid_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )
    wrong_node = model.validate_risk_transition(
        node_id="node-b",
        next_risk=next_risk,
        certificate=valid_cert,
    )
    wrong_network_cert = dict(valid_cert)
    wrong_network_cert["network_id"] = "wrong-network"
    wrong_network = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=wrong_network_cert,
    )
    wrong_chain_cert = dict(valid_cert)
    wrong_chain_cert["chain_id"] = "wrong-chain"
    wrong_chain = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=wrong_chain_cert,
    )
    insufficient_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=4,
    )
    insufficient = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=insufficient_cert,
    )
    good = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=valid_cert,
    )
    replay = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=valid_cert,
    )
    return _scenario_report(
        "recovery_certificate_binding",
        model,
        [wrong_node, wrong_network, wrong_chain, insufficient, good, replay],
    )


def scenario_risk_vector_recovery_budget() -> dict[str, Any]:
    model = _base_model()
    next_risk = {"value_loss": 3, "replay_exposure": 2, "authority_drift": 1}
    insufficient_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=5,
    )
    insufficient = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=insufficient_cert,
    )
    exact_cert = model.build_recovery_certificate(
        node_id="node-a",
        next_risk=next_risk,
        expiration_epoch=10,
        recovery_amount=6,
    )
    exact = model.validate_risk_transition(
        node_id="node-a",
        next_risk=next_risk,
        certificate=exact_cert,
    )
    lower_risk = model.validate_risk_transition(
        node_id="node-a",
        next_risk={"value_loss": 2, "replay_exposure": 1, "authority_drift": 0},
    )
    return _scenario_report("risk_vector_recovery_budget", model, [insufficient, exact, lower_risk])


def scenario_risk_profile_shape() -> dict[str, Any]:
    model = _base_model()
    unknown = model.validate_risk_transition(node_id="node-a", next_risk={"unknown_risk": 1})
    negative = model.validate_risk_transition(node_id="node-a", next_risk={"value_loss": -1})
    bool_value = model.validate_risk_transition(node_id="node-a", next_risk={"value_loss": True})
    unchanged = model.validate_risk_transition(node_id="node-a", next_risk={"value_loss": 0})
    return _scenario_report("risk_profile_shape", model, [unknown, negative, bool_value, unchanged])


def scenario_canonical_hash_validation() -> dict[str, Any]:
    model = _base_model()
    valid_first = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a"))
    nonhex_body = BlockEnvelope(
        **{
            **model.make_block(node_id="node-a", salt="nonhex-body").__dict__,
            "body_root": "0x" + "zz" * 32,
        }
    )
    nonhex_body_result = model.submit_block(node_id="node-a", envelope=nonhex_body)
    uppercase_checkpoint = BlockEnvelope(
        **{
            **model.make_block(node_id="node-a", salt="uppercase-checkpoint").__dict__,
            "checkpoint_hash": "0x" + "AA" * 32,
        }
    )
    uppercase_checkpoint_result = model.submit_block(node_id="node-a", envelope=uppercase_checkpoint)
    valid_second = model.submit_block(
        node_id="node-a",
        envelope=model.make_block(node_id="node-a", salt="after-invalid-hashes"),
    )
    return _scenario_report(
        "canonical_hash_validation",
        model,
        [valid_first, nonhex_body_result, uppercase_checkpoint_result, valid_second],
    )


def scenario_block_rejection_cross_product() -> dict[str, Any]:
    model = _base_model()
    accepted = model.submit_block(node_id="node-a", envelope=model.make_block(node_id="node-a"))
    bad = BlockEnvelope(
        envelope_id="node-a:1:ok",
        height=2,
        previous_hash="0x" + "ff" * 32,
        block_hash="0x" + "12" * 32,
        proposer_id="validator-c",
        body_root="0x" + "zz" * 32,
        checkpoint_hash="not-a-hash",
        tx_count=101,
        auth_token="bad",
    )
    rejected = model.submit_block(node_id="node-a", envelope=bad)
    recovery = model.submit_block(
        node_id="node-a",
        envelope=model.make_block(node_id="node-a", salt="after-cross-product-reject"),
    )
    return _scenario_report("block_rejection_cross_product", model, [accepted, rejected, recovery])


def scenario_sybil_peers() -> dict[str, Any]:
    model = _base_model()
    results = []
    for i in range(4):
        results.append(model.admit_peer(node_id="node-a", peer_id=f"peer-{i}"))
    rejected = model.admit_peer(node_id="node-a", peer_id="peer-4")
    results.append(rejected)
    return _scenario_report("sybil_peers", model, results)


def scenario_malformed_blocks() -> dict[str, Any]:
    model = _base_model()
    block = model.make_block(node_id="node-a")
    valid_result = model.submit_block(node_id="node-a", envelope=block)

    invalid_height = BlockEnvelope(**{**block.__dict__, "envelope_id": "invalid_height", "height": 0})
    invalid_height_result = model.submit_block(node_id="node-a", envelope=invalid_height)

    wrong_body = BlockEnvelope(**{**block.__dict__, "envelope_id": "wrong_body", "body_root": "not-a-hash"})
    wrong_body_result = model.submit_block(node_id="node-a", envelope=wrong_body)

    wrong_checkpoint = BlockEnvelope(
        **{**block.__dict__, "envelope_id": "wrong_checkpoint", "checkpoint_hash": "not-a-hash"}
    )
    wrong_checkpoint_result = model.submit_block(node_id="node-a", envelope=wrong_checkpoint)

    return _scenario_report(
        "malformed_blocks",
        model,
        [valid_result, invalid_height_result, wrong_body_result, wrong_checkpoint_result],
    )


def scenario_malformed_checkpoints() -> dict[str, Any]:
    model = _base_model()
    duplicate = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-a"],
    )
    unknown = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "unknown-validator"],
    )
    bad_hash = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="not-a-hash",
        signers=["validator-a", "validator-b"],
    )
    good = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-b"],
    )
    return _scenario_report("malformed_checkpoints", model, [duplicate, unknown, bad_hash, good])


def scenario_checkpoint_byzantine_cross_product() -> dict[str, Any]:
    model = _base_model()
    bad = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="not-a-hash",
        signers=["validator-a", "validator-a", "unknown-validator"],
    )
    good = model.checkpoint_quorum_check(
        node_id="node-a",
        payload_hash="0x" + "01" * 32,
        signers=["validator-a", "validator-b"],
    )
    return _scenario_report("checkpoint_byzantine_cross_product", model, [bad, good])


def scenario_tau_rule_drift() -> dict[str, Any]:
    model = _base_model()
    stable = _tau_rule_commitment(revision=1)
    stable_hash = str(stable["tau_rule_commitment_hash"])
    accepted = model.validate_tau_rule_commitment(
        node_id="node-a",
        commitment=stable,
        expected_tau_network_id="tau-local",
        expected_tau_adapter_ref="zenodex-local-app-bridge-v0",
        expected_tau_rule_commitment_hash=stable_hash,
    )

    drifted_semantics = _tau_rule_commitment(revision=2)
    semantic_drift = model.validate_tau_rule_commitment(
        node_id="node-a",
        commitment=drifted_semantics,
        expected_tau_network_id="tau-local",
        expected_tau_adapter_ref="zenodex-local-app-bridge-v0",
        expected_tau_rule_commitment_hash=stable_hash,
    )

    wrong_network = _tau_rule_commitment(revision=1, tau_network_id="tau-fork")
    network_drift = model.validate_tau_rule_commitment(
        node_id="node-a",
        commitment=wrong_network,
        expected_tau_network_id="tau-local",
        expected_tau_adapter_ref="zenodex-local-app-bridge-v0",
        expected_tau_rule_commitment_hash=stable_hash,
    )

    tampered = dict(stable)
    tampered["semantic_contracts_hash"] = "0x" + "12" * 32
    tamper = model.validate_tau_rule_commitment(
        node_id="node-a",
        commitment=tampered,
        expected_tau_network_id="tau-local",
        expected_tau_adapter_ref="zenodex-local-app-bridge-v0",
        expected_tau_rule_commitment_hash=stable_hash,
    )

    return _scenario_report("tau_rule_drift", model, [accepted, semantic_drift, network_drift, tamper])


def _tau_rule_commitment(*, revision: int, tau_network_id: str = "tau-local") -> dict[str, Any]:
    return build_tau_rule_commitment_v0(
        tau_network_id=tau_network_id,
        tau_adapter_ref="zenodex-local-app-bridge-v0",
        tau_language_semantics_ref="tau-language:local-chaos",
        semantic_contracts={
            "schema": "zenodex.test.semantic-contracts.v0",
            "revision": revision,
            "specs": [{"contract_id": "settlement", "meaning": f"revision-{revision}"}],
        },
        supported_runtime_contract={
            "schema": "zenodex.test.supported-runtime.v0",
            "revision": revision,
            "execution_lanes": ["spec_mode_stable"],
        },
        spec_profiles={"schema": "zenodex.test.spec-profiles.v0", "revision": revision},
        active_spec_inventory={"schema": "zenodex.test.active-spec-inventory.v0", "revision": revision},
    )


SCENARIOS: dict[str, Callable[[], dict[str, Any]]] = {
    "peer_churn": scenario_peer_churn,
    "gossip_flood": scenario_gossip_flood,
    "equivocation": scenario_equivocation,
    "fork_choice": scenario_fork_choice,
    "auth_failures": scenario_auth_failures,
    "validator_schedule": scenario_validator_schedule,
    "live_quorum": scenario_live_quorum,
    "degraded_network": scenario_degraded_network,
    "state_transition_risk": scenario_state_transition_risk,
    "partition_healing": scenario_partition_healing,
    "partition_height_divergence": scenario_partition_height_divergence,
    "invalid_recovery_certificate": scenario_invalid_recovery_certificate,
    "recovery_certificate_binding": scenario_recovery_certificate_binding,
    "risk_vector_recovery_budget": scenario_risk_vector_recovery_budget,
    "risk_profile_shape": scenario_risk_profile_shape,
    "canonical_hash_validation": scenario_canonical_hash_validation,
    "block_rejection_cross_product": scenario_block_rejection_cross_product,
    "sybil_peers": scenario_sybil_peers,
    "malformed_blocks": scenario_malformed_blocks,
    "malformed_checkpoints": scenario_malformed_checkpoints,
    "checkpoint_byzantine_cross_product": scenario_checkpoint_byzantine_cross_product,
    "tau_rule_drift": scenario_tau_rule_drift,
}


def run_chaos_harness(selected: list[str] | None = None) -> dict[str, Any]:
    names = selected or sorted(SCENARIOS)
    scenario_reports = [SCENARIOS[name]() for name in names]
    errors: list[str] = []
    for report in scenario_reports:
        errors.extend(f"{report['scenario']}: {error}" for error in report["errors"])
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "scenario_count": len(scenario_reports),
        "scenarios": scenario_reports,
    }


def _scenario_report(name: str, model: ChaosNetworkModel, results: list[dict[str, Any]]) -> dict[str, Any]:
    report = model.report()
    errors = _invariant_errors(name, report, results)
    return {
        "schema": "zenodex.zeno_ledger.chaos_scenario_report.v0",
        "scenario": name,
        "ok": not errors,
        "errors": errors,
        "steps": results,
        "model_report": report,
    }


def _invariant_errors(name: str, report: dict[str, Any], results: list[dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    metrics = report["metrics"]
    if name == "gossip_flood" and metrics.get("block_rejected:duplicate_gossip_envelope", 0) < 1:
        errors.append("duplicate gossip envelope was not rejected")
    if name == "equivocation":
        node = report["nodes"]["node-a"]
        if node["equivocation_event_count"] < 1 or node["slashing_receipt_count"] < 1:
            errors.append("same-height conflict did not emit equivocation/slashing evidence")
    if name == "auth_failures" and metrics.get("block_rejected:auth_failed", 0) < 1:
        errors.append("auth failure was not rejected")
    if name == "validator_schedule" and metrics.get("block_rejected:wrong_proposer", 0) < 1:
        errors.append("wrong proposer was not rejected")
    if name == "live_quorum":
        if metrics.get("checkpoint_rejected:checkpoint_quorum_missing", 0) < 1:
            errors.append("missing quorum was not rejected")
        if metrics.get("checkpoint_accepted", 0) < 1:
            errors.append("valid checkpoint quorum was not accepted")
    if name == "peer_churn":
        if metrics.get("peer_rejected:duplicate_peer", 0) < 1:
            errors.append("duplicate peer was not rejected")
        if metrics.get("peer_rejected:peer_chain_id_mismatch", 0) < 1:
            errors.append("wrong-chain peer was not rejected")
        if metrics.get("peer_rejected:peer_network_id_mismatch", 0) < 1:
            errors.append("wrong-network peer was not rejected")
    if name == "state_transition_risk":
        if metrics.get("risk_transition_rejected:risk_increased_without_certificate", 0) < 1:
            errors.append("risk increase without certificate was not rejected")
        if metrics.get("risk_transition_accepted", 0) < 1:
            errors.append("valid certified risk transition was not accepted")
    if name == "partition_healing":
        if metrics.get("network_partitioned", 0) < 1 or metrics.get("network_healed", 0) < 1:
            errors.append("partition or heal event was not recorded")
        if (
            metrics.get("network_reconciled:same_tip", 0) < 1
            and metrics.get("network_reconciled:fork_evidence", 0) < 1
        ):
            errors.append("partition heal did not produce convergence or fork evidence")
    if name == "partition_height_divergence":
        if metrics.get("network_partitioned", 0) < 1 or metrics.get("network_healed", 0) < 1:
            errors.append("partition or heal event was not recorded")
        if metrics.get("network_reconciled:height_divergence", 0) < 1:
            errors.append("partition height divergence was not detected")
    if name == "invalid_recovery_certificate":
        if metrics.get("risk_transition_rejected:certificate_expired", 0) < 1:
            errors.append("expired certificate was not rejected")
        if metrics.get("risk_transition_rejected:recovery_cap_exceeded", 0) < 1:
            errors.append("over-cap recovery certificate was not rejected")
        if metrics.get("risk_transition_rejected:invalid_certificate_schema", 0) < 1:
            errors.append("invalid certificate schema was not rejected")
        if metrics.get("risk_transition_rejected:invalid_certificate_signature", 0) < 1:
            errors.append("invalid certificate signature was not rejected")
        if metrics.get("risk_transition_rejected:certificate_risk_mismatch", 0) < 1:
            errors.append("risk-mismatched recovery certificate was not rejected")
    if name == "recovery_certificate_binding":
        if metrics.get("risk_transition_rejected:certificate_node_mismatch", 0) < 1:
            errors.append("wrong-node recovery certificate was not rejected")
        if metrics.get("risk_transition_rejected:certificate_network_mismatch", 0) < 1:
            errors.append("wrong-network recovery certificate was not rejected")
        if metrics.get("risk_transition_rejected:certificate_chain_mismatch", 0) < 1:
            errors.append("wrong-chain recovery certificate was not rejected")
        if metrics.get("risk_transition_rejected:recovery_amount_insufficient", 0) < 1:
            errors.append("underfunded recovery certificate was not rejected")
        if metrics.get("risk_transition_rejected:certificate_replay", 0) < 1:
            errors.append("replayed recovery certificate was not rejected")
        if metrics.get("risk_transition_accepted", 0) < 1:
            errors.append("valid bound recovery certificate was not accepted")
    if name == "risk_vector_recovery_budget":
        if metrics.get("risk_transition_rejected:recovery_amount_insufficient", 0) < 1:
            errors.append("multi-component underfunded recovery certificate was not rejected")
        if metrics.get("risk_transition_accepted", 0) < 2:
            errors.append("multi-component exact recovery or lower-risk transition was not accepted")
    if name == "risk_profile_shape":
        if metrics.get("risk_transition_rejected:risk_component_unknown", 0) < 1:
            errors.append("unknown risk component was not rejected")
        if metrics.get("risk_transition_rejected:risk_value_invalid", 0) < 2:
            errors.append("invalid risk values were not rejected")
        if metrics.get("risk_transition_accepted", 0) < 1:
            errors.append("unchanged valid risk profile was not accepted")
    if name == "canonical_hash_validation":
        if metrics.get("block_rejected:wrong_body_root", 0) < 1:
            errors.append("non-hex body root was not rejected")
        if metrics.get("block_rejected:wrong_checkpoint", 0) < 1:
            errors.append("non-canonical checkpoint hash was not rejected")
        if metrics.get("block_accepted", 0) < 2:
            errors.append("valid blocks were not accepted around malformed hashes")
    if name == "block_rejection_cross_product":
        for reason in (
            "duplicate_gossip_envelope",
            "auth_failed",
            "gossip_oversized_tx_count",
            "wrong_proposer",
            "wrong_previous_hash",
            "wrong_body_root",
            "wrong_checkpoint",
        ):
            if metrics.get(f"block_rejected:{reason}", 0) < 1:
                errors.append(f"cross-product block rejection missed {reason}")
        if metrics.get("block_accepted", 0) < 2:
            errors.append("valid blocks were not accepted around cross-product block rejection")
    if name == "sybil_peers" and metrics.get("peer_rejected:peer_cap_exceeded", 0) < 1:
        errors.append("peer cap exceeded was not rejected")
    if name == "malformed_blocks":
        if metrics.get("block_rejected:invalid_height", 0) < 1:
            errors.append("invalid height was not rejected")
        if metrics.get("block_rejected:wrong_body_root", 0) < 1:
            errors.append("wrong body root was not rejected")
        if metrics.get("block_rejected:wrong_checkpoint", 0) < 1:
            errors.append("wrong checkpoint was not rejected")
    if name == "malformed_checkpoints":
        if metrics.get("checkpoint_rejected:duplicate_checkpoint_signer", 0) < 1:
            errors.append("duplicate checkpoint signer was not rejected")
        if metrics.get("checkpoint_rejected:unknown_checkpoint_signer", 0) < 1:
            errors.append("unknown checkpoint signer was not rejected")
        if metrics.get("checkpoint_rejected:checkpoint_payload_hash_invalid", 0) < 1:
            errors.append("invalid checkpoint payload hash was not rejected")
    if name == "checkpoint_byzantine_cross_product":
        for reason in (
            "duplicate_checkpoint_signer",
            "unknown_checkpoint_signer",
            "checkpoint_quorum_missing",
            "checkpoint_payload_hash_invalid",
        ):
            if metrics.get(f"checkpoint_rejected:{reason}", 0) < 1:
                errors.append(f"cross-product checkpoint rejection missed {reason}")
        if metrics.get("checkpoint_accepted", 0) < 1:
            errors.append("valid checkpoint was not accepted after cross-product rejection")
    if name == "tau_rule_drift":
        if metrics.get("tau_rule_accepted", 0) < 1:
            errors.append("valid Tau rule commitment was not accepted")
        for reason in (
            "tau_rule_commitment_hash_mismatch",
            "tau_rule_commitment_tau_network_id_mismatch",
        ):
            if metrics.get(f"tau_rule_rejected:{reason}", 0) < 1:
                errors.append(f"Tau rule drift rejection missed {reason}")
        if metrics.get("tau_rule_rejected:tau_rule_commitment_hash_mismatch", 0) < 2:
            errors.append("semantic drift and tampering did not both reject by commitment hash")
    if not any(step["ok"] for step in results):
        errors.append("scenario did not accept any valid action")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario", action="append", choices=sorted(SCENARIOS))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = run_chaos_harness(args.scenario)
    print(json.dumps(report, indent=2 if args.json else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
