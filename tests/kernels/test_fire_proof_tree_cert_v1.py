from __future__ import annotations

import pytest

from src.fire.registry.replay_input_v1 import FireReplayInput
from src.fire.verifier.proof_tree_cert_v1 import (
    expected_fire_proof_tree_replay_summary,
    verify_fire_proof_tree_certificate,
)


OBJECT_HASH = "sha256:" + ("1" * 64)
INSTANCE_HASH = "sha256:" + ("2" * 64)
CERTIFICATE_SHA256 = "sha256:" + ("4" * 64)
REPLAY_INPUT_SHA256 = "sha256:" + ("5" * 64)
KERNEL_SETTLEMENT_RECEIPT_SHA256 = "sha256:" + ("6" * 64)


def _replay_input() -> FireReplayInput:
    return FireReplayInput(
        object_name="BurnBoostCall",
        object_version="v1",
        object_family="capped_index_call",
        object_hash=OBJECT_HASH,
        instance_hash=INSTANCE_HASH,
        holder_posted=0,
        writer_posted=30,
        holder_balance=100,
        writer_balance=250,
        witness_inputs={"witness_final": 7},
    )


def _valid_payload() -> dict[str, object]:
    return {
        "version": "FIRE_CERT_RULES_v0.1",
        "object_hash": OBJECT_HASH,
        "instance_hash": INSTANCE_HASH,
        "certificate_sha256": CERTIFICATE_SHA256,
        "runtime_certificate_summary": {
            "root_rule": "min",
            "root_interval": {"lower": 0, "upper": 3},
            "node_count": 3,
            "exact_params": [{"name": "cap_index", "value": 3}],
            "source_bounds": [{"name": "burn_final", "lower": 0, "upper": 9}],
            "operator_tree": {
                "rule": "min",
                "lower": 0,
                "upper": 3,
                "children": [
                    {
                        "rule": "source_bound",
                        "name": "burn_final",
                        "lower": 0,
                        "upper": 9,
                        "children": [],
                    },
                    {
                        "rule": "exact_param",
                        "name": "cap_index",
                        "lower": 3,
                        "upper": 3,
                        "children": [],
                    },
                ],
            },
        },
        "dependency_hashes": [
            {
                "name": "burn_index_v1",
                "version": "1.0.0",
                "hash": "sha256:" + ("3" * 64),
            }
        ],
        "evidence_floor": "contract",
        "claims": {
            "BoundOK": {
                "evidence": "proved",
                "claim": "0 <= payoff <= cap",
                "root_node": "n_bound",
            },
            "CollateralOK": {
                "evidence": "contract",
                "claim": "writer collateral >= cap",
                "root_node": "n_collateral",
            },
        },
        "proof_tree": [
            {
                "id": "n_bound_expr_0",
                "rule": "source_bound",
                "claim": {
                    "predicate": "BoundLeafSourceBound",
                    "name": "burn_final",
                    "lower": "0",
                    "upper": "9",
                },
                "evidence": "proved",
            },
            {
                "id": "n_bound_expr_1",
                "rule": "exact_param",
                "claim": {
                    "predicate": "BoundLeafExactParam",
                    "name": "cap_index",
                    "value": "3",
                    "lower": "3",
                    "upper": "3",
                },
                "evidence": "proved",
            },
            {
                "id": "n_bound_expr",
                "rule": "interval_min",
                "claim": {
                    "predicate": "BoundExpr",
                    "runtime_rule": "min",
                    "lower": "0",
                    "upper": "3",
                },
                "inputs": ["n_bound_expr_0", "n_bound_expr_1"],
                "evidence": "proved",
            },
            {
                "id": "n_bound",
                "rule": "witness_bound_intro",
                "claim": {
                    "predicate": "BoundOK",
                    "lower": "0",
                    "upper": "3",
                    "runtime_root_rule": "min",
                    "runtime_node_count": "3",
                },
                "inputs": ["n_bound_expr"],
                "evidence": "proved",
            },
            {
                "id": "n_collateral",
                "rule": "collateral_one_sided_writer",
                "claim": {
                    "predicate": "CollateralOK",
                    "party": "writer",
                    "asset": "zUSD",
                },
                "inputs": ["n_bound"],
                "evidence": "contract",
            },
        ],
    }


def test_verify_fire_proof_tree_certificate_accepts_repo_sha256_draft() -> None:
    ok, err, verification = verify_fire_proof_tree_certificate(
        _valid_payload(),
        expected_object_hash=OBJECT_HASH,
        expected_instance_hash=INSTANCE_HASH,
        expected_certificate_sha256=CERTIFICATE_SHA256,
        expected_claim_evidence={
            "BoundOK": "proved",
            "CollateralOK": "contract",
        },
    )

    assert ok is True, err
    assert verification is not None
    assert verification.object_hash == OBJECT_HASH
    assert verification.instance_hash == INSTANCE_HASH
    assert verification.certificate_sha256 == CERTIFICATE_SHA256
    assert verification.evidence_floor == "contract"
    assert verification.claim_count == 2
    assert verification.proof_node_count == 5


def test_expected_fire_proof_tree_replay_summary_requires_bool_firev_accept() -> None:
    kernel_settlement_receipt = {
        "holder_delta": 0,
        "writer_delta": 0,
        "payoff_out": 0,
        "firev_accept": "false",
    }

    with pytest.raises(TypeError, match="kernel_settlement_receipt.firev_accept must be a bool"):
        expected_fire_proof_tree_replay_summary(
            _replay_input(),
            replay_input_sha256=REPLAY_INPUT_SHA256,
            kernel_settlement_receipt=kernel_settlement_receipt,
            kernel_settlement_receipt_sha256=KERNEL_SETTLEMENT_RECEIPT_SHA256,
        )


def test_expected_fire_proof_tree_replay_summary_requires_integer_deltas() -> None:
    kernel_settlement_receipt = {
        "holder_delta": "0",
        "writer_delta": 0,
        "payoff_out": 0,
        "firev_accept": True,
    }

    with pytest.raises(TypeError, match="kernel_settlement_receipt.holder_delta must be an int"):
        expected_fire_proof_tree_replay_summary(
            _replay_input(),
            replay_input_sha256=REPLAY_INPUT_SHA256,
            kernel_settlement_receipt=kernel_settlement_receipt,
            kernel_settlement_receipt_sha256=KERNEL_SETTLEMENT_RECEIPT_SHA256,
        )


def test_verify_fire_proof_tree_certificate_rejects_bad_evidence_floor() -> None:
    payload = _valid_payload()
    payload["evidence_floor"] = "proved"

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_evidence_floor_mismatch"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_missing_root_node_reference() -> None:
    payload = _valid_payload()
    claims = payload["claims"]
    assert isinstance(claims, dict)
    claim = claims["BoundOK"]
    assert isinstance(claim, dict)
    claim["root_node"] = "missing_node"

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_missing_root_node:BoundOK:missing_node"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_unknown_rule_id() -> None:
    payload = _valid_payload()
    proof_tree = payload["proof_tree"]
    assert isinstance(proof_tree, list)
    node = proof_tree[0]
    assert isinstance(node, dict)
    node["rule"] = "nonexistent_rule"

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_unknown_rule:nonexistent_rule"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_rule_predicate_mismatch() -> None:
    payload = _valid_payload()
    proof_tree = payload["proof_tree"]
    assert isinstance(proof_tree, list)
    node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_collateral")
    assert isinstance(node, dict)
    node["rule"] = "interval_min"

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_rule_predicate_mismatch:n_collateral"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_root_predicate_mismatch() -> None:
    payload = _valid_payload()
    claims = payload["claims"]
    assert isinstance(claims, dict)
    claim = claims["BoundOK"]
    assert isinstance(claim, dict)
    claim["root_node"] = "n_collateral"

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_claim_root_predicate_mismatch:BoundOK"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_rule_input_predicate_mismatch() -> None:
    payload = _valid_payload()
    proof_tree = payload["proof_tree"]
    assert isinstance(proof_tree, list)
    node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_collateral")
    assert isinstance(node, dict)
    node["inputs"] = ["n_bound_expr"]

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_rule_input_predicates_mismatch:n_collateral"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_mismatched_certificate_sha256() -> None:
    payload = _valid_payload()

    ok, err, verification = verify_fire_proof_tree_certificate(
        payload,
        expected_certificate_sha256="sha256:" + ("9" * 64),
    )

    assert ok is False
    assert err == "proof_tree_cert_certificate_sha256_mismatch"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_runtime_summary_mismatch() -> None:
    payload = _valid_payload()

    ok, err, verification = verify_fire_proof_tree_certificate(
        payload,
        expected_runtime_certificate_summary={
            "root_rule": "mul",
            "root_interval": {"lower": 0, "upper": 30},
            "node_count": 7,
            "exact_params": [{"name": "n_notional", "value": 10}],
            "source_bounds": [{"name": "burn_final", "lower": 0, "upper": 9}],
            "operator_tree": {
                "rule": "mul",
                "lower": 0,
                "upper": 30,
                "children": [
                    {
                        "rule": "exact_param",
                        "name": "n_notional",
                        "lower": 10,
                        "upper": 10,
                        "children": [],
                    },
                    {
                        "rule": "min",
                        "lower": 0,
                        "upper": 3,
                        "children": [
                            {
                                "rule": "source_bound",
                                "name": "burn_final",
                                "lower": 0,
                                "upper": 9,
                                "children": [],
                            },
                            {
                                "rule": "exact_param",
                                "name": "cap_index",
                                "lower": 3,
                                "upper": 3,
                                "children": [],
                            },
                        ],
                    },
                ],
            },
        },
    )

    assert ok is False
    assert err == "proof_tree_cert_runtime_certificate_summary_mismatch"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_bound_interval_mismatch() -> None:
    payload = _valid_payload()
    proof_tree = payload["proof_tree"]
    assert isinstance(proof_tree, list)
    bound_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_bound")
    assert isinstance(bound_node, dict)
    claim = bound_node["claim"]
    assert isinstance(claim, dict)
    claim["upper"] = "4"

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_bound_upper_mismatch"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_missing_exact_param_leaf() -> None:
    payload = _valid_payload()
    proof_tree = payload["proof_tree"]
    assert isinstance(proof_tree, list)
    payload["proof_tree"] = [node for node in proof_tree if not (isinstance(node, dict) and node.get("id") == "n_bound_expr_1")]

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_missing_input_node:n_bound_expr_1"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_unlinked_source_bound_leaf() -> None:
    payload = _valid_payload()
    proof_tree = payload["proof_tree"]
    assert isinstance(proof_tree, list)
    bound_node = next(node for node in proof_tree if isinstance(node, dict) and node.get("id") == "n_bound_expr")
    assert isinstance(bound_node, dict)
    bound_node["inputs"] = ["n_bound_expr_1"]

    ok, err, verification = verify_fire_proof_tree_certificate(payload)

    assert ok is False
    assert err == "proof_tree_cert_bound_expr_inputs_mismatch:n_bound_expr"
    assert verification is None
