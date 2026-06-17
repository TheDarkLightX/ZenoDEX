from __future__ import annotations

import pytest

import src.fire.verifier.proof_tree_cert_v1 as proof_tree
from src.fire.verifier.cert_v1 import FireCertNode, FireIntervalCertificate
from src.fire.verifier.proof_tree_cert_v1 import (
    _build_bound_proof_nodes,
    expected_fire_proof_tree_integer_eval_summary,
    summarize_fire_interval_certificate,
    verify_fire_proof_tree_certificate,
)

OBJECT_HASH = "sha256:" + ("1" * 64)
INSTANCE_HASH = "sha256:" + ("2" * 64)
CERTIFICATE_SHA256 = "sha256:" + ("4" * 64)


def _malformed_node(**fields: object) -> FireCertNode:
    node = object.__new__(FireCertNode)
    defaults = {
        "rule": "exact_param",
        "lower": 0,
        "upper": 0,
        "value": None,
        "name": None,
        "children": (),
    }
    defaults.update(fields)
    for name, value in defaults.items():
        object.__setattr__(node, name, value)
    return node


def test_summarize_fire_interval_certificate_rejects_missing_exact_param_name_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="exact_param", name=None))

    with pytest.raises(ValueError, match="exact_param runtime certificate node missing name"):
        summarize_fire_interval_certificate(certificate)


def test_summarize_fire_interval_certificate_rejects_missing_source_bound_name_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="source_bound", name=None))

    with pytest.raises(ValueError, match="source_bound runtime certificate node missing name"):
        summarize_fire_interval_certificate(certificate)


def test_integer_eval_summary_rejects_malformed_exact_param_summary_without_assert(monkeypatch: pytest.MonkeyPatch) -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="const", value=0))

    def bad_summary(_certificate: FireIntervalCertificate) -> dict[str, object]:
        return {
            "root_rule": "const",
            "root_interval": {"lower": 0, "upper": 0},
            "node_count": 1,
            "exact_params": {},
            "source_bounds": [],
            "operator_tree": {},
        }

    monkeypatch.setattr(proof_tree, "summarize_fire_interval_certificate", bad_summary)

    with pytest.raises(TypeError, match="exact_params must be a list"):
        expected_fire_proof_tree_integer_eval_summary(certificate)


def test_build_bound_proof_nodes_rejects_malformed_children_without_assert() -> None:
    with pytest.raises(TypeError, match="runtime operator node children must be a list"):
        _build_bound_proof_nodes({"rule": "const", "children": "bad"}, evidence="implemented")


def _valid_proof_tree_payload() -> dict[str, object]:
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


def test_verify_fire_proof_tree_certificate_rejects_missing_predicate_without_assert(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(proof_tree, "_proof_tree_node_predicate", lambda _node_id, _node_map: (True, None, None))

    ok, err, verification = verify_fire_proof_tree_certificate(_valid_proof_tree_payload())

    assert ok is False
    assert err == "proof_tree_cert_predicate_missing:n_bound_expr_0"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_missing_predicate_error_without_assert(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(proof_tree, "_proof_tree_node_predicate", lambda _node_id, _node_map: (False, None, None))

    ok, err, verification = verify_fire_proof_tree_certificate(_valid_proof_tree_payload())

    assert ok is False
    assert err == "proof_tree_cert_predicate_error_missing:n_bound_expr_0"
    assert verification is None


def test_verify_fire_proof_tree_certificate_rejects_missing_bound_error_without_assert(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(proof_tree, "_verify_bound_proof_tree_node", lambda *_args, **_kwargs: (False, None))

    ok, err, verification = verify_fire_proof_tree_certificate(_valid_proof_tree_payload())

    assert ok is False
    assert err == "proof_tree_cert_bound_error_missing"
    assert verification is None
