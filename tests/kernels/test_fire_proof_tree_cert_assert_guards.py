from __future__ import annotations

import pytest

import src.fire.verifier.proof_tree_cert_v1 as proof_tree
from src.fire.verifier.cert_v1 import FireCertNode, FireIntervalCertificate
from src.fire.verifier.proof_tree_cert_v1 import (
    _build_bound_proof_nodes,
    expected_fire_proof_tree_integer_eval_summary,
    summarize_fire_interval_certificate,
)


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
