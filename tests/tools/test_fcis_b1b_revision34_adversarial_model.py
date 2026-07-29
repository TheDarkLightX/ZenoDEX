from __future__ import annotations

import dataclasses

from tools.fcis_b1b_revision34_adversarial_model import (
    UpdateFacts,
    UpdateModelCode,
    _topological_order,
    build_report,
    derive_revision34_update,
    derive_unsafe_admit_then_root_update,
    receipt_cycle_mutant_edges,
    revision34_dependency_edges,
)


def _valid() -> UpdateFacts:
    return UpdateFacts(*(True for _ in range(10)))


def test_exhaustive_guard_model_has_one_accepting_assignment() -> None:
    report = build_report()
    assert report["cases"] == 1_024
    assert report["safe_accepts"] == 1
    assert report["all_guards_required_for_accept"] is True
    assert report["unsafe_semantically_invalid_accepts"] > 0


def test_each_semantic_guard_is_individually_necessary() -> None:
    expected = {
        "algorithm_matches": UpdateModelCode.ALGORITHM_REJECT,
        "language_matches": UpdateModelCode.LANGUAGE_REJECT,
        "policy_root_matches": UpdateModelCode.POLICY_ROOT_REJECT,
        "embedded_configuration_root_matches": UpdateModelCode.EMBEDDED_ROOT_REJECT,
        "command_root_matches": UpdateModelCode.COMMAND_ROOT_REJECT,
        "deployment_matches": UpdateModelCode.DEPLOYMENT_REJECT,
        "domain_matches": UpdateModelCode.DOMAIN_REJECT,
        "version_increments": UpdateModelCode.VERSION_REJECT,
        "activation_is_successor_sequence": UpdateModelCode.ACTIVATION_REJECT,
    }
    valid = _valid()
    for name, code in expected.items():
        mutant = dataclasses.replace(valid, **{name: False})
        assert derive_revision34_update(mutant) is code


def test_refuted_admit_then_root_shape_accepts_invalid_algorithm_and_roots() -> None:
    invalid_algorithm = dataclasses.replace(_valid(), algorithm_matches=False)
    wrong_policy_root = dataclasses.replace(_valid(), policy_root_matches=False)
    wrong_embedded_root = dataclasses.replace(
        _valid(),
        embedded_configuration_root_matches=False,
    )

    for mutant in (invalid_algorithm, wrong_policy_root, wrong_embedded_root):
        assert derive_unsafe_admit_then_root_update(mutant) is UpdateModelCode.ACCEPT
        assert derive_revision34_update(mutant) is not UpdateModelCode.ACCEPT


def test_candidate_decision_receipt_bundle_graph_is_acyclic() -> None:
    order = _topological_order(revision34_dependency_edges())
    assert order is not None
    assert order.index("evaluation_candidate") < order.index("receipt")
    assert order.index("receipt") < order.index("decision")
    assert order.index("decision") < order.index("commit_bundle")


def test_receipt_inside_evaluation_candidate_mutant_creates_a_cycle() -> None:
    assert _topological_order(receipt_cycle_mutant_edges()) is None
