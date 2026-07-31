"""Adversarial tests for the M6-R01 OwnedSettlementV2 Revision 3 contract."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

from tools.check_fcis_m6_r01_owned_settlement_v2_revision3_contract import (
    DEFAULT_CONTRACT,
    _report,
    validate_contract,
)

REPO_ROOT = Path(__file__).resolve().parents[2]


def _contract() -> dict[str, Any]:
    return json.loads(DEFAULT_CONTRACT.read_text(encoding="utf-8"))


def _errors(mutator: object) -> list[str]:
    contract = copy.deepcopy(_contract())
    assert callable(mutator)
    mutator(contract)
    return validate_contract(contract, repo_root=REPO_ROOT)


def _remove_edge(
    contract: dict[str, Any],
    source: str,
    target: str,
) -> None:
    contract["dependency_graph"]["edges"].remove(
        {
            "from": source,
            "to": target,
        }
    )


def test_clean_revision3_contract_is_design_only_and_unmounted() -> None:
    code, report = _report(DEFAULT_CONTRACT)
    assert code == 0
    assert report == {
        "acceptance_case_count": 14,
        "errors": [],
        "implementation_authorized": False,
        "mount_authorized": False,
        "ok": True,
        "schema": "zenodex/fcis/m6-r01-owned-settlement-v2-revision3-atdd/v1",
        "status": "draft_for_independent_review_unmounted",
    }


def test_submitted_claim_tuple_cannot_enter_replay_projection() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["replay_projection_fields"].append(
            "provisional_protocol_fee_witnesses"
        )

    errors = _errors(mutate)
    assert "REPLAY_PROJECTION_FIELDS" in errors
    assert (
        "REPLAY_PROJECTION_FORBIDDEN_FIELD:provisional_protocol_fee_witnesses"
        in errors
    )


def test_replay_projection_cannot_hide_a_second_claim_field() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["replay_projection_forbidden_fields"] = []

    assert "REPLAY_PROJECTION_FORBIDDEN_FIELDS" in _errors(mutate)


@pytest.mark.parametrize(
    "source",
    [
        "exact_settlement_replay_projection_v2",
        "admitted_intent_tuple_v2",
        "exact_pre_state_v2",
        "state_bound_active_configuration_v2",
        "authenticated_execution_context_v2",
    ],
)
def test_every_claim_erased_replay_predecessor_is_mandatory(source: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(contract, source, "recomputed_local_claim_tuple_v2")

    errors = _errors(mutate)
    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and f"{source}->recomputed_local_claim_tuple_v2" in error
        for error in errors
    )
    assert any(
        error.startswith(
            "DEPENDENCY_PREDECESSORS:recomputed_local_claim_tuple_v2:"
        )
        for error in errors
    )


@pytest.mark.parametrize(
    "source",
    [
        "exact_authenticated_command_v2",
        "admitted_owned_settlement_v2",
        "admitted_local_claim_tuple_v2",
    ],
)
def test_claim_bearing_source_cannot_feed_fresh_replay(source: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].append(
            {"from": source, "to": "recomputed_local_claim_tuple_v2"}
        )

    errors = _errors(mutate)
    assert any(
        error.startswith("DEPENDENCY_EDGES_UNKNOWN:")
        and f"{source}->recomputed_local_claim_tuple_v2" in error
        for error in errors
    )
    assert any(
        error.startswith("DEPENDENCY_FORBIDDEN_EDGE:")
        and f"{source}->recomputed_local_claim_tuple_v2" in error
        for error in errors
    )


@pytest.mark.parametrize(
    "law",
    [
        "projection_excludes_submitted_local_claim_tuple",
        "projection_components_are_recursively_closed_claim_independent_types",
        "recomputed_claim_predecessors_are_exact_and_claim_erased",
        "equal_projection_and_independent_sources_imply_equal_recomputed_claims",
        "claim_only_mutation_preserves_projection_and_recomputed_claims",
        "whole_claim_bearing_settlement_and_command_are_not_replay_inputs",
    ],
)
def test_every_replay_noninterference_law_is_mandatory(law: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["noninterference_laws"].remove(law)

    assert "NONINTERFERENCE_LAWS" in _errors(mutate)


def test_claim_only_mutation_law_cannot_be_weakened_to_root_equality() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        laws = contract["decision"]["noninterference_laws"]
        index = laws.index(
            "claim_only_mutation_preserves_projection_and_recomputed_claims"
        )
        laws[index] = "claim_only_mutation_changes_only_the_settlement_root"

    assert "NONINTERFERENCE_LAWS" in _errors(mutate)


@pytest.mark.parametrize(
    "source",
    [
        "admitted_local_claim_tuple_v2",
        "recomputed_local_claim_tuple_v2",
    ],
)
def test_controlled_claim_tuple_requires_both_equality_inputs(source: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(contract, source, "exact_controlled_claim_tuple_v2")

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and f"{source}->exact_controlled_claim_tuple_v2" in error
        for error in _errors(mutate)
    )


def test_controlled_occurrence_has_exact_claim_and_identifier_only() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["controlled_occurrence_fields"].append(
            "claim_tuple_index"
        )

    assert "CONTROLLED_OCCURRENCE_FIELDS" in _errors(mutate)


def test_occurrence_identifier_cannot_be_a_batch_parallel_tuple() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["controlled_batch_fields"].append(
            "exact_occurrence_id_tuple"
        )

    errors = _errors(mutate)
    assert "CONTROLLED_BATCH_FIELDS" in errors
    assert (
        "CONTROLLED_BATCH_DUPLICATED_FIELD:exact_occurrence_id_tuple" in errors
    )


def test_parallel_occurrence_id_tuple_node_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        graph = contract["dependency_graph"]
        graph["nodes"].append("occurrence_id_tuple_v2")
        graph["topological_order"].append("occurrence_id_tuple_v2")

    assert any(
        error.startswith("DEPENDENCY_NODE_SET:")
        and "occurrence_id_tuple_v2" in error
        for error in _errors(mutate)
    )


@pytest.mark.parametrize(
    "law",
    [
        "pair_count_equals_controlled_claim_count",
        "pair_i_claim_equals_controlled_claim_i",
        "pair_i_id_hashes_command_root_and_claim_i_settlement_fill_ordinal",
        "pair_order_equals_controlled_claim_order",
        "occurrence_ids_are_unique",
        "occurrence_ids_are_derived_and_never_caller_supplied",
        "normal_form_lineage_commits_every_ordered_occurrence_id",
        "equal_claims_under_distinct_command_roots_have_distinct_lineage",
    ],
)
def test_every_pointwise_occurrence_pairing_law_is_mandatory(law: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["occurrence_pairing_laws"].remove(law)

    assert "OCCURRENCE_PAIRING_LAWS" in _errors(mutate)


@pytest.mark.parametrize(
    "source",
    [
        "exact_controlled_claim_tuple_v2",
        "command_root_v2",
    ],
)
def test_paired_occurrence_tuple_requires_claims_and_command_root(source: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(contract, source, "exact_controlled_occurrence_tuple_v2")

    errors = _errors(mutate)
    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and f"{source}->exact_controlled_occurrence_tuple_v2" in error
        for error in errors
    )
    assert any(
        error.startswith(
            "DEPENDENCY_PREDECESSORS:exact_controlled_occurrence_tuple_v2:"
        )
        for error in errors
    )


@pytest.mark.parametrize(
    "field",
    [
        "exact_settlement_replay_projection",
        "exact_controlled_claim_tuple",
        "exact_occurrence_id_tuple",
        "command_root",
        "pre_state_root",
        "configuration_root",
        "configuration_version",
        "algorithm_version",
        "accepted_language_version",
        "execution_context_hash",
        "owned_settlement_root",
        "witness_batch_root",
    ],
)
def test_controlled_batch_cannot_duplicate_derived_or_parallel_fact(
    field: str,
) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["controlled_batch_fields"].append(field)

    errors = _errors(mutate)
    assert "CONTROLLED_BATCH_FIELDS" in errors
    assert f"CONTROLLED_BATCH_DUPLICATED_FIELD:{field}" in errors
