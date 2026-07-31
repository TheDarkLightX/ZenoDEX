"""Adversarial tests for the M6-R01 OwnedSettlementV2 Revision 2 contract."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

from tools.check_fcis_m6_r01_owned_settlement_v2_revision2_contract import (
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


def test_clean_revision2_contract_is_design_only_and_unmounted() -> None:
    code, report = _report(DEFAULT_CONTRACT)
    assert code == 0
    assert report == {
        "acceptance_case_count": 12,
        "errors": [],
        "implementation_authorized": False,
        "mount_authorized": False,
        "ok": True,
        "schema": "zenodex/fcis/m6-r01-owned-settlement-v2-revision2-atdd/v1",
        "status": "draft_for_independent_review_unmounted",
    }


def test_inner_settlement_root_field_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["inner_claim_fields"].append("owned_settlement_root")

    errors = _errors(mutate)
    assert "INNER_CLAIM_FIELDS" in errors
    assert "INNER_CLAIM_FORBIDDEN_FIELD:owned_settlement_root" in errors


def test_ambiguous_fill_position_field_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        fields = contract["decision"]["inner_claim_fields"]
        fields[fields.index("settlement_fill_ordinal")] = "fill_position"

    errors = _errors(mutate)
    assert "INNER_CLAIM_FIELDS" in errors
    assert "INNER_CLAIM_FORBIDDEN_FIELD:fill_position" in errors


def test_root_projection_that_omits_claims_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["root_strategy"] = "settlement_body_without_claims"

    assert "ROOT_STRATEGY" in _errors(mutate)


def test_claim_tuple_must_feed_the_full_settlement_root() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(
            contract,
            "admitted_local_claim_tuple_v2",
            "owned_settlement_root_v2",
        )

    assert any(
        "admitted_local_claim_tuple_v2->owned_settlement_root_v2" in error
        for error in _errors(mutate)
    )


@pytest.mark.parametrize(
    ("source", "target"),
    [
        ("exact_pre_state_v2", "state_bound_active_configuration_v2"),
        (
            "validated_active_configuration_claim_v2",
            "state_bound_active_configuration_v2",
        ),
        (
            "state_bound_active_configuration_v2",
            "recomputed_local_claim_tuple_v2",
        ),
        (
            "state_bound_active_configuration_v2",
            "state_bound_witness_batch_v2",
        ),
    ],
)
def test_state_binding_edges_are_mandatory(source: str, target: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(contract, source, target)

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and f"{source}->{target}" in error
        for error in _errors(mutate)
    )


@pytest.mark.parametrize(
    "law",
    [
        "validated_root_equals_recomputed_body_root",
        "validated_root_equals_exact_pre_state_header_configuration_root",
        "validated_deployment_equals_exact_pre_state_header_deployment",
        "validated_activation_sequence_lte_exact_pre_state_header_sequence",
    ],
)
def test_every_state_binding_law_is_mandatory(law: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["state_binding_laws"].remove(law)

    assert "STATE_BINDING_LAWS" in _errors(mutate)


def test_validated_claim_cannot_bypass_state_binding_for_replay() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(
            contract,
            "state_bound_active_configuration_v2",
            "recomputed_local_claim_tuple_v2",
        )
        contract["dependency_graph"]["edges"].append(
            {
                "from": "validated_active_configuration_claim_v2",
                "to": "recomputed_local_claim_tuple_v2",
            }
        )

    errors = _errors(mutate)
    assert any(error.startswith("DEPENDENCY_EDGES_MISSING:") for error in errors)
    assert any(error.startswith("DEPENDENCY_EDGES_UNKNOWN:") for error in errors)


def test_state_binding_source_hash_drift_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["normative_source"]["state_binding_sha256"] = "0" * 64

    errors = _errors(mutate)
    assert "NORMATIVE_SOURCE_IDENTITY:state_binding_sha256" in errors
    assert any(
        error.startswith("NORMATIVE_SOURCE_HASH:")
        and "COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4" in error
        for error in errors
    )


@pytest.mark.parametrize(
    "field",
    [
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
def test_controlled_batch_cannot_duplicate_derived_fact(field: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["controlled_batch_fields"].append(field)

    errors = _errors(mutate)
    assert "CONTROLLED_BATCH_FIELDS" in errors
    assert f"CONTROLLED_BATCH_DUPLICATED_FIELD:{field}" in errors


@pytest.mark.parametrize(
    "source",
    [
        "admitted_local_claim_tuple_v2",
        "recomputed_local_claim_tuple_v2",
    ],
)
def test_controlled_claim_tuple_requires_both_exact_predecessors(source: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(contract, source, "exact_controlled_claim_tuple_v2")

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and f"{source}->exact_controlled_claim_tuple_v2" in error
        for error in _errors(mutate)
    )


def test_occurrence_identity_must_use_controlled_claim_tuple() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(
            contract,
            "exact_controlled_claim_tuple_v2",
            "occurrence_id_tuple_v2",
        )

    assert any(
        "exact_controlled_claim_tuple_v2->occurrence_id_tuple_v2" in error
        for error in _errors(mutate)
    )


def test_loose_consumed_tuple_node_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["nodes"].append("consumed_local_claim_tuple_v2")
        contract["dependency_graph"]["topological_order"].append(
            "consumed_local_claim_tuple_v2"
        )

    assert any(
        error.startswith("DEPENDENCY_NODE_SET:")
        and "consumed_local_claim_tuple_v2" in error
        for error in _errors(mutate)
    )


def test_normal_form_cannot_bypass_batch_owned_tuple() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(
            contract,
            "batch_owned_claim_tuple_v2",
            "v2_occurrence_normal_form_v2",
        )
        contract["dependency_graph"]["edges"].append(
            {
                "from": "exact_controlled_claim_tuple_v2",
                "to": "v2_occurrence_normal_form_v2",
            }
        )

    errors = _errors(mutate)
    assert any(error.startswith("DEPENDENCY_EDGES_MISSING:") for error in errors)
    assert any(error.startswith("DEPENDENCY_EDGES_UNKNOWN:") for error in errors)


def test_batch_must_own_the_downstream_claim_tuple() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(
            contract,
            "state_bound_witness_batch_v2",
            "batch_owned_claim_tuple_v2",
        )

    assert any(
        "state_bound_witness_batch_v2->batch_owned_claim_tuple_v2" in error
        for error in _errors(mutate)
    )


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("ordinal_contiguous", True),
        ("downstream_reenumeration_allowed", True),
        ("ordinal_field", "claim_position"),
        ("occurrence_id_ordinal_source", "claim_position"),
        ("ordinal_order", "contiguous"),
        ("ordinal_upper_bound_source", "len(exact_controlled_claim_tuple_v2)"),
    ],
)
def test_sparse_settlement_ordinal_policy_is_exact(
    field: str,
    value: object,
) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["claim_cardinality_policy"][field] = value

    assert "CLAIM_CARDINALITY_POLICY" in _errors(mutate)


def test_zero_fee_claim_mutation_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["claim_cardinality_policy"]["zero_fee_emits_claim"] = True

    assert "CLAIM_CARDINALITY_POLICY" in _errors(mutate)


@pytest.mark.parametrize(
    "output",
    [
        "replay_candidate",
        "controlled_claim_tuple",
        "occurrence_id_tuple",
        "witness_batch",
        "successor",
        "patch",
        "allocation",
        "receipt",
        "bundle",
        "proof_input",
        "effect",
        "outbox",
    ],
)
def test_every_early_rejection_output_is_forbidden(output: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["no_successor_outputs"].remove(output)

    assert "NO_SUCCESSOR_OUTPUTS" in _errors(mutate)


def test_submitted_root_cannot_become_authority() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["source_roles"]["submitted_roots"] = "trusted authority inputs"

    assert "SUBMITTED_ROOT_AUTHORITY" in _errors(mutate)


def test_design_contract_cannot_authorize_implementation_or_mount() -> None:
    def implementation(contract: dict[str, Any]) -> None:
        contract["implementation_authorized"] = True

    def mount(contract: dict[str, Any]) -> None:
        contract["mount_authorized"] = True

    assert "IMPLEMENTATION_AUTHORITY" in _errors(implementation)
    assert "MOUNT_AUTHORITY" in _errors(mount)


def test_required_acceptance_case_cannot_be_deleted() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["acceptance_cases"].pop()

    assert any(
        error.startswith(
            "ACCEPTANCE_CASE_IDS:missing=ATDD-M6-R01-OSV2-R2-012"
        )
        for error in _errors(mutate)
    )


def test_revision1_target_identity_drift_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["normative_source"]["revision_1_target_commit"] = "0" * 40

    assert (
        "NORMATIVE_SOURCE_IDENTITY:revision_1_target_commit"
        in _errors(mutate)
    )


def test_witness_batch_root_cannot_feed_its_own_preimage() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].append(
            {
                "from": "witness_batch_root_v2",
                "to": "state_bound_witness_batch_v2",
            }
        )

    errors = _errors(mutate)
    assert any(error.startswith("DEPENDENCY_EDGES_UNKNOWN:") for error in errors)
    assert any(error.startswith("DEPENDENCY_BACK_EDGE:") for error in errors)
    assert any(
        error.startswith("DEPENDENCY_CYCLE_OR_ORDER:") for error in errors
    )


def test_duplicate_json_member_is_rejected(tmp_path: Path) -> None:
    raw = DEFAULT_CONTRACT.read_text(encoding="utf-8")
    path = tmp_path / "duplicate.json"
    path.write_text(
        raw.replace(
            '"contract_version": "2.0.0",',
            '"contract_version": "2.0.0",\n  "contract_version": "2.0.0",',
            1,
        ),
        encoding="utf-8",
    )

    code, report = _report(path)
    assert code == 1
    assert report["errors"] == [
        "CONTRACT_INVALID:DuplicateJsonMember:contract_version"
    ]
