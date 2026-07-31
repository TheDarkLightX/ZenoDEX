"""Downstream and rejection mutations for the M6-R01 Revision 3 contract."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, cast

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


def _remove_edge(contract: dict[str, Any], source: str, target: str) -> None:
    contract["dependency_graph"]["edges"].remove({"from": source, "to": target})


def test_normal_form_cannot_consume_claim_tuple_without_occurrence_identity() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        _remove_edge(
            contract,
            "batch_owned_controlled_occurrence_tuple_v2",
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
    assert any(
        error.startswith("DEPENDENCY_PREDECESSORS:v2_occurrence_normal_form_v2:")
        for error in errors
    )


def test_downstream_source_cannot_name_claim_only_projection() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["downstream_occurrence_source"] = (
            "state_bound_witness_batch_v2.exact_controlled_claim_tuple"
        )

    assert "DECISION_VALUE:downstream_occurrence_source" in _errors(mutate)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("ordinal_contiguous", True),
        ("downstream_reenumeration_allowed", True),
        ("ordinal_field", "claim_position"),
        ("occurrence_id_ordinal_source", "claim_tuple_index"),
        ("ordinal_order", "contiguous"),
        ("ordinal_upper_bound_source", "len(exact_controlled_claim_tuple_v2)"),
        ("zero_fee_emits_claim", True),
        ("positive_fee_emits_exactly_one_claim", False),
    ],
)
def test_sparse_settlement_ordinal_and_cardinality_policy_is_exact(
    field: str,
    value: object,
) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["claim_cardinality_policy"][field] = value

    assert "CLAIM_CARDINALITY_POLICY" in _errors(mutate)


@pytest.mark.parametrize(
    "law",
    [
        "validated_root_equals_recomputed_body_root",
        "validated_root_equals_exact_pre_state_header_configuration_root",
        "validated_deployment_equals_exact_pre_state_header_deployment",
        "validated_activation_sequence_lte_exact_pre_state_header_sequence",
    ],
)
def test_every_state_binding_law_remains_mandatory(law: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["state_binding_laws"].remove(law)

    assert "STATE_BINDING_LAWS" in _errors(mutate)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("binder_establishes", "store_current_configuration"),
        ("binder_does_not_establish", "nothing"),
        ("historical_state_status", "current_authority"),
        ("publication_requirement", "trust_bundle_carried_exact_state"),
    ],
)
def test_state_binding_cannot_overclaim_store_currentness(
    field: str,
    value: str,
) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["currentness_policy"][field] = value

    assert "CURRENTNESS_POLICY" in _errors(mutate)


@pytest.mark.parametrize(
    "output",
    [
        "state_bound_active_configuration",
        "replay_candidate",
        "controlled_claim_tuple",
        "controlled_occurrence_tuple",
        "occurrence_id",
        "witness_batch",
        "batch_owned_controlled_occurrence_tuple",
        "v2_occurrence_normal_form",
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
def test_every_composite_rejection_output_is_closed(output: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["no_authority_outputs"].remove(output)

    assert "NO_AUTHORITY_OUTPUTS" in _errors(mutate)


def test_full_settlement_root_must_commit_submitted_claim_tuple() -> None:
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


def test_inner_occurrence_cannot_store_command_root() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["inner_claim_fields"].append("command_root")

    errors = _errors(mutate)
    assert "INNER_CLAIM_FIELDS" in errors
    assert "INNER_CLAIM_FORBIDDEN_FIELD:command_root" in errors


def test_revision2_identity_and_state_binding_hash_are_pinned() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["normative_source"]["revision_2_packet_commit"] = "0" * 40
        contract["normative_source"]["state_binding_sha256"] = "0" * 64

    errors = _errors(mutate)
    assert "NORMATIVE_SOURCE_IDENTITY:revision_2_packet_commit" in errors
    assert "NORMATIVE_SOURCE_IDENTITY:state_binding_sha256" in errors
    assert any(error.startswith("NORMATIVE_SOURCE_HASH:") for error in errors)


def test_missing_acceptance_case_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["acceptance_cases"].pop()

    errors = _errors(mutate)
    assert any(
        error.startswith("ACCEPTANCE_CASE_IDS:")
        and "ATDD-M6-R01-OSV2-R3-014" in error
        for error in errors
    )


@pytest.mark.parametrize(
    "flag",
    ["implementation_authorized", "mount_authorized"],
)
def test_design_contract_cannot_authorize_runtime(flag: str) -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract[flag] = True

    expected = (
        "IMPLEMENTATION_AUTHORITY"
        if flag.startswith("implementation")
        else "MOUNT_AUTHORITY"
    )
    assert expected in _errors(mutate)


def test_batch_root_cycle_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].append(
            {
                "from": "witness_batch_root_v2",
                "to": "state_bound_witness_batch_v2",
            }
        )

    errors = _errors(mutate)
    assert any(error.startswith("DEPENDENCY_FORBIDDEN_EDGE:") for error in errors)
    assert any(error.startswith("DEPENDENCY_CYCLE_OR_ORDER:") for error in errors)


def test_duplicate_json_member_is_rejected(tmp_path: Path) -> None:
    raw = DEFAULT_CONTRACT.read_text(encoding="utf-8")
    duplicate = raw.replace(
        '  "contract_version": "3.0.0",',
        '  "contract_version": "3.0.0",\n  "contract_version": "3.0.0",',
        1,
    )
    path = tmp_path / "duplicate.json"
    path.write_text(duplicate, encoding="utf-8")

    code, report = _report(path)
    assert code == 1
    assert report["ok"] is False
    assert any(
        error.startswith("CONTRACT_INVALID:DuplicateJsonMember:")
        for error in cast(list[str], report["errors"])
    )
