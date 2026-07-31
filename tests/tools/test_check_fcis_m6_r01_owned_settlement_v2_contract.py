"""Adversarial tests for the M6-R01 OwnedSettlementV2 design contract."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

from tools.check_fcis_m6_r01_owned_settlement_v2_contract import (
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


def test_clean_contract_is_acyclic_design_only_and_unmounted() -> None:
    code, report = _report(DEFAULT_CONTRACT)
    assert code == 0
    assert report == {
        "acceptance_case_count": 8,
        "errors": [],
        "implementation_authorized": False,
        "mount_authorized": False,
        "ok": True,
        "schema": "zenodex/fcis/m6-r01-owned-settlement-v2-atdd/v1",
        "status": "draft_for_independent_review_unmounted",
    }


def test_inner_settlement_root_field_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["inner_claim_fields"].append("owned_settlement_root")

    errors = _errors(mutate)
    assert "INNER_CLAIM_FIELDS" in errors
    assert "INNER_CLAIM_DOWNSTREAM_FIELD:owned_settlement_root" in errors


def test_inner_command_derived_occurrence_id_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["inner_claim_fields"].append("occurrence_id")

    errors = _errors(mutate)
    assert "INNER_CLAIM_FIELDS" in errors
    assert "INNER_CLAIM_DOWNSTREAM_FIELD:occurrence_id" in errors


def test_root_projection_that_omits_claims_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["decision"]["root_strategy"] = "settlement_body_without_claims"

    assert "ROOT_STRATEGY" in _errors(mutate)


def test_claim_tuple_must_feed_the_full_settlement_root() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].remove(
            {
                "from": "admitted_local_claim_tuple_v2",
                "to": "owned_settlement_root_v2",
            }
        )

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and "admitted_local_claim_tuple_v2->owned_settlement_root_v2" in error
        for error in _errors(mutate)
    )


def test_witness_batch_back_edge_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].append(
            {
                "from": "witness_batch_root_v2",
                "to": "admitted_owned_settlement_v2",
            }
        )

    errors = _errors(mutate)
    assert any(error.startswith("DEPENDENCY_EDGES_UNKNOWN:") for error in errors)
    assert any(error.startswith("DEPENDENCY_BACK_EDGE:") for error in errors)
    assert any(error.startswith("DEPENDENCY_CYCLE_OR_ORDER:") for error in errors)


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


def test_fresh_replay_pre_state_edge_is_mandatory() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].remove(
            {
                "from": "exact_pre_state_v2",
                "to": "recomputed_local_claim_tuple_v2",
            }
        )

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and "exact_pre_state_v2->recomputed_local_claim_tuple_v2" in error
        for error in _errors(mutate)
    )


def test_configuration_cannot_be_removed_from_controlled_batch() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].remove(
            {
                "from": "configuration_root_v2",
                "to": "state_bound_witness_batch_v2",
            }
        )

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and "configuration_root_v2->state_bound_witness_batch_v2" in error
        for error in _errors(mutate)
    )


def test_exact_source_values_reach_controlled_derivation() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["dependency_graph"]["edges"].remove(
            {
                "from": "exact_pre_state_v2",
                "to": "state_bound_witness_batch_v2",
            }
        )

    assert any(
        error.startswith("DEPENDENCY_EDGES_MISSING:")
        and "exact_pre_state_v2->state_bound_witness_batch_v2" in error
        for error in _errors(mutate)
    )


def test_submitted_root_cannot_become_authority() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["source_roles"]["submitted_roots"] = "trusted authority inputs"

    assert "SUBMITTED_ROOT_AUTHORITY" in _errors(mutate)


def test_zero_fee_claim_mutation_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["claim_cardinality_policy"]["zero_fee_emits_claim"] = True

    assert "CLAIM_CARDINALITY_POLICY" in _errors(mutate)


def test_missing_no_successor_output_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["no_successor_outputs"].remove("outbox")

    assert "NO_SUCCESSOR_OUTPUTS" in _errors(mutate)


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
        error.startswith("ACCEPTANCE_CASE_IDS:missing=ATDD-M6-R01-OSV2-008")
        for error in _errors(mutate)
    )


def test_normative_source_hash_drift_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["normative_source"]["architecture_sha256"] = "0" * 64

    hash_error = (
        "NORMATIVE_SOURCE_HASH:"
        "docs/research/prompts/"
        "fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/"
        "SRGD_V1_AMENDMENT.md"
    )
    errors = _errors(mutate)
    assert "NORMATIVE_SOURCE_IDENTITY:architecture_sha256" in errors
    assert hash_error in errors


def test_implementation_base_identity_drift_is_rejected() -> None:
    def mutate(contract: dict[str, Any]) -> None:
        contract["normative_source"]["implementation_base_commit"] = "0" * 40

    assert (
        "NORMATIVE_SOURCE_IDENTITY:implementation_base_commit"
        in _errors(mutate)
    )


def test_duplicate_json_member_is_rejected(tmp_path: Path) -> None:
    raw = DEFAULT_CONTRACT.read_text(encoding="utf-8")
    path = tmp_path / "duplicate.json"
    path.write_text(
        raw.replace(
            '"contract_version": "1.0.0",',
            '"contract_version": "1.0.0",\n  "contract_version": "1.0.0",',
            1,
        ),
        encoding="utf-8",
    )

    code, report = _report(path)
    assert code == 1
    assert report["errors"] == [
        "CONTRACT_INVALID:DuplicateJsonMember:contract_version"
    ]
