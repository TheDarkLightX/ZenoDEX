from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import check_production_readiness_architecture_candidate_v2 as checker
from tools import production_readiness_architecture_candidate_contract_v2 as contract
from tools import render_production_readiness_architecture_candidate_v2 as renderer


def _document() -> dict[str, Any]:
    return json.loads(checker.DEFAULT_ARTIFACT.read_text(encoding="utf-8"))


def _row(rows: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    return next(row for row in rows if row["id"] == row_id)


def _composition(document: dict[str, Any]) -> dict[str, Any]:
    return document["composition_contract"]


def _mutate_ack_from_shell(document: dict[str, Any]) -> None:
    _composition(document)["effects"]["outbox_shell_economic_mutation_allowed"] = True


def _mutate_ack_bypass(document: dict[str, Any]) -> None:
    _composition(document)["effects"]["ack_reentry_port_id"] = "P_OUTBOX_ACK_SUBMISSION"


def _mutate_ack_epoch_omitted(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_OUTBOX_ACK_SUBMISSION")
    port["request_guarantees"].remove("WRITER_EPOCH_BOUND")


def _mutate_advisory_selection(document: dict[str, Any]) -> None:
    document["architecture_selected"] = True


def _mutate_invented_atom(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_ROUTE_RESOLUTION")
    port["request_guarantees"] = ["X"]
    port["callee_request_assumptions"] = ["X"]


def _mutate_caller_authority(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_POLICY_VERIFICATION")
    port["caller_constructible_authority"] = True


def _mutate_governance_caller_authority(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_GOVERNANCE_AUTHORIZATION")
    port["caller_constructible_authority"] = True


def _mutate_command_omitted(document: dict[str, Any]) -> None:
    document["routes"] = [row for row in document["routes"] if row["id"] != "spot_swap"]


def _mutate_command_order(document: dict[str, Any]) -> None:
    _composition(document)["batch_command_order"] = "MODULE_THEN_COMMAND_INDEX"


def _mutate_wrong_module(document: dict[str, Any]) -> None:
    _row(document["routes"], "zusd_borrow")["primary_module_id"] = "SPOT_LP_MODULE"


def _mutate_dependency_cycle(document: dict[str, Any]) -> None:
    _row(document["module_descriptors"], "SETTLEMENT_ABI")["build_depends_on"] = [
        "SETTLEMENT_KERNEL"
    ]


def _mutate_guest_core(document: dict[str, Any]) -> None:
    _composition(document)["zrpf_core_id"] = "GUEST_SPECIFIC_CORE"


def _mutate_direct_carries_zrpf_witness(document: dict[str, Any]) -> None:
    type_row = _row(document["type_registry"], "ExecutionAdmissionV2")
    contract_row = type_row["variant_field_contracts"]["DIRECT_EXECUTION"]
    contract_row["forbidden_field_ids"].remove("verified_zrpf_journal")


def _mutate_drain_create(document: dict[str, Any]) -> None:
    _composition(document)["drain_primary_object_creation_allowed"] = True


def _mutate_epoch_control_untyped(document: dict[str, Any]) -> None:
    _composition(document).pop("authoritative_input_sum")


def _mutate_effect_before_commit(document: dict[str, Any]) -> None:
    _composition(document)["effects"]["dispatch_stage"] = "BEFORE_HEAD_COMMIT"


def _mutate_foreign_write(document: dict[str, Any]) -> None:
    _row(document["module_descriptors"], "PERPS_MODULE")["proposal_write_domains"].append(
        "ZUSD_STATE"
    )


def _mutate_governance_witness_dropped(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_RELEASE_CONTROL")
    port["request_type"] = "GovernedEpochControlV2"


def _mutate_issue_wrong_asset(document: dict[str, Any]) -> None:
    capability = _row(
        document["intent_capabilities"], "SPOT_LP_MODULE:AUTHORIZED_ISSUE"
    )
    capability["asset_scope"] = "ZUSD_ONLY"


def _mutate_burn_wrong_asset(document: dict[str, Any]) -> None:
    capability = _row(
        document["intent_capabilities"], "PROTOCOL_FINANCE_MODULE:AUTHORIZED_BURN"
    )
    capability["asset_scope"] = "ANY_ASSET"


def _mutate_migration_class(document: dict[str, Any]) -> None:
    _composition(document)["migration"]["classification_variants"].remove("RETAINED_PINNED")


def _mutate_migration_kind(document: dict[str, Any]) -> None:
    _composition(document)["migration"]["object_kind_registry"].remove("PRIVATE_SWAP")


def _mutate_native_backup_without_evidence(document: dict[str, Any]) -> None:
    type_row = _row(document["type_registry"], "VerifierExecutionProfileV2")
    required = type_row["variant_field_contracts"]["NATIVE_BACKUP"]["required_field_ids"]
    required.remove("equivalence_receipt_root")
    required.remove("governance_authorization_root")


def _mutate_occurrence_release_set(document: dict[str, Any]) -> None:
    _composition(document)["occurrence_identity_fields"].remove("MODULE_RELEASE_SET_ROOT")


def _mutate_outbox_publication(document: dict[str, Any]) -> None:
    _composition(document)["effects"]["idempotency_fields"].remove("PUBLICATION_ROOT")


def _mutate_stronger_assumption(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_ROUTE_RESOLUTION")
    port["caller_response_assumptions"].append("PROMOTION_SUBJECT_BOUND")


def _mutate_arrival_order(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_SPOT_LP_MODULE_EVALUATION")
    port["order"] = "ARRIVAL_ORDER"


def _mutate_any_type(document: dict[str, Any]) -> None:
    port = _row(document["port_contracts"], "P_SPOT_LP_MODULE_EVALUATION")
    port["request_type"] = "ANY"


def _mutate_publication_duplicate(document: dict[str, Any]) -> None:
    contract_row = _composition(document)["candidate_publication_contract"]
    contract_row["duplicated_history_nullifier_proof_effect_fields"] = True


def _mutate_release_bypass(document: dict[str, Any]) -> None:
    _composition(document)["epoch_control_commit_capability"] = "DIRECT_RELEASE_WRITE"


def _mutate_partial_control_commit(document: dict[str, Any]) -> None:
    _composition(document)["epoch_control_contract"]["partial_commit_possible"] = True


def _mutate_route_intent(document: dict[str, Any]) -> None:
    _row(document["routes"], "perp_open")["required_intent_ids"].append("AUTHORIZED_ISSUE")


def _mutate_route_step_steals_intent(document: dict[str, Any]) -> None:
    route = _row(document["routes"], "protocol_buy_and_burn")
    route["steps"][1]["required_intent_ids"].append("AUTHORIZED_BURN")
    route["steps"][2]["required_intent_ids"].remove("AUTHORIZED_BURN")


def _mutate_second_writer(document: dict[str, Any]) -> None:
    _row(document["state_domains"], "PERPS_STATE")["durable_writers"].append("PERPS_MODULE")


def _mutate_self_attestation(document: dict[str, Any]) -> None:
    gate = _row(document["evidence_gates"], "COMMAND_ROUTE_CLOSURE")
    gate["evidence_status"] = "VERIFIED"
    gate["evidence_refs"] = ["self-attested"]


def _mutate_source_execution_split(document: dict[str, Any]) -> None:
    document["verifier_bootstrap"]["identity_status"] = "SELF_VERIFIED"


def _mutate_solver_unknown(document: dict[str, Any]) -> None:
    _composition(document)["formal_verification"]["esso_unknown_timeout_disagreement_policy"] = (
        "ACCEPT"
    )


def _mutate_module_delta(document: dict[str, Any]) -> None:
    _composition(document)["module_delta_authoritative"] = True
    _composition(document)["value_delta_source"] = "MODULE_DECLARATION"


def _mutate_tau_release_escalation(document: dict[str, Any]) -> None:
    module = _row(document["module_descriptors"], "TAU_ESCROW_MODULE")
    module["allowed_intent_ids"].append("MODULE_RELEASE_LIFECYCLE_CHANGE")


def _mutate_tau_failover_ungoverned(document: dict[str, Any]) -> None:
    profiles = _composition(document)["verifier"]["execution_profiles"]
    profile = next(
        row for row in profiles if row["id"] == "TAU_PRIMARY_NATIVE_GOVERNED_FAILOVER"
    )
    profile["governed_mode_switch_required"] = False


def _mutate_tau_failover_per_query(document: dict[str, Any]) -> None:
    _composition(document)["verifier"]["backend_selection_source"] = "PER_QUERY_CALLER"


def _mutate_tau_quantity_omitted(document: dict[str, Any]) -> None:
    representation = _row(document["type_registry"], "ResolvedTauRepresentationV2")
    representation["field_specs"] = [
        row for row in representation["field_specs"] if row["id"] != "scale_denominator"
    ]


def _mutate_tau_representation_unresolved(document: dict[str, Any]) -> None:
    route = _row(document["routes"], "tau_escrow_deposit")
    route["required_view_ids"].remove("RESOLVED_TAU_REPRESENTATION")


def _mutate_transfer_wrong_role(document: dict[str, Any]) -> None:
    capability = _row(document["intent_capabilities"], "SPOT_LP_MODULE:LEDGER_TRANSFER")
    capability["account_role_scope"] = ["ZUSD_SUPPLY"]


def _mutate_unknown_intent(document: dict[str, Any]) -> None:
    module = _row(document["module_descriptors"], "PERPS_MODULE")
    module["allowed_intent_ids"].append("UNKNOWN_INTENT_KIND")


def _mutate_unported_dependency(document: dict[str, Any]) -> None:
    _row(document["module_descriptors"], "PERPS_MODULE")["runtime_port_ids"].append(
        "P_HIDDEN_ORACLE_READ"
    )


def _mutate_verifier_mismatch(document: dict[str, Any]) -> None:
    _composition(document)["verifier"]["mismatch_policy"] = "PREFER_TAU"


def _mutate_profile_substitution(document: dict[str, Any]) -> None:
    _composition(document)["verifier"]["profile_binding_required"] = False


def _mutate_zrpf_writer(document: dict[str, Any]) -> None:
    _composition(document)["zrpf_admission_contract"]["separate_zrpf_writer_allowed"] = True


def _mutate_zrpf_candidate_substitution(document: dict[str, Any]) -> None:
    fields = _composition(document)["zrpf_admission_contract"][
        "witness_candidate_equality_fields"
    ]
    fields.remove("POST_STATE_ROOT")


def _mutate_zrpf_binding_path(document: dict[str, Any]) -> None:
    paths = _composition(document)["zrpf_admission_contract"]["binding_schema_paths"]
    paths["OUTBOX_ROOT"][1] = "ExecutionAdmissionV2.missing_outbox_root"


def _mutate_zrpf_witness_omitted(document: dict[str, Any]) -> None:
    type_row = _row(document["type_registry"], "ExecutionAdmissionV2")
    required = type_row["variant_field_contracts"]["ZRPF_ROOT"]["required_field_ids"]
    required.remove("verified_zrpf_journal")


MUTANTS: tuple[tuple[str, Callable[[dict[str, Any]], None], str], ...] = (
    ("ACK_EPOCH_OMITTED", _mutate_ack_epoch_omitted, "ACK_EPOCH_OMITTED"),
    ("ACK_BYPASSES_SETTLEMENT", _mutate_ack_bypass, "ACK_BYPASSES_SETTLEMENT"),
    ("ACK_MUTATES_FROM_SHELL", _mutate_ack_from_shell, "ACK_MUTATES_FROM_SHELL"),
    ("ADVISORY_SELECTION", _mutate_advisory_selection, "ADVISORY_SELECTION"),
    ("ASSUMPTION_TOKEN_INVENTED", _mutate_invented_atom, "ASSUMPTION_TOKEN_INVENTED"),
    ("CALLER_CONSTRUCTED_AUTHORITY", _mutate_caller_authority, "CALLER_CONSTRUCTED_AUTHORITY"),
    (
        "CALLER_CONSTRUCTED_GOVERNANCE_AUTHORITY",
        _mutate_governance_caller_authority,
        "CALLER_CONSTRUCTED_GOVERNANCE_AUTHORITY",
    ),
    ("COMMAND_OMITTED", _mutate_command_omitted, "COMMAND_ROUTE_CLOSURE"),
    ("COMMAND_ORDER_AFTER_MODULE_ORDER", _mutate_command_order, "COMMAND_ORDER_AFTER_MODULE_ORDER"),
    ("COMMAND_WRONG_MODULE", _mutate_wrong_module, "COMMAND_WRONG_MODULE"),
    ("DEPENDENCY_CYCLE", _mutate_dependency_cycle, "DEPENDENCY_CYCLE"),
    (
        "DIRECT_CARRIES_ZRPF_WITNESS",
        _mutate_direct_carries_zrpf_witness,
        "DIRECT_CARRIES_ZRPF_WITNESS",
    ),
    ("DIRECT_GUEST_CORE_MISMATCH", _mutate_guest_core, "DIRECT_GUEST_CORE_MISMATCH"),
    ("DRAIN_CREATES_OBJECT", _mutate_drain_create, "DRAIN_CREATES_OBJECT"),
    ("EPOCH_CONTROL_UNTYPED", _mutate_epoch_control_untyped, "EPOCH_CONTROL_UNTYPED"),
    (
        "EXTERNAL_EFFECT_BEFORE_COMMIT",
        _mutate_effect_before_commit,
        "EXTERNAL_EFFECT_BEFORE_COMMIT",
    ),
    ("FOREIGN_PROPOSAL_WRITE", _mutate_foreign_write, "FOREIGN_PROPOSAL_WRITE"),
    (
        "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM",
        _mutate_governance_witness_dropped,
        "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM",
    ),
    ("ISSUE_WRONG_ASSET", _mutate_issue_wrong_asset, "ISSUE_WRONG_ASSET"),
    ("BURN_WRONG_ASSET", _mutate_burn_wrong_asset, "BURN_WRONG_ASSET"),
    ("MIGRATION_CLASS_OMITTED", _mutate_migration_class, "MIGRATION_CLASS_OMITTED"),
    ("MIGRATION_OBJECT_KIND_OMITTED", _mutate_migration_kind, "MIGRATION_OBJECT_KIND_OMITTED"),
    (
        "NATIVE_BACKUP_WITHOUT_GOVERNANCE_OR_EQUIVALENCE",
        _mutate_native_backup_without_evidence,
        "NATIVE_BACKUP_WITHOUT_GOVERNANCE_OR_EQUIVALENCE",
    ),
    (
        "OCCURRENCE_OMITS_RELEASE_SET",
        _mutate_occurrence_release_set,
        "OCCURRENCE_OMITS_RELEASE_SET",
    ),
    ("OUTBOX_ID_OMITS_PUBLICATION", _mutate_outbox_publication, "OUTBOX_ID_OMITS_PUBLICATION"),
    (
        "PORT_ASSUMPTION_NOT_GUARANTEED",
        _mutate_stronger_assumption,
        "PORT_ASSUMPTION_NOT_GUARANTEED",
    ),
    ("PORT_ORDER_ARRIVAL", _mutate_arrival_order, "port_contracts"),
    ("PORT_TYPE_ANY", _mutate_any_type, "PORT_TYPE_ANY"),
    (
        "PUBLICATION_DUPLICATE_BINDING",
        _mutate_publication_duplicate,
        "PUBLICATION_DUPLICATE_BINDING",
    ),
    ("RELEASE_CONTROL_BYPASS", _mutate_release_bypass, "RELEASE_CONTROL_BYPASS"),
    (
        "POLICY_RELEASE_PARTIAL_COMMIT",
        _mutate_partial_control_commit,
        "POLICY_RELEASE_PARTIAL_COMMIT",
    ),
    ("ROUTE_INTENT_EXCEEDS_CAPABILITY", _mutate_route_intent, "ROUTE_INTENT_EXCEEDS_CAPABILITY"),
    ("ROUTE_STEP_STEALS_INTENT", _mutate_route_step_steals_intent, "ROUTE_STEP_STEALS_INTENT"),
    ("SECOND_DURABLE_WRITER", _mutate_second_writer, "SECOND_DURABLE_WRITER"),
    ("SELF_ATTESTED_EVIDENCE", _mutate_self_attestation, "SELF_ATTESTED_EVIDENCE"),
    ("SOLVER_UNKNOWN_ACCEPTED", _mutate_solver_unknown, "formal_verification"),
    (
        "SOURCE_EXECUTION_SNAPSHOT_SPLIT",
        _mutate_source_execution_split,
        "SOURCE_EXECUTION_SNAPSHOT_SPLIT",
    ),
    ("TRUST_MODULE_DELTA", _mutate_module_delta, "TRUST_MODULE_DELTA"),
    (
        "TAU_ESCALATES_TO_RELEASE_CONTROL",
        _mutate_tau_release_escalation,
        "TAU_ESCALATES_TO_RELEASE_CONTROL",
    ),
    ("TAU_FAILOVER_UNGOVERNED", _mutate_tau_failover_ungoverned, "TAU_FAILOVER_UNGOVERNED"),
    (
        "TAU_FAILOVER_PER_QUERY_SWITCH",
        _mutate_tau_failover_per_query,
        "TAU_FAILOVER_PER_QUERY_SWITCH",
    ),
    (
        "TAU_QUANTITY_CONTRACT_OMITTED",
        _mutate_tau_quantity_omitted,
        "TAU_QUANTITY_CONTRACT_OMITTED",
    ),
    (
        "TAU_REPRESENTATION_UNRESOLVED",
        _mutate_tau_representation_unresolved,
        "TAU_REPRESENTATION_UNRESOLVED",
    ),
    (
        "TRANSFER_WRONG_CUSTODY_ROLE",
        _mutate_transfer_wrong_role,
        "TRANSFER_WRONG_CUSTODY_ROLE",
    ),
    ("UNPORTED_DEPENDENCY", _mutate_unported_dependency, "UNPORTED_DEPENDENCY"),
    ("UNKNOWN_INTENT", _mutate_unknown_intent, "UNKNOWN_INTENT"),
    ("VERIFIER_MISMATCH_FAILS_OPEN", _mutate_verifier_mismatch, "VERIFIER_MISMATCH_FAILS_OPEN"),
    (
        "VERIFIER_PROFILE_SUBSTITUTION",
        _mutate_profile_substitution,
        "VERIFIER_PROFILE_SUBSTITUTION",
    ),
    ("ZRPF_BYPASSES_SHARED_COMMIT", _mutate_zrpf_writer, "ZRPF_BYPASSES_SHARED_COMMIT"),
    (
        "ZRPF_BINDING_PATH_UNREALIZABLE",
        _mutate_zrpf_binding_path,
        "ZRPF_BINDING_PATH_UNREALIZABLE",
    ),
    ("ZRPF_WITNESS_OMITTED", _mutate_zrpf_witness_omitted, "ZRPF_WITNESS_OMITTED"),
    (
        "ZRPF_WITNESS_CANDIDATE_SUBSTITUTION",
        _mutate_zrpf_candidate_substitution,
        "ZRPF_WITNESS_CANDIDATE_SUBSTITUTION",
    ),
)

NON_DOCUMENT_MUTANTS = {"SOURCE_SPLIT_SNAPSHOT", "SOURCE_SYMLINK_SUBSTITUTION"}


def test_candidate_is_exact_structural_research_and_unselected() -> None:
    report = checker.check_artifact()

    assert report["ok"] is True
    assert report["command_count"] == report["route_count"] == 33
    assert report["module_count"] == 20
    assert report["state_domain_count"] == 13
    assert report["type_count"] == 46
    assert report["intent_capability_count"] == 56
    assert report["command_payload_schema_closed_count"] == 0
    assert report["authoritative_input_variant_count"] == 3
    assert report["governed_control_variant_count"] == 3
    assert report["nested_abi_complete"] is False
    assert report["port_count"] == 25
    assert report["restricted_implication_direction_count"] == 50
    assert report["named_mutant_count"] == 54
    assert report["esso_required"] is True
    assert report["esso_verified"] is False
    assert report["lean_required"] is True
    assert report["lean_verified"] is False
    assert report["verifier_bootstrap_verified"] is False
    assert report["promotion_eligible"] is False
    assert report["architecture_selected"] is False
    assert report["production_ready"] is False


def test_generated_manifest_bytes_are_current() -> None:
    assert checker.DEFAULT_ARTIFACT.read_text(encoding="utf-8") == renderer.render(
        renderer.build_document()
    )


def test_generated_manifest_is_python_hash_seed_invariant() -> None:
    script = (
        "from tools import render_production_readiness_architecture_candidate_v2 as r; "
        "import hashlib; "
        "print(hashlib.sha256(r.render(r.build_document()).encode()).hexdigest())"
    )
    digests = {
        subprocess.run(
            [sys.executable, "-c", script],
            cwd=checker.REPO_ROOT,
            env={**os.environ, "PYTHONHASHSEED": seed},
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        for seed in ("1", "2", "3")
    }

    assert len(digests) == 1


def test_buy_and_burn_is_explicit_three_step_route_with_release_set() -> None:
    route = _row(_document()["routes"], "protocol_buy_and_burn")

    assert [step["module_id"] for step in route["steps"]] == [
        "PROTOCOL_FINANCE_MODULE",
        "SPOT_LP_MODULE",
        "PROTOCOL_FINANCE_MODULE",
    ]
    assert [step["depends_on_step_indexes"] for step in route["steps"]] == [[], [0], [1]]
    assert route["release_participant_module_ids"] == [
        "ORACLE_MODULE",
        "PROTOCOL_FINANCE_MODULE",
        "SPOT_LP_MODULE",
    ]
    assert "SURPLUS_PRIORITY_AND_BURN_FLOOR" in route["constraint_ids"]
    assert "AT_LEAST_TWO_LEDGER_TRANSFER_LEGS" in route["constraint_ids"]
    assert route["steps"][1]["required_intent_ids"] == ["LEDGER_TRANSFER"]
    assert route["steps"][2]["required_intent_ids"] == [
        "AUTHORIZED_BURN",
        "TERMINAL_OBLIGATION_CHANGE",
    ]


def test_control_authorities_and_tau_mode_are_separate_and_atomically_published() -> None:
    document = _document()
    composition = _composition(document)
    tau_module = _row(document["module_descriptors"], "TAU_ESCROW_MODULE")

    assert "TAU_CONNECTIVITY_MODE_CHANGE" in tau_module["allowed_intent_ids"]
    assert "MODULE_RELEASE_LIFECYCLE_CHANGE" not in tau_module["allowed_intent_ids"]
    assert "POLICY_PROFILE_CHANGE" not in tau_module["allowed_intent_ids"]
    assert composition["epoch_control_contract"]["authorization_port_id"] == (
        "P_GOVERNANCE_AUTHORIZATION"
    )
    assert composition["epoch_control_contract"]["partial_commit_possible"] is False
    assert composition["epoch_control_contract"]["publication_port_id"] == (
        "P_SETTLEMENT_PUBLICATION"
    )
    assert _row(document["port_contracts"], "P_RELEASE_CONTROL")["request_type"] == (
        "AuthorizedReleaseControlRequestV2"
    )
    assert _row(document["port_contracts"], "P_POLICY_CONTROL")["request_type"] == (
        "AuthorizedPolicyControlRequestV2"
    )


def test_tau_value_routes_require_resolved_representation_and_replay_nullifiers() -> None:
    document = _document()
    deposit = _row(document["routes"], "tau_escrow_deposit")
    reward = _row(document["routes"], "zrpf_prover_reward")

    assert "RESOLVED_TAU_REPRESENTATION" in deposit["required_view_ids"]
    assert "NULLIFIER_CONSUME" in deposit["required_intent_ids"]
    assert "NULLIFIER_CONSUME" in reward["required_intent_ids"]
    representation = _row(document["type_registry"], "ResolvedTauRepresentationV2")
    fields = {row["id"] for row in representation["field_specs"]}
    assert {"scale_denominator", "rounding_mode", "permanence_anchor_root"} <= fields


def test_verified_zrpf_admission_is_bound_once_into_publication() -> None:
    document = _document()
    composition = _composition(document)
    zrpf = composition["zrpf_admission_contract"]
    publication = composition["candidate_publication_contract"]

    assert set(zrpf["witness_candidate_equality_fields"]) == set(
        contract.REQUIRED_ZRPF_ADMISSION_BINDING_FIELDS
    )
    assert {
        "OUTBOX_ROOT",
        "VERIFIED_WITNESS_ID",
        "VERIFIER_REGISTRY_ROOT",
    } <= set(zrpf["witness_candidate_equality_fields"])
    assert all(
        checker._schema_path_exists(path)
        for paths in zrpf["binding_schema_paths"].values()
        for path in paths
    )
    assert zrpf["execution_admission_type"] == "ExecutionAdmissionV2"
    assert zrpf["verified_witness_type"] == "VerifiedZRPFJournalV2"
    assert _row(document["port_contracts"], "P_ZRPF_PROOF_VERIFICATION")[
        "response_type"
    ] == "VerifiedZRPFJournalV2"
    commitment_fields = {
        row["id"]
        for row in _row(document["type_registry"], "ExecutionCommitmentsV2")["field_specs"]
    }
    assert {"history_root", "nullifier_root", "outbox_root", "parent_state_root"} <= (
        commitment_fields
    )
    assert publication["duplicated_history_nullifier_proof_effect_fields"] is False
    assert publication["value_delta_certificate_root_equals_commitment"] is True
    assert publication["candidate_root_recomputed_by_writer"] is True


def test_tau_primary_native_backup_requires_governed_equivalence() -> None:
    document = _document()
    verifier = _composition(document)["verifier"]
    profiles = verifier["execution_profiles"]
    failover = next(
        row for row in profiles if row["id"] == "TAU_PRIMARY_NATIVE_GOVERNED_FAILOVER"
    )

    assert failover["governed_mode_switch_required"] is True
    assert failover["same_profile_equivalence_receipt_required"] is True
    assert failover["silent_per_query_fallback_allowed"] is False
    assert failover["native_backup_activation_authority"] == "GOVERNED_POLICY_CONTROL_ONLY"
    assert verifier["backend_selection_source"] == "EPOCH_BOUND_VERIFIED_PROFILE"
    assert verifier["per_query_backend_override_allowed"] is False
    assert verifier["execution_profile_type"] == "VerifierExecutionProfileV2"
    for type_id in ("PolicyProfileControlV2", "PolicyQueryV2", "VerifiedAdmissionV2"):
        fields = {
            row["id"] for row in _row(document["type_registry"], type_id)["field_specs"]
        }
        assert any("verifier_execution_profile" in field_id for field_id in fields)


def test_outbox_ack_port_binds_writer_epoch_in_both_directions() -> None:
    port = _row(_document()["port_contracts"], "P_OUTBOX_ACK_SUBMISSION")

    for field_id in (
        "request_guarantees",
        "callee_request_assumptions",
        "response_guarantees",
        "caller_response_assumptions",
    ):
        assert "WRITER_EPOCH_BOUND" in port[field_id]


def test_verifier_bootstrap_remains_an_external_unverified_premise() -> None:
    bootstrap = _document()["verifier_bootstrap"]

    assert bootstrap == contract.EXPECTED_VERIFIER_BOOTSTRAP
    assert bootstrap["identity_status"] == "REQUIRED_EXTERNAL_AUTHENTICATED_RECEIPT"
    assert bootstrap["self_verification_allowed"] is False
    assert bootstrap["promotion_use_allowed"] is False


def test_variant_field_contracts_close_direct_zrpf_and_native_backup() -> None:
    document = _document()
    admission = _row(document["type_registry"], "ExecutionAdmissionV2")
    proof = _row(document["type_registry"], "ProofRecordV2")
    verifier = _row(document["type_registry"], "VerifierExecutionProfileV2")

    admission_contracts = admission["variant_field_contracts"]
    assert "verified_zrpf_journal" in admission_contracts["ZRPF_ROOT"][
        "required_field_ids"
    ]
    assert "verified_zrpf_journal" in admission_contracts["DIRECT_EXECUTION"][
        "forbidden_field_ids"
    ]
    assert {
        "image_id",
        "journal_root",
        "verified_witness_id",
    } <= set(proof["variant_field_contracts"]["ZRPF_ROOT"]["required_field_ids"])
    assert {
        "equivalence_receipt_root",
        "governance_authorization_root",
    } <= set(verifier["variant_field_contracts"]["NATIVE_BACKUP"]["required_field_ids"])


def test_renderer_document_mutation_cannot_change_checker_owned_contract() -> None:
    document = renderer.build_document()
    type_row = _row(document["type_registry"], "VerifiedAdmissionV2")
    type_row["caller_constructible_authority"] = True

    assert contract.EXPECTED_TYPE_SPECS["VerifiedAdmissionV2"][
        "caller_constructible_authority"
    ] is False
    report = checker.check_document(document)
    assert report["ok"] is False
    assert any("type_registry[VerifiedAdmissionV2]" in error for error in report["errors"])


@pytest.mark.parametrize(
    ("mutant_id", "mutate", "expected_error"),
    MUTANTS,
    ids=[mutant_id for mutant_id, _, _ in MUTANTS],
)
def test_named_structural_mutants_fail_closed(
    mutant_id: str,
    mutate: Callable[[dict[str, Any]], None],
    expected_error: str,
) -> None:
    document = _document()
    mutate(document)

    report = checker.check_document(document)

    assert mutant_id in contract.EXPECTED_MUTANTS
    assert report["ok"] is False
    assert any(expected_error in error for error in report["errors"])
    assert report["promotion_eligible"] is False
    assert report["architecture_selected"] is False
    assert report["production_ready"] is False


def test_mutant_registry_matches_executable_mutations() -> None:
    declared = {row["id"] for row in _document()["named_mutants"]}
    executable = {mutant_id for mutant_id, _, _ in MUTANTS}

    assert declared == (executable | NON_DOCUMENT_MUTANTS) == contract.EXPECTED_MUTANTS


def test_source_split_snapshot_fails_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    original = checker._read_one_source
    target = "docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json"
    calls: dict[str, int] = {}

    def split_read(
        repo_root: Path, relative_path: str, errors: list[str]
    ) -> checker.SourceSnapshot | None:
        snapshot = original(repo_root, relative_path, errors)
        calls[relative_path] = calls.get(relative_path, 0) + 1
        if relative_path == target and calls[relative_path] == 2 and snapshot is not None:
            changed = b"{}"
            return checker.SourceSnapshot(
                relative_path=relative_path,
                data=changed,
                sha256=checker._sha256(changed),
                device=snapshot.device,
                inode=snapshot.inode,
                size=len(changed),
                mtime_ns=snapshot.mtime_ns + 1,
            )
        return snapshot

    monkeypatch.setattr(checker, "_read_one_source", split_read)
    report = checker.check_artifact()

    assert report["ok"] is False
    assert any("SOURCE_SPLIT_SNAPSHOT" in error for error in report["errors"])


def test_contract_execution_snapshot_split_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    document = _document()
    original = checker._read_one_source
    target = "tools/production_readiness_architecture_candidate_contract_v2.py"
    changed = b"# stable replacement contract bytes\n"
    source_pin = _row(document["source_pins"], target)
    source_pin["sha256"] = checker._sha256(changed)

    def substituted_read(
        repo_root: Path, relative_path: str, errors: list[str]
    ) -> checker.SourceSnapshot | None:
        snapshot = original(repo_root, relative_path, errors)
        if relative_path != target or snapshot is None:
            return snapshot
        return checker.SourceSnapshot(
            relative_path=relative_path,
            data=changed,
            sha256=checker._sha256(changed),
            device=snapshot.device,
            inode=snapshot.inode,
            size=len(changed),
            mtime_ns=snapshot.mtime_ns,
        )

    monkeypatch.setattr(checker, "_read_one_source", substituted_read)
    report = checker.check_document(document)

    assert report["ok"] is False
    assert any("SOURCE_EXECUTION_SNAPSHOT_SPLIT" in error for error in report["errors"])


def test_source_symlink_substitution_fails_closed(tmp_path: Path) -> None:
    target = tmp_path / "target.json"
    target.write_text("{}\n", encoding="utf-8")
    link = tmp_path / "source.json"
    link.symlink_to(target.name)
    errors: list[str] = []

    snapshot = checker._read_one_source(tmp_path, "source.json", errors)

    assert snapshot is None
    assert any("SOURCE_SYMLINK_SUBSTITUTION" in error for error in errors)


def test_intermediate_source_symlink_substitution_fails_closed(tmp_path: Path) -> None:
    real_directory = tmp_path / "real"
    real_directory.mkdir()
    (real_directory / "source.json").write_text("{}\n", encoding="utf-8")
    (tmp_path / "alias").symlink_to(real_directory.name, target_is_directory=True)
    errors: list[str] = []

    snapshot = checker._read_one_source(tmp_path, "alias/source.json", errors)

    assert snapshot is None
    assert any("SOURCE_SYMLINK_SUBSTITUTION" in error for error in errors)


def test_source_pin_tampering_fails_closed() -> None:
    document = _document()
    document["source_pins"][0]["sha256"] = "0" * 64

    report = checker.check_document(document)

    assert report["ok"] is False
    assert any("source pin digest mismatch" in error for error in report["errors"])


def test_g1_command_binding_tampering_fails_closed() -> None:
    document = _document()
    _row(document["command_registry"], "spot_swap")["source_semantics_id"] = "lp_add"

    report = checker.check_document(document)

    assert report["ok"] is False
    assert any("exact source binding" in error for error in report["errors"])


def test_duplicate_json_key_is_rejected(tmp_path: Path) -> None:
    artifact = tmp_path / "duplicate.json"
    artifact.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    report = checker.check_artifact(artifact)

    assert report["ok"] is False
    assert "duplicate JSON keys" in report["errors"][0]
