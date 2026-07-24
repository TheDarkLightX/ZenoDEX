#!/usr/bin/env python3
"""Packet-bound, authority-neutral release checks for remote ZRPF reproof V2.

This adapter closes the final executable stage of the remote reproof handoff.
It validates the pre-release execution packet, binds every declared input byte,
recomposes the existing Spot V7 release closure, and cross-checks the V7 and
mutation reports against their exact artifacts.  It deliberately cannot mint
proof, release, settlement, ledger, or production authority.

The completed Return V5 bundle is intentionally absent from this ABI.  It is
constructed only after this stage publishes its terminal marker; consuming it
here would create a release-evidence/marker/return self-reference.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import stat
import sys
from pathlib import Path
from typing import Any, Final, Mapping, NoReturn, Sequence, cast

if __package__ in {None, ""}:  # pragma: no cover - direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import check_zrpf_spot_settlement_v7_local_evidence as v7_static
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as identity
from tools import run_zrpf_remote_worker_prover_build_stage_v2 as worker_build
from tools import zrpf_remote_reproof_handoff_v2_catalog as catalog
from tools import zrpf_remote_reproof_worker_v2_contract as worker_contract
from tools import zrpf_spot_v7_release_closure as release
from tools import zrpf_spot_v7_release_schema as release_schema
from tools import zrpf_v6_v7_post_pin_governance as governance

EXPECTATION_SCHEMA_V1: Final = "zenodex/zrpf_remote_release_plan_expectation/v1"
EXPECTATION_STATUS_V1: Final = "external_exact_release_plan_expectation"
EVIDENCE_SCHEMA_V2: Final = "zenodex/zrpf_remote_release_checks_evidence/v2"
EVIDENCE_STATUS_V2: Final = "packet_bound_authority_neutral_release_checks_complete"
EVIDENCE_DOMAIN_V2: Final = b"zenodex/zrpf_remote_release_checks_evidence_id/v2\0"
ZERO_SHA256: Final = "0" * 64

MAX_EXPECTATION_BYTES: Final = 64 * 1024
MAX_EXECUTION_PACKET_BYTES: Final = 256 * 1024
MAX_JSON_DEPTH: Final = 12
MAX_JSON_INTEGER_DIGITS: Final = 20
MUTATION_RECEIPT_PROFILE_ID: Final = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
MAX_VALUE_NODE_JOURNAL_BYTES_V4: Final = 65_536
MUTATION_JOURNAL_MAXIMUMS_V1: Final = {
    "v6_leaf": MAX_VALUE_NODE_JOURNAL_BYTES_V4,
    "v6_l1": MAX_VALUE_NODE_JOURNAL_BYTES_V4,
    "v6_l2": MAX_VALUE_NODE_JOURNAL_BYTES_V4,
    "v6_settlement": v7_static.MAX_V6_CHILD_JOURNAL_BYTES_V1,
    "v7_settlement": v7_static.V7_MAX_OUTPUT_BYTES_V1,
}

AUTHORITY_FIELDS_V2: Final = (
    "complete_build_input_closure_verified",
    "cross_host_reproducible_build",
    "data_availability_verified",
    "finality_verified",
    "proof_authority",
    "proofs_generated",
    "production_authority",
    "receipts_verified",
    "release_authority",
    "runtime_execution_verified",
    "settlement_authority",
    "source_to_program_binary_provenance_verified",
)

NON_CLAIMS_V2: Final = (
    "release_checks_bind_returned_bytes_but_do_not_reverify_every_receipt",
    "worker_reports_and_publication_markers_are_authority_neutral_observations",
    "release_evidence_does_not_independently_reopen_or_validate_marker_records",
    "direct_adapter_output_pair_publication_is_not_atomic_without_worker_terminal_marker",
    "no_complete_build_input_or_cross_host_reproducibility_claim",
    "no_data_availability_retrievability_or_finality_authority",
    "no_live_jailer_firecracker_or_runtime_attestation",
    "no_release_selection_activation_revocation_or_rollback_authority",
    "no_proof_ledger_settlement_release_or_production_authority",
    "final_return_v5_is_validated_only_after_terminal_marker_publication",
)

VALIDATED_FACTS_V2: Final = {
    "execution_packet_identity_checked": True,
    "ordered_input_artifact_ids_recomputed": True,
    "ordered_predecessor_marker_digest_list_committed": True,
    "identity_and_governance_reports_recomposed": True,
    "worker_build_report_bound_to_exact_outputs": True,
    "v7_report_bound_to_exact_artifacts": True,
    "mutation_report_bound_to_exact_programs_receipts_and_mutations": True,
    "release_closure_plan_recomposed": True,
    "external_plan_expectation_matched": True,
    "final_return_v5_excluded_to_preserve_acyclicity": True,
    "no_authority_promoted": True,
}
REPORT_BINDING_FIELDS_V2: Final = {
    "identity_candidate_report_sha256",
    "post_pin_governance_sha256",
    "worker_build_report_sha256",
    "mutation_report_id",
    "mutation_report_sha256",
    "v7_report_sha256",
    "v7_program_id",
    "release_runtime_identity_sha256",
}
CLOSURE_EVIDENCE_FIELDS_V1: Final = {
    "schema",
    "status",
    "plan_sha256",
    "c0_commit",
    "c1_commit",
    "c2_commit",
    "governance_commit",
    "governance_tree",
    "v7_child_image_id",
    "source_closure_root_sha256",
    "lockfile_set_root_sha256",
    "runtime_identity_sha256",
    "validated_facts",
    "authority",
    "non_claims",
}
CLOSURE_VALIDATED_FACTS_V1: Final = {
    "literal_c0_c1_c2_g_ancestry_checked": True,
    "governed_nonzero_v7_child_pin_checked": True,
    "recursive_local_path_dependency_graph_checked": True,
    "local_cargo_patch_and_replace_overrides_checked": True,
    "all_reached_workspace_lockfiles_bound": True,
    "ancestor_cargo_configs_bound": True,
    "tracked_workspace_source_superset_bound": True,
    "literal_external_compiler_inputs_bound": True,
    "literal_compiler_input_fixed_point_checked": True,
    "literal_compiler_source_graph_acyclic": True,
    "toolchain_and_container_identities_bound": True,
    "declared_runtime_identity_bound": True,
    "no_authority_promoted": True,
}

EXPECTATION_NON_CLAIMS_V1: Final = (
    "expectation_bytes_do_not_attest_build_or_runtime_execution",
    "expectation_bytes_do_not_verify_proofs_receipts_or_mutations",
    "expectation_bytes_grant_no_release_settlement_or_production_authority",
)

IDENTITY_PROGRAM_ROLES: Final = (
    "source_program",
    "v2_adapter_program",
    "v6_leaf_program",
    "v6_l1_program",
    "v6_l2_program",
    "v6_settlement_program",
)

WORKER_BUILD_OUTPUT_ROLES: Final = tuple(worker_build.BUILD_OUTPUT_ROLES)

PROOF_ARTIFACT_ROLES: Final = (
    "source_proof",
    "v2_adapter_receipt",
    "v6_leaf_receipt",
    "v6_l1_receipt",
    "v6_l2_receipt",
    "v6_settlement_receipt",
    "v7_receipt",
    "v6_settlement_journal",
    "v7_journal",
    "v7_guest_input",
    "v7_verifier_output",
    "v7_plan_b",
    "v6_leaf_seal_mutation",
    "v6_l1_seal_mutation",
    "v6_l2_seal_mutation",
    "v6_settlement_seal_mutation",
    "v7_seal_mutation",
    "v7_report",
    "mutation_report",
)

RELEASE_CHECK_ARTIFACT_ROLES: Final = catalog.RELEASE_CHECK_ARTIFACT_ROLES
PACKET_INPUT_ROLES: Final = catalog.RELEASE_CHECK_INPUT_ROLES

MUTATION_STAGE_BINDINGS: Final = (
    (
        "v6_leaf",
        "v6_leaf_program",
        "v6_leaf_receipt",
        "v6_leaf_seal_mutation",
        None,
        "VerifiedSourceOpenedSpotValueLeafReceiptV6",
    ),
    (
        "v6_l1",
        "v6_l1_program",
        "v6_l1_receipt",
        "v6_l1_seal_mutation",
        None,
        "VerifiedValueAggregateReceiptV5",
    ),
    (
        "v6_l2",
        "v6_l2_program",
        "v6_l2_receipt",
        "v6_l2_seal_mutation",
        None,
        "VerifiedValueAggregateReceiptV5",
    ),
    (
        "v6_settlement",
        "v6_settlement_program",
        "v6_settlement_receipt",
        "v6_settlement_seal_mutation",
        "v6_settlement_journal",
        "VerifiedSourceOpenedSpotSettlementAdmissionV6",
    ),
    (
        "v7_settlement",
        "v7_program",
        "v7_receipt",
        "v7_seal_mutation",
        "v7_journal",
        "VerifiedSpotSettlementV7ReceiptV1",
    ),
)

MUTATION_REPORT_FIELDS: Final = (
    "schema",
    "status",
    "report_id",
    "receipt_profile_id",
    "positive_receipts_verified",
    "exact_seal_mutations_rejected",
    "settlement_l2_claim_bound",
    "stages",
    "authority",
    "non_claims",
)
MUTATION_STAGE_FIELDS: Final = (
    "stage_id",
    "program",
    "receipt_profile_id",
    "positive_receipt_bytes",
    "positive_receipt_sha256",
    "positive_journal_sha256",
    "mutation_receipt_bytes",
    "mutation_receipt_sha256",
    "mutation",
    "reject_boundary",
    "reject_code",
)
MUTATION_PROGRAM_FIELDS: Final = (
    "program_bytes",
    "program_sha256",
    "expected_image_id",
)
MUTATION_FACT_FIELDS: Final = (
    "word_count",
    "word_index",
    "original_word",
    "mutated_word",
    "xor_mask",
)
MUTATION_AUTHORITY_FIELDS: Final = (
    "proof_authority",
    "release_authority",
    "settlement_authority",
    "production_authority",
)
MUTATION_NON_CLAIMS: Final = (
    "report_is_an_unkeyed_authority_neutral_process_observation",
    "report_does_not_establish_source_to_binary_or_release_provenance",
    "report_does_not_establish_data_availability_finality_or_ledger_admission",
    "report_does_not_grant_proof_release_settlement_or_production_authority",
)
MUTATION_REPORT_DOMAIN: Final = b"zenodex/zrpf_remote_mutation_verification_report_id/v1\0"
MUTATION_REPORT_SCHEMA: Final = "zenodex/zrpf_remote_mutation_verification/v1"
MUTATION_REPORT_STATUS: Final = "five_positive_receipts_verified_and_five_exact_mutations_rejected"

V7_REPORT_FIELDS: Final = {
    "schema",
    "status",
    "v7_program_id",
    "v7_profile_id",
    "v7_program_manifest_root",
    "v7_journal_sha256",
    "v7_receipt_sha256",
    "v7_receipt_seal_mutation_sha256",
    "v7_verifier_output_sha256",
    "v7_plan_b_sha256",
    "v7_guest_input_sha256",
    "v6_child_receipt_sha256",
    "receipt_kind",
    "exact_seal_mutation_rejected",
    "release_authority",
    "settlement_authority",
    "production_authority",
    "zero_knowledge_privacy",
    "nonclaims",
}
V7_NON_CLAIMS: Final = (
    "candidate generation does not establish source or build provenance",
    "candidate generation does not establish Firecracker execution",
    "candidate generation does not establish data retrievability or finality",
    "candidate generation grants no release settlement or production authority",
)


class RemoteReleaseChecksError(ValueError):
    """Stable fail-closed rejection at the packet-bound release stage."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


def false_authority_v2() -> dict[str, bool]:
    return {field: False for field in AUTHORITY_FIELDS_V2}


def derive_release_evidence_id_v2(document: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(document))
    candidate["evidence_id"] = ZERO_SHA256
    return hashlib.sha256(EVIDENCE_DOMAIN_V2 + handoff.canonical_json_bytes(candidate)).hexdigest()


def run_release_checks_stage_v2(
    *,
    repository: Path,
    execution_packet_path: Path,
    expectation_path: Path,
    artifact_paths: Mapping[str, Path],
    release_plan_output: Path,
    release_evidence_output: Path,
) -> dict[str, object]:
    """Validate one exact release packet and write its two authority-false outputs."""

    repo = _canonical_directory(repository, "repository")
    paths = _require_artifact_path_inventory(artifact_paths)
    expectation_raw = _stable_read(
        expectation_path, "release plan expectation", MAX_EXPECTATION_BYTES
    )
    expectation = _parse_expectation(expectation_raw)
    packet_raw = _stable_read(
        execution_packet_path, "release execution packet", MAX_EXECUTION_PACKET_BYTES
    )
    packet = _parse_release_packet(packet_raw)
    observations, artifact_raw = _bind_packet_artifacts(packet, paths, expectation_raw)

    runtime_raw = artifact_raw["release_runtime_identity"]
    runtime = _decode_sorted_canonical_json(runtime_raw, "release runtime identity")
    runtime = release_schema.validate_runtime_identity(runtime)
    _validate_expectation_bindings(expectation, packet, runtime_raw)

    identity_images = _validate_identity_and_governance(repo, packet, expectation, artifact_raw)
    v7_report = _validate_v7_report(artifact_raw)
    _validate_worker_build(packet, artifact_raw, v7_report)
    mutation_report = _validate_mutation_report(artifact_raw, identity_images, v7_report)

    plan = release.build_release_closure_plan(repo, runtime)
    plan_sha256 = release.canonical_sha256(plan)
    if plan_sha256 != expectation["expected_plan_sha256"]:
        raise RemoteReleaseChecksError("release_plan_expectation_mismatch")
    closure_evidence = release.check_release_closure_plan(
        repo,
        plan,
        runtime,
        expected_plan_sha256=plan_sha256,
    )
    _require_existing_authority_false(
        closure_evidence.get("authority"), "closure_evidence_authority"
    )

    evidence = _build_evidence(
        packet=packet,
        plan_sha256=plan_sha256,
        closure_evidence=closure_evidence,
        observations=observations,
        artifact_raw=artifact_raw,
        mutation_report=mutation_report,
        v7_report=v7_report,
    )
    plan_raw = handoff.canonical_json_bytes(plan)
    evidence_raw = handoff.canonical_json_bytes(evidence)
    _require_distinct_absent_outputs(release_plan_output, release_evidence_output)
    _write_new(release_plan_output, plan_raw, "release plan")
    _write_new(release_evidence_output, evidence_raw, "release evidence")
    return evidence


def validate_release_evidence_v2(raw: bytes) -> dict[str, object]:
    """Strictly decode and self-authenticate one authority-neutral evidence object."""

    document = _decode_sorted_canonical_json(raw, "release evidence")
    fields = {
        "schema",
        "status",
        "evidence_id",
        "handoff_id",
        "execution_packet_id",
        "source_binding_id",
        "task_id",
        "stage_id",
        "ordinal",
        "worker_commit",
        "worker_tree",
        "proof_profile_id",
        "release_plan_sha256",
        "release_closure_evidence",
        "input_artifact_ids",
        "input_publication_marker_ids",
        "input_observations",
        "report_bindings",
        "validated_facts",
        "authority",
        "non_claims",
    }
    _require_exact_fields(document, fields, "release_evidence_fields")
    if document.get("schema") != EVIDENCE_SCHEMA_V2 or document.get("status") != EVIDENCE_STATUS_V2:
        raise RemoteReleaseChecksError("release_evidence_schema_status")
    if document.get("evidence_id") != derive_release_evidence_id_v2(document):
        raise RemoteReleaseChecksError("release_evidence_id")
    for field in (
        "handoff_id",
        "execution_packet_id",
        "source_binding_id",
        "task_id",
        "release_plan_sha256",
    ):
        _require_lower_hex(document.get(field), 64, f"release_evidence_{field}")
    for field in ("worker_commit", "worker_tree"):
        _require_lower_hex(document.get(field), 40, f"release_evidence_{field}")
    if (
        document.get("task_id") is None
        or document.get("stage_id") != "release_checks"
        or document.get("ordinal") != len(catalog.TASK_SPECS) - 1
        or document.get("proof_profile_id") != handoff.SUCCINCT_PROFILE_ID
    ):
        raise RemoteReleaseChecksError("release_evidence_stage")
    artifact_ids = _string_digest_list(
        document.get("input_artifact_ids"), "release_evidence_artifact_ids"
    )
    if len(artifact_ids) != len(PACKET_INPUT_ROLES) or len(set(artifact_ids)) != len(artifact_ids):
        raise RemoteReleaseChecksError("release_evidence_artifact_inventory")
    marker_ids = _string_digest_list(
        document.get("input_publication_marker_ids"), "release_evidence_marker_ids"
    )
    if len(marker_ids) != len(catalog.RELEASE_CHECK_PREDECESSOR_STAGE_IDS) or len(
        set(marker_ids)
    ) != len(marker_ids):
        raise RemoteReleaseChecksError("release_evidence_marker_inventory")
    observation_sha256 = _validate_evidence_observations(
        document.get("input_observations"), artifact_ids
    )
    report_bindings = _validate_report_bindings(document.get("report_bindings"))
    expected_report_observations = {
        "identity_candidate_report_sha256": observation_sha256["identity_candidate_report"],
        "post_pin_governance_sha256": observation_sha256["post_pin_governance_result"],
        "worker_build_report_sha256": observation_sha256["worker_build_report"],
        "mutation_report_sha256": observation_sha256["mutation_report"],
        "v7_report_sha256": observation_sha256["v7_report"],
        "release_runtime_identity_sha256": observation_sha256["release_runtime_identity"],
    }
    if any(
        report_bindings[field] != digest for field, digest in expected_report_observations.items()
    ):
        raise RemoteReleaseChecksError("release_evidence_report_observation_binding")
    _require_exact_boolean_facts(
        document.get("validated_facts"), VALIDATED_FACTS_V2, "release_evidence_facts"
    )
    _validate_closure_evidence(
        document.get("release_closure_evidence"),
        expected_plan_sha256=cast(str, document["release_plan_sha256"]),
        expected_worker_commit=cast(str, document["worker_commit"]),
        expected_runtime_identity_sha256=report_bindings["release_runtime_identity_sha256"],
    )
    _require_false_authority(
        document.get("authority"), AUTHORITY_FIELDS_V2, "release_evidence_authority"
    )
    if document.get("non_claims") != list(NON_CLAIMS_V2):
        raise RemoteReleaseChecksError("release_evidence_non_claims")
    if "bundle_id" in document or "return_bundle_id" in document:
        raise RemoteReleaseChecksError("release_evidence_return_cycle")
    return document


def _parse_expectation(raw: bytes) -> dict[str, object]:
    document = _decode_sorted_canonical_json(raw, "release plan expectation")
    _require_exact_fields(
        document,
        {
            "schema",
            "status",
            "expected_plan_sha256",
            "expected_c0_commit",
            "expected_worker_commit",
            "expected_runtime_identity_sha256",
            "authority",
            "non_claims",
        },
        "release_expectation_fields",
    )
    if (
        document.get("schema") != EXPECTATION_SCHEMA_V1
        or document.get("status") != EXPECTATION_STATUS_V1
    ):
        raise RemoteReleaseChecksError("release_expectation_schema_status")
    for field in ("expected_plan_sha256", "expected_runtime_identity_sha256"):
        _require_lower_hex(document.get(field), 64, f"release_expectation_{field}")
    for field in ("expected_c0_commit", "expected_worker_commit"):
        _require_lower_hex(document.get(field), 40, f"release_expectation_{field}")
    _require_false_authority(
        document.get("authority"), AUTHORITY_FIELDS_V2, "release_expectation_authority"
    )
    if document.get("non_claims") != list(EXPECTATION_NON_CLAIMS_V1):
        raise RemoteReleaseChecksError("release_expectation_non_claims")
    return document


def _parse_release_packet(raw: bytes) -> dict[str, object]:
    packet = _decode_sorted_canonical_json(raw, "release execution packet")
    _require_exact_fields(packet, worker_contract.EXECUTION_PACKET_FIELDS, "release_packet_fields")
    if packet.get("schema") != handoff.EXECUTION_PACKET_SCHEMA:
        raise RemoteReleaseChecksError("release_packet_schema")
    if packet.get("status") != "exact_inputs_bound_without_execution_provenance":
        raise RemoteReleaseChecksError("release_packet_status")
    if packet.get("execution_packet_id") != handoff.derive_execution_packet_id(packet):
        raise RemoteReleaseChecksError("release_packet_id")
    if (
        packet.get("stage_id") != "release_checks"
        or packet.get("ordinal") != len(catalog.TASK_SPECS) - 1
    ):
        raise RemoteReleaseChecksError("release_packet_stage")
    _require_false_authority(
        packet.get("authority"), handoff.AUTHORITY_FIELDS, "release_packet_authority"
    )
    if packet.get("non_claims") != list(handoff.NON_CLAIMS):
        raise RemoteReleaseChecksError("release_packet_non_claims")
    for field in ("handoff_id", "source_binding_id", "task_id"):
        _require_lower_hex(packet.get(field), 64, f"release_packet_{field}")
    for field in ("worker_commit", "worker_tree"):
        _require_lower_hex(packet.get(field), 40, f"release_packet_{field}")
    if packet.get("proof_profile_id") != handoff.SUCCINCT_PROFILE_ID:
        raise RemoteReleaseChecksError("release_packet_proof_profile")
    input_ids = _string_digest_list(packet.get("input_artifact_ids"), "release_packet_input_ids")
    if len(input_ids) != len(PACKET_INPUT_ROLES) or len(set(input_ids)) != len(input_ids):
        raise RemoteReleaseChecksError("release_packet_input_inventory")
    marker_ids = _string_digest_list(
        packet.get("input_publication_marker_ids"), "release_packet_marker_ids"
    )
    if len(marker_ids) != len(catalog.TASK_SPECS) - 1 or len(set(marker_ids)) != len(marker_ids):
        raise RemoteReleaseChecksError("release_packet_marker_inventory")
    return packet


def _bind_packet_artifacts(
    packet: Mapping[str, object],
    paths: Mapping[str, Path],
    expectation_raw: bytes,
) -> tuple[list[dict[str, object]], dict[str, bytes]]:
    contracts = {str(row["role"]): row for row in handoff._artifact_contracts()}
    observations: list[dict[str, object]] = []
    raw_by_role: dict[str, bytes] = {}
    for role in PACKET_INPUT_ROLES:
        try:
            contract = contracts[role]
        except KeyError as exc:
            raise RemoteReleaseChecksError("release_packet_contract_inventory") from exc
        maximum = cast(int, contract["maximum_bytes"])
        raw = (
            expectation_raw
            if role == "release_plan_expectation"
            else _stable_read(paths[role], role, maximum)
        )
        record = handoff._artifact_record_from_bytes(contract, cast(str, contract["path"]), raw)
        observations.append(
            {
                "role": role,
                "artifact_id": record["artifact_id"],
                "sha256": record["sha256"],
                "size_bytes": record["size_bytes"],
            }
        )
        raw_by_role[role] = raw
    expected_ids = [row["artifact_id"] for row in observations]
    if packet.get("input_artifact_ids") != expected_ids:
        raise RemoteReleaseChecksError("release_packet_artifact_binding")
    return observations, raw_by_role


def _validate_expectation_bindings(
    expectation: Mapping[str, object],
    packet: Mapping[str, object],
    runtime_raw: bytes,
) -> None:
    if expectation.get("expected_worker_commit") != packet.get("worker_commit"):
        raise RemoteReleaseChecksError("release_expectation_worker_commit")
    if (
        expectation.get("expected_runtime_identity_sha256")
        != hashlib.sha256(runtime_raw).hexdigest()
    ):
        raise RemoteReleaseChecksError("release_expectation_runtime_identity")


def _validate_identity_and_governance(
    repository: Path,
    packet: Mapping[str, object],
    expectation: Mapping[str, object],
    raw: Mapping[str, bytes],
) -> dict[str, str]:
    plan = _decode_sorted_canonical_json(raw["identity_plan"], "identity plan")
    observations = _decode_sorted_canonical_json(
        raw["identity_observations"], "identity observations"
    )
    report = _decode_sorted_canonical_json(raw["identity_candidate_report"], "identity report")
    c0 = cast(str, expectation["expected_c0_commit"])
    try:
        expected_plan = identity.build_plan(c0, catalog.IDENTITY_RUN_ROOT, repo_root=repository)
    except identity.RebuildPlanError as exc:
        raise RemoteReleaseChecksError("release_identity_plan_recomposition") from exc
    if not handoff._canonical_values_equal(plan, expected_plan):
        raise RemoteReleaseChecksError("release_identity_plan")
    try:
        expected_report = identity.check_observations(plan, observations, repo_root=repository)
    except identity.RebuildPlanError as exc:
        raise RemoteReleaseChecksError("release_identity_observations") from exc
    if not handoff._canonical_values_equal(report, expected_report):
        raise RemoteReleaseChecksError("release_identity_report")
    image_ids = _crosscheck_identity_programs(report, raw)

    governance_raw = raw["post_pin_governance_result"]
    observed_governance = _decode_sorted_canonical_json(governance_raw, "post-pin governance")
    try:
        expected_governance = governance.check_post_pin_governance(repository)
    except governance.GovernanceError as exc:
        raise RemoteReleaseChecksError("release_governance_recomposition") from exc
    if not handoff._canonical_values_equal(observed_governance, expected_governance):
        raise RemoteReleaseChecksError("release_governance_report")
    if (
        observed_governance.get("c0_commit") != c0
        or observed_governance.get("governance_commit") != packet.get("worker_commit")
        or observed_governance.get("plan_sha256")
        != hashlib.sha256(raw["identity_plan"]).hexdigest()
        or observed_governance.get("observations_sha256")
        != hashlib.sha256(raw["identity_observations"]).hexdigest()
        or observed_governance.get("candidate_report_sha256")
        != hashlib.sha256(raw["identity_candidate_report"]).hexdigest()
    ):
        raise RemoteReleaseChecksError("release_governance_lineage")
    return image_ids


def _crosscheck_identity_programs(
    report: Mapping[str, object], raw: Mapping[str, bytes]
) -> dict[str, str]:
    programs = report.get("programs")
    if type(programs) is not list or len(programs) != len(IDENTITY_PROGRAM_ROLES):
        raise RemoteReleaseChecksError("release_identity_program_inventory")
    expected_stage_by_role = {role: stage for stage, role in handoff.IDENTITY_STAGE_ROLES.items()}
    image_ids: dict[str, str] = {}
    for role, row in zip(IDENTITY_PROGRAM_ROLES, programs, strict=True):
        if type(row) is not dict or row.get("stage_id") != expected_stage_by_role[role]:
            raise RemoteReleaseChecksError("release_identity_program_order")
        program_raw = raw[role]
        if (
            row.get("program_binary_bytes") != len(program_raw)
            or row.get("program_binary_sha256") != hashlib.sha256(program_raw).hexdigest()
        ):
            raise RemoteReleaseChecksError("release_identity_program_binding")
        image_ids[role] = _require_lower_hex(row.get("image_id"), 64, "release_identity_image")
    return image_ids


def _validate_worker_build(
    packet: Mapping[str, object], raw: Mapping[str, bytes], v7_report: Mapping[str, object]
) -> None:
    output_bytes = {role: raw[role] for role in WORKER_BUILD_OUTPUT_ROLES}
    try:
        worker_build.validate_worker_build_report(
            raw["worker_build_report"],
            output_bytes,
            raw["post_pin_governance_result"],
            expected_source_commit=cast(str, packet["worker_commit"]),
            expected_v7_image_id=cast(str, v7_report["v7_program_id"]),
        )
    except worker_build.WorkerBuildError as exc:
        raise RemoteReleaseChecksError("release_worker_build_report") from exc


def _validate_v7_report(raw: Mapping[str, bytes]) -> dict[str, object]:
    try:
        analysis = v7_static.analyze_artifacts_v1(
            {
                "v7_receipt": raw["v7_receipt"],
                "v7_receipt_seal_mutation": raw["v7_seal_mutation"],
                "v6_child_receipt": raw["v6_settlement_receipt"],
                "v7_guest_input": raw["v7_guest_input"],
                "v7_journal": raw["v7_journal"],
                "v7_verifier_output": raw["v7_verifier_output"],
                "v7_plan_b": raw["v7_plan_b"],
            }
        )
    except v7_static.EvidenceError as exc:
        raise RemoteReleaseChecksError("release_v7_static_relations") from exc
    report = _decode_ordered_json_line(raw["v7_report"], "V7 proof report")
    _require_exact_fields(report, V7_REPORT_FIELDS, "release_v7_report_fields")
    if report.get("schema") != "zenodex/zrpf_spot_settlement_v7_proof_report/v1":
        raise RemoteReleaseChecksError("release_v7_report_schema")
    if report.get("status") != "spot_settlement_v7_succinct_receipt_verified_before_persistence":
        raise RemoteReleaseChecksError("release_v7_report_status")
    bindings = {
        "v7_journal_sha256": "v7_journal",
        "v7_receipt_sha256": "v7_receipt",
        "v7_receipt_seal_mutation_sha256": "v7_seal_mutation",
        "v7_verifier_output_sha256": "v7_verifier_output",
        "v7_plan_b_sha256": "v7_plan_b",
        "v7_guest_input_sha256": "v7_guest_input",
        "v6_child_receipt_sha256": "v6_settlement_receipt",
    }
    for field, role in bindings.items():
        if report.get(field) != hashlib.sha256(raw[role]).hexdigest():
            raise RemoteReleaseChecksError("release_v7_report_artifact_binding")
    for field in ("v7_program_id", "v7_profile_id", "v7_program_manifest_root"):
        _require_lower_hex(report.get(field), 64, f"release_v7_{field}")
    if (
        report.get("v7_program_id") != analysis.output.fixed_fields[0].hex()
        or report.get("v7_profile_id") != analysis.output.fixed_fields[1].hex()
        or report.get("v7_program_manifest_root") != analysis.output.fixed_fields[2].hex()
    ):
        raise RemoteReleaseChecksError("release_v7_output_identity_binding")
    if (
        report.get("receipt_kind") != "succinct"
        or report.get("exact_seal_mutation_rejected") is not True
    ):
        raise RemoteReleaseChecksError("release_v7_report_receipt_policy")
    for field in (
        "release_authority",
        "settlement_authority",
        "production_authority",
        "zero_knowledge_privacy",
    ):
        if report.get(field) is not False:
            raise RemoteReleaseChecksError("release_v7_report_authority")
    if report.get("nonclaims") != list(V7_NON_CLAIMS):
        raise RemoteReleaseChecksError("release_v7_report_nonclaims")
    return report


def _validate_mutation_report(
    raw: Mapping[str, bytes],
    identity_images: Mapping[str, str],
    v7_report: Mapping[str, object],
) -> dict[str, object]:
    report = _decode_ordered_json_line(raw["mutation_report"], "mutation report")
    if tuple(report) != MUTATION_REPORT_FIELDS:
        raise RemoteReleaseChecksError("release_mutation_report_fields")
    if (
        report.get("schema") != MUTATION_REPORT_SCHEMA
        or report.get("status") != MUTATION_REPORT_STATUS
    ):
        raise RemoteReleaseChecksError("release_mutation_report_schema_status")
    if report.get("report_id") != _derive_mutation_report_id(report):
        raise RemoteReleaseChecksError("release_mutation_report_id")
    if (
        report.get("positive_receipts_verified") != 5
        or report.get("exact_seal_mutations_rejected") != 5
        or report.get("settlement_l2_claim_bound") is not True
    ):
        raise RemoteReleaseChecksError("release_mutation_report_facts")
    _require_false_authority(
        report.get("authority"), MUTATION_AUTHORITY_FIELDS, "release_mutation_authority"
    )
    if report.get("non_claims") != list(MUTATION_NON_CLAIMS):
        raise RemoteReleaseChecksError("release_mutation_nonclaims")
    stages = report.get("stages")
    if type(stages) is not list or len(stages) != len(MUTATION_STAGE_BINDINGS):
        raise RemoteReleaseChecksError("release_mutation_stage_inventory")
    common_profile = report.get("receipt_profile_id")
    if common_profile != MUTATION_RECEIPT_PROFILE_ID:
        raise RemoteReleaseChecksError("release_mutation_profile")
    for row, binding in zip(stages, MUTATION_STAGE_BINDINGS, strict=True):
        _validate_mutation_stage(row, binding, raw, identity_images, v7_report, common_profile)
    return report


def _validate_mutation_stage(
    value: object,
    binding: tuple[str, str, str, str, str | None, str],
    raw: Mapping[str, bytes],
    identity_images: Mapping[str, str],
    v7_report: Mapping[str, object],
    common_profile: str,
) -> None:
    if type(value) is not dict or tuple(value) != MUTATION_STAGE_FIELDS:
        raise RemoteReleaseChecksError("release_mutation_stage_fields")
    row = cast(dict[str, object], value)
    stage_id, program_role, receipt_role, mutation_role, journal_role, boundary = binding
    if row.get("stage_id") != stage_id or row.get("receipt_profile_id") != common_profile:
        raise RemoteReleaseChecksError("release_mutation_stage_identity")
    program = row.get("program")
    mutation = row.get("mutation")
    if type(program) is not dict or tuple(program) != MUTATION_PROGRAM_FIELDS:
        raise RemoteReleaseChecksError("release_mutation_program_fields")
    if type(mutation) is not dict or tuple(mutation) != MUTATION_FACT_FIELDS:
        raise RemoteReleaseChecksError("release_mutation_fact_fields")
    program_raw, receipt_raw, mutation_raw = (
        raw[program_role],
        raw[receipt_role],
        raw[mutation_role],
    )
    if (
        program.get("program_bytes") != len(program_raw)
        or program.get("program_sha256") != hashlib.sha256(program_raw).hexdigest()
    ):
        raise RemoteReleaseChecksError("release_mutation_program_binding")
    expected_image = (
        cast(str, v7_report["v7_program_id"])
        if program_role == "v7_program"
        else identity_images[program_role]
    )
    if program.get("expected_image_id") != expected_image:
        raise RemoteReleaseChecksError("release_mutation_image_binding")
    if (
        row.get("positive_receipt_bytes") != len(receipt_raw)
        or row.get("positive_receipt_sha256") != hashlib.sha256(receipt_raw).hexdigest()
    ):
        raise RemoteReleaseChecksError("release_mutation_receipt_binding")
    if (
        row.get("mutation_receipt_bytes") != len(mutation_raw)
        or row.get("mutation_receipt_sha256") != hashlib.sha256(mutation_raw).hexdigest()
    ):
        raise RemoteReleaseChecksError("release_mutation_artifact_binding")
    _require_lower_hex(row.get("positive_journal_sha256"), 64, "release_mutation_journal")
    if (
        journal_role is not None
        and row.get("positive_journal_sha256") != hashlib.sha256(raw[journal_role]).hexdigest()
    ):
        raise RemoteReleaseChecksError("release_mutation_journal_binding")
    derived_mutation, derived_journal_sha256, derived_claimed_image_id = (
        _derive_exact_receipt_mutation(
            receipt_raw,
            mutation_raw,
            maximum_journal_bytes=MUTATION_JOURNAL_MAXIMUMS_V1[stage_id],
        )
    )
    _validate_one_bit_mutation(mutation)
    if dict(mutation) != derived_mutation:
        raise RemoteReleaseChecksError("release_mutation_report_relation_binding")
    if row.get("positive_journal_sha256") != derived_journal_sha256:
        raise RemoteReleaseChecksError("release_mutation_receipt_journal_binding")
    if derived_claimed_image_id != expected_image:
        raise RemoteReleaseChecksError("release_mutation_receipt_image_binding")
    if (
        row.get("reject_boundary") != boundary
        or row.get("reject_code") != "receipt_verification_failed"
    ):
        raise RemoteReleaseChecksError("release_mutation_reject_boundary")


def _validate_one_bit_mutation(mutation: Mapping[str, object]) -> None:
    values = tuple(mutation.get(field) for field in MUTATION_FACT_FIELDS)
    if any(type(value) is not int for value in values):
        raise RemoteReleaseChecksError("release_mutation_integer_fields")
    word_count, word_index, original_word, mutated_word, xor_mask = cast(tuple[int, ...], values)
    if (
        word_count <= 1
        or word_index != 1
        or xor_mask != 1
        or not 0 <= original_word <= 0xFFFF_FFFF
        or not 0 <= mutated_word <= 0xFFFF_FFFF
        or mutated_word != original_word ^ 1
    ):
        raise RemoteReleaseChecksError("release_mutation_relation")


def _derive_exact_receipt_mutation(
    source_raw: bytes,
    candidate_raw: bytes,
    *,
    maximum_journal_bytes: int,
) -> tuple[dict[str, int], str, str]:
    if (
        not 0 < len(source_raw) <= v7_static.MAX_RECEIPT_BYTES_V1
        or not 0 < len(candidate_raw) <= v7_static.MAX_RECEIPT_BYTES_V1
    ):
        raise RemoteReleaseChecksError("release_mutation_receipt_size")
    try:
        source = v7_static._decode_receipt(
            source_raw,
            "positive receipt",
            maximum_journal_bytes=maximum_journal_bytes,
        )
        candidate = v7_static._decode_receipt(
            candidate_raw,
            "mutation receipt",
            maximum_journal_bytes=maximum_journal_bytes,
        )
        original_word, mutated_word, word_count = v7_static._require_exact_seal_mutation(
            source,
            candidate,
        )
    except v7_static.EvidenceError as exc:
        raise RemoteReleaseChecksError("release_mutation_receipt_relation") from exc
    return (
        {
            "word_count": word_count,
            "word_index": 1,
            "original_word": original_word,
            "mutated_word": mutated_word,
            "xor_mask": 1,
        },
        hashlib.sha256(source.journal_bytes).hexdigest(),
        source.claimed_image_id.hex(),
    )


def _derive_mutation_report_id(report: Mapping[str, object]) -> str:
    committed = copy.deepcopy(dict(report))
    committed["report_id"] = ZERO_SHA256
    canonical = json.dumps(committed, ensure_ascii=True, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(MUTATION_REPORT_DOMAIN + canonical).hexdigest()


def _build_evidence(
    *,
    packet: Mapping[str, object],
    plan_sha256: str,
    closure_evidence: Mapping[str, object],
    observations: Sequence[Mapping[str, object]],
    artifact_raw: Mapping[str, bytes],
    mutation_report: Mapping[str, object],
    v7_report: Mapping[str, object],
) -> dict[str, object]:
    document: dict[str, object] = {
        "schema": EVIDENCE_SCHEMA_V2,
        "status": EVIDENCE_STATUS_V2,
        "evidence_id": ZERO_SHA256,
        "handoff_id": packet["handoff_id"],
        "execution_packet_id": packet["execution_packet_id"],
        "source_binding_id": packet["source_binding_id"],
        "task_id": packet["task_id"],
        "stage_id": packet["stage_id"],
        "ordinal": packet["ordinal"],
        "worker_commit": packet["worker_commit"],
        "worker_tree": packet["worker_tree"],
        "proof_profile_id": packet["proof_profile_id"],
        "release_plan_sha256": plan_sha256,
        "release_closure_evidence": copy.deepcopy(dict(closure_evidence)),
        "input_artifact_ids": list(cast(Sequence[str], packet["input_artifact_ids"])),
        "input_publication_marker_ids": list(
            cast(Sequence[str], packet["input_publication_marker_ids"])
        ),
        "input_observations": [dict(row) for row in observations],
        "report_bindings": {
            "identity_candidate_report_sha256": hashlib.sha256(
                artifact_raw["identity_candidate_report"]
            ).hexdigest(),
            "post_pin_governance_sha256": hashlib.sha256(
                artifact_raw["post_pin_governance_result"]
            ).hexdigest(),
            "worker_build_report_sha256": hashlib.sha256(
                artifact_raw["worker_build_report"]
            ).hexdigest(),
            "mutation_report_id": mutation_report["report_id"],
            "mutation_report_sha256": hashlib.sha256(artifact_raw["mutation_report"]).hexdigest(),
            "v7_report_sha256": hashlib.sha256(artifact_raw["v7_report"]).hexdigest(),
            "v7_program_id": v7_report["v7_program_id"],
            "release_runtime_identity_sha256": hashlib.sha256(
                artifact_raw["release_runtime_identity"]
            ).hexdigest(),
        },
        "validated_facts": dict(VALIDATED_FACTS_V2),
        "authority": false_authority_v2(),
        "non_claims": list(NON_CLAIMS_V2),
    }
    document["evidence_id"] = derive_release_evidence_id_v2(document)
    return validate_release_evidence_v2(handoff.canonical_json_bytes(document))


def _require_artifact_path_inventory(value: Mapping[str, Path]) -> dict[str, Path]:
    if set(value) != set(RELEASE_CHECK_ARTIFACT_ROLES):
        raise RemoteReleaseChecksError("release_artifact_role_inventory")
    return {role: Path(value[role]) for role in RELEASE_CHECK_ARTIFACT_ROLES}


def _validate_evidence_observations(value: object, artifact_ids: Sequence[str]) -> dict[str, str]:
    if type(value) is not list or len(value) != len(PACKET_INPUT_ROLES):
        raise RemoteReleaseChecksError("release_evidence_observation_inventory")
    contracts = {str(row["role"]): row for row in handoff._artifact_contracts()}
    sha256_by_role: dict[str, str] = {}
    for role, artifact_id, item in zip(PACKET_INPUT_ROLES, artifact_ids, value, strict=True):
        if type(item) is not dict or set(item) != {"role", "artifact_id", "sha256", "size_bytes"}:
            raise RemoteReleaseChecksError("release_evidence_observation_fields")
        if item.get("role") != role or item.get("artifact_id") != artifact_id:
            raise RemoteReleaseChecksError("release_evidence_observation_order")
        digest = _require_lower_hex(item.get("sha256"), 64, "release_evidence_observation_sha256")
        maximum = cast(int, contracts[role]["maximum_bytes"])
        size = item.get("size_bytes")
        if type(size) is not int or not 0 < size <= maximum:
            raise RemoteReleaseChecksError("release_evidence_observation_size")
        expected_record: dict[str, object] = {
            "schema": handoff.ARTIFACT_RECORD_SCHEMA,
            "artifact_id": ZERO_SHA256,
            "contract_id": contracts[role]["contract_id"],
            "role": role,
            "path": contracts[role]["path"],
            "sha256": digest,
            "size_bytes": size,
            "producer_stage": contracts[role]["producer_stage"],
        }
        if artifact_id != handoff._derive_artifact_id(expected_record):
            raise RemoteReleaseChecksError("release_evidence_observation_artifact_id")
        sha256_by_role[role] = digest
    return sha256_by_role


def _validate_report_bindings(value: object) -> dict[str, str]:
    if type(value) is not dict or set(value) != REPORT_BINDING_FIELDS_V2:
        raise RemoteReleaseChecksError("release_evidence_report_bindings")
    result: dict[str, str] = {}
    for field in REPORT_BINDING_FIELDS_V2:
        result[field] = _require_lower_hex(value.get(field), 64, f"release_evidence_report_{field}")
    return result


def _validate_closure_evidence(
    value: object,
    *,
    expected_plan_sha256: str,
    expected_worker_commit: str,
    expected_runtime_identity_sha256: str,
) -> None:
    if type(value) is not dict or set(value) != CLOSURE_EVIDENCE_FIELDS_V1:
        raise RemoteReleaseChecksError("release_evidence_closure_fields")
    if (
        value.get("schema") != release_schema.EVIDENCE_SCHEMA
        or value.get("status") != "authority_neutral_v7_release_closure_checked"
        or value.get("plan_sha256") != expected_plan_sha256
        or value.get("governance_commit") != expected_worker_commit
        or value.get("runtime_identity_sha256") != expected_runtime_identity_sha256
    ):
        raise RemoteReleaseChecksError("release_evidence_closure_binding")
    for field in (
        "source_closure_root_sha256",
        "lockfile_set_root_sha256",
        "runtime_identity_sha256",
        "v7_child_image_id",
    ):
        _require_lower_hex(value.get(field), 64, f"release_evidence_closure_{field}")
    for field in ("c0_commit", "c1_commit", "c2_commit", "governance_commit", "governance_tree"):
        _require_lower_hex(value.get(field), 40, f"release_evidence_closure_{field}")
    _require_exact_boolean_facts(
        value.get("validated_facts"),
        CLOSURE_VALIDATED_FACTS_V1,
        "release_evidence_closure_facts",
    )
    _require_false_authority(
        value.get("authority"),
        release_schema.AUTHORITY_FIELDS,
        "release_evidence_closure_authority",
    )
    if value.get("non_claims") != list(release_schema.NON_CLAIMS):
        raise RemoteReleaseChecksError("release_evidence_closure_non_claims")


def _require_exact_boolean_facts(value: object, expected: Mapping[str, bool], label: str) -> None:
    if (
        type(value) is not dict
        or value != expected
        or any(type(value.get(field)) is not bool for field in expected)
    ):
        raise RemoteReleaseChecksError(label)


def _require_existing_authority_false(value: object, label: str) -> None:
    expected = {field: False for field in release_schema.AUTHORITY_FIELDS}
    if (
        type(value) is not dict
        or value != expected
        or any(item is not False for item in value.values())
    ):
        raise RemoteReleaseChecksError(label)


def _require_false_authority(value: object, fields: Sequence[str], label: str) -> None:
    expected = {field: False for field in fields}
    if (
        type(value) is not dict
        or value != expected
        or any(item is not False for item in value.values())
    ):
        raise RemoteReleaseChecksError(label)


def _string_digest_list(value: object, label: str) -> list[str]:
    if type(value) is not list:
        raise RemoteReleaseChecksError(label)
    return [_require_lower_hex(item, 64, label) for item in value]


def _require_lower_hex(value: object, length: int, label: str) -> str:
    if (
        type(value) is not str
        or len(value) != length
        or any(byte not in "0123456789abcdef" for byte in value)
        or value == "0" * length
    ):
        raise RemoteReleaseChecksError(label)
    return value


def _require_exact_fields(value: object, fields: set[str] | frozenset[str], label: str) -> None:
    if type(value) is not dict or set(value) != set(fields):
        raise RemoteReleaseChecksError(label)


def _decode_sorted_canonical_json(raw: bytes, label: str) -> dict[str, object]:
    value = _decode_json(raw, label)
    if handoff.canonical_json_bytes(value) != raw:
        raise RemoteReleaseChecksError(f"{label}_canonical")
    return value


def _decode_ordered_json_line(raw: bytes, label: str) -> dict[str, object]:
    value = _decode_json(raw, label)
    expected = (json.dumps(value, ensure_ascii=True, separators=(",", ":")) + "\n").encode("ascii")
    if expected != raw:
        raise RemoteReleaseChecksError(f"{label}_canonical")
    return value


def _decode_json(raw: bytes, label: str) -> dict[str, object]:
    if not raw or not raw.endswith(b"\n") or raw.count(b"\n") != 1:
        raise RemoteReleaseChecksError(f"{label}_framing")
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_int=_bounded_int,
            parse_constant=_reject_float,
        )
    except RemoteReleaseChecksError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RemoteReleaseChecksError(f"{label}_json") from exc
    _validate_json_depth(value, 0)
    if type(value) is not dict:
        raise RemoteReleaseChecksError(f"{label}_object")
    return cast(dict[str, object], value)


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RemoteReleaseChecksError("duplicate_json_key")
        result[key] = value
    return result


def _reject_float(_value: str) -> NoReturn:
    raise RemoteReleaseChecksError("non_integer_json_number")


def _bounded_int(value: str) -> int:
    digits = value[1:] if value.startswith("-") else value
    if not digits or len(digits) > MAX_JSON_INTEGER_DIGITS:
        raise RemoteReleaseChecksError("json_integer_bound")
    return int(value)


def _validate_json_depth(value: object, depth: int) -> None:
    if depth > MAX_JSON_DEPTH:
        raise RemoteReleaseChecksError("json_depth")
    if type(value) is dict:
        for key, child in cast(dict[object, object], value).items():
            if type(key) is not str:
                raise RemoteReleaseChecksError("json_key")
            _validate_json_depth(child, depth + 1)
    elif type(value) is list:
        for child in value:
            _validate_json_depth(child, depth + 1)
    elif value is not None and type(value) not in {str, int, bool}:
        raise RemoteReleaseChecksError("json_scalar")


def _stable_read(path: Path, label: str, maximum: int) -> bytes:
    descriptor: int | None = None
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or not 0 < before.st_size <= maximum
        ):
            raise RemoteReleaseChecksError(f"{label}_file")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                raise RemoteReleaseChecksError(f"{label}_short_read")
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        after = os.fstat(descriptor)
    except OSError as exc:
        raise RemoteReleaseChecksError(f"{label}_read") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    if _stat_identity(before) != _stat_identity(after) or len(raw) != before.st_size:
        raise RemoteReleaseChecksError(f"{label}_changed")
    return raw


def _stat_identity(facts: os.stat_result) -> tuple[int, int, int, int, int, int, int]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_mode,
        facts.st_nlink,
        facts.st_size,
        facts.st_mtime_ns,
        facts.st_ctime_ns,
    )


def _canonical_directory(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise RemoteReleaseChecksError(f"{label}_absolute")
    try:
        resolved = path.resolve(strict=True)
        facts = path.lstat()
    except OSError as exc:
        raise RemoteReleaseChecksError(f"{label}_directory") from exc
    if resolved != path or path.is_symlink() or not stat.S_ISDIR(facts.st_mode):
        raise RemoteReleaseChecksError(f"{label}_canonical")
    return resolved


def _require_distinct_absent_outputs(left: Path, right: Path) -> None:
    if (
        not left.is_absolute()
        or not right.is_absolute()
        or left == right
        or left.exists()
        or left.is_symlink()
        or right.exists()
        or right.is_symlink()
    ):
        raise RemoteReleaseChecksError("release_output_precondition")
    parents: list[Path] = []
    for parent in (left.parent, right.parent):
        try:
            resolved = parent.resolve(strict=True)
            facts = parent.lstat()
        except OSError as exc:
            raise RemoteReleaseChecksError("release_output_parent") from exc
        if resolved != parent or parent.is_symlink() or not stat.S_ISDIR(facts.st_mode):
            raise RemoteReleaseChecksError("release_output_parent")
        parents.append(resolved)
    if left.parent == right.parent and parents[0] != parents[1]:
        raise RemoteReleaseChecksError("release_output_parent")


def _write_new(path: Path, raw: bytes, label: str) -> None:
    descriptor: int | None = None
    try:
        descriptor = os.open(
            path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        offset = 0
        while offset < len(raw):
            written = os.write(descriptor, raw[offset:])
            if written <= 0:
                raise RemoteReleaseChecksError(f"{label}_write_progress")
            offset += written
        os.fsync(descriptor)
    except OSError as exc:
        raise RemoteReleaseChecksError(f"{label}_write") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def _artifact_paths_from_args(args: argparse.Namespace) -> dict[str, Path]:
    return _require_artifact_path_inventory(
        {role: Path(getattr(args, f"artifact_{role}")) for role in RELEASE_CHECK_ARTIFACT_ROLES}
    )


def _parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--execution-packet", type=Path, required=True)
    parser.add_argument("--release-plan-expectation", type=Path, required=True)
    for role in RELEASE_CHECK_ARTIFACT_ROLES:
        parser.add_argument(
            f"--artifact-{role.replace('_', '-')}",
            dest=f"artifact_{role}",
            type=Path,
            required=True,
        )
    parser.add_argument("--release-plan-out", type=Path, required=True)
    parser.add_argument("--release-evidence-out", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        run_release_checks_stage_v2(
            repository=_repository_from_cli(args.repository),
            execution_packet_path=args.execution_packet,
            expectation_path=args.release_plan_expectation,
            artifact_paths=_artifact_paths_from_args(args),
            release_plan_output=args.release_plan_out,
            release_evidence_output=args.release_evidence_out,
        )
    except (RemoteReleaseChecksError, release_schema.ReleaseClosureError) as exc:
        raise SystemExit(f"release_checks_rejected:{exc}") from exc
    return 0


def _repository_from_cli(path: Path) -> Path:
    if path == Path("."):
        return _canonical_directory(Path.cwd(), "repository")
    return _canonical_directory(path, "repository")


if __name__ == "__main__":
    raise SystemExit(main())
