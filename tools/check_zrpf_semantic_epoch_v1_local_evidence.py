#!/usr/bin/env python3
"""Validate bounded local Semantic Epoch V1 proof evidence.

The Rust RISC0 verifiers authenticate seals, image IDs, receipt profiles, and
exact journals. This checker authenticates the reviewed manifest bytes, the
complete retained artifact inventory, report-to-receipt bindings, and the
bounded positive/negative topology. It never verifies a RISC0 seal.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

if __package__:
    from tools import zrpf_semantic_epoch_v1_evidence_support as support
else:
    import zrpf_semantic_epoch_v1_evidence_support as support  # type: ignore[no-redef]


ROOT_FIELDS = {
    "schema",
    "version",
    "evidence_date",
    "scope",
    "status",
    "artifact_root",
    "build_provenance",
    "programs",
    "artifacts",
    "topology",
    "verifier_boundary",
    "claims",
    "non_claims",
}

EXPECTED_HEADER = {
    "schema": support.SCHEMA,
    "version": 1,
    "evidence_date": "2026-07-11",
    "scope": "bounded_three_leaf_v1_adapter_semantic_epoch_local_proof",
    "status": "fresh_current_source_local_semantic_epoch_receipt_verified",
}

EXPECTED_BUILD_PROVENANCE = {
    "cargo_lock_sha256": "025447c0d667c98f881690c1d600c8e26e006f2f7da28ed8a36bf512658cd79f",
    "complete_build_input_closure_verified": False,
    "container_image_id": "sha256:de7091a181792417fbd5eaf6b3aff77d8a26ae0f2ae7ce298c01bf4ad9cd4b9c",
    "cross_host_reproduced": False,
    "final_clean_rebuild_guest_bytes_match": True,
    "path_independent_reproducibility": False,
    "risc0_zkvm_version": "3.0.5",
    "source_closure_artifact_id": "stage-d2-source-closure-record",
    "source_closure_file_count": 56,
    "source_closure_sha256": "50e7ab1790de7d9505abc241e3780c15144c9266ba5c6ac348a587d06c867eaa",
    "final_build_record_artifact_id": "final-independent-build-record",
    "toolchain_lock_sha256": "1be127ec1174a52ec246f04fd887d0ab3b89c246401a9cf4489d0e07c10cb2ab",
}

EXPECTED_PROGRAMS = [
    {
        "role": "v1_leaf_adapter",
        "image_id": "d2c2f1a321c53e0228455b2cf22942fde7595030a379c3fd5484af446ac75d64",
        "raw_elf_sha256": "486baaeb25e392c12c220186d6c43d376b24c2eba3afa0399e75abf8fa107b89",
        "raw_elf_size_bytes": 223_312,
        "combined_elf_sha256": "903bf90d191c4cdc2cfbba51b220ae8b1206a98353490839bba1b479fe0a1cc1",
        "combined_elf_size_bytes": 255_736,
    },
    {
        "role": "structural_l1",
        "image_id": "71e9af087cce2074f2272ea8dec3a16383651014effcf65eac18c48a2722e9a9",
        "raw_elf_sha256": "05e85935ae8f30422d9582a6b4093a83b78ef2c6e0a1a785f3cf99da73a3489e",
        "raw_elf_size_bytes": 308_672,
        "combined_elf_sha256": "93d9ba866e64556ab30acea44c764fb8aced5f289dd9b3996aeda43d35e9c06c",
        "combined_elf_size_bytes": 341_096,
    },
    {
        "role": "structural_l2",
        "image_id": "a92e8ec445e2fea9f61928e0ddf1192552044018e0b49f24374bfa59a45085b3",
        "raw_elf_sha256": "fee9475f070057aefe209df8d35a5e016d49c5c6439f2190455dde777f5bc9f7",
        "raw_elf_size_bytes": 307_712,
        "combined_elf_sha256": "1d0e0609d3e0370a357f4fa26d15e7d1c54582c73f1fd0269ccf20d6503b4a53",
        "combined_elf_size_bytes": 340_136,
    },
    {
        "role": "semantic_epoch",
        "image_id": "dea9abab5cc382af0929779bf84bfcb5430f33b337b86f57e7712b303f3c3c51",
        "raw_elf_sha256": "900e9d45002cfaf1365f1443f7be7a82511aebcda486ebcd95eb0be3ce857fbf",
        "raw_elf_size_bytes": 414_820,
        "combined_elf_sha256": "331225d296d80e24ab8ea803576c43c7156c83b1baec2c8a9daf117abc222ed9",
        "combined_elf_size_bytes": 447_244,
    },
]

EXPECTED_VERIFIER_BOUNDARY = {
    "control_id": "53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a",
    "dev_mode_disabled_by_rust_verifier": True,
    "hash_function": "poseidon2",
    "profile_id": "risc0_succinct_poseidon2_resolve_3_0_5_v1",
    "python_verifies_artifact_bytes_and_topology_only": True,
    "python_verifies_risc0_seals": False,
    "receipt_kind": "succinct",
    "rust_verifier_cryptographically_verified_retained_receipts": True,
    "verifier_parameters": "ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013",
}

EXPECTED_CLAIMS = {
    "asset_conservation_verified": False,
    "complete_build_input_closure_verified": False,
    "cross_host_reproducible_build": False,
    "cross_subtree_duplicate_semantic_source_rejected": True,
    "cryptographic_duplicate_reject_receipt_exists": False,
    "data_availability_verified": False,
    "durable_atomic_admission_verified": False,
    "fresh_adapter_receipts_locally_verified": True,
    "fresh_level_one_receipts_locally_verified": True,
    "fresh_semantic_epoch_receipt_locally_verified": True,
    "guest_image_ids_recomputed_from_fresh_elfs": True,
    "exact_semantic_succinct_seal_mutation_rejected": True,
    "nonempty_receipt_message_or_nullifier_sets_verified": False,
    "path_independent_reproducibility": False,
    "persisted_semantic_receipt_exactly_replayed": True,
    "pre_post_state_continuity_verified": False,
    "privacy_or_zero_knowledge": False,
    "production_authority": False,
    "proof_generation_reproducible": False,
    "proof_tree_and_semantic_epoch_roots_separately_bound": True,
    "public_replay": False,
    "python_verifies_risc0_seals": False,
    "release_authority": False,
    "same_host_clean_guest_rebuild_match": True,
    "schedule_or_carry_verified": False,
    "semantic_economic_completeness": False,
    "settlement_authority": False,
    "throughput_or_tps": False,
}

EXPECTED_NON_CLAIMS = [
    "no_complete_build_input_or_cross_host_reproducibility_claim",
    "no_reproducible_proof_generation_or_receipt_byte_determinism_claim",
    "no_cryptographic_reject_receipt_for_duplicate_source_control",
    "no_complete_zenodex_economic_or_asset_conservation_claim",
    "no_pre_post_state_continuity_claim",
    "no_nonempty_receipt_message_or_nullifier_set_claim",
    "no_data_availability_schedule_or_carry_claim",
    "no_durable_atomic_ledger_admission_claim",
    "no_public_replay_release_settlement_or_production_authority",
    "no_independent_verifier_implementation_claim",
    "no_privacy_or_zero_knowledge_claim",
    "no_throughput_tps_latency_or_cost_claim",
    "python_checker_does_not_verify_risc0_seals",
]

ARTIFACT_FIELDS = {
    "id",
    "kind",
    "path",
    "sha256",
    "size_bytes",
    "encoding",
    "journal_sha256",
    "journal_size_bytes",
}
ARTIFACT_KINDS = frozenset(
    {
        "source_proof_artifact",
        "risc0_receipt",
        "adapter_report",
        "level_one_report",
        "semantic_report",
        "duplicate_source_report",
        "semantic_verification_report",
        "semantic_seal_mutation_report",
        "source_closure_record",
        "final_build_record",
    }
)
EXPECTED_ENCODING_BY_KIND = {
    "source_proof_artifact": "json_sorted_compact",
    "risc0_receipt": "json_compact_insertion",
    "adapter_report": "json_sorted_compact_newline",
    "level_one_report": "json_sorted_compact_newline",
    "semantic_report": "json_sorted_compact_newline",
    "duplicate_source_report": "json_sorted_compact_newline",
    "semantic_verification_report": "json_sorted_compact_newline",
    "semantic_seal_mutation_report": "json_sorted_compact_newline",
    "source_closure_record": "json_sorted_compact",
    "final_build_record": "json_sorted_compact_newline",
}

TOPOLOGY_FIELDS = {
    "leaves",
    "level_one_groups",
    "positive_epoch",
    "duplicate_source_control",
}
LEAF_FIELDS = {
    "id",
    "ordinal",
    "semantic_source_id",
    "source_receipt_sha256",
    "source_artifact_id",
    "adapter_receipt_artifact_id",
    "adapter_report_artifact_id",
}
GROUP_FIELDS = {
    "id",
    "partition_start",
    "partition_end_exclusive",
    "child_leaf_ids",
    "receipt_artifact_id",
    "report_artifact_id",
}
POSITIVE_FIELDS = {
    "leaf_ids",
    "l1_group_ids",
    "leaf_count",
    "operation_count",
    "semantic_receipt_artifact_id",
    "semantic_report_artifact_id",
    "semantic_verification_report_artifact_id",
    "semantic_seal_mutation_receipt_artifact_id",
    "semantic_seal_mutation_report_artifact_id",
    "semantic_epoch_root",
    "proof_tree_root",
    "proposal_hash",
    "program_manifest_root",
}
NEGATIVE_FIELDS = {
    "leaf_ids",
    "l1_group_ids",
    "duplicated_leaf_ids",
    "negative_report_artifact_id",
    "semantic_receipt_artifact_id",
}

EXPECTED_LEAF_IDS = [
    "leaf-0",
    "leaf-1",
    "leaf-2-positive",
    "leaf-2-duplicate",
]
EXPECTED_GROUP_IDS = ["l1-left", "l1-right-positive", "l1-right-duplicate"]
EXPECTED_POSITIVE_LEAVES = ["leaf-0", "leaf-1", "leaf-2-positive"]
EXPECTED_NEGATIVE_LEAVES = ["leaf-0", "leaf-1", "leaf-2-duplicate"]
EXPECTED_POSITIVE_GROUPS = ["l1-left", "l1-right-positive"]
EXPECTED_NEGATIVE_GROUPS = ["l1-left", "l1-right-duplicate"]
EXPECTED_DUPLICATED_LEAVES = ["leaf-1", "leaf-2-duplicate"]

ADAPTER_REPORT_FIELDS = {
    "adapter_image_id",
    "adapter_program_bytes",
    "adapter_receipt_bytes",
    "adapter_receipt_sha256",
    "adapter_receipt_written",
    "assigned_leaf_ordinal",
    "journal_hash",
    "journal_sha256",
    "nonclaims",
    "ok",
    "source_receipt_sha256",
    "status",
}
ADAPTER_REPORT_NONCLAIMS = [
    "temporary compiler-visible path is not a release image identity",
    "no aggregate V3 receipt or semantic-composition claim",
    "no settlement, ledger-admission, or production authority",
]
LEVEL_ONE_REPORT_FIELDS = {
    "adapter_image_id",
    "child_count",
    "journal_hash",
    "journal_sha256",
    "level_one_image_id",
    "nonclaims",
    "ok",
    "receipt_bytes",
    "receipt_sha256",
    "receipt_written",
    "status",
}
LEVEL_ONE_REPORT_NONCLAIMS = [
    "the structural L1 receipt does not prove application-level semantic composition",
    "proof generation does not grant ledger, settlement, release, or production authority",
]
SEMANTIC_REPORT_FIELDS = {
    "adapter_image_id",
    "leaf_count",
    "level_one_group_count",
    "level_one_image_id",
    "level_two_image_id",
    "nonclaims",
    "ok",
    "operation_count",
    "program_manifest_root",
    "proof_tree_root",
    "proposal_hash",
    "receipt_bytes",
    "receipt_sha256",
    "receipt_written",
    "semantic_epoch_image_id",
    "semantic_epoch_root",
    "status",
    "structural_level_two_journal_hash",
}
SEMANTIC_REPORT_NONCLAIMS = [
    "this receipt does not prove complete ZenoDEX economic or value-flow semantics",
    "this receipt does not prove data availability or durable atomic ledger admission",
    "proof generation and local verification do not grant settlement, release, privacy, or production authority",
]
NEGATIVE_REPORT_FIELDS = {
    "adapter_image_id",
    "adapter_receipts_sealed_verified",
    "authoritative_negative_evidence",
    "candidate_accepted",
    "cryptographic_reject_receipt_exists",
    "dynamic_loader_closure_verified",
    "executor_backend",
    "executor_binary_sealed_memfd",
    "executor_binary_sha256",
    "executor_environment_allowlist",
    "executor_environment_exact",
    "guest_execution_attempted",
    "guest_execution_failed",
    "guest_execution_rejected",
    "guest_reject_boundary",
    "guest_reject_code",
    "host_mirror_reject",
    "level_one_assumptions_supplied",
    "level_one_group_count",
    "level_one_image_id",
    "level_one_receipts_sealed_verified",
    "level_two_image_id",
    "methods_validated",
    "nonclaims",
    "ok",
    "receipt_written",
    "same_uid_source_mutation_resistance",
    "semantic_epoch_image_id",
    "semantic_input_bytes",
    "semantic_input_sha256",
    "semantic_receipt_created",
    "status",
}
NEGATIVE_REPORT_NONCLAIMS = [
    "guest execution failure is not a cryptographic reject receipt",
    "the dynamic loader and shared-library closure are not verified by this report",
    "this negative control grants no semantic, settlement, release, privacy, or production authority",
]
PERSISTED_VERIFICATION_REPORT_FIELDS = {
    "adapter_image_id",
    "adapter_receipts_sealed_verified",
    "claim_binding",
    "dependency_programs_governed",
    "exact_expected_proposal_verified",
    "groups",
    "leaf_count",
    "level_one_group_count",
    "level_one_image_id",
    "level_one_receipts_sealed_verified",
    "level_two_image_id",
    "methods_validated",
    "nonclaims",
    "ok",
    "operation_count",
    "program_manifest_root",
    "proof_tree_root",
    "proposal_hash",
    "receipt_profile_id",
    "schema",
    "semantic_epoch_image_id",
    "semantic_epoch_root",
    "semantic_receipt",
    "status",
    "structural_level_two_journal_hash",
}
PERSISTED_VERIFICATION_NONCLAIMS = [
    "local persisted-receipt verification is not public replay or an independent verifier implementation",
    "the semantic profile does not prove complete ZenoDEX economic or value-flow semantics",
    "the receipt does not prove data availability or durable atomic ledger admission",
    "no settlement, release, zero-knowledge privacy, or production authority",
]
RECEIPT_IDENTITY_FIELDS = {"journal_sha256", "receipt_bytes", "receipt_sha256"}
GROUP_IDENTITY_FIELDS = {"adapter_receipts", "level_one_receipt"}
SEAL_MUTATION_REPORT_FIELDS = {
    "adapter_receipts_sealed_verified",
    "baseline_exact_expected_proposal_verified",
    "baseline_semantic_receipt_verified",
    "candidate_accepted",
    "candidate_create_new",
    "candidate_origin",
    "candidate_reopened_with_created_file_identity",
    "control_passed",
    "expected_image_id",
    "level_one_receipts_sealed_verified",
    "mutated_receipt_sha256",
    "mutation",
    "nonclaims",
    "ok",
    "reject",
    "schema",
    "semantic_epoch_root",
    "source_receipt_sha256",
    "status",
}
SEAL_MUTATION_FIELDS = {
    "journal_unchanged",
    "kind",
    "non_seal_receipt_bytes_unchanged",
    "seal_word_count",
    "seal_word_index",
    "seal_word_mutated",
    "seal_word_original",
    "xor_mask",
}
TYPED_REJECT_FIELDS = {"boundary", "code", "outer_code", "variant"}
SEAL_MUTATION_NONCLAIMS = [
    "the mutation control does not regenerate the semantic proof",
    "the mutation control is not public replay or an independent verifier implementation",
    "the semantic profile does not prove complete ZenoDEX economic or value-flow semantics",
    "no settlement, release, zero-knowledge privacy, or production authority",
]
FINAL_BUILD_RECORD_FIELDS = {
    "schema",
    "status",
    "source_closure_sha256",
    "source_closure_file_count",
    "cargo_lock_sha256",
    "toolchain_lock_sha256",
    "container_image_id",
    "risc0_zkvm_version",
    "network_disabled",
    "root_filesystem_read_only",
    "same_host_clean_guest_rebuild_match",
    "complete_build_input_closure_verified",
    "cross_host_reproduced",
    "path_independent_reproducibility",
    "proofs_regenerated_by_final_rebuild",
    "guest_programs",
    "host_binaries",
    "nonclaims",
}
HOST_BINARY_FIELDS = {"role", "sha256", "size_bytes"}
EXPECTED_HOST_BINARY_ROLES = [
    "adapter_harness",
    "structural_l1_prover",
    "semantic_epoch_prover",
    "semantic_epoch_verifier",
]
FINAL_BUILD_NONCLAIMS = [
    "no_complete_build_input_closure_claim",
    "no_cross_host_or_path_independent_reproducibility_claim",
    "final_clean_rebuild_did_not_regenerate_receipts",
    "no_release_settlement_or_production_authority",
]


def _report(errors: list[str], *, manifest_sha256: str, checked: int) -> dict[str, Any]:
    return {
        "schema": support.REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "facts": {
            "artifact_files_checked": checked,
            "manifest_sha256": manifest_sha256,
            "python_verifies_risc0_seals": False,
            "scoped_local_evidence_valid": not errors,
        },
    }


def _require_exact_fields(
    value: Any,
    expected: set[str],
    label: str,
    errors: list[str],
) -> bool:
    if not isinstance(value, dict):
        errors.append(f"{label} must be an object")
        return False
    missing = sorted(expected - set(value))
    unknown = sorted(set(value) - expected)
    if missing:
        errors.append(f"{label} missing fields: {','.join(missing)}")
    if unknown:
        errors.append(f"{label} has unknown fields: {','.join(unknown)}")
    return not missing and not unknown


def _program_id(role: str) -> str:
    for row in EXPECTED_PROGRAMS:
        if row["role"] == role:
            return str(row["image_id"])
    raise ValueError(f"unknown governed program role: {role}")


def check_manifest(
    path: Path = support.DEFAULT_MANIFEST,
    *,
    repo_root: Path = support.REPO_ROOT,
    expected_manifest_sha256: str = support.EXPECTED_MANIFEST_SHA256,
) -> dict[str, Any]:
    try:
        loaded = support.load_manifest(path)
    except support.EvidenceInputError as exc:
        return _report(errors=[str(exc)], manifest_sha256="", checked=0)
    return validate_manifest(
        loaded.document,
        raw=loaded.raw,
        repo_root=repo_root,
        expected_manifest_sha256=expected_manifest_sha256,
    )


def validate_manifest(
    document: Any,
    *,
    raw: bytes,
    repo_root: Path,
    expected_manifest_sha256: str,
) -> dict[str, Any]:
    errors: list[str] = []
    manifest_sha256 = support.sha256_bytes(raw)
    if raw != support.canonical_manifest_bytes(document):
        errors.append("manifest JSON bytes are not canonical")
    if not support.is_digest(expected_manifest_sha256):
        errors.append("governed manifest SHA-256 anchor is not finalized")
    elif manifest_sha256 != expected_manifest_sha256:
        errors.append("manifest SHA-256 differs from governed anchor")
    if not isinstance(document, dict):
        errors.append("manifest root must be an object")
        return _report(errors, manifest_sha256=manifest_sha256, checked=0)

    _validate_header(document, errors)
    _validate_build_provenance(document.get("build_provenance"), errors)
    _validate_programs(document.get("programs"), errors)
    rows = _validate_artifact_rows(document.get("artifacts"), errors)
    leaves, groups, positive, negative = _validate_topology(document.get("topology"), rows, errors)
    _validate_exact_record(
        document.get("verifier_boundary"),
        EXPECTED_VERIFIER_BOUNDARY,
        "verifier_boundary",
        errors,
    )
    _validate_exact_record(document.get("claims"), EXPECTED_CLAIMS, "claims", errors)
    if document.get("non_claims") != EXPECTED_NON_CLAIMS:
        errors.append("non_claims mismatch")

    materials: dict[str, support.ArtifactMaterial] = {}
    artifact_root: Path | None = None
    artifact_root_value = document.get("artifact_root")
    if isinstance(artifact_root_value, str):
        try:
            artifact_root = support.resolve_relative_directory(repo_root, artifact_root_value)
        except support.EvidenceInputError as exc:
            errors.append(str(exc))
    if artifact_root is not None:
        _validate_inventory(artifact_root, rows, errors)
        materials = _load_materials(artifact_root, rows, errors)
        _validate_provenance_artifacts(document.get("build_provenance"), rows, materials, errors)
        _validate_report_bindings(
            rows,
            materials,
            leaves,
            groups,
            positive,
            negative,
            errors,
        )
    return _report(
        errors,
        manifest_sha256=manifest_sha256,
        checked=len(materials),
    )


def _validate_header(document: dict[str, Any], errors: list[str]) -> None:
    _require_exact_fields(document, ROOT_FIELDS, "manifest", errors)
    for field, expected in EXPECTED_HEADER.items():
        if not _exact_type_and_value(document.get(field), expected):
            errors.append(f"manifest header mismatch: {field}")
    if not support.is_safe_relative_path(document.get("artifact_root")):
        errors.append("artifact_root is not a safe relative path")


def _validate_exact_record(
    value: Any,
    expected: dict[str, Any],
    label: str,
    errors: list[str],
) -> None:
    if not _require_exact_fields(value, set(expected), label, errors):
        return
    if not _exact_type_and_value(value, expected):
        errors.append(f"{label} mismatch")


def _validate_build_provenance(value: Any, errors: list[str]) -> None:
    if not _require_exact_fields(value, set(EXPECTED_BUILD_PROVENANCE), "build_provenance", errors):
        return
    fixed = {
        key: expected
        for key, expected in EXPECTED_BUILD_PROVENANCE.items()
        if key not in {"source_closure_file_count", "source_closure_sha256"}
    }
    for key, expected in fixed.items():
        if not _exact_type_and_value(value.get(key), expected):
            errors.append(f"build_provenance mismatch: {key}")
    if type(value.get("source_closure_file_count")) is not int or not (
        0 < value["source_closure_file_count"] <= 1_024
    ):
        errors.append("build_provenance source closure file count is invalid")
    if not support.is_digest(value.get("source_closure_sha256")):
        errors.append("build_provenance source closure SHA-256 is invalid")


def _exact_type_and_value(actual: Any, expected: Any) -> bool:
    """Compare JSON values without Python's bool/int equality coercion."""

    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return set(actual) == set(expected) and all(
            _exact_type_and_value(actual[key], value) for key, value in expected.items()
        )
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            _exact_type_and_value(left, right) for left, right in zip(actual, expected, strict=True)
        )
    return bool(actual == expected)


def _validate_programs(value: Any, errors: list[str]) -> None:
    if not isinstance(value, list) or len(value) != len(EXPECTED_PROGRAMS):
        errors.append("programs must contain exactly four rows")
        return
    expected_fields = set(EXPECTED_PROGRAMS[0])
    for index, row in enumerate(value):
        _require_exact_fields(row, expected_fields, f"programs[{index}]", errors)
    if not _exact_type_and_value(value, EXPECTED_PROGRAMS):
        errors.append("program identity records mismatch")


def _validate_artifact_rows(value: Any, errors: list[str]) -> dict[str, dict[str, Any]]:
    if not isinstance(value, list) or not value:
        errors.append("artifacts must be a nonempty list")
        return {}
    rows: dict[str, dict[str, Any]] = {}
    ids: list[str] = []
    paths: list[str] = []
    for index, row in enumerate(value):
        if not _require_exact_fields(row, ARTIFACT_FIELDS, f"artifacts[{index}]", errors):
            continue
        artifact_id = row.get("id")
        if not isinstance(artifact_id, str) or not artifact_id:
            errors.append(f"artifacts[{index}].id is invalid")
            continue
        ids.append(artifact_id)
        path = row.get("path")
        if not support.is_safe_relative_path(path):
            errors.append(f"artifact path is unsafe: {artifact_id}")
        elif isinstance(path, str):
            paths.append(path)
        kind = row.get("kind")
        if not isinstance(kind, str) or kind not in ARTIFACT_KINDS:
            errors.append(f"artifact kind is unsupported: {artifact_id}")
        elif row.get("encoding") != EXPECTED_ENCODING_BY_KIND[kind]:
            errors.append(f"artifact encoding mismatch: {artifact_id}")
        if not support.is_digest(row.get("sha256")):
            errors.append(f"artifact SHA-256 is invalid: {artifact_id}")
        if type(row.get("size_bytes")) is not int or not (
            0 < row["size_bytes"] <= support.MAX_ARTIFACT_BYTES
        ):
            errors.append(f"artifact size is invalid: {artifact_id}")

        journal_sha256 = row.get("journal_sha256")
        journal_size = row.get("journal_size_bytes")
        if kind == "risc0_receipt":
            if not support.is_digest(journal_sha256):
                errors.append(f"receipt journal SHA-256 is invalid: {artifact_id}")
            if type(journal_size) is not int or not (0 < journal_size <= support.MAX_JOURNAL_BYTES):
                errors.append(f"receipt journal size is invalid: {artifact_id}")
        elif journal_sha256 is not None or journal_size is not None:
            errors.append(f"non-receipt artifact carries journal facts: {artifact_id}")
        rows[artifact_id] = row

    if ids != sorted(ids) or len(ids) != len(set(ids)):
        errors.append("artifact IDs must be unique and sorted")
    if len(paths) != len(set(paths)):
        errors.append("artifact paths must be unique")
    return rows


def _validate_topology(
    value: Any,
    artifacts: dict[str, dict[str, Any]],
    errors: list[str],
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, dict[str, Any]],
    dict[str, Any],
    dict[str, Any],
]:
    empty: dict[str, Any] = {}
    if not _require_exact_fields(value, TOPOLOGY_FIELDS, "topology", errors):
        return {}, {}, empty, empty
    leaves = _validate_leaves(value.get("leaves"), artifacts, errors)
    groups = _validate_groups(value.get("level_one_groups"), artifacts, leaves, errors)
    positive = _validate_positive(value.get("positive_epoch"), artifacts, leaves, groups, errors)
    negative = _validate_negative(
        value.get("duplicate_source_control"), artifacts, leaves, groups, errors
    )
    _validate_artifact_references(artifacts, leaves, groups, positive, negative, errors)
    return leaves, groups, positive, negative


def _validate_leaves(
    value: Any,
    artifacts: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, dict[str, Any]]:
    if not isinstance(value, list) or len(value) != 4:
        errors.append("topology.leaves must contain exactly four rows")
        return {}
    rows: dict[str, dict[str, Any]] = {}
    ids: list[Any] = []
    for index, row in enumerate(value):
        if not _require_exact_fields(row, LEAF_FIELDS, f"topology.leaves[{index}]", errors):
            continue
        leaf_id = row.get("id")
        ids.append(leaf_id)
        if not isinstance(leaf_id, str):
            errors.append(f"topology.leaves[{index}].id is invalid")
            continue
        rows[leaf_id] = row
        if type(row.get("ordinal")) is not int or row["ordinal"] < 0:
            errors.append(f"leaf ordinal is invalid: {leaf_id}")
        if not support.is_digest(row.get("semantic_source_id")):
            errors.append(f"leaf semantic source ID is invalid: {leaf_id}")
        if not support.is_digest(row.get("source_receipt_sha256")):
            errors.append(f"leaf source receipt SHA-256 is invalid: {leaf_id}")
        _require_artifact_kind(
            artifacts, row.get("source_artifact_id"), "source_proof_artifact", leaf_id, errors
        )
        _require_artifact_kind(
            artifacts, row.get("adapter_receipt_artifact_id"), "risc0_receipt", leaf_id, errors
        )
        _require_artifact_kind(
            artifacts, row.get("adapter_report_artifact_id"), "adapter_report", leaf_id, errors
        )
    if ids != EXPECTED_LEAF_IDS:
        errors.append("semantic leaf IDs or order mismatch")
    if [rows.get(leaf_id, {}).get("ordinal") for leaf_id in EXPECTED_LEAF_IDS] != [0, 1, 2, 2]:
        errors.append("semantic leaf ordinal profile mismatch")
    return rows


def _validate_groups(
    value: Any,
    artifacts: dict[str, dict[str, Any]],
    leaves: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, dict[str, Any]]:
    if not isinstance(value, list) or len(value) != 3:
        errors.append("topology.level_one_groups must contain exactly three rows")
        return {}
    rows: dict[str, dict[str, Any]] = {}
    ids: list[Any] = []
    for index, row in enumerate(value):
        if not _require_exact_fields(
            row, GROUP_FIELDS, f"topology.level_one_groups[{index}]", errors
        ):
            continue
        group_id = row.get("id")
        ids.append(group_id)
        if not isinstance(group_id, str):
            errors.append(f"topology.level_one_groups[{index}].id is invalid")
            continue
        rows[group_id] = row
        children = row.get("child_leaf_ids")
        children_are_known_strings = (
            isinstance(children, list)
            and bool(children)
            and len(children) <= 8
            and all(isinstance(child, str) and child in leaves for child in children)
        )
        if not children_are_known_strings or len(children) != len(set(children)):
            errors.append(f"level-one child list is invalid: {group_id}")
        start = row.get("partition_start")
        end = row.get("partition_end_exclusive")
        if type(start) is not int or type(end) is not int or not (0 <= start < end <= 64):
            errors.append(f"level-one partition is invalid: {group_id}")
        elif children_are_known_strings:
            ordinals = [leaves[child].get("ordinal") for child in children]
            if ordinals != list(range(start, end)):
                errors.append(f"level-one child partitions are not dense: {group_id}")
        _require_artifact_kind(
            artifacts, row.get("receipt_artifact_id"), "risc0_receipt", group_id, errors
        )
        _require_artifact_kind(
            artifacts, row.get("report_artifact_id"), "level_one_report", group_id, errors
        )
    if ids != EXPECTED_GROUP_IDS:
        errors.append("level-one group IDs or order mismatch")
    expected_children = {
        "l1-left": ["leaf-0", "leaf-1"],
        "l1-right-positive": ["leaf-2-positive"],
        "l1-right-duplicate": ["leaf-2-duplicate"],
    }
    for group_id, children in expected_children.items():
        if rows.get(group_id, {}).get("child_leaf_ids") != children:
            errors.append(f"level-one group child binding mismatch: {group_id}")
    return rows


def _validate_positive(
    value: Any,
    artifacts: dict[str, dict[str, Any]],
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, Any]:
    if not _require_exact_fields(value, POSITIVE_FIELDS, "topology.positive_epoch", errors):
        return {}
    if value.get("leaf_ids") != EXPECTED_POSITIVE_LEAVES:
        errors.append("positive epoch leaf order mismatch")
    if value.get("l1_group_ids") != EXPECTED_POSITIVE_GROUPS:
        errors.append("positive epoch level-one group order mismatch")
    _validate_epoch_partition(value, leaves, groups, errors, "positive epoch")
    if value.get("leaf_count") != 3 or value.get("operation_count") != 3:
        errors.append("positive epoch bounded counts mismatch")
    for field in (
        "semantic_epoch_root",
        "proof_tree_root",
        "proposal_hash",
        "program_manifest_root",
    ):
        if not support.is_digest(value.get(field)):
            errors.append(f"positive epoch digest is invalid: {field}")
    _require_artifact_kind(
        artifacts,
        value.get("semantic_receipt_artifact_id"),
        "risc0_receipt",
        "positive epoch",
        errors,
    )
    _require_artifact_kind(
        artifacts,
        value.get("semantic_report_artifact_id"),
        "semantic_report",
        "positive epoch",
        errors,
    )
    _require_artifact_kind(
        artifacts,
        value.get("semantic_verification_report_artifact_id"),
        "semantic_verification_report",
        "positive epoch persisted verification",
        errors,
    )
    _require_artifact_kind(
        artifacts,
        value.get("semantic_seal_mutation_receipt_artifact_id"),
        "risc0_receipt",
        "positive epoch seal mutation",
        errors,
    )
    _require_artifact_kind(
        artifacts,
        value.get("semantic_seal_mutation_report_artifact_id"),
        "semantic_seal_mutation_report",
        "positive epoch seal mutation",
        errors,
    )
    return value


def _validate_negative(
    value: Any,
    artifacts: dict[str, dict[str, Any]],
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, Any]:
    if not _require_exact_fields(
        value, NEGATIVE_FIELDS, "topology.duplicate_source_control", errors
    ):
        return {}
    if value.get("leaf_ids") != EXPECTED_NEGATIVE_LEAVES:
        errors.append("duplicate-source control leaf order mismatch")
    if value.get("l1_group_ids") != EXPECTED_NEGATIVE_GROUPS:
        errors.append("duplicate-source control level-one group order mismatch")
    if value.get("duplicated_leaf_ids") != EXPECTED_DUPLICATED_LEAVES:
        errors.append("duplicate-source control duplicated pair mismatch")
    _validate_epoch_partition(value, leaves, groups, errors, "duplicate-source control")
    duplicate_rows = [leaves.get(leaf_id, {}) for leaf_id in EXPECTED_DUPLICATED_LEAVES]
    semantic_ids = [row.get("semantic_source_id") for row in duplicate_rows]
    if (
        len(semantic_ids) != 2
        or not all(support.is_digest(semantic_id) for semantic_id in semantic_ids)
        or semantic_ids[0] != semantic_ids[1]
    ):
        errors.append("duplicate-source control does not reuse one semantic source")
    source_artifacts = [row.get("source_artifact_id") for row in duplicate_rows]
    if (
        len(source_artifacts) != 2
        or not all(isinstance(artifact, str) for artifact in source_artifacts)
        or source_artifacts[0] == source_artifacts[1]
    ):
        errors.append("duplicate-source control source artifacts must remain distinct")
    if value.get("semantic_receipt_artifact_id") is not None:
        errors.append("duplicate-source control must not declare a semantic receipt")
    _require_artifact_kind(
        artifacts,
        value.get("negative_report_artifact_id"),
        "duplicate_source_report",
        "duplicate-source control",
        errors,
    )
    return value


def _validate_epoch_partition(
    value: dict[str, Any],
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    errors: list[str],
    label: str,
) -> None:
    leaf_ids = value.get("leaf_ids")
    group_ids = value.get("l1_group_ids")
    if (
        not isinstance(leaf_ids, list)
        or not isinstance(group_ids, list)
        or any(not isinstance(leaf_id, str) for leaf_id in leaf_ids)
        or any(not isinstance(group_id, str) for group_id in group_ids)
    ):
        errors.append(f"{label} lists are malformed")
        return
    if any(leaf_id not in leaves for leaf_id in leaf_ids):
        errors.append(f"{label} references an unknown leaf")
        return
    if any(group_id not in groups for group_id in group_ids):
        errors.append(f"{label} references an unknown level-one group")
        return
    child_lists = [groups[group_id].get("child_leaf_ids") for group_id in group_ids]
    flattened: list[str] = []
    for children in child_lists:
        if not isinstance(children, list) or any(not isinstance(child, str) for child in children):
            errors.append(f"{label} level-one child lists are malformed")
            return
        flattened.extend(children)
    if flattened != leaf_ids:
        errors.append(f"{label} group-to-leaf topology mismatch")
    ordinals = [leaves[leaf_id].get("ordinal") for leaf_id in leaf_ids]
    if ordinals != list(range(len(leaf_ids))):
        errors.append(f"{label} leaf partitions are not dense")


def _require_artifact_kind(
    artifacts: dict[str, dict[str, Any]],
    artifact_id: Any,
    expected_kind: str,
    owner: str,
    errors: list[str],
) -> None:
    if not isinstance(artifact_id, str) or artifact_id not in artifacts:
        errors.append(f"unknown artifact reference for {owner}")
    elif artifacts[artifact_id].get("kind") != expected_kind:
        errors.append(f"artifact kind mismatch for {owner}: {artifact_id}")


def _validate_artifact_references(
    artifacts: dict[str, dict[str, Any]],
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    positive: dict[str, Any],
    negative: dict[str, Any],
    errors: list[str],
) -> None:
    referenced: set[str] = {
        str(EXPECTED_BUILD_PROVENANCE["source_closure_artifact_id"]),
        str(EXPECTED_BUILD_PROVENANCE["final_build_record_artifact_id"]),
    }
    for row in leaves.values():
        referenced.update(
            value
            for value in (
                row.get("source_artifact_id"),
                row.get("adapter_receipt_artifact_id"),
                row.get("adapter_report_artifact_id"),
            )
            if isinstance(value, str)
        )
    for row in groups.values():
        referenced.update(
            value
            for value in (row.get("receipt_artifact_id"), row.get("report_artifact_id"))
            if isinstance(value, str)
        )
    for field in (
        "semantic_receipt_artifact_id",
        "semantic_report_artifact_id",
        "semantic_verification_report_artifact_id",
        "semantic_seal_mutation_receipt_artifact_id",
        "semantic_seal_mutation_report_artifact_id",
    ):
        value = positive.get(field)
        if isinstance(value, str):
            referenced.add(value)
    value = negative.get("negative_report_artifact_id")
    if isinstance(value, str):
        referenced.add(value)
    if set(artifacts) != referenced:
        errors.append("artifact declarations and topology references differ")


def _validate_inventory(
    artifact_root: Path,
    artifacts: dict[str, dict[str, Any]],
    errors: list[str],
) -> None:
    actual, inventory_errors = support.artifact_inventory(artifact_root)
    errors.extend(inventory_errors)
    declared = sorted(row["path"] for row in artifacts.values() if isinstance(row.get("path"), str))
    if actual != declared:
        errors.append("artifact directory inventory differs from manifest")


def _validate_provenance_artifacts(
    build: Any,
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    if not isinstance(build, dict):
        return
    closure_id = build.get("source_closure_artifact_id")
    build_record_id = build.get("final_build_record_artifact_id")
    _require_artifact_kind(
        artifacts,
        closure_id,
        "source_closure_record",
        "build provenance source closure",
        errors,
    )
    _require_artifact_kind(
        artifacts,
        build_record_id,
        "final_build_record",
        "build provenance final build record",
        errors,
    )
    closure = _material_document(materials, closure_id)
    if closure is not None:
        try:
            file_count, closure_sha256 = support.source_closure_facts(closure)
        except support.EvidenceInputError:
            pass
        else:
            if file_count != build.get("source_closure_file_count"):
                errors.append("source closure file count differs from build provenance")
            if closure_sha256 != build.get("source_closure_sha256"):
                errors.append("source closure root differs from build provenance")
    final_build = _material_document(materials, build_record_id)
    _validate_final_build_record(final_build, build, errors)


def _validate_final_build_record(
    value: Any,
    build: dict[str, Any],
    errors: list[str],
) -> None:
    if not isinstance(value, dict) or not _require_exact_fields(
        value, FINAL_BUILD_RECORD_FIELDS, "final build record", errors
    ):
        return
    expected = {
        "schema": "zenodex/zrpf_semantic_epoch_v1_final_build_record/v1",
        "status": "same_host_final_clean_guest_rebuild_matched",
        "source_closure_sha256": build.get("source_closure_sha256"),
        "source_closure_file_count": build.get("source_closure_file_count"),
        "cargo_lock_sha256": build.get("cargo_lock_sha256"),
        "toolchain_lock_sha256": build.get("toolchain_lock_sha256"),
        "container_image_id": build.get("container_image_id"),
        "risc0_zkvm_version": build.get("risc0_zkvm_version"),
        "network_disabled": True,
        "root_filesystem_read_only": True,
        "same_host_clean_guest_rebuild_match": True,
        "complete_build_input_closure_verified": False,
        "cross_host_reproduced": False,
        "path_independent_reproducibility": False,
        "proofs_regenerated_by_final_rebuild": False,
        "guest_programs": EXPECTED_PROGRAMS,
        "nonclaims": FINAL_BUILD_NONCLAIMS,
    }
    for key, expected_value in expected.items():
        if not _exact_type_and_value(value.get(key), expected_value):
            errors.append(f"final build record binding mismatch: {key}")
    binaries = value.get("host_binaries")
    if not isinstance(binaries, list) or len(binaries) != len(EXPECTED_HOST_BINARY_ROLES):
        errors.append("final build record host binary inventory mismatch")
        return
    roles: list[Any] = []
    for index, binary in enumerate(binaries):
        if not _require_exact_fields(
            binary, HOST_BINARY_FIELDS, f"final build host_binaries[{index}]", errors
        ):
            continue
        roles.append(binary.get("role"))
        if not support.is_digest(binary.get("sha256")):
            errors.append(f"final build host binary SHA-256 is invalid: {index}")
        if type(binary.get("size_bytes")) is not int or not (
            0 < binary["size_bytes"] <= support.MAX_ARTIFACT_BYTES
        ):
            errors.append(f"final build host binary size is invalid: {index}")
    if roles != EXPECTED_HOST_BINARY_ROLES:
        errors.append("final build record host binary roles or order mismatch")


def _load_materials(
    artifact_root: Path,
    artifacts: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, support.ArtifactMaterial]:
    materials: dict[str, support.ArtifactMaterial] = {}
    for artifact_id in sorted(artifacts):
        row = artifacts[artifact_id]
        try:
            material = support.load_artifact(artifact_root, row)
            if row["kind"] == "risc0_receipt":
                journal_size, journal_sha256 = support.receipt_journal_facts(material.document)
                if journal_size != row["journal_size_bytes"]:
                    raise support.EvidenceInputError(
                        f"receipt journal size mismatch: {artifact_id}"
                    )
                if journal_sha256 != row["journal_sha256"]:
                    raise support.EvidenceInputError(
                        f"receipt journal SHA-256 mismatch: {artifact_id}"
                    )
            elif row["kind"] == "source_proof_artifact":
                support.source_proof_receipt_sha256(material.document)
            elif row["kind"] == "source_closure_record":
                support.source_closure_facts(material.document)
            materials[artifact_id] = material
        except (KeyError, support.EvidenceInputError) as exc:
            errors.append(str(exc))
    return materials


def _validate_report_bindings(
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    positive: dict[str, Any],
    negative: dict[str, Any],
    errors: list[str],
) -> None:
    for leaf_id, leaf in leaves.items():
        _validate_adapter_report(leaf_id, leaf, artifacts, materials, errors)
    for group_id, group in groups.items():
        _validate_level_one_report(group_id, group, artifacts, materials, errors)
    _validate_semantic_report(positive, artifacts, materials, errors)
    _validate_persisted_verification_report(positive, leaves, groups, artifacts, materials, errors)
    _validate_seal_mutation_report(positive, artifacts, materials, errors)
    _validate_negative_report(negative, materials, errors)


def _material_document(
    materials: dict[str, support.ArtifactMaterial], artifact_id: Any
) -> Any | None:
    if not isinstance(artifact_id, str):
        return None
    material = materials.get(artifact_id)
    return material.document if material is not None else None


def _list_length(value: Any) -> int:
    return len(value) if isinstance(value, list) else -1


def _validate_adapter_report(
    leaf_id: str,
    leaf: dict[str, Any],
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    report_id = leaf.get("adapter_report_artifact_id")
    receipt_id = leaf.get("adapter_receipt_artifact_id")
    source_id = leaf.get("source_artifact_id")
    report = _material_document(materials, report_id)
    receipt = artifacts.get(receipt_id, {}) if isinstance(receipt_id, str) else {}
    if not isinstance(report, dict) or not _require_exact_fields(
        report, ADAPTER_REPORT_FIELDS, f"adapter report {leaf_id}", errors
    ):
        return
    expected = {
        "adapter_image_id": _program_id("v1_leaf_adapter"),
        "adapter_program_bytes": EXPECTED_PROGRAMS[0]["combined_elf_size_bytes"],
        "adapter_receipt_bytes": receipt.get("size_bytes"),
        "adapter_receipt_sha256": receipt.get("sha256"),
        "adapter_receipt_written": True,
        "assigned_leaf_ordinal": leaf.get("ordinal"),
        "journal_sha256": receipt.get("journal_sha256"),
        "nonclaims": ADAPTER_REPORT_NONCLAIMS,
        "ok": True,
        "source_receipt_sha256": leaf.get("source_receipt_sha256"),
        "status": "temporary_path_spot_v1_adapter_receipt_verified",
    }
    for key, value in expected.items():
        if not _exact_type_and_value(report.get(key), value):
            errors.append(f"adapter report binding mismatch: {leaf_id}:{key}")
    if not support.is_digest(report.get("journal_hash")):
        errors.append(f"adapter report journal hash is invalid: {leaf_id}")
    source_document = _material_document(materials, source_id)
    if source_document is not None:
        try:
            embedded_sha256 = support.source_proof_receipt_sha256(source_document)
        except support.EvidenceInputError:
            return
        if embedded_sha256 != leaf.get("source_receipt_sha256"):
            errors.append(f"source proof receipt binding mismatch: {leaf_id}")


def _validate_level_one_report(
    group_id: str,
    group: dict[str, Any],
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    report_id = group.get("report_artifact_id")
    receipt_id = group.get("receipt_artifact_id")
    report = _material_document(materials, report_id)
    receipt = artifacts.get(receipt_id, {}) if isinstance(receipt_id, str) else {}
    if not isinstance(report, dict) or not _require_exact_fields(
        report, LEVEL_ONE_REPORT_FIELDS, f"level-one report {group_id}", errors
    ):
        return
    expected = {
        "adapter_image_id": _program_id("v1_leaf_adapter"),
        "child_count": _list_length(group.get("child_leaf_ids")),
        "journal_sha256": receipt.get("journal_sha256"),
        "level_one_image_id": _program_id("structural_l1"),
        "nonclaims": LEVEL_ONE_REPORT_NONCLAIMS,
        "ok": True,
        "receipt_bytes": receipt.get("size_bytes"),
        "receipt_sha256": receipt.get("sha256"),
        "receipt_written": True,
        "status": "bounded_structural_l1_succinct_receipt_verified",
    }
    for key, value in expected.items():
        if not _exact_type_and_value(report.get(key), value):
            errors.append(f"level-one report binding mismatch: {group_id}:{key}")
    if not support.is_digest(report.get("journal_hash")):
        errors.append(f"level-one report journal hash is invalid: {group_id}")


def _validate_semantic_report(
    positive: dict[str, Any],
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    report_id = positive.get("semantic_report_artifact_id")
    receipt_id = positive.get("semantic_receipt_artifact_id")
    report = _material_document(materials, report_id)
    receipt = artifacts.get(receipt_id, {}) if isinstance(receipt_id, str) else {}
    if not isinstance(report, dict) or not _require_exact_fields(
        report, SEMANTIC_REPORT_FIELDS, "semantic report", errors
    ):
        return
    expected = {
        "adapter_image_id": _program_id("v1_leaf_adapter"),
        "leaf_count": positive.get("leaf_count"),
        "level_one_group_count": _list_length(positive.get("l1_group_ids")),
        "level_one_image_id": _program_id("structural_l1"),
        "level_two_image_id": _program_id("structural_l2"),
        "nonclaims": SEMANTIC_REPORT_NONCLAIMS,
        "ok": True,
        "operation_count": positive.get("operation_count"),
        "program_manifest_root": positive.get("program_manifest_root"),
        "proof_tree_root": positive.get("proof_tree_root"),
        "proposal_hash": positive.get("proposal_hash"),
        "receipt_bytes": receipt.get("size_bytes"),
        "receipt_sha256": receipt.get("sha256"),
        "receipt_written": True,
        "semantic_epoch_image_id": _program_id("semantic_epoch"),
        "semantic_epoch_root": positive.get("semantic_epoch_root"),
        "status": "bounded_v1_adapter_semantic_epoch_succinct_receipt_verified",
        "structural_level_two_journal_hash": positive.get("proof_tree_root"),
    }
    for key, value in expected.items():
        if not _exact_type_and_value(report.get(key), value):
            errors.append(f"semantic report binding mismatch: {key}")


def _validate_persisted_verification_report(
    positive: dict[str, Any],
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    report = _material_document(materials, positive.get("semantic_verification_report_artifact_id"))
    if not isinstance(report, dict) or not _require_exact_fields(
        report,
        PERSISTED_VERIFICATION_REPORT_FIELDS,
        "persisted semantic verification report",
        errors,
    ):
        return
    expected = {
        "adapter_image_id": _program_id("v1_leaf_adapter"),
        "adapter_receipts_sealed_verified": positive.get("leaf_count"),
        "dependency_programs_governed": True,
        "exact_expected_proposal_verified": True,
        "leaf_count": positive.get("leaf_count"),
        "level_one_group_count": _list_length(positive.get("l1_group_ids")),
        "level_one_image_id": _program_id("structural_l1"),
        "level_one_receipts_sealed_verified": _list_length(positive.get("l1_group_ids")),
        "level_two_image_id": _program_id("structural_l2"),
        "methods_validated": True,
        "nonclaims": PERSISTED_VERIFICATION_NONCLAIMS,
        "ok": True,
        "operation_count": positive.get("operation_count"),
        "program_manifest_root": positive.get("program_manifest_root"),
        "proof_tree_root": positive.get("proof_tree_root"),
        "proposal_hash": positive.get("proposal_hash"),
        "receipt_profile_id": EXPECTED_VERIFIER_BOUNDARY["profile_id"],
        "schema": "zenodex/zrpf_semantic_epoch_persisted_verification/v1",
        "semantic_epoch_image_id": _program_id("semantic_epoch"),
        "semantic_epoch_root": positive.get("semantic_epoch_root"),
        "status": "persisted_bounded_v1_semantic_epoch_exact_receipt_verified",
        "structural_level_two_journal_hash": positive.get("proof_tree_root"),
    }
    for key, value in expected.items():
        if not _exact_type_and_value(report.get(key), value):
            errors.append(f"persisted semantic report binding mismatch: {key}")
    if not support.is_digest(report.get("claim_binding")):
        errors.append("persisted semantic report claim binding is invalid")

    semantic_receipt_id = positive.get("semantic_receipt_artifact_id")
    semantic_receipt = (
        artifacts.get(semantic_receipt_id, {}) if isinstance(semantic_receipt_id, str) else {}
    )
    _validate_receipt_identity(
        report.get("semantic_receipt"),
        semantic_receipt,
        "persisted semantic receipt",
        errors,
    )
    report_groups = report.get("groups")
    group_ids = positive.get("l1_group_ids")
    if not isinstance(report_groups, list) or not isinstance(group_ids, list):
        errors.append("persisted semantic report groups are malformed")
        return
    if len(report_groups) != len(group_ids):
        errors.append("persisted semantic report group count mismatch")
        return
    for index, (report_group, group_id) in enumerate(zip(report_groups, group_ids, strict=True)):
        _validate_persisted_group_identity(
            report_group,
            group_id,
            index,
            leaves,
            groups,
            artifacts,
            errors,
        )


def _validate_persisted_group_identity(
    value: Any,
    group_id: Any,
    index: int,
    leaves: dict[str, dict[str, Any]],
    groups: dict[str, dict[str, Any]],
    artifacts: dict[str, dict[str, Any]],
    errors: list[str],
) -> None:
    label = f"persisted semantic report groups[{index}]"
    if not _require_exact_fields(value, GROUP_IDENTITY_FIELDS, label, errors):
        return
    if not isinstance(group_id, str) or group_id not in groups:
        errors.append(f"{label} references an unknown group")
        return
    group = groups[group_id]
    level_one_id = group.get("receipt_artifact_id")
    level_one = artifacts.get(level_one_id, {}) if isinstance(level_one_id, str) else {}
    _validate_receipt_identity(
        value.get("level_one_receipt"), level_one, f"{label}.level_one_receipt", errors
    )
    report_leaves = value.get("adapter_receipts")
    child_ids = group.get("child_leaf_ids")
    if not isinstance(report_leaves, list) or not isinstance(child_ids, list):
        errors.append(f"{label}.adapter_receipts is malformed")
        return
    if len(report_leaves) != len(child_ids):
        errors.append(f"{label}.adapter_receipts count mismatch")
        return
    for leaf_index, (identity, leaf_id) in enumerate(zip(report_leaves, child_ids, strict=True)):
        leaf = leaves.get(leaf_id, {}) if isinstance(leaf_id, str) else {}
        receipt_id = leaf.get("adapter_receipt_artifact_id")
        receipt = artifacts.get(receipt_id, {}) if isinstance(receipt_id, str) else {}
        _validate_receipt_identity(
            identity,
            receipt,
            f"{label}.adapter_receipts[{leaf_index}]",
            errors,
        )


def _validate_receipt_identity(
    value: Any,
    artifact: dict[str, Any],
    label: str,
    errors: list[str],
) -> None:
    if not _require_exact_fields(value, RECEIPT_IDENTITY_FIELDS, label, errors):
        return
    expected = {
        "journal_sha256": artifact.get("journal_sha256"),
        "receipt_bytes": artifact.get("size_bytes"),
        "receipt_sha256": artifact.get("sha256"),
    }
    if not _exact_type_and_value(value, expected):
        errors.append(f"{label} binding mismatch")


def _validate_seal_mutation_report(
    positive: dict[str, Any],
    artifacts: dict[str, dict[str, Any]],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    source_id = positive.get("semantic_receipt_artifact_id")
    mutation_id = positive.get("semantic_seal_mutation_receipt_artifact_id")
    report_id = positive.get("semantic_seal_mutation_report_artifact_id")
    source_document = _material_document(materials, source_id)
    mutation_document = _material_document(materials, mutation_id)
    report = _material_document(materials, report_id)
    if source_document is None or mutation_document is None:
        return
    try:
        mutation_facts = support.exact_succinct_seal_word_one_xor_one(
            source_document, mutation_document
        )
    except support.EvidenceInputError as exc:
        errors.append(str(exc))
        return
    if not isinstance(report, dict) or not _require_exact_fields(
        report, SEAL_MUTATION_REPORT_FIELDS, "semantic seal-mutation report", errors
    ):
        return
    source = artifacts.get(source_id, {}) if isinstance(source_id, str) else {}
    mutation = artifacts.get(mutation_id, {}) if isinstance(mutation_id, str) else {}
    expected = {
        "adapter_receipts_sealed_verified": positive.get("leaf_count"),
        "baseline_exact_expected_proposal_verified": True,
        "baseline_semantic_receipt_verified": True,
        "candidate_accepted": False,
        "candidate_create_new": True,
        "candidate_origin": "verifier_created_from_exact_baseline",
        "candidate_reopened_with_created_file_identity": True,
        "control_passed": True,
        "expected_image_id": _program_id("semantic_epoch"),
        "level_one_receipts_sealed_verified": _list_length(positive.get("l1_group_ids")),
        "mutated_receipt_sha256": mutation.get("sha256"),
        "nonclaims": SEAL_MUTATION_NONCLAIMS,
        "ok": True,
        "schema": "zenodex/zrpf_semantic_epoch_succinct_seal_mutation_reject/v1",
        "semantic_epoch_root": positive.get("semantic_epoch_root"),
        "source_receipt_sha256": source.get("sha256"),
        "status": "persisted_semantic_epoch_succinct_seal_mutation_rejected",
    }
    for key, value in expected.items():
        if not _exact_type_and_value(report.get(key), value):
            errors.append(f"semantic seal-mutation report binding mismatch: {key}")
    mutation_record = report.get("mutation")
    if _require_exact_fields(
        mutation_record, SEAL_MUTATION_FIELDS, "semantic seal mutation", errors
    ):
        expected_mutation = {
            "journal_unchanged": True,
            "kind": "succinct_seal_word_1_xor_1_v1",
            "non_seal_receipt_bytes_unchanged": True,
            "seal_word_count": mutation_facts.word_count,
            "seal_word_index": mutation_facts.word_index,
            "seal_word_mutated": mutation_facts.mutated_word,
            "seal_word_original": mutation_facts.original_word,
            "xor_mask": 1,
        }
        if not _exact_type_and_value(mutation_record, expected_mutation):
            errors.append("semantic seal mutation facts mismatch")
    reject = report.get("reject")
    if _require_exact_fields(reject, TYPED_REJECT_FIELDS, "semantic typed reject", errors):
        expected_reject = {
            "boundary": "VerifiedSemanticEpochReceiptV1::verify_exact_succinct_bytes",
            "code": "receipt_verification_failed",
            "outer_code": "semantic_receipt_artifact_rejected",
            "variant": "ReceiptArtifact(ReceiptVerificationFailed)",
        }
        if not _exact_type_and_value(reject, expected_reject):
            errors.append("semantic seal mutation typed reject mismatch")


def _validate_negative_report(
    negative: dict[str, Any],
    materials: dict[str, support.ArtifactMaterial],
    errors: list[str],
) -> None:
    report = _material_document(materials, negative.get("negative_report_artifact_id"))
    if not isinstance(report, dict) or not _require_exact_fields(
        report, NEGATIVE_REPORT_FIELDS, "duplicate-source report", errors
    ):
        return
    leaf_count = _list_length(negative.get("leaf_ids"))
    group_count = _list_length(negative.get("l1_group_ids"))
    expected = {
        "adapter_image_id": _program_id("v1_leaf_adapter"),
        "adapter_receipts_sealed_verified": leaf_count,
        "authoritative_negative_evidence": False,
        "candidate_accepted": False,
        "cryptographic_reject_receipt_exists": False,
        "dynamic_loader_closure_verified": False,
        "executor_backend": "governed_ipc_r0vm_sealed_memfd",
        "executor_binary_sealed_memfd": True,
        "executor_binary_sha256": "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b",
        "executor_environment_allowlist": ["RISC0_SERVER_PATH", "TMPDIR"],
        "executor_environment_exact": True,
        "guest_execution_attempted": True,
        "guest_execution_failed": True,
        "guest_execution_rejected": True,
        "guest_reject_boundary": "semantic_epoch_composition",
        "guest_reject_code": "duplicate_semantic_source",
        "host_mirror_reject": "duplicate_semantic_source",
        "level_one_assumptions_supplied": group_count,
        "level_one_group_count": group_count,
        "level_one_image_id": _program_id("structural_l1"),
        "level_one_receipts_sealed_verified": group_count,
        "level_two_image_id": _program_id("structural_l2"),
        "methods_validated": True,
        "nonclaims": NEGATIVE_REPORT_NONCLAIMS,
        "ok": True,
        "receipt_written": False,
        "same_uid_source_mutation_resistance": True,
        "semantic_epoch_image_id": _program_id("semantic_epoch"),
        "semantic_receipt_created": False,
        "status": "bounded_v1_duplicate_semantic_source_guest_execution_rejected",
    }
    for key, value in expected.items():
        if not _exact_type_and_value(report.get(key), value):
            errors.append(f"duplicate-source report binding mismatch: {key}")
    if type(report.get("semantic_input_bytes")) is not int or not (
        0 < report["semantic_input_bytes"] <= 297_147
    ):
        errors.append("duplicate-source report semantic input size is invalid")
    if not support.is_digest(report.get("semantic_input_sha256")):
        errors.append("duplicate-source report semantic input SHA-256 is invalid")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=support.DEFAULT_MANIFEST)
    parser.add_argument("--repo-root", type=Path, default=support.REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_manifest(args.manifest, repo_root=args.repo_root)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
