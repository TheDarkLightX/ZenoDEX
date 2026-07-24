#!/usr/bin/env python3
"""Check one authority-neutral Spot V7 retained-proof evidence bundle.

The checker establishes exact byte identities and deterministic relations among
one structurally Succinct V7 receipt, its exact V6 child receipt, guest input,
journal, data-only verifier output, Plan B, and one exact seal mutation.  It
does not execute a RISC0 verifier or establish build, Firecracker, release,
settlement, or production authority.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import stat
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import Any, Mapping, NoReturn

EVIDENCE_SCHEMA_V1 = "zenodex/zrpf_spot_settlement_v7_local_evidence/v1"
REPORT_SCHEMA_V1 = "zenodex/zrpf_spot_settlement_v7_local_evidence_check/v1"
RECEIPT_SECURITY_PROFILE_ID_V1 = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1 = "zenodex/zrpf_spot_settlement_v7_verified_output/v1"
_V7_PROFILE_DOMAIN_V1 = b"zenodex.zrpf.spot_settlement_v7.profile.v1"
_V7_MANIFEST_DOMAIN_V1 = b"zenodex.zrpf.spot_settlement_v7.manifest.v1"
_RECEIPT_SECURITY_DOMAIN_V4 = b"zenodex.zrpf.receipt_security_profile_id.v4"

RECEIPT_VERIFIER_PARAMETERS_WORDS_V1 = (
    3_102_336_492,
    3_939_904_686,
    3_022_461_035,
    1_208_221_540,
    3_740_575_737,
    10_233_549,
    1_979_579_783,
    329_288_969,
)
RECEIPT_CONTROL_ID_WORDS_V1 = (
    1_035_118_419,
    1_570_699_527,
    1_491_633_494,
    504_952_180,
    648_709_764,
    132_516_474,
    1_203_431_935,
    1_255_849_416,
)

V7_OUTPUT_MAGIC_V1 = b"ZSPTV7O1"
V7_OUTPUT_VERSION_V1 = 1
V7_GUEST_ENVELOPE_VERSION_V1 = 1
V7_OUTPUT_FIXED_FIELD_COUNT_V1 = 19
V7_OUTPUT_FIXED_FIELDS_OFFSET_V1 = 26
V7_OUTPUT_HEADER_BYTES_V1 = V7_OUTPUT_FIXED_FIELDS_OFFSET_V1 + V7_OUTPUT_FIXED_FIELD_COUNT_V1 * 32
V7_JOURNAL_MAGIC_V1 = b"ZSPTV7J1"
V7_JOURNAL_VERSION_V1 = 1
V7_JOURNAL_FIXED_FIELD_COUNT_V1 = 13
V7_JOURNAL_HEADER_BYTES_V1 = 26
V7_SEMANTIC_JOURNAL_BYTES_V1 = 2 + 8 * 32 + 48 + 4
V7_EFFECT_BINDING_JOURNAL_BYTES_V1 = 2 + 12 * 32
V7_MAX_PLAN_B_BYTES_V1 = 48 * 1_024
V7_MAX_OUTPUT_BYTES_V1 = 64 * 1_024
MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 = 8 * 1_024 * 1_024
MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 = 1_024
MAX_V6_CHILD_JOURNAL_BYTES_V1 = (
    971 + MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 + MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2
)
MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 = 512
MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3 = 8 * 1_024 * 1_024
MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 = 16_384
MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1 = (
    2
    + (4 + 4 + 4 + 16)
    + MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 * (48 + 32 + 16)
    + MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 * (32 * 3 + 16 * 3 + 4 + 8)
    + MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 * (48 + 32 + 16)
    + 32
    + 32
)
V7_MAX_GUEST_INPUT_BYTES_V1 = (
    2
    + 4 * 4
    + MAX_V6_CHILD_JOURNAL_BYTES_V1
    + MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1
    + MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3
    + MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1
)
MAX_RECEIPT_BYTES_V1 = 16 * 1_024 * 1_024
MAX_EVIDENCE_BYTES_V1 = 256 * 1_024
MAX_TOTAL_ARTIFACT_BYTES_V1 = 80 * 1_024 * 1_024
_EFFECT_BINDING_COMMITMENT_DOMAIN_V1 = b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1"

ARTIFACT_SPECS_V1 = (
    (
        "v7_receipt",
        "spot-settlement-v7.receipt.json",
        "canonical_risc0_receipt",
        MAX_RECEIPT_BYTES_V1,
    ),
    (
        "v7_receipt_seal_mutation",
        "spot-settlement-v7.seal-word-1-xor-lsb.receipt.json",
        "canonical_risc0_receipt_exact_seal_mutation",
        MAX_RECEIPT_BYTES_V1,
    ),
    (
        "v6_child_receipt",
        "source-opened-spot-settlement-v6.child.receipt.json",
        "canonical_risc0_receipt",
        MAX_RECEIPT_BYTES_V1,
    ),
    ("v7_guest_input", "spot-settlement-v7.guest-input.bin", "binary", V7_MAX_GUEST_INPUT_BYTES_V1),
    ("v7_journal", "spot-settlement-v7.journal.bin", "binary", V7_MAX_OUTPUT_BYTES_V1),
    (
        "v7_verifier_output",
        "spot-settlement-v7.verifier-output.bin",
        "spot_settlement_v7_verifier_output_v1",
        V7_MAX_OUTPUT_BYTES_V1,
    ),
    (
        "v7_plan_b",
        "spot-settlement-v7.plan-b.bin",
        "settlement_effect_plan_v2",
        V7_MAX_PLAN_B_BYTES_V1,
    ),
)

_CLAIMS_V1 = {
    "artifact_identity_and_relations_statically_checked": True,
    "exact_seal_mutation_relation_checked": True,
    "receipt_profile_structure_checked": True,
    "receipt_seals_cryptographically_verified": False,
    "governed_source_build_verified": False,
    "firecracker_execution_verified": False,
    "cross_host_reproducible_build": False,
    "bundle_and_evidence_publication_atomic": False,
    "release_authority": False,
    "settlement_authority": False,
    "production_authority": False,
    "zero_knowledge_privacy": False,
}

_NONCLAIMS_V1 = (
    "static_checker_does_not_verify_risc0_seals",
    "verifier_output_is_data_without_governed_execution_provenance",
    "program_identity_is_observed_and_protocol_identities_are_not_source_build_governed",
    "v6_child_receipt_is_structurally_bound_not_cryptographically_reverified",
    "no_source_or_complete_build_input_closure_verified",
    "no_firecracker_jailer_or_attestation_evidence",
    "data_availability_certificate_bytes_are_retained_without_static_semantic_decode",
    "no_data_retrievability_finality_or_atomic_application_state_commit",
    "no_release_settlement_production_privacy_or_covert_channel_authority",
)


class EvidenceError(ValueError):
    """Stable fail-closed evidence rejection."""


@dataclass(frozen=True)
class ReceiptFactsV1:
    journal_bytes: bytes
    seal_words: tuple[int, ...]
    normalized_non_mutation_sha256: str
    claimed_image_id: bytes


@dataclass(frozen=True)
class GuestInputFactsV1:
    child_journal: bytes
    data_availability_certificate: bytes
    source_replay: bytes
    state_root_host_input: bytes


@dataclass(frozen=True)
class JournalFactsV1:
    fixed_fields: tuple[bytes, ...]
    plan_b: bytes
    effect_binding_fields: tuple[bytes, ...]
    state_root_host_input_length: int


@dataclass(frozen=True)
class VerifierOutputFactsV1:
    fixed_fields: tuple[bytes, ...]
    journal_bytes: bytes
    journal: JournalFactsV1
    declared_plan_b_length: int
    state_root_host_input_length: int


@dataclass(frozen=True)
class ArtifactAnalysisV1:
    v7_receipt: ReceiptFactsV1
    v6_child_receipt: ReceiptFactsV1
    mutation_original_word: int
    mutation_word: int
    mutation_word_count: int
    guest_input: GuestInputFactsV1
    output: VerifierOutputFactsV1


def canonical_evidence_bytes(document: Any) -> bytes:
    """Return the only accepted evidence-record representation."""

    return (json.dumps(document, indent=2, sort_keys=False) + "\n").encode("utf-8")


def canonical_compact_json_bytes(document: Any) -> bytes:
    return json.dumps(document, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def compose_evidence_document_v1(
    *,
    recorded_at: str,
    artifact_raw: Mapping[str, bytes],
) -> dict[str, Any]:
    """Derive an evidence record exclusively from exact artifact bytes."""

    _require_date(recorded_at, "recorded_at")
    _require_exact_artifact_ids(artifact_raw)
    analysis = analyze_artifacts_v1(artifact_raw)
    return {
        "schema": EVIDENCE_SCHEMA_V1,
        "recorded_at": recorded_at,
        "artifacts": _artifact_records_v1(artifact_raw),
        "identities": _identity_records_v1(analysis),
        "relations": _relation_records_v1(analysis, artifact_raw),
        "claims": dict(_CLAIMS_V1),
        "nonclaims": list(_NONCLAIMS_V1),
    }


def _artifact_records_v1(artifact_raw: Mapping[str, bytes]) -> list[dict[str, Any]]:
    return [
        {
            "id": artifact_id,
            "path": file_name,
            "kind": kind,
            "size_bytes": len(artifact_raw[artifact_id]),
            "sha256": _sha256(artifact_raw[artifact_id]),
        }
        for artifact_id, file_name, kind, _maximum in ARTIFACT_SPECS_V1
    ]


def _identity_records_v1(analysis: ArtifactAnalysisV1) -> dict[str, Any]:
    output = analysis.output
    return {
        "v7_program_id": output.fixed_fields[0].hex(),
        "v7_image_id": output.fixed_fields[0].hex(),
        "v7_profile_id": output.fixed_fields[1].hex(),
        "v7_program_manifest_root": output.fixed_fields[2].hex(),
        "v6_child_program_id": output.fixed_fields[4].hex(),
        "v6_child_image_id": output.fixed_fields[4].hex(),
        "required_v6_child_receipt_security_profile_id": output.fixed_fields[5].hex(),
        "receipt_security_profile": {
            "profile_id": RECEIPT_SECURITY_PROFILE_ID_V1,
            "receipt_kind": "Succinct",
            "hash_function": "poseidon2",
            "risc0_zkvm_version": "3.0.5",
            "verifier_parameters_words": list(RECEIPT_VERIFIER_PARAMETERS_WORDS_V1),
            "control_id_words": list(RECEIPT_CONTROL_ID_WORDS_V1),
        },
    }


def _relation_records_v1(
    analysis: ArtifactAnalysisV1, artifact_raw: Mapping[str, bytes]
) -> dict[str, Any]:
    journal = analysis.output.journal
    return {
        "v7_receipt_journal_sha256": _sha256(analysis.v7_receipt.journal_bytes),
        "v6_child_receipt_journal_sha256": _sha256(analysis.v6_child_receipt.journal_bytes),
        "v7_guest_input_sha256": _sha256(artifact_raw["v7_guest_input"]),
        "v7_verifier_output_sha256": _sha256(artifact_raw["v7_verifier_output"]),
        "v7_journal_sha256": _sha256(analysis.output.journal_bytes),
        "v7_plan_b_sha256": _sha256(journal.plan_b),
        "v7_plan_b_commitment": journal.fixed_fields[10].hex(),
        "source_replay_sha256": _sha256(analysis.guest_input.source_replay),
        "state_root_host_input_sha256": _sha256(analysis.guest_input.state_root_host_input),
        "state_root_host_input_size_bytes": len(analysis.guest_input.state_root_host_input),
        "exact_seal_mutation": {
            "kind": "succinct_seal_word_1_xor_1_v1",
            "word_count": analysis.mutation_word_count,
            "word_index": 1,
            "original_word": analysis.mutation_original_word,
            "mutated_word": analysis.mutation_word,
            "xor_mask": 1,
            "journal_unchanged": True,
            "non_seal_receipt_bytes_unchanged": True,
        },
    }


def analyze_artifacts_v1(artifact_raw: Mapping[str, bytes]) -> ArtifactAnalysisV1:
    """Check all cross-artifact relations without claiming proof validity."""

    _require_exact_artifact_ids(artifact_raw)
    v7 = _decode_receipt(
        artifact_raw["v7_receipt"],
        "V7 receipt",
        maximum_journal_bytes=V7_MAX_OUTPUT_BYTES_V1,
    )
    mutation = _decode_receipt(
        artifact_raw["v7_receipt_seal_mutation"],
        "V7 receipt mutation",
        maximum_journal_bytes=V7_MAX_OUTPUT_BYTES_V1,
    )
    child = _decode_receipt(
        artifact_raw["v6_child_receipt"],
        "V6 child receipt",
        maximum_journal_bytes=MAX_V6_CHILD_JOURNAL_BYTES_V1,
    )
    original_word, mutated_word, word_count = _require_exact_seal_mutation(v7, mutation)
    guest = _decode_guest_input(artifact_raw["v7_guest_input"])
    output = _decode_verifier_output(artifact_raw["v7_verifier_output"])

    _require_equal(v7.journal_bytes, artifact_raw["v7_journal"], "V7 receipt journal")
    _require_equal(output.journal_bytes, artifact_raw["v7_journal"], "verifier output journal")
    _require_equal(output.journal.plan_b, artifact_raw["v7_plan_b"], "exact Plan B")
    _require_equal(v7.claimed_image_id, output.fixed_fields[0], "V7 receipt image ID")
    _require_equal(child.claimed_image_id, output.fixed_fields[4], "V6 child receipt image ID")
    _require_equal(child.journal_bytes, guest.child_journal, "V6 child guest-input journal")
    _require_equal(
        _sha256_raw(child.journal_bytes),
        output.journal.fixed_fields[3],
        "V6 child journal SHA-256",
    )
    _require_equal(
        _sha256_raw(guest.source_replay),
        output.journal.fixed_fields[6],
        "source replay SHA-256",
    )
    _require_equal(
        _sha256_raw(guest.state_root_host_input),
        output.journal.fixed_fields[7],
        "state-root host input SHA-256",
    )
    _require_equal(
        len(guest.state_root_host_input),
        output.state_root_host_input_length,
        "state-root host input length",
    )
    return ArtifactAnalysisV1(
        v7_receipt=v7,
        v6_child_receipt=child,
        mutation_original_word=original_word,
        mutation_word=mutated_word,
        mutation_word_count=word_count,
        guest_input=guest,
        output=output,
    )


def load_evidence(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = read_bounded_regular_file_v1(
        path, maximum_bytes=MAX_EVIDENCE_BYTES_V1, label="evidence record"
    )
    document = _load_json(raw, "evidence record")
    if type(document) is not dict:
        raise EvidenceError("evidence root must be an object")
    if canonical_evidence_bytes(document) != raw:
        raise EvidenceError("evidence record bytes are noncanonical")
    return document, raw


def check_evidence(
    evidence_path: Path,
    *,
    artifact_directory: Path,
    expected_evidence_sha256: str | None = None,
) -> dict[str, Any]:
    document, raw = load_evidence(evidence_path)
    evidence_sha256 = _sha256(raw)
    if expected_evidence_sha256 is not None:
        _require_hash(expected_evidence_sha256, "expected evidence SHA-256")
        _require_equal(evidence_sha256, expected_evidence_sha256, "expected evidence SHA-256")
    artifact_raw = load_exact_artifact_directory_v1(artifact_directory)
    expected = compose_evidence_document_v1(
        recorded_at=_recorded_at(document), artifact_raw=artifact_raw
    )
    expected_raw = canonical_evidence_bytes(expected)
    if raw != expected_raw:
        _raise_document_mismatch(document, expected)
    analysis = analyze_artifacts_v1(artifact_raw)
    return {
        "ok": True,
        "schema": REPORT_SCHEMA_V1,
        "evidence_sha256": evidence_sha256,
        "governed_anchor_checked": expected_evidence_sha256 is not None,
        "artifacts_checked": len(ARTIFACT_SPECS_V1),
        "receipt_profiles_structurally_checked": 3,
        "receipt_journal_bindings_checked": 2,
        "receipt_image_bindings_checked": 2,
        "protocol_identity_derivations_checked": 3,
        "exact_seal_mutations_checked": 1,
        "guest_input_component_bindings_checked": 3,
        "verifier_output_journal_bindings_checked": V7_OUTPUT_FIXED_FIELD_COUNT_V1,
        "plan_b_exact_bytes_checked": analysis.output.journal.plan_b == artifact_raw["v7_plan_b"],
        "v7_program_id": analysis.output.fixed_fields[0].hex(),
        "v7_profile_id": analysis.output.fixed_fields[1].hex(),
        "v7_program_manifest_root": analysis.output.fixed_fields[2].hex(),
        "v6_child_program_id": analysis.output.fixed_fields[4].hex(),
        "receipt_seals_cryptographically_verified": False,
        "governed_source_build_verified": False,
        "firecracker_execution_verified": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }


def load_exact_artifact_directory_v1(directory: Path) -> dict[str, bytes]:
    try:
        root_stat = directory.lstat()
    except OSError as exc:
        raise EvidenceError("artifact directory is unavailable") from exc
    if stat.S_ISLNK(root_stat.st_mode) or not stat.S_ISDIR(root_stat.st_mode):
        raise EvidenceError("artifact directory must be a real directory")
    expected_names = {spec[1] for spec in ARTIFACT_SPECS_V1}
    try:
        observed_names = {entry.name for entry in directory.iterdir()}
    except OSError as exc:
        raise EvidenceError("artifact directory inventory failed") from exc
    if observed_names != expected_names:
        raise EvidenceError("artifact directory inventory mismatch")
    result: dict[str, bytes] = {}
    total = 0
    for artifact_id, file_name, _kind, maximum in ARTIFACT_SPECS_V1:
        raw = read_bounded_regular_file_v1(
            directory / file_name,
            maximum_bytes=maximum,
            label=f"artifact {artifact_id}",
        )
        total += len(raw)
        if total > MAX_TOTAL_ARTIFACT_BYTES_V1:
            raise EvidenceError("total artifact bytes exceed governed bound")
        result[artifact_id] = raw
    return result


def read_bounded_regular_file_v1(path: Path, *, maximum_bytes: int, label: str) -> bytes:
    """Read one stable regular file without following a final symlink."""

    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise EvidenceError(f"{label} open failed") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
            raise EvidenceError(f"{label} must be a single-link regular file")
        if before.st_size <= 0 or before.st_size > maximum_bytes:
            raise EvidenceError(f"{label} byte length is unsupported")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                raise EvidenceError(f"{label} changed while reading")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise EvidenceError(f"{label} grew while reading")
        after = os.fstat(descriptor)
        identity_before = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        identity_after = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if identity_before != identity_after:
            raise EvidenceError(f"{label} changed while reading")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _decode_receipt(
    raw: bytes,
    label: str,
    *,
    maximum_journal_bytes: int,
) -> ReceiptFactsV1:
    value = _load_json(raw, label)
    if type(value) is not dict or set(value) != {"inner", "journal", "metadata"}:
        raise EvidenceError(f"{label} outer field set mismatch")
    succinct, seal = _validated_succinct_body(value, label)
    journal_bytes = _receipt_journal_bytes(
        value["journal"], label, maximum_journal_bytes=maximum_journal_bytes
    )
    if canonical_compact_json_bytes(value) != raw:
        raise EvidenceError(f"{label} bytes are noncanonical")
    claimed_image_id = _receipt_claimed_image_id(succinct["claim"], label)
    normalized = copy.deepcopy(value)
    normalized["inner"]["Succinct"]["seal"][1] = 0
    return ReceiptFactsV1(
        journal_bytes,
        seal,
        _sha256(canonical_compact_json_bytes(normalized)),
        claimed_image_id,
    )


def _validated_succinct_body(
    value: dict[str, Any], label: str
) -> tuple[dict[str, Any], tuple[int, ...]]:
    inner = value["inner"]
    if type(inner) is not dict or set(inner) != {"Succinct"}:
        raise EvidenceError(f"{label} is not structurally Succinct")
    succinct = inner["Succinct"]
    expected_succinct = {
        "seal",
        "control_id",
        "claim",
        "hashfn",
        "verifier_parameters",
        "control_inclusion_proof",
    }
    if type(succinct) is not dict or set(succinct) != expected_succinct:
        raise EvidenceError(f"{label} Succinct field set mismatch")
    if succinct["hashfn"] != "poseidon2":
        raise EvidenceError(f"{label} hash function mismatch")
    if succinct["control_id"] != list(RECEIPT_CONTROL_ID_WORDS_V1):
        raise EvidenceError(f"{label} control ID mismatch")
    expected_parameters = list(RECEIPT_VERIFIER_PARAMETERS_WORDS_V1)
    if succinct["verifier_parameters"] != expected_parameters:
        raise EvidenceError(f"{label} verifier parameters mismatch")
    if value["metadata"] != {"verifier_parameters": expected_parameters}:
        raise EvidenceError(f"{label} metadata mismatch")
    seal = succinct["seal"]
    if (
        type(seal) is not list
        or len(seal) <= 1
        or any(type(word) is not int or not 0 <= word <= 0xFFFF_FFFF for word in seal)
    ):
        raise EvidenceError(f"{label} Succinct seal is malformed")
    return succinct, tuple(seal)


def _receipt_journal_bytes(journal: Any, label: str, *, maximum_journal_bytes: int) -> bytes:
    if type(journal) is not dict or set(journal) != {"bytes"}:
        raise EvidenceError(f"{label} journal envelope mismatch")
    values = journal["bytes"]
    if (
        type(values) is not list
        or not values
        or len(values) > maximum_journal_bytes
        or any(type(value) is not int or not 0 <= value <= 255 for value in values)
    ):
        raise EvidenceError(f"{label} journal bytes are malformed")
    return bytes(values)


def _require_exact_seal_mutation(
    source: ReceiptFactsV1, candidate: ReceiptFactsV1
) -> tuple[int, int, int]:
    if source.journal_bytes != candidate.journal_bytes:
        raise EvidenceError("seal mutation changes the receipt journal")
    if source.normalized_non_mutation_sha256 != candidate.normalized_non_mutation_sha256:
        raise EvidenceError("seal mutation changes non-seal receipt bytes")
    if len(source.seal_words) != len(candidate.seal_words):
        raise EvidenceError("seal mutation changes the seal length")
    differences = [
        (index, original, mutated)
        for index, (original, mutated) in enumerate(
            zip(source.seal_words, candidate.seal_words, strict=True)
        )
        if original != mutated
    ]
    if len(differences) != 1:
        raise EvidenceError("seal mutation must change exactly one word")
    index, original, mutated = differences[0]
    if index != 1 or original ^ mutated != 1:
        raise EvidenceError("seal mutation must XOR word 1 by exactly one")
    return original, mutated, len(source.seal_words)


def _decode_guest_input(raw: bytes) -> GuestInputFactsV1:
    if not raw or len(raw) > V7_MAX_GUEST_INPUT_BYTES_V1:
        raise EvidenceError("V7 guest input byte length is unsupported")
    cursor = 0
    version, cursor = _take_u16(raw, cursor, "guest input version")
    if version != 1:
        raise EvidenceError("V7 guest input version mismatch")
    components: list[bytes] = []
    for label, maximum in (
        ("source child journal", MAX_V6_CHILD_JOURNAL_BYTES_V1),
        ("data availability certificate", MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1),
        ("source replay", MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3),
        ("state-root host input", MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1),
    ):
        length, cursor = _take_u32(raw, cursor, f"{label} length")
        if not 0 < length <= maximum:
            raise EvidenceError(f"V7 guest input {label} length is unsupported")
        component, cursor = _take(raw, cursor, length, label)
        components.append(component)
    if cursor != len(raw):
        raise EvidenceError("V7 guest input has trailing bytes")
    return GuestInputFactsV1(*components)


def _decode_verifier_output(raw: bytes) -> VerifierOutputFactsV1:
    if not V7_OUTPUT_HEADER_BYTES_V1 < len(raw) <= V7_MAX_OUTPUT_BYTES_V1:
        raise EvidenceError("V7 verifier output byte length is unsupported")
    if raw[:8] != V7_OUTPUT_MAGIC_V1:
        raise EvidenceError("V7 verifier output magic mismatch")
    version = int.from_bytes(raw[8:10], "big")
    total = int.from_bytes(raw[10:14], "big")
    journal_length = int.from_bytes(raw[14:18], "big")
    plan_length = int.from_bytes(raw[18:22], "big")
    host_input_length = int.from_bytes(raw[22:26], "big")
    if version != V7_OUTPUT_VERSION_V1 or total != len(raw):
        raise EvidenceError("V7 verifier output framing mismatch")
    if journal_length != len(raw) - V7_OUTPUT_HEADER_BYTES_V1:
        raise EvidenceError("V7 verifier output journal length mismatch")
    if not 0 < plan_length <= V7_MAX_PLAN_B_BYTES_V1 or host_input_length <= 0:
        raise EvidenceError("V7 verifier output bounded length mismatch")
    fixed = _read_nonzero_fields(
        raw,
        V7_OUTPUT_FIXED_FIELDS_OFFSET_V1,
        V7_OUTPUT_FIXED_FIELD_COUNT_V1,
        "V7 verifier output",
    )
    journal_bytes = raw[V7_OUTPUT_HEADER_BYTES_V1:]
    journal = _decode_journal(journal_bytes)
    if plan_length != len(journal.plan_b):
        raise EvidenceError("V7 verifier output Plan B length mismatch")
    if host_input_length != journal.state_root_host_input_length:
        raise EvidenceError("V7 verifier output host input length mismatch")
    associations = (
        (fixed[3], _sha256_raw(journal_bytes)),
        (fixed[4], journal.fixed_fields[0]),
        (fixed[5], journal.fixed_fields[1]),
        (fixed[6], journal.fixed_fields[2]),
        (fixed[7], journal.fixed_fields[3]),
        (fixed[8], journal.fixed_fields[4]),
        (fixed[9], journal.fixed_fields[5]),
        (fixed[10], journal.fixed_fields[10]),
        (fixed[11], journal.fixed_fields[11]),
        (fixed[12], journal.effect_binding_fields[6]),
        (fixed[13], journal.effect_binding_fields[7]),
        (fixed[14], journal.fixed_fields[12]),
        (fixed[18], journal.fixed_fields[7]),
    )
    if any(actual != expected for actual, expected in associations):
        raise EvidenceError("V7 verifier output journal association mismatch")
    _require_protocol_identities(fixed)
    return VerifierOutputFactsV1(
        fixed_fields=fixed,
        journal_bytes=journal_bytes,
        journal=journal,
        declared_plan_b_length=plan_length,
        state_root_host_input_length=host_input_length,
    )


def _decode_journal(raw: bytes) -> JournalFactsV1:
    minimum = (
        V7_JOURNAL_HEADER_BYTES_V1
        + V7_JOURNAL_FIXED_FIELD_COUNT_V1 * 32
        + V7_SEMANTIC_JOURNAL_BYTES_V1
        + V7_EFFECT_BINDING_JOURNAL_BYTES_V1
    )
    if not minimum < len(raw) <= minimum + V7_MAX_PLAN_B_BYTES_V1:
        raise EvidenceError("V7 journal byte length is unsupported")
    if raw[:8] != V7_JOURNAL_MAGIC_V1:
        raise EvidenceError("V7 journal magic mismatch")
    version = int.from_bytes(raw[8:10], "big")
    total = int.from_bytes(raw[10:14], "big")
    host_input_length = int.from_bytes(raw[14:18], "big")
    semantic_length = int.from_bytes(raw[18:20], "big")
    binding_length = int.from_bytes(raw[20:22], "big")
    plan_length = int.from_bytes(raw[22:26], "big")
    if (
        version != V7_JOURNAL_VERSION_V1
        or total != len(raw)
        or host_input_length <= 0
        or semantic_length != V7_SEMANTIC_JOURNAL_BYTES_V1
        or binding_length != V7_EFFECT_BINDING_JOURNAL_BYTES_V1
        or not 0 < plan_length <= V7_MAX_PLAN_B_BYTES_V1
        or minimum + plan_length != len(raw)
    ):
        raise EvidenceError("V7 journal framing mismatch")
    fixed = _read_nonzero_fields(
        raw,
        V7_JOURNAL_HEADER_BYTES_V1,
        V7_JOURNAL_FIXED_FIELD_COUNT_V1,
        "V7 journal",
    )
    cursor = V7_JOURNAL_HEADER_BYTES_V1 + V7_JOURNAL_FIXED_FIELD_COUNT_V1 * 32
    semantic, cursor = _take(raw, cursor, semantic_length, "semantic journal")
    binding, cursor = _take(raw, cursor, binding_length, "effect-binding journal")
    plan, cursor = _take(raw, cursor, plan_length, "Plan B")
    if cursor != len(raw):
        raise EvidenceError("V7 journal has trailing bytes")
    if _sha256_raw(semantic) != fixed[8]:
        raise EvidenceError("V7 semantic journal SHA-256 mismatch")
    expected_binding = _sha256_raw(
        len(_EFFECT_BINDING_COMMITMENT_DOMAIN_V1).to_bytes(2, "big")
        + _EFFECT_BINDING_COMMITMENT_DOMAIN_V1
        + binding
    )
    if expected_binding != fixed[9]:
        raise EvidenceError("V7 effect-binding commitment mismatch")
    if int.from_bytes(binding[:2], "big") != 1:
        raise EvidenceError("V7 effect-binding version mismatch")
    binding_fields = _read_nonzero_fields(binding, 2, 12, "V7 effect-binding journal")
    if binding_fields[4] != fixed[10]:
        raise EvidenceError("V7 Plan B commitment association mismatch")
    if _sha256_raw(plan) != fixed[11]:
        raise EvidenceError("V7 Plan B SHA-256 mismatch")
    return JournalFactsV1(fixed, plan, binding_fields, host_input_length)


def _read_nonzero_fields(raw: bytes, offset: int, count: int, label: str) -> tuple[bytes, ...]:
    end = offset + count * 32
    if end > len(raw):
        raise EvidenceError(f"{label} fixed fields are truncated")
    fields = tuple(raw[index : index + 32] for index in range(offset, end, 32))
    if len(fields) != count or any(len(field) != 32 or not any(field) for field in fields):
        raise EvidenceError(f"{label} fixed field is zero or malformed")
    return fields


def _receipt_claimed_image_id(claim: Any, label: str) -> bytes:
    try:
        words = claim["Value"]["pre"]["Value"]["merkle_root"]
    except (KeyError, TypeError) as exc:
        raise EvidenceError(f"{label} claimed image ID is unavailable") from exc
    if (
        type(words) is not list
        or len(words) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFF_FFFF for word in words)
    ):
        raise EvidenceError(f"{label} claimed image ID words are malformed")
    return b"".join(word.to_bytes(4, "little") for word in words)


def _require_protocol_identities(fixed: tuple[bytes, ...]) -> None:
    expected_profile, expected_child_profile, expected_manifest = derive_protocol_identities_v1(
        v7_program_id=fixed[0],
        v6_child_program_id=fixed[4],
    )
    for actual, expected, label in (
        (fixed[1], expected_profile, "V7 profile ID"),
        (fixed[5], expected_child_profile, "V6 child receipt security profile ID"),
        (fixed[2], expected_manifest, "V7 program manifest root"),
    ):
        _require_equal(actual, expected, label)


def derive_protocol_identities_v1(
    *,
    v7_program_id: bytes,
    v6_child_program_id: bytes,
) -> tuple[bytes, bytes, bytes]:
    """Mirror the V7 verifier's protocol identity derivations exactly."""

    for value, label in (
        (v7_program_id, "V7 program ID"),
        (v6_child_program_id, "V6 child program ID"),
    ):
        if type(value) is not bytes or len(value) != 32 or not any(value):
            raise EvidenceError(f"{label} is malformed")
    expected_profile = _domain_hash(_V7_PROFILE_DOMAIN_V1, ())
    expected_child_profile = _hash_framed(
        _RECEIPT_SECURITY_DOMAIN_V4,
        (
            RECEIPT_SECURITY_PROFILE_ID_V1.encode("ascii"),
            b"succinct",
            _risc0_words_to_bytes(RECEIPT_VERIFIER_PARAMETERS_WORDS_V1),
            b"poseidon2",
            _risc0_words_to_bytes(RECEIPT_CONTROL_ID_WORDS_V1),
        ),
    )
    expected_manifest = _domain_hash(
        _V7_MANIFEST_DOMAIN_V1,
        (
            v7_program_id,
            expected_profile,
            v6_child_program_id,
            expected_child_profile,
            RECEIPT_SECURITY_PROFILE_ID_V1.encode("ascii"),
            SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1.encode("ascii"),
            V7_GUEST_ENVELOPE_VERSION_V1.to_bytes(2, "big"),
            V7_JOURNAL_MAGIC_V1,
            V7_JOURNAL_VERSION_V1.to_bytes(2, "big"),
            V7_OUTPUT_MAGIC_V1,
            V7_OUTPUT_VERSION_V1.to_bytes(2, "big"),
        ),
    )
    return expected_profile, expected_child_profile, expected_manifest


def _risc0_words_to_bytes(words: tuple[int, ...]) -> bytes:
    if len(words) != 8 or any(not 0 <= word <= 0xFFFF_FFFF for word in words):
        raise EvidenceError("RISC0 digest words are malformed")
    return b"".join(word.to_bytes(4, "little") for word in words)


def _domain_hash(domain: bytes, fields: tuple[bytes, ...]) -> bytes:
    hasher = hashlib.sha256()
    hasher.update(len(domain).to_bytes(2, "big"))
    hasher.update(domain)
    hasher.update(len(fields).to_bytes(2, "big"))
    for field in fields:
        hasher.update(len(field).to_bytes(4, "big"))
        hasher.update(field)
    return hasher.digest()


def _hash_framed(domain: bytes, fields: tuple[bytes, ...]) -> bytes:
    hasher = hashlib.sha256()
    hasher.update(len(domain).to_bytes(2, "big"))
    hasher.update(domain)
    for field in fields:
        hasher.update(len(field).to_bytes(4, "big"))
        hasher.update(field)
    return hasher.digest()


def _take(raw: bytes, cursor: int, length: int, label: str) -> tuple[bytes, int]:
    end = cursor + length
    if length < 0 or end < cursor or end > len(raw):
        raise EvidenceError(f"{label} is truncated")
    return raw[cursor:end], end


def _take_u16(raw: bytes, cursor: int, label: str) -> tuple[int, int]:
    value, cursor = _take(raw, cursor, 2, label)
    return int.from_bytes(value, "big"), cursor


def _take_u32(raw: bytes, cursor: int, label: str) -> tuple[int, int]:
    value, cursor = _take(raw, cursor, 4, label)
    return int.from_bytes(value, "big"), cursor


def _load_json(raw: bytes, label: str) -> Any:
    try:
        return json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, EvidenceError) as exc:
        raise EvidenceError(f"{label} JSON rejected: {exc}") from exc


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(_value: str) -> NoReturn:
    raise EvidenceError("floating-point JSON numbers are forbidden")


def _recorded_at(document: dict[str, Any]) -> str:
    if set(document) != {
        "schema",
        "recorded_at",
        "artifacts",
        "identities",
        "relations",
        "claims",
        "nonclaims",
    }:
        raise EvidenceError("evidence field set mismatch")
    recorded_at = document.get("recorded_at")
    return _require_date(recorded_at, "evidence.recorded_at")


def _require_date(value: Any, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"\d{4}-\d{2}-\d{2}", value) is None:
        raise EvidenceError(f"{label} must be a canonical date")
    try:
        if date.fromisoformat(value).isoformat() != value:
            raise ValueError
    except ValueError as exc:
        raise EvidenceError(f"{label} must be a canonical date") from exc
    return value


def _require_exact_artifact_ids(artifact_raw: Mapping[str, bytes]) -> None:
    expected = {spec[0] for spec in ARTIFACT_SPECS_V1}
    if set(artifact_raw) != expected:
        raise EvidenceError("artifact input IDs mismatch")
    for artifact_id, _name, _kind, maximum in ARTIFACT_SPECS_V1:
        raw = artifact_raw[artifact_id]
        if type(raw) is not bytes or not raw or len(raw) > maximum:
            raise EvidenceError(f"artifact {artifact_id} byte length is unsupported")


def _raise_document_mismatch(actual: Any, expected: Any, path: str = "evidence") -> NoReturn:
    if type(actual) is not type(expected):
        raise EvidenceError(f"{path} type mismatch")
    if isinstance(expected, dict):
        if set(actual) != set(expected):
            missing = sorted(set(expected) - set(actual))
            unknown = sorted(set(actual) - set(expected))
            detail = f"missing={missing}, unknown={unknown}"
            raise EvidenceError(f"{path} field set mismatch: {detail}")
        for key in expected:
            if actual[key] != expected[key] or type(actual[key]) is not type(expected[key]):
                _raise_document_mismatch(actual[key], expected[key], f"{path}.{key}")
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            raise EvidenceError(f"{path} length mismatch")
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            if left != right or type(left) is not type(right):
                _raise_document_mismatch(left, right, f"{path}[{index}]")
    elif actual != expected or type(actual) is not type(expected):
        raise EvidenceError(f"{path} value mismatch")
    raise EvidenceError(f"{path} differs from derived evidence")


def _require_hash(value: Any, label: str) -> None:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise EvidenceError(f"{label} must be lowercase SHA-256")


def _require_equal(actual: Any, expected: Any, label: str) -> None:
    if type(actual) is not type(expected) or actual != expected:
        raise EvidenceError(f"{label} mismatch")


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_raw(raw: bytes) -> bytes:
    return hashlib.sha256(raw).digest()


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--artifact-directory", type=Path, required=True)
    parser.add_argument("--expected-evidence-sha256")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = check_evidence(
            args.evidence,
            artifact_directory=args.artifact_directory,
            expected_evidence_sha256=args.expected_evidence_sha256,
        )
    except EvidenceError as exc:
        report = {"ok": False, "schema": REPORT_SCHEMA_V1, "error": str(exc)}
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("ok" if report["ok"] else f"rejected: {report['error']}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
