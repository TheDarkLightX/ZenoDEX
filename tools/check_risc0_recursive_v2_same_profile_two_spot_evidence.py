#!/usr/bin/env python3
"""Replay claim-limited recursive-v2 same-profile two-spot evidence.

The committed evidence manifest, recursive-v2 rebuild reference, and existing
source-pinned two-leaf evidence are fixed trust inputs. Live artifact paths are
caller supplied, bounded, and checked against those committed inputs.

The evidence manifest is pinned by both raw-file and canonical-JSON digests.
Structural validation independently recomputes the identity commitments before
live artifacts are staged and replayed.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import importlib
import json
import os
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from tools.check_risc0_recursive_v2_rebuild_evidence import (
        EvidenceError,
        FileDigest,
    )

_MODULE_PREFIX = "tools." if __package__ else ""
baseline = importlib.import_module(
    f"{_MODULE_PREFIX}check_risc0_recursive_v2_two_leaf_source_pinned_evidence"
)


v2 = baseline.v2
ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PATH = (
    ROOT
    / "docs/research/RECURSIVE_STARK_V2_SAME_PROFILE_TWO_SPOT_EVIDENCE_20260710.json"
)

EVIDENCE_SCHEMA = "zenodex/recursive_stark_v2_same_profile_two_spot_evidence/v1"
REPORT_SCHEMA = "zenodex/recursive_stark_v2_same_profile_two_spot_evidence_check/v1"
EXPECTED_STATUS = "same_host_source_frozen_same_profile_two_spot_receipts_generated_and_verified"
ACCEPTED_STATUS = "same_profile_two_spot_evidence_replayed"

EXPECTED_EVIDENCE_FILE_SHA256 = "18141ffae7279b1a717edb41674b4fae101a489e2d7870b920c45c8d6810512a"
EXPECTED_EVIDENCE_CANONICAL_SHA256 = (
    "6536149d32040a3ebb7a525434ddf1ec7c36890a4219ce2d3295f6f5934754fb"
)

MAX_MANIFEST_BYTES = 1024 * 1024
MAX_LEAF_BYTES = 16 * 1024 * 1024
MAX_NODE_BYTES = 16 * 1024 * 1024
MAX_EXECUTABLE_BYTES = 256 * 1024 * 1024

SPOT_PROOF_TYPE = "risc0.zenodex_recursive_spot_leaf.v1"
SPOT_PROFILE = "recursive_spot_leaf_v1"
SPOT_IMAGE_ID = "1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403"
SPOT_LANE_KIND = "spot"
VERIFIER_STATUS = "recursive_v2_two_leaf_pair_verified"
SEAL_MUTATION_KIND = "succinct_seal_word_xor_lsb_v1"
DUPLICATE_LANE_STDERR = "duplicate authenticated leaf lane ID\n"
DUPLICATE_SOURCE_STDERR = "duplicate authenticated leaf semantic source ID\n"
SWAPPED_NODES_STDERR = "two-leaf pair shape mismatch\n"
ALIAS_HARNESS_STDERR = (
    'derive node commitments: InvalidInput("descendant source IDs not unique")\n'
)
SEAL_REJECT_STDERR_PREFIX = "leaf receipt verification failed:"

LEAF_SOURCE_ID_DOMAIN = b"zenodex.risc0.recursive.leaf_source_id.v2"
ASSIGNED_LEAF_ID_DOMAIN = b"zenodex.risc0.recursive.assigned_leaf_id.v2"
CHILD_VERIFIER_ID_DOMAIN = b"zenodex.risc0.recursive.child_verifier_id.v1"
CHILD_JOURNAL_HASH_DOMAIN = b"zenodex.risc0.recursive.child_journal_hash.v1"
CHILD_CLAIM_HASH_DOMAIN = b"zenodex.risc0.recursive.child_verification_claim_hash.v1"
IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN = (
    b"zenodex.risc0.recursive.immediate_verifier_set_root.v2"
)
DESCENDANT_SOURCES_ROOT_DOMAIN = b"zenodex.risc0.recursive.descendant_sources_root.v2"
ASSIGNED_LEAF_IDS_ROOT_DOMAIN = b"zenodex.risc0.recursive.assigned_leaf_ids_root.v2"

ROOT_KEYS = frozenset(
    {
        "aggregate_v2",
        "claims",
        "date",
        "leaf_claims",
        "negative_controls",
        "nonclaims",
        "proof_pair",
        "same_profile_identity",
        "schema",
        "specialized_host_verifier",
        "status",
        "trust_roots",
        "verification",
        "version",
    }
)
LEAF_KEYS = frozenset(
    {
        "artifact_file_sha256",
        "artifact_size_bytes",
        "assigned_leaf_id",
        "image_id",
        "journal_sha256",
        "lane_id",
        "lane_kind",
        "profile",
        "proof_type",
        "protocol_child_journal_hash",
        "receipt_sha256",
        "role",
        "source_id",
        "statement_hash",
        "verification_claim_hash",
    }
)
NODE_KEYS = frozenset(
    {
        "artifact_file_sha256",
        "artifact_size_bytes",
        "descendant_sources_root",
        "flat_leaf_count",
        "immediate_child_count",
        "immediate_verifier_set_root",
        "journal_sha256",
        "profile",
        "protocol_journal_hash",
        "receipt_sha256",
        "statement_hash",
        "subtree_node_count",
        "tree_height",
    }
)
SHARED_ROOT_KEYS = frozenset(
    {
        "aggregation_scope_hash",
        "assigned_leaf_ids_root",
        "descendant_claims_root",
        "descendant_sources_root",
        "flat_v1_post_state_root",
        "flat_v1_statement_hash",
        "leaf_disclosures_root",
    }
)
IDENTITY_KEYS = frozenset(
    {
        "child_count",
        "derived_child_verifier_id",
        "distinct_lane_id_count",
        "distinct_source_id_count",
        "distinct_statement_hash_count",
        "inner_descendant_sources_root",
        "inner_immediate_verifier_set_root",
        "unique_image_id_count",
        "unique_profile_count",
        "unique_proof_type_count",
        "unique_verifier_id_count",
    }
)
RESULT_KEYS = frozenset({"exit_code", "stderr", "stderr_sha256"})

EXPECTED_CLAIMS = {
    "arbitrary_depth_recursion": False,
    "bounded_host_fanout_constructor_source_pinned": True,
    "cross_environment_reproducibility": False,
    "current_image_same_profile_two_spot_receipts_generated": True,
    "current_image_two_leaf_fixed_height_receipt_integrity": True,
    "data_availability_verified": False,
    "distinct_semantic_source_ids_cryptographically_exercised": True,
    "duplicate_semantic_source_rejection_live_replayed": True,
    "durable_atomic_admission": False,
    "exact_leaf_and_node_binding_verified": True,
    "general_multi_leaf_profile_promoted": False,
    "governed_statement_authority": False,
    "independent_proof_implementation": False,
    "new_receipt_seal_mutation_rejected": True,
    "nonempty_receipt_partition_merge_cryptographically_exercised": False,
    "privacy": False,
    "production_ready": False,
    "proof_regeneration_determinism": False,
    "public_claim_allowed": False,
    "public_replay_available": False,
    "release_authority": False,
    "same_host_source_frozen_build": True,
    "same_profile_verifier_set_cryptographically_exercised": True,
    "settlement_authorization": False,
    "throughput_claim_allowed": False,
    "v1_outer_envelope_canonicality_verified": False,
}

EXPECTED_NONCLAIMS = (
    "This evidence covers one same-host, source-frozen, fanout-two, fixed-height pair containing two distinct authenticated spot statements under one current image and profile.",
    "The inner proof exercises two authenticated child receipts whose derived verifier set contains one unique verifier ID.",
    "The accepted spot leaves have distinct authenticated statement hashes; this run does not exercise two value-moving spot batches or establish throughput.",
    "The lane-alias control confirms that a distinct lane and assigned leaf ID cannot substitute for a distinct semantic source.",
    "The specialized verifier shares RISC0 and recursive-v2 libraries with the prover and is not an independent proof implementation.",
    "Both accepted leaves have empty receipt-ID partitions, so nonempty accepted and rejected receipt-set composition remains unverified.",
    "Schedule, data-availability, and carry fields remain commitment-only for this profile.",
    "The V1 outer envelope does not yet reject duplicate keys or unknown nested fields.",
    "RISC0 receipt verification establishes computational integrity for the authenticated journals; it does not establish witness privacy or zero knowledge.",
    "Arbitrary depth, multiple root subtrees, eight-leaf evidence, cross-host reproducibility, and a governed general fanout profile remain open.",
    "This evidence grants no governance, release, settlement, ledger-admission, throughput, public-replay, or production authority.",
)


def _reject(code: str, detail: str) -> EvidenceError:
    return v2.EvidenceError(code, detail)


def _mapping(value: object, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise _reject("EVIDENCE_SCHEMA", f"{label} must be an object")
    return value


def _exact_keys(value: Mapping[str, Any], expected: frozenset[str], label: str) -> None:
    if frozenset(value) != expected:
        raise _reject("EVIDENCE_SCHEMA", f"{label} keys mismatch")


def _text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise _reject("EVIDENCE_SCHEMA", f"{label} must be a nonempty string")
    return value


def _integer(value: object, label: str, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
        raise _reject("EVIDENCE_SCHEMA", f"{label} must be an integer >= {minimum}")
    return value


def _hex(value: object, label: str, *, bytes_len: int = 32) -> str:
    text = _text(value, label)
    if len(text) != bytes_len * 2:
        raise _reject("EVIDENCE_SCHEMA", f"{label} length mismatch")
    try:
        decoded = bytes.fromhex(text)
    except ValueError as exc:
        raise _reject("EVIDENCE_SCHEMA", f"{label} must be lowercase hexadecimal") from exc
    if decoded.hex() != text:
        raise _reject("EVIDENCE_SCHEMA", f"{label} must be lowercase hexadecimal")
    return text


def _u32(value: int) -> bytes:
    return value.to_bytes(4, "big")


def _framed_text(value: str) -> bytes:
    encoded = value.encode("utf-8")
    if len(encoded) > 0xFFFFFFFF:
        raise _reject("EVIDENCE_IDENTITY", "string length exceeds u32")
    return _u32(len(encoded)) + encoded


def _image_id_words_be(image_id: str) -> bytes:
    raw = bytes.fromhex(_hex(image_id, "image_id"))
    if raw == bytes(32):
        raise _reject("EVIDENCE_IDENTITY", "image ID must be nonzero")
    # RISC0 displays each Digest word in little-endian byte order. Protocol
    # hashing frames the corresponding u32 words in big-endian order.
    return b"".join(
        int.from_bytes(raw[offset : offset + 4], "little").to_bytes(4, "big")
        for offset in range(0, len(raw), 4)
    )


def derive_leaf_source_id(lane_kind: str, statement_hash: str) -> str:
    if not lane_kind:
        raise _reject("EVIDENCE_IDENTITY", "leaf source namespace must be nonempty")
    statement = bytes.fromhex(_hex(statement_hash, "statement_hash"))
    if statement == bytes(32):
        raise _reject("EVIDENCE_IDENTITY", "leaf source statement hash must be nonzero")
    digest = hashlib.sha256()
    digest.update(LEAF_SOURCE_ID_DOMAIN)
    digest.update(_framed_text(lane_kind))
    digest.update(statement)
    return digest.hexdigest()


def derive_assigned_leaf_id(scope_hash: str, lane_id: str, source_id: str) -> str:
    if not lane_id:
        raise _reject("EVIDENCE_IDENTITY", "leaf lane ID must be nonempty")
    scope = bytes.fromhex(_hex(scope_hash, "aggregation_scope_hash"))
    source = bytes.fromhex(_hex(source_id, "source_id"))
    if scope == bytes(32):
        raise _reject("EVIDENCE_IDENTITY", "aggregation scope hash must be nonzero")
    if source == bytes(32):
        raise _reject("EVIDENCE_IDENTITY", "leaf source ID must be nonzero")
    digest = hashlib.sha256()
    digest.update(ASSIGNED_LEAF_ID_DOMAIN)
    digest.update(scope)
    digest.update(_framed_text(lane_id))
    digest.update(source)
    return digest.hexdigest()


def derive_child_verifier_id(image_id: str, profile: str) -> str:
    if not profile:
        raise _reject("EVIDENCE_IDENTITY", "child profile must be nonempty")
    digest = hashlib.sha256()
    digest.update(CHILD_VERIFIER_ID_DOMAIN)
    digest.update(_image_id_words_be(image_id))
    digest.update(_framed_text(profile))
    return digest.hexdigest()


def _root_list(domain: bytes, values: Sequence[str], label: str) -> str:
    decoded = sorted(bytes.fromhex(_hex(value, label)) for value in values)
    if (
        len(decoded) > 0xFFFFFFFF
        or bytes(32) in decoded
        or any(left >= right for left, right in zip(decoded, decoded[1:], strict=False))
    ):
        raise _reject("EVIDENCE_IDENTITY", f"{label} values must be unique")
    digest = hashlib.sha256()
    digest.update(domain)
    digest.update(_u32(len(decoded)))
    for value in decoded:
        digest.update(value)
    return digest.hexdigest()


def derive_immediate_verifier_set_root(verifier_ids: Sequence[str]) -> str:
    return _root_list(IMMEDIATE_VERIFIER_SET_ROOT_DOMAIN, verifier_ids, "verifier_id")


def derive_descendant_sources_root(source_ids: Sequence[str]) -> str:
    return _root_list(DESCENDANT_SOURCES_ROOT_DOMAIN, source_ids, "source_id")


def derive_assigned_leaf_ids_root(assigned_ids: Sequence[str]) -> str:
    return _root_list(ASSIGNED_LEAF_IDS_ROOT_DOMAIN, assigned_ids, "assigned_leaf_id")


def _canonical_sha256(value: object) -> str:
    return hashlib.sha256(v2._canonical_json_bytes(value)).hexdigest()


def _walk_public_strings(value: object) -> None:
    stack = [value]
    while stack:
        current = stack.pop()
        if isinstance(current, Mapping):
            stack.extend(current.values())
        elif isinstance(current, list):
            stack.extend(current)
        elif isinstance(current, str):
            lowered = current.lower()
            if current.startswith(("/", "\\")) or "/home/" in lowered or "/media/" in lowered:
                raise _reject("PUBLIC_PATH_LEAK", current[:160])
            if "private_project_marker" in lowered:
                raise _reject("PUBLIC_PRIVATE_MARKER", current[:160])


def _validate_leaf_row(value: object, label: str) -> Mapping[str, Any]:
    row = _mapping(value, label)
    _exact_keys(row, LEAF_KEYS, label)
    for key in (
        "artifact_file_sha256",
        "assigned_leaf_id",
        "image_id",
        "journal_sha256",
        "protocol_child_journal_hash",
        "receipt_sha256",
        "source_id",
        "statement_hash",
        "verification_claim_hash",
    ):
        _hex(row.get(key), f"{label}.{key}")
    _integer(row.get("artifact_size_bytes"), f"{label}.artifact_size_bytes", minimum=1)
    for key in ("role", "proof_type", "profile", "lane_kind", "lane_id"):
        _text(row.get(key), f"{label}.{key}")
    return row


def _validate_node_row(value: object, label: str) -> Mapping[str, Any]:
    row = _mapping(value, label)
    _exact_keys(row, NODE_KEYS, label)
    for key in (
        "artifact_file_sha256",
        "descendant_sources_root",
        "immediate_verifier_set_root",
        "journal_sha256",
        "protocol_journal_hash",
        "receipt_sha256",
        "statement_hash",
    ):
        _hex(row.get(key), f"{label}.{key}")
    _integer(row.get("artifact_size_bytes"), f"{label}.artifact_size_bytes", minimum=1)
    for key in (
        "flat_leaf_count",
        "immediate_child_count",
        "subtree_node_count",
        "tree_height",
    ):
        _integer(row.get(key), f"{label}.{key}", minimum=1)
    _text(row.get("profile"), f"{label}.profile")
    return row


def _validate_result(value: object, label: str) -> Mapping[str, Any]:
    row = _mapping(value, label)
    _exact_keys(row, RESULT_KEYS, label)
    if _integer(row.get("exit_code"), f"{label}.exit_code", minimum=1) != 1:
        raise _reject("EVIDENCE_CONTROLS", f"{label} exit code must be 1")
    stderr = _text(row.get("stderr"), f"{label}.stderr")
    if hashlib.sha256(stderr.encode("utf-8")).hexdigest() != _hex(
        row.get("stderr_sha256"), f"{label}.stderr_sha256"
    ):
        raise _reject("EVIDENCE_CONTROLS", f"{label} stderr digest mismatch")
    return row


def validate_evidence(
    evidence: Mapping[str, Any],
    reference: Mapping[str, Any],
    source_pinned_baseline: Mapping[str, Any],
    *,
    reference_file_sha256: str,
    baseline_file_sha256: str,
) -> None:
    """Validate an evidence object against already authenticated trust roots."""

    _exact_keys(evidence, ROOT_KEYS, "evidence")
    if (
        evidence.get("schema") != EVIDENCE_SCHEMA
        or evidence.get("version") != 1
        or evidence.get("date") != "2026-07-10"
        or evidence.get("status") != EXPECTED_STATUS
    ):
        raise _reject("EVIDENCE_SCHEMA", "identity mismatch")
    if evidence.get("claims") != EXPECTED_CLAIMS:
        raise _reject("EVIDENCE_CLAIMS", "claim policy mismatch")
    if tuple(evidence.get("nonclaims", ())) != EXPECTED_NONCLAIMS:
        raise _reject("EVIDENCE_NONCLAIMS", "nonclaim policy mismatch")
    _walk_public_strings(evidence)

    trust = _mapping(evidence.get("trust_roots"), "trust_roots")
    _exact_keys(
        trust,
        frozenset({"recursive_v2_rebuild_reference", "source_pinned_two_leaf_baseline"}),
        "trust_roots",
    )
    reference_link = _mapping(
        trust.get("recursive_v2_rebuild_reference"), "recursive_v2_rebuild_reference"
    )
    baseline_link = _mapping(
        trust.get("source_pinned_two_leaf_baseline"), "source_pinned_two_leaf_baseline"
    )
    link_keys = frozenset({"canonical_json_sha256", "file_sha256", "path"})
    _exact_keys(reference_link, link_keys, "recursive_v2_rebuild_reference")
    _exact_keys(baseline_link, link_keys, "source_pinned_two_leaf_baseline")
    if reference_link != {
        "path": "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json",
        "file_sha256": _hex(reference_file_sha256, "reference_file_sha256"),
        "canonical_json_sha256": v2.reference_canonical_sha256(reference),
    }:
        raise _reject("EVIDENCE_REFERENCE_BINDING", "recursive-v2 reference mismatch")
    if baseline_link != {
        "path": "docs/research/RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json",
        "file_sha256": _hex(baseline_file_sha256, "baseline_file_sha256"),
        "canonical_json_sha256": _canonical_sha256(source_pinned_baseline),
    }:
        raise _reject("EVIDENCE_BASELINE_BINDING", "source-pinned baseline mismatch")

    aggregate = _mapping(evidence.get("aggregate_v2"), "aggregate_v2")
    _exact_keys(
        aggregate,
        frozenset({"image_id", "program_sha256", "program_size_bytes", "sdk_version"}),
        "aggregate_v2",
    )
    baseline_aggregate = _mapping(source_pinned_baseline.get("aggregate_v2"), "baseline aggregate")
    expected_aggregate = {
        "sdk_version": reference["sdk_version"],
        "image_id": reference["program"]["image_id"],
        "program_sha256": reference["program"]["program_sha256"],
        "program_size_bytes": reference["program"]["program_bytes"],
    }
    if aggregate != expected_aggregate or aggregate != {
        key: baseline_aggregate[key] for key in expected_aggregate
    }:
        raise _reject("EVIDENCE_PROGRAM_BINDING", "aggregate program mismatch")

    verifier = _mapping(evidence.get("specialized_host_verifier"), "specialized verifier")
    verifier_keys = frozenset(
        {
            "binary_sha256",
            "binary_size_bytes",
            "independent_proof_implementation",
            "repository_source_pinned",
            "source_path",
            "source_sha256",
            "source_size_bytes",
            "status",
        }
    )
    _exact_keys(verifier, verifier_keys, "specialized verifier")
    baseline_verifier = source_pinned_baseline["verification"]["specialized_host_verifier"]
    source_path = "zk/recursive_stark_v2_risc0/harness/src/bin/verify_recursive_v2_two_leaf_pair.rs"
    source_row = next(
        (row for row in reference["source_compile"]["files"] if row.get("path") == source_path),
        None,
    )
    expected_verifier = {
        "repository_source_pinned": True,
        "independent_proof_implementation": False,
        "source_path": source_path,
        "source_sha256": source_row["sha256"] if source_row else None,
        "source_size_bytes": source_row["size_bytes"] if source_row else None,
        "binary_sha256": reference["proof_pair"]["two_leaf_static_verifier"]["sha256"],
        "binary_size_bytes": reference["proof_pair"]["two_leaf_static_verifier"]["size_bytes"],
        "status": VERIFIER_STATUS,
    }
    if source_row is None or verifier != expected_verifier:
        raise _reject("EVIDENCE_VERIFIER_BINDING", "specialized verifier mismatch")
    for key in (
        "repository_source_pinned",
        "independent_proof_implementation",
        "source_path",
        "source_sha256",
        "binary_sha256",
        "binary_size_bytes",
        "status",
    ):
        if baseline_verifier.get(key) != verifier.get(key):
            raise _reject("EVIDENCE_VERIFIER_BINDING", f"baseline verifier mismatch:{key}")

    leaves_value = evidence.get("leaf_claims")
    if not isinstance(leaves_value, list) or len(leaves_value) != 2:
        raise _reject("EVIDENCE_LEAVES", "expected exactly two accepted leaves")
    leaves = [
        _validate_leaf_row(value, f"leaf_claims[{index}]")
        for index, value in enumerate(leaves_value)
    ]
    if [row["role"] for row in leaves] != [
        "spot_baseline",
        "spot_distinct_statement_variant",
    ]:
        raise _reject("EVIDENCE_LEAVES", "leaf role order mismatch")
    for row in leaves:
        if (
            row["proof_type"] != SPOT_PROOF_TYPE
            or row["profile"] != SPOT_PROFILE
            or row["image_id"] != SPOT_IMAGE_ID
            or row["lane_kind"] != SPOT_LANE_KIND
        ):
            raise _reject("EVIDENCE_LEAVES", "accepted leaf surface mismatch")
        if row["source_id"] != derive_leaf_source_id(row["lane_kind"], row["statement_hash"]):
            raise _reject("EVIDENCE_IDENTITY", f"source ID mismatch:{row['role']}")
    baseline_spot_rows = [
        row
        for row in source_pinned_baseline.get("leaf_claims", ())
        if isinstance(row, Mapping) and row.get("role") == "spot"
    ]
    if len(baseline_spot_rows) != 1:
        raise _reject("EVIDENCE_BASELINE_BINDING", "baseline spot leaf missing or ambiguous")
    baseline_spot = baseline_spot_rows[0]
    for key in (
        "proof_type",
        "profile",
        "lane_id",
        "image_id",
        "artifact_file_sha256",
        "artifact_size_bytes",
        "receipt_sha256",
    ):
        if leaves[0].get(key) != baseline_spot.get(key):
            raise _reject("EVIDENCE_BASELINE_BINDING", f"baseline spot mismatch:{key}")
    if len({row["lane_id"] for row in leaves}) != 2:
        raise _reject("EVIDENCE_IDENTITY", "accepted lane IDs not distinct")
    if len({row["statement_hash"] for row in leaves}) != 2:
        raise _reject("EVIDENCE_IDENTITY", "accepted statements not distinct")
    if len({row["source_id"] for row in leaves}) != 2:
        raise _reject("EVIDENCE_IDENTITY", "accepted source IDs not distinct")

    pair = _mapping(evidence.get("proof_pair"), "proof_pair")
    _exact_keys(pair, frozenset({"inner", "root", "shared_authenticated_roots"}), "proof_pair")
    inner = _validate_node_row(pair.get("inner"), "proof_pair.inner")
    root = _validate_node_row(pair.get("root"), "proof_pair.root")
    shared = _mapping(pair.get("shared_authenticated_roots"), "shared roots")
    _exact_keys(shared, SHARED_ROOT_KEYS, "shared roots")
    for key in SHARED_ROOT_KEYS:
        _hex(shared.get(key), f"shared roots.{key}")
    if (
        (
            inner["profile"],
            inner["immediate_child_count"],
            inner["flat_leaf_count"],
            inner["tree_height"],
            inner["subtree_node_count"],
        )
        != ("recursive_closed_subtree_v2", 2, 2, 1, 3)
        or (
            root["profile"],
            root["immediate_child_count"],
            root["flat_leaf_count"],
            root["tree_height"],
            root["subtree_node_count"],
        )
        != ("recursive_epoch_root_v2", 1, 2, 2, 4)
    ):
        raise _reject("EVIDENCE_TOPOLOGY", "fixed-height two-leaf topology mismatch")
    if inner["descendant_sources_root"] != shared["descendant_sources_root"] or root[
        "descendant_sources_root"
    ] != shared["descendant_sources_root"]:
        raise _reject("EVIDENCE_IDENTITY", "descendant sources root propagation mismatch")

    scope_hash = shared["aggregation_scope_hash"]
    for row in leaves:
        expected_assigned = derive_assigned_leaf_id(scope_hash, row["lane_id"], row["source_id"])
        if row["assigned_leaf_id"] != expected_assigned:
            raise _reject("EVIDENCE_IDENTITY", f"assigned leaf ID mismatch:{row['role']}")
    verifier_id = derive_child_verifier_id(SPOT_IMAGE_ID, SPOT_PROFILE)
    verifier_root = derive_immediate_verifier_set_root([verifier_id])
    source_root = derive_descendant_sources_root([row["source_id"] for row in leaves])
    assigned_root = derive_assigned_leaf_ids_root([row["assigned_leaf_id"] for row in leaves])
    if inner["immediate_verifier_set_root"] != verifier_root:
        raise _reject("EVIDENCE_IDENTITY", "inner verifier set root mismatch")
    if source_root != shared["descendant_sources_root"]:
        raise _reject("EVIDENCE_IDENTITY", "descendant source root mismatch")
    if assigned_root != shared["assigned_leaf_ids_root"]:
        raise _reject("EVIDENCE_IDENTITY", "assigned leaf root mismatch")

    identity = _mapping(evidence.get("same_profile_identity"), "same_profile_identity")
    _exact_keys(identity, IDENTITY_KEYS, "same_profile_identity")
    expected_identity = {
        "child_count": 2,
        "unique_proof_type_count": 1,
        "unique_profile_count": 1,
        "unique_image_id_count": 1,
        "unique_verifier_id_count": 1,
        "distinct_lane_id_count": 2,
        "distinct_statement_hash_count": 2,
        "distinct_source_id_count": 2,
        "derived_child_verifier_id": verifier_id,
        "inner_immediate_verifier_set_root": verifier_root,
        "inner_descendant_sources_root": source_root,
    }
    if identity != expected_identity:
        raise _reject("EVIDENCE_IDENTITY", "same-profile identity summary mismatch")

    controls = _mapping(evidence.get("negative_controls"), "negative_controls")
    _exact_keys(
        controls,
        frozenset(
            {
                "distinct_leaf_receipt_seal_mutation",
                "duplicate_lane_same_artifact",
                "duplicate_source_lane_alias",
                "swapped_node_levels",
            }
        ),
        "negative_controls",
    )
    duplicate_lane = _validate_result(
        controls.get("duplicate_lane_same_artifact"), "duplicate lane"
    )
    swapped_nodes = _validate_result(controls.get("swapped_node_levels"), "swapped nodes")
    if duplicate_lane["stderr"] != DUPLICATE_LANE_STDERR:
        raise _reject("EVIDENCE_CONTROLS", "duplicate lane reject mismatch")
    if swapped_nodes["stderr"] != SWAPPED_NODES_STDERR:
        raise _reject("EVIDENCE_CONTROLS", "swapped-node reject mismatch")
    alias = _mapping(controls.get("duplicate_source_lane_alias"), "duplicate source alias")
    _exact_keys(
        alias,
        frozenset({"harness_reject", "leaf", "verifier_reject"}),
        "duplicate source alias",
    )
    alias_leaf = _validate_leaf_row(alias.get("leaf"), "duplicate source alias.leaf")
    alias_harness_reject = _validate_result(
        alias.get("harness_reject"), "duplicate source alias.harness_reject"
    )
    alias_verifier_reject = _validate_result(
        alias.get("verifier_reject"), "duplicate source alias.verifier_reject"
    )
    if alias_harness_reject["stderr"] != ALIAS_HARNESS_STDERR:
        raise _reject("EVIDENCE_CONTROLS", "duplicate source harness reject mismatch")
    if alias_verifier_reject["stderr"] != DUPLICATE_SOURCE_STDERR:
        raise _reject("EVIDENCE_CONTROLS", "duplicate source reject mismatch")
    baseline_leaf = leaves[0]
    if (
        alias_leaf["role"] != "spot_lane_alias_control"
        or alias_leaf["proof_type"] != SPOT_PROOF_TYPE
        or alias_leaf["profile"] != SPOT_PROFILE
        or alias_leaf["image_id"] != SPOT_IMAGE_ID
        or alias_leaf["lane_kind"] != SPOT_LANE_KIND
        or alias_leaf["lane_id"] == baseline_leaf["lane_id"]
        or alias_leaf["statement_hash"] != baseline_leaf["statement_hash"]
        or alias_leaf["source_id"] != baseline_leaf["source_id"]
    ):
        raise _reject("EVIDENCE_ALIAS_CONTROL", "lane-alias semantic identity mismatch")
    expected_alias_assigned = derive_assigned_leaf_id(
        scope_hash, alias_leaf["lane_id"], alias_leaf["source_id"]
    )
    if (
        alias_leaf["assigned_leaf_id"] != expected_alias_assigned
        or alias_leaf["assigned_leaf_id"] == baseline_leaf["assigned_leaf_id"]
    ):
        raise _reject("EVIDENCE_ALIAS_CONTROL", "lane-alias assigned identity mismatch")

    mutation = _mapping(
        controls.get("distinct_leaf_receipt_seal_mutation"), "receipt seal mutation"
    )
    _exact_keys(
        mutation,
        frozenset(
            {
                "mutation_kind",
                "seal_word_index",
                "seal_word_mutated",
                "seal_word_original",
                "target_role",
                "verifier_reject",
            }
        ),
        "receipt seal mutation",
    )
    if mutation.get("mutation_kind") != SEAL_MUTATION_KIND or mutation.get(
        "target_role"
    ) != "spot_distinct_statement_variant":
        raise _reject("EVIDENCE_CONTROLS", "seal mutation identity mismatch")
    index = _integer(mutation.get("seal_word_index"), "seal_word_index")
    original = _integer(mutation.get("seal_word_original"), "seal_word_original")
    mutated = _integer(mutation.get("seal_word_mutated"), "seal_word_mutated")
    if index > 1_000_000 or original ^ 1 != mutated:
        raise _reject("EVIDENCE_CONTROLS", "seal mutation must XOR one low bit")
    seal_reject = _validate_result(
        mutation.get("verifier_reject"), "seal mutation.verifier_reject"
    )
    seal_stderr = seal_reject["stderr"]
    if (
        not seal_stderr.startswith(SEAL_REJECT_STDERR_PREFIX)
        or not seal_stderr.endswith("\n")
        or "\x00" in seal_stderr
        or len(seal_stderr.encode("utf-8")) > 1024
    ):
        raise _reject("EVIDENCE_CONTROLS", "seal mutation reject class mismatch")

    verification = _mapping(evidence.get("verification"), "verification")
    expected_verification = {
        "dry_run_order_invariant": True,
        "duplicate_lane_reject_verified": True,
        "duplicate_source_alias_reject_verified": True,
        "producer_verified_generated_receipts_and_exact_journal_bytes": True,
        "receipt_seal_mutation_reject_verified": True,
        "specialized_verifier_order_invariant": True,
        "swapped_node_reject_verified": True,
    }
    if verification != expected_verification:
        raise _reject("EVIDENCE_VERIFICATION", "verification fact mismatch")


def load_evidence() -> Mapping[str, Any]:
    digest = v2._read_regular(EVIDENCE_PATH, label="evidence", max_bytes=MAX_MANIFEST_BYTES)
    if digest.sha256 != EXPECTED_EVIDENCE_FILE_SHA256:
        raise _reject("EVIDENCE_FILE_DIGEST_MISMATCH", digest.sha256)
    evidence = _mapping(v2._parse_json(digest.raw, label="EVIDENCE"), "evidence")
    canonical = _canonical_sha256(evidence)
    if canonical != EXPECTED_EVIDENCE_CANONICAL_SHA256:
        raise _reject("EVIDENCE_CANONICAL_DIGEST_MISMATCH", canonical)
    return evidence


def load_trust_roots() -> tuple[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]]:
    evidence = load_evidence()
    source_pinned_baseline, reference, _ = baseline.load_trust_roots()
    validate_evidence(
        evidence,
        reference,
        source_pinned_baseline,
        reference_file_sha256=baseline.EXPECTED_REFERENCE_FILE_SHA256,
        baseline_file_sha256=baseline.EXPECTED_EVIDENCE_FILE_SHA256,
    )
    return evidence, reference, source_pinned_baseline


def _decode_leaf_artifact(raw: bytes, *, label: str) -> tuple[Mapping[str, Any], bytes, bytes]:
    outer = _mapping(v2._parse_json(raw, label=label), label)
    required = {"meta", "proof", "proof_type", "schema", "schema_version", "state_hash"}
    if set(outer) != required:
        raise _reject("LIVE_LEAF_SCHEMA", f"{label} outer keys mismatch")
    encoded = outer.get("proof")
    if not isinstance(encoded, str) or not encoded:
        raise _reject("LIVE_LEAF_SCHEMA", f"{label}.proof must be base64")
    try:
        receipt_raw = base64.b64decode(encoded.encode("ascii"), validate=True)
    except (UnicodeEncodeError, binascii.Error, ValueError) as exc:
        raise _reject("LIVE_LEAF_SCHEMA", f"{label}.proof base64") from exc
    if base64.b64encode(receipt_raw).decode("ascii") != encoded:
        raise _reject("LIVE_LEAF_SCHEMA", f"{label}.proof base64 noncanonical")
    receipt = _mapping(v2._parse_json(receipt_raw, label=f"{label}_RECEIPT"), f"{label}.receipt")
    journal = _mapping(receipt.get("journal"), f"{label}.receipt.journal")
    journal_values = journal.get("bytes")
    if (
        not isinstance(journal_values, list)
        or not journal_values
        or any(
            not isinstance(value, int)
            or isinstance(value, bool)
            or value < 0
            or value > 255
            for value in journal_values
        )
    ):
        raise _reject("LIVE_LEAF_SCHEMA", f"{label}.receipt journal bytes")
    return outer, receipt_raw, bytes(journal_values)


def _validate_live_leaf(raw: bytes, row: Mapping[str, Any], *, label: str) -> None:
    outer, receipt_raw, journal = _decode_leaf_artifact(raw, label=label)
    meta = _mapping(outer.get("meta"), f"{label}.meta")
    for field, expected in (
        ("proof_type", row["proof_type"]),
        ("proof_profile", row["profile"]),
        ("lane_kind", row["lane_kind"]),
        ("lane_id", row["lane_id"]),
        ("risc0_image_id", row["image_id"]),
        ("statement_hash", row["statement_hash"]),
    ):
        if meta.get(field) != expected:
            raise _reject("LIVE_LEAF_BINDING", f"{label}.meta.{field}")
    if outer.get("proof_type") != row["proof_type"]:
        raise _reject("LIVE_LEAF_BINDING", f"{label}.proof_type")
    if hashlib.sha256(receipt_raw).hexdigest() != row["receipt_sha256"]:
        raise _reject("LIVE_LEAF_BINDING", f"{label}.receipt_sha256")
    if hashlib.sha256(journal).hexdigest() != row["journal_sha256"]:
        raise _reject("LIVE_LEAF_BINDING", f"{label}.journal_sha256")
    journal_hash = hashlib.sha256(
        CHILD_JOURNAL_HASH_DOMAIN + _u32(len(journal)) + journal
    ).hexdigest()
    claim_hash = hashlib.sha256(
        CHILD_CLAIM_HASH_DOMAIN
        + _image_id_words_be(row["image_id"])
        + _u32(len(journal))
        + journal
    ).hexdigest()
    if journal_hash != row["protocol_child_journal_hash"]:
        raise _reject("LIVE_LEAF_BINDING", f"{label}.protocol_child_journal_hash")
    if claim_hash != row["verification_claim_hash"]:
        raise _reject("LIVE_LEAF_BINDING", f"{label}.verification_claim_hash")


def _bytes32_from_json(value: object, label: str) -> str:
    if (
        not isinstance(value, list)
        or len(value) != 32
        or any(
            not isinstance(item, int)
            or isinstance(item, bool)
            or item < 0
            or item > 255
            for item in value
        )
    ):
        raise _reject("LIVE_NODE_SCHEMA", f"{label} must be 32 bytes")
    return bytes(value).hex()


def _validate_live_node(raw: bytes, row: Mapping[str, Any], *, label: str) -> None:
    outer = _mapping(v2._parse_json(raw, label=label), label)
    journal = _mapping(outer.get("journal"), f"{label}.journal")
    for field in (
        "descendant_sources_root",
        "immediate_verifier_set_root",
        "statement_hash",
    ):
        if _bytes32_from_json(journal.get(field), f"{label}.journal.{field}") != row[field]:
            raise _reject("LIVE_NODE_BINDING", f"{label}.{field}")
    for field in (
        "flat_leaf_count",
        "immediate_child_count",
        "subtree_node_count",
        "tree_height",
    ):
        if journal.get(field) != row[field]:
            raise _reject("LIVE_NODE_BINDING", f"{label}.{field}")
    if journal.get("profile") != row["profile"]:
        raise _reject("LIVE_NODE_BINDING", f"{label}.profile")
    for field in ("journal_sha256", "protocol_journal_hash", "receipt_sha256"):
        if outer.get(field) != row[field]:
            raise _reject("LIVE_NODE_BINDING", f"{label}.{field}")


def _expected_verifier_output(evidence: Mapping[str, Any]) -> Mapping[str, Any]:
    leaves = sorted(evidence["leaf_claims"], key=lambda row: row["lane_id"])
    pair = evidence["proof_pair"]
    return {
        "aggregate_v2_image_id": evidence["aggregate_v2"]["image_id"],
        "inner_receipt_sha256": pair["inner"]["receipt_sha256"],
        "leaf_receipt_sha256s": [row["receipt_sha256"] for row in leaves],
        "ok": True,
        "root_receipt_sha256": pair["root"]["receipt_sha256"],
        "status": VERIFIER_STATUS,
    }


def _validate_dry_run(report: Mapping[str, Any], evidence: Mapping[str, Any]) -> None:
    leaves = sorted(evidence["leaf_claims"], key=lambda row: row["lane_id"])
    pair = evidence["proof_pair"]
    if (
        report.get("ok") is not True
        or report.get("dry_run") is not True
        or report.get("aggregate_v2_image_id") != evidence["aggregate_v2"]["image_id"]
        or report.get("input_leaf_count") != 2
        or report.get("input_leaf_receipt_sha256s")
        != [row["receipt_sha256"] for row in leaves]
    ):
        raise _reject("LIVE_DRY_RUN", "header mismatch")
    shared = pair["shared_authenticated_roots"]
    for role, output_name in (("inner", "inner"), ("root", "epoch_root")):
        observed = _mapping(report.get(output_name), f"dry-run {output_name}")
        expected = pair[role]
        for key in (
            "journal_sha256",
            "protocol_journal_hash",
            "profile",
            "statement_hash",
            "immediate_child_count",
            "flat_leaf_count",
            "tree_height",
            "subtree_node_count",
        ):
            if observed.get(key) != expected[key]:
                raise _reject("LIVE_DRY_RUN", f"{role}:{key}")
        for key in (
            "aggregation_scope_hash",
            "assigned_leaf_ids_root",
            "descendant_claims_root",
            "flat_v1_post_state_root",
            "flat_v1_statement_hash",
            "leaf_disclosures_root",
        ):
            if observed.get(key) != shared[key]:
                raise _reject("LIVE_DRY_RUN", f"{role}:{key}")


def _expect_reject(
    result: Any,
    policy: Mapping[str, Any],
    *,
    label: str,
) -> None:
    expected_stderr = policy["stderr"].encode("utf-8")
    if (
        result.returncode != policy["exit_code"]
        or result.stdout
        or result.stderr != expected_stderr
        or hashlib.sha256(result.stderr).hexdigest() != policy["stderr_sha256"]
    ):
        raise _reject("LIVE_NEGATIVE_CONTROL", label)


def _mutate_succinct_seal_word(raw: bytes, mutation: Mapping[str, Any]) -> bytes:
    outer, _, _ = _decode_leaf_artifact(raw, label="MUTATION_SOURCE")
    encoded = outer["proof"]
    receipt_raw = base64.b64decode(encoded.encode("ascii"), validate=True)
    receipt = _mapping(v2._parse_json(receipt_raw, label="MUTATION_RECEIPT"), "receipt")
    inner = _mapping(receipt.get("inner"), "receipt.inner")
    succinct = _mapping(inner.get("Succinct"), "receipt.inner.Succinct")
    seal = succinct.get("seal")
    index = mutation["seal_word_index"]
    if not isinstance(seal, list) or index >= len(seal):
        raise _reject("LIVE_SEAL_MUTATION", "seal word index out of range")
    if seal[index] != mutation["seal_word_original"]:
        raise _reject("LIVE_SEAL_MUTATION", "seal word original mismatch")
    seal[index] = mutation["seal_word_mutated"]
    mutated_receipt = json.dumps(
        receipt, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    mutated_outer = dict(outer)
    mutated_outer["proof"] = base64.b64encode(mutated_receipt).decode("ascii")
    return json.dumps(mutated_outer, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _write_private_staged_file(
    directory: Path,
    *,
    filename: str,
    raw: bytes,
    executable: bool,
) -> Path:
    if not filename or Path(filename).name != filename:
        raise _reject("LIVE_STAGING", "invalid staged filename")
    root = v2._canonical_path(directory, label="staging directory", directory=True)
    if root.stat(follow_symlinks=False).st_mode & 0o777 != 0o700:
        raise _reject("LIVE_STAGING", "staging directory mode must be 0700")
    destination = root / filename
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if not isinstance(nofollow, int):
        raise _reject("PLATFORM_UNSUPPORTED", "O_NOFOLLOW")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0) | nofollow
    mode = 0o700 if executable else 0o600
    try:
        descriptor = os.open(destination, flags, mode)
    except OSError as exc:
        raise _reject("LIVE_STAGING", filename) from exc
    try:
        os.fchmod(descriptor, mode)
        remaining = memoryview(raw)
        while remaining:
            written = os.write(descriptor, remaining)
            if written <= 0:
                raise _reject("LIVE_STAGING", f"short write:{filename}")
            remaining = remaining[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    return destination


def _stage_verified_file(
    directory: Path,
    *,
    filename: str,
    digest: FileDigest,
    executable: bool,
    max_bytes: int,
) -> Path:
    destination = _write_private_staged_file(
        directory,
        filename=filename,
        raw=digest.raw,
        executable=executable,
    )
    staged = baseline._verify_file(
        destination,
        label=f"staged {filename}",
        expected_sha256=digest.sha256,
        expected_size=digest.size_bytes,
        max_bytes=max_bytes,
        executable=executable,
    )
    expected_mode = 0o700 if executable else 0o600
    if (
        staged != digest
        or destination.stat(follow_symlinks=False).st_mode & 0o777 != expected_mode
    ):
        raise _reject("LIVE_STAGING", f"staged file drift:{filename}")
    return destination


def _clean_execution_env(staging_directory: Path) -> dict[str, str]:
    root = v2._canonical_path(
        staging_directory, label="staging directory", directory=True
    )
    if root.stat(follow_symlinks=False).st_mode & 0o777 != 0o700:
        raise _reject("LIVE_STAGING", "staging directory mode must be 0700")
    home = root / "home"
    try:
        os.mkdir(home, mode=0o700)
        os.chmod(home, 0o700)
    except OSError as exc:
        raise _reject("LIVE_STAGING", "create private HOME") from exc
    private_home = v2._canonical_path(home, label="private HOME", directory=True)
    if private_home.stat(follow_symlinks=False).st_mode & 0o777 != 0o700:
        raise _reject("LIVE_STAGING", "private HOME mode must be 0700")
    if any(private_home.iterdir()):
        raise _reject("LIVE_STAGING", "private HOME must start empty")
    return {
        "HOME": str(private_home),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "RISC0_DEV_MODE": "0",
        "TZ": "UTC",
    }


def _check_staged(
    *,
    evidence: Mapping[str, Any],
    source_pinned_baseline: Mapping[str, Any],
    digests: Mapping[str, FileDigest],
    staged: Mapping[str, Path],
    staging_directory: Path,
) -> dict[str, Any]:
    leaves = evidence["leaf_claims"]
    pair = evidence["proof_pair"]
    controls = evidence["negative_controls"]
    alias_row = controls["duplicate_source_lane_alias"]["leaf"]

    _validate_live_leaf(digests["baseline spot leaf"].raw, leaves[0], label="BASELINE_LEAF")
    _validate_live_leaf(digests["distinct spot leaf"].raw, leaves[1], label="DISTINCT_LEAF")
    _validate_live_leaf(
        digests["duplicate-source alias leaf"].raw,
        alias_row,
        label="ALIAS_LEAF",
    )
    _validate_live_node(digests["inner artifact"].raw, pair["inner"], label="INNER")
    _validate_live_node(digests["root artifact"].raw, pair["root"], label="ROOT")

    clean_env = _clean_execution_env(staging_directory)
    harness = str(staged["release harness"])
    verifier = str(staged["two-leaf verifier"])
    first = str(staged["baseline spot leaf"])
    second = str(staged["distinct spot leaf"])
    alias = str(staged["duplicate-source alias leaf"])
    inner = str(staged["inner artifact"])
    root = str(staged["root artifact"])

    dry_forward = baseline._stdout_json(
        baseline._run([harness, first, second, "--dry-run"], env=clean_env),
        label="SAME_PROFILE_DRY_FORWARD",
    )
    dry_reverse = baseline._stdout_json(
        baseline._run([harness, second, first, "--dry-run"], env=clean_env),
        label="SAME_PROFILE_DRY_REVERSE",
    )
    _validate_dry_run(dry_forward, evidence)
    _validate_dry_run(dry_reverse, evidence)
    if dry_forward != dry_reverse:
        raise _reject("LIVE_ORDER_INVARIANCE", "dry-run output mismatch")

    expected_verifier = _expected_verifier_output(evidence)
    verify_forward = baseline._stdout_json(
        baseline._run([verifier, first, second, inner, root], env=clean_env),
        label="SAME_PROFILE_VERIFY_FORWARD",
    )
    verify_reverse = baseline._stdout_json(
        baseline._run([verifier, second, first, inner, root], env=clean_env),
        label="SAME_PROFILE_VERIFY_REVERSE",
    )
    if verify_forward != expected_verifier or verify_reverse != expected_verifier:
        raise _reject("LIVE_TWO_LEAF_VERIFIER", "same-profile verifier output mismatch")

    _expect_reject(
        baseline._run([verifier, first, first, inner, root], env=clean_env),
        controls["duplicate_lane_same_artifact"],
        label="duplicate lane",
    )
    alias_control = controls["duplicate_source_lane_alias"]
    _expect_reject(
        baseline._run([harness, first, alias, "--dry-run"], env=clean_env),
        alias_control["harness_reject"],
        label="duplicate-source harness",
    )
    _expect_reject(
        baseline._run([verifier, first, alias, inner, root], env=clean_env),
        alias_control["verifier_reject"],
        label="duplicate-source verifier",
    )
    _expect_reject(
        baseline._run([verifier, first, second, root, inner], env=clean_env),
        controls["swapped_node_levels"],
        label="swapped nodes",
    )

    mutation = controls["distinct_leaf_receipt_seal_mutation"]
    mutated_raw = _mutate_succinct_seal_word(digests["distinct spot leaf"].raw, mutation)
    mutated_path = _write_private_staged_file(
        staging_directory,
        filename="mutated-leaf.json",
        raw=mutated_raw,
        executable=False,
    )
    mutated_digest = v2._read_regular(
        mutated_path, label="staged mutated leaf", max_bytes=MAX_LEAF_BYTES
    )
    if (
        mutated_digest.raw != mutated_raw
        or mutated_path.stat(follow_symlinks=False).st_mode & 0o777 != 0o600
    ):
        raise _reject("LIVE_STAGING", "mutated leaf staging mismatch")
    _expect_reject(
        baseline._run([verifier, first, str(mutated_path), inner, root], env=clean_env),
        mutation["verifier_reject"],
        label="receipt seal mutation",
    )

    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": ACCEPTED_STATUS,
        "evidence_file_sha256": EXPECTED_EVIDENCE_FILE_SHA256,
        "aggregate_v2_image_id": evidence["aggregate_v2"]["image_id"],
        "source_root_sha256": source_pinned_baseline["source_frozen_build"][
            "source_closure"
        ]["root_sha256"],
        "leaf_receipt_sha256s": expected_verifier["leaf_receipt_sha256s"],
        "inner_receipt_sha256": expected_verifier["inner_receipt_sha256"],
        "root_receipt_sha256": expected_verifier["root_receipt_sha256"],
        "unique_leaf_verifier_id_count": 1,
        "distinct_semantic_source_id_count": 2,
        "private_staging_verified": True,
        "dry_run_order_invariant": True,
        "specialized_verifier_order_invariant": True,
        "duplicate_lane_reject_verified": True,
        "duplicate_source_alias_reject_verified": True,
        "receipt_seal_mutation_reject_verified": True,
        "swapped_node_reject_verified": True,
        "general_multi_leaf_profile_promoted": False,
        "cross_environment_reproducibility": False,
        "public_replay_available": False,
        "release_authority": False,
        "throughput_claim_allowed": False,
        "public_claim_allowed": False,
        "production_ready": False,
        "settlement_authorization": False,
        "privacy": False,
    }


def check_live(
    *,
    baseline_spot_leaf: Path,
    distinct_spot_leaf: Path,
    duplicate_source_alias_leaf: Path,
    inner_artifact: Path,
    root_artifact: Path,
    release_harness: Path,
    two_leaf_verifier: Path,
) -> dict[str, Any]:
    evidence, _reference, source_pinned_baseline = load_trust_roots()
    leaves = evidence["leaf_claims"]
    pair = evidence["proof_pair"]
    controls = evidence["negative_controls"]
    alias_row = controls["duplicate_source_lane_alias"]["leaf"]

    live_files = (
        (
            baseline_spot_leaf,
            leaves[0]["artifact_file_sha256"],
            leaves[0]["artifact_size_bytes"],
            "baseline spot leaf",
            MAX_LEAF_BYTES,
            False,
        ),
        (
            distinct_spot_leaf,
            leaves[1]["artifact_file_sha256"],
            leaves[1]["artifact_size_bytes"],
            "distinct spot leaf",
            MAX_LEAF_BYTES,
            False,
        ),
        (
            duplicate_source_alias_leaf,
            alias_row["artifact_file_sha256"],
            alias_row["artifact_size_bytes"],
            "duplicate-source alias leaf",
            MAX_LEAF_BYTES,
            False,
        ),
        (
            inner_artifact,
            pair["inner"]["artifact_file_sha256"],
            pair["inner"]["artifact_size_bytes"],
            "inner artifact",
            MAX_NODE_BYTES,
            False,
        ),
        (
            root_artifact,
            pair["root"]["artifact_file_sha256"],
            pair["root"]["artifact_size_bytes"],
            "root artifact",
            MAX_NODE_BYTES,
            False,
        ),
        (
            release_harness,
            source_pinned_baseline["source_frozen_build"]["release_harness_binary"]["sha256"],
            source_pinned_baseline["source_frozen_build"]["release_harness_binary"][
                "size_bytes"
            ],
            "release harness",
            MAX_EXECUTABLE_BYTES,
            True,
        ),
        (
            two_leaf_verifier,
            evidence["specialized_host_verifier"]["binary_sha256"],
            evidence["specialized_host_verifier"]["binary_size_bytes"],
            "two-leaf verifier",
            MAX_EXECUTABLE_BYTES,
            True,
        ),
    )
    digests: dict[str, FileDigest] = {}
    for path, expected_sha256, expected_size, label, limit, executable in live_files:
        digest = baseline._verify_file(
            path,
            label=label,
            expected_sha256=expected_sha256,
            expected_size=expected_size,
            max_bytes=limit,
            executable=executable,
        )
        digests[label] = digest

    staged_specs = {
        "baseline spot leaf": ("baseline-spot-leaf.json", False, MAX_LEAF_BYTES),
        "distinct spot leaf": ("distinct-spot-leaf.json", False, MAX_LEAF_BYTES),
        "duplicate-source alias leaf": ("alias-spot-leaf.json", False, MAX_LEAF_BYTES),
        "inner artifact": ("inner-artifact.json", False, MAX_NODE_BYTES),
        "root artifact": ("root-artifact.json", False, MAX_NODE_BYTES),
        "release harness": ("recursive-v2-harness", True, MAX_EXECUTABLE_BYTES),
        "two-leaf verifier": ("two-leaf-verifier", True, MAX_EXECUTABLE_BYTES),
    }
    with tempfile.TemporaryDirectory(prefix="zenodex-same-profile-stage-") as temporary:
        staging_directory = Path(temporary)
        os.chmod(staging_directory, 0o700)
        staged = {
            label: _stage_verified_file(
                staging_directory,
                filename=filename,
                digest=digests[label],
                executable=executable,
                max_bytes=max_bytes,
            )
            for label, (filename, executable, max_bytes) in staged_specs.items()
        }
        return _check_staged(
            evidence=evidence,
            source_pinned_baseline=source_pinned_baseline,
            digests=digests,
            staged=staged,
            staging_directory=staging_directory,
        )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-spot-leaf", type=Path, required=True)
    parser.add_argument("--distinct-spot-leaf", type=Path, required=True)
    parser.add_argument("--duplicate-source-alias-leaf", type=Path, required=True)
    parser.add_argument("--inner-artifact", type=Path, required=True)
    parser.add_argument("--root-artifact", type=Path, required=True)
    parser.add_argument("--release-harness", type=Path, required=True)
    parser.add_argument("--two-leaf-verifier", type=Path, required=True)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        report = check_live(
            baseline_spot_leaf=args.baseline_spot_leaf,
            distinct_spot_leaf=args.distinct_spot_leaf,
            duplicate_source_alias_leaf=args.duplicate_source_alias_leaf,
            inner_artifact=args.inner_artifact,
            root_artifact=args.root_artifact,
            release_harness=args.release_harness,
            two_leaf_verifier=args.two_leaf_verifier,
        )
    except v2.EvidenceError as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "error_code": exc.code,
            "error": exc.detail,
            "public_claim_allowed": False,
            "production_ready": False,
        }
        if args.json:
            print(json.dumps(report, sort_keys=True, separators=(",", ":")))
        else:
            print(f"same-profile evidence rejected: {exc}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print(f"same-profile evidence: {report['status']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
