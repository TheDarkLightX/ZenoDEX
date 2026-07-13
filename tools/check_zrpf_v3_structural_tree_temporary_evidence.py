#!/usr/bin/env python3
"""Check the path-redacted temporary ZRPF V3 structural-tree evidence.

The Rust RISC0 verifier-only harness is the authority for receipt seals, image
IDs, and exact recomposed journals. This Python checker validates a reviewed
manifest, repository source closures, and optional opaque receipt/transcript
bytes. It deliberately has no cryptographic receipt-verification authority.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

if __package__:
    from tools import zrpf_v3_structural_tree_evidence_support as support
else:
    import zrpf_v3_structural_tree_evidence_support as support  # type: ignore[no-redef]


REPO_ROOT = support.REPO_ROOT
DEFAULT_MANIFEST = support.DEFAULT_MANIFEST
REPORT_SCHEMA = support.REPORT_SCHEMA
EXPECTED_SCHEMA = support.EXPECTED_SCHEMA
MAX_MANIFEST_BYTES = support.MAX_MANIFEST_BYTES

EXPECTED_PROGRAMS = {
    "v1_leaf_adapter": {
        "image_id": "71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574",
        "elf_sha256": "545c832d0dbe54ed2379f7fa423e490177cf4e3475c208ce5edf2d6bd4cb9797",
        "elf_size_bytes": 255660,
    },
    "structural_l1": {
        "image_id": "4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b",
        "elf_sha256": "cfd04b048cbe51536161dde09a02fb7b56a1de2b43fcc2b4e00ee4dc9ac7980f",
        "elf_size_bytes": 343544,
    },
    "structural_l2": {
        "image_id": "3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736",
        "elf_sha256": "5912e984b89fc244ec450d3d7ff49f555b090de6502ae328c272fe6e02460a1f",
        "elf_size_bytes": 342576,
    },
}

EXPECTED_NODES: dict[str, dict[str, Any]] = {
    "leaf-0": {
        "role": "leaf",
        "parent_id": "l1-left",
        "child_ids": [],
        "artifact_path": "adapter-leaf-0.receipt.json",
        "program_role": "v1_leaf_adapter",
        "receipt_sha256": "cc65e529bd881b331531aa615298e46471e31a36d3b8d57af2290031969dda61",
        "receipt_size_bytes": 593505,
        "journal_protocol_hash": "d81782dbf7c324b7c7f08d7c3e7da3a4116be9a809f6e8da17c7c789da273e22",
        "journal_sha256": "4333dc78ca7db8d78a503f619a752d6c0b50d5a362ece524d9b6939af1c720d1",
        "topology": (0, 0, 1, 1, 1, 0, 1),
    },
    "leaf-1": {
        "role": "leaf",
        "parent_id": "l1-left",
        "child_ids": [],
        "artifact_path": "adapter-leaf-1.receipt.json",
        "program_role": "v1_leaf_adapter",
        "receipt_sha256": "a610ed093ae4da1a60e5fd4b955a3b3013d8b9410e3d801e70dada81d903fdd3",
        "receipt_size_bytes": 593322,
        "journal_protocol_hash": "b00e05948cb68a689f4b2ab21f0782036e9659059c92d300b962d3e128bca626",
        "journal_sha256": "df382cb13d0130e9087eed660918c48a56d5ed67ba80aeb276940d49e743244d",
        "topology": (0, 0, 1, 1, 1, 1, 2),
    },
    "leaf-2": {
        "role": "leaf",
        "parent_id": "l1-right",
        "child_ids": [],
        "artifact_path": "adapter-leaf-2.receipt.json",
        "program_role": "v1_leaf_adapter",
        "receipt_sha256": "056ff6fd6557dd42547487c7610697b045402e45bb57726d98c7c99759ecd5bc",
        "receipt_size_bytes": 593263,
        "journal_protocol_hash": "0629323d94feb82120b564aebf1a2f4020a463ac1826666b860eecfe203b188a",
        "journal_sha256": "f9b2f88c56a05405ca469e1fefc1e853acad33c32eaecad5ce317fcfc8666a9e",
        "topology": (0, 0, 1, 1, 1, 2, 3),
    },
    "leaf-3": {
        "role": "leaf",
        "parent_id": "l1-right",
        "child_ids": [],
        "artifact_path": "adapter-leaf-3.receipt.json",
        "program_role": "v1_leaf_adapter",
        "receipt_sha256": "a99509e5664a9cd089b5c95c0c93adf35a85df2dd7c934cf6df012d0e3397db7",
        "receipt_size_bytes": 593126,
        "journal_protocol_hash": "f4e8c1824dc6cd763b9b61dc40d99a2e0015b3a4dbdec220a95aaccbd8fa7410",
        "journal_sha256": "dbd3dfc0cae288de3f24cf83e3b533e97a495f3d16eb7131e338b1df77640e4e",
        "topology": (0, 0, 1, 1, 1, 3, 4),
    },
    "l1-left": {
        "role": "aggregate",
        "parent_id": "l2-root",
        "child_ids": ["leaf-0", "leaf-1"],
        "artifact_path": "structural-tree/structural-l1-left.receipt.json",
        "program_role": "structural_l1",
        "receipt_sha256": "78977e2e2d75e63811b7d7e2f30987bbe76fde4764e1aef423bbd8ffa30f32ba",
        "receipt_size_bytes": 593131,
        "journal_protocol_hash": "6546b9e8fcc884d865f1a3892ef04ec77c6689e2e9c7310c5fdd83355df44a4e",
        "journal_sha256": "e876b967a4ba61a7c49ebc2bc1fa0af900b6b7eaee0b0ce048a20789ad5121fb",
        "topology": (1, 2, 2, 2, 3, 0, 2),
    },
    "l1-right": {
        "role": "aggregate",
        "parent_id": "l2-root",
        "child_ids": ["leaf-2", "leaf-3"],
        "artifact_path": "structural-tree/structural-l1-right.receipt.json",
        "program_role": "structural_l1",
        "receipt_sha256": "085b3095271061f4baa57c7a5ca79c6ffefb87206840df1e7158730b7520eedb",
        "receipt_size_bytes": 593429,
        "journal_protocol_hash": "fdfdac79c3278eb3ba7143bd5c31ff15739640fdebbfc2f3e505f52947c531bf",
        "journal_sha256": "538330fd18d5c5313f8279ca46bb92c62972acfdd6eaa3100e5d9c4ee66613cb",
        "topology": (1, 2, 2, 2, 3, 2, 4),
    },
    "l2-root": {
        "role": "aggregate",
        "parent_id": None,
        "child_ids": ["l1-left", "l1-right"],
        "artifact_path": "structural-tree/structural-l2-root.receipt.json",
        "program_role": "structural_l2",
        "receipt_sha256": "021af13025e7dc7c40e06d689ad30e3194e58793435cd11ae07d684c80ddfd33",
        "receipt_size_bytes": 593096,
        "journal_protocol_hash": "2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768",
        "journal_sha256": "da94385eb3d1f6cfd9ca8b440371e34ebf59882f0b13dc2d748c01bb76f81290",
        "topology": (2, 2, 4, 4, 7, 0, 4),
    },
}

EXPECTED_NODE_ORDER = [
    "leaf-0",
    "leaf-1",
    "leaf-2",
    "leaf-3",
    "l1-left",
    "l1-right",
    "l2-root",
]

EXPECTED_CLAIMS = {
    "rust_risc0_verifier_replay_verified_every_receipt": True,
    "temporary_local_structural_tree_computational_integrity": True,
    "structural_child_commitments_aggregated": True,
    "proof_generation_source_closure_attested": False,
    "release_backed": False,
    "public_replay": False,
    "full_zenodex_semantic_composition": False,
    "data_availability_or_carry_semantics": False,
    "asset_conservation_or_value_flow": False,
    "ledger_or_settlement_admission_authority": False,
    "production_authority": False,
    "zero_knowledge_or_witness_privacy": False,
}

EXPECTED_NON_CLAIMS = [
    "no_proof_generation_source_closure_attestation",
    "no_release_or_cross_host_reproducibility_claim",
    "no_public_replay_claim",
    "no_full_zenodex_semantic_composition_claim",
    "no_data_availability_or_carry_semantics_claim",
    "no_asset_conservation_or_value_flow_claim",
    "no_zenoledger_or_settlement_admission_claim",
    "no_production_authority_claim",
    "no_zero_knowledge_or_witness_privacy_claim",
    "no_receipt_byte_determinism_claim",
]

ROOT_FIELDS = {
    "schema",
    "version",
    "evidence_date",
    "scope",
    "status",
    "sanitization",
    "build_scope",
    "toolchain",
    "tree_profile",
    "programs",
    "nodes",
    "receipt_verification",
    "negative_controls",
    "prover_execution",
    "verifier_replay",
    "guest_build_sources",
    "verification_sources",
    "claims",
    "non_claims",
}


class EvidenceInputError(ValueError):
    """Manifest JSON is ambiguous or outside the accepted grammar."""


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise EvidenceInputError(f"non-finite JSON number: {value}")


def load_manifest(path: Path = DEFAULT_MANIFEST) -> tuple[Any | None, list[str]]:
    try:
        raw = path.read_bytes()
    except OSError:
        return None, ["manifest read failed"]
    if not raw or len(raw) > MAX_MANIFEST_BYTES:
        return None, ["manifest byte length is empty or exceeds the cap"]
    try:
        document = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        EvidenceInputError,
        RecursionError,
    ) as exc:
        return None, [f"manifest JSON rejected: {exc}"]
    return document, []


def validate_manifest(document: Any, *, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(document, dict):
        return _report(["manifest root must be an object"], 0, "")
    canonical_sha256 = support.canonical_sha256(document)
    if not support.EXPECTED_MANIFEST_CANONICAL_SHA256:
        errors.append("reviewed manifest SHA-256 is not configured")
    elif canonical_sha256 != support.EXPECTED_MANIFEST_CANONICAL_SHA256:
        errors.append("manifest canonical SHA-256 differs from the reviewed record")
    _validate_shapes(document, errors)
    _validate_header(document, errors)
    _validate_programs(document.get("programs"), errors)
    nodes = _validate_nodes(document.get("nodes"), errors)
    _validate_tree(nodes, errors)
    _validate_verification_boundary(document, errors)
    support.validate_redaction(document, errors)
    source_count = support.validate_source_closure(
        document.get("guest_build_sources"), repo_root, errors
    )
    source_count += support.validate_source_closure(
        document.get("verification_sources"), repo_root, errors
    )
    return _report(errors, source_count, canonical_sha256)


def _report(errors: list[str], source_count: int, canonical_sha256: str) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "facts": {
            "manifest_canonical_sha256": canonical_sha256,
            "source_files_checked": source_count,
            "python_verifies_risc0_seal": False,
            "receipt_nodes_declared": len(EXPECTED_NODES),
            "evidence_ready": not errors,
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


def _validate_shapes(document: dict[str, Any], errors: list[str]) -> None:
    _require_exact_fields(document, ROOT_FIELDS, "manifest", errors)
    _require_exact_fields(
        document.get("sanitization"),
        {"absolute_paths_included", "private_project_names_included", "public_safe_record"},
        "sanitization",
        errors,
    )
    _require_exact_fields(
        document.get("build_scope"),
        {
            "compiler_visible_path_stable",
            "cross_host_reproduced",
            "release_authority",
        },
        "build_scope",
        errors,
    )
    _require_exact_fields(
        document.get("toolchain"),
        {
            "risc0_zkvm_version",
            "rustc_version",
            "rustc_commit",
            "cargo_version",
            "cargo_commit",
        },
        "toolchain",
        errors,
    )
    _require_exact_fields(
        document.get("tree_profile"),
        {
            "journal_schema",
            "aggregate_profile",
            "count_unit",
            "receipt_kind",
            "fanout_limit",
            "depth_limit",
            "observed_leaf_count",
            "observed_node_count",
        },
        "tree_profile",
        errors,
    )
    programs = document.get("programs")
    if not isinstance(programs, list) or len(programs) != 3:
        errors.append("programs must contain exactly three rows")
    else:
        for index, row in enumerate(programs):
            _require_exact_fields(
                row, {"role", "image_id", "image_id_words", "elf"}, f"programs[{index}]", errors
            )
            if isinstance(row, dict):
                _require_exact_fields(
                    row.get("elf"), {"sha256", "size_bytes"}, f"programs[{index}].elf", errors
                )
    nodes = document.get("nodes")
    if not isinstance(nodes, list) or len(nodes) != 7:
        errors.append("nodes must contain exactly seven rows")
    else:
        for index, row in enumerate(nodes):
            _require_exact_fields(
                row,
                {
                    "id",
                    "role",
                    "parent_id",
                    "child_ids",
                    "artifact_path",
                    "program_role",
                    "receipt",
                    "journal",
                    "topology",
                },
                f"nodes[{index}]",
                errors,
            )
            if isinstance(row, dict):
                _require_exact_fields(
                    row.get("receipt"), {"kind", "sha256", "size_bytes"}, f"nodes[{index}].receipt", errors
                )
                _require_exact_fields(
                    row.get("journal"),
                    {"protocol_hash", "sha256", "size_bytes"},
                    f"nodes[{index}].journal",
                    errors,
                )
                _require_exact_fields(
                    row.get("topology"),
                    {
                        "level",
                        "child_count",
                        "leaf_count",
                        "operation_count",
                        "subtree_node_count",
                        "partition_start",
                        "partition_end",
                    },
                    f"nodes[{index}].topology",
                    errors,
                )
    _validate_boundary_shapes(document, errors)
    for closure_name in ("guest_build_sources", "verification_sources"):
        closure = document.get(closure_name)
        _require_exact_fields(
            closure,
            {"scope", "finalized", "definition", "file_count", "sha256", "files"},
            closure_name,
            errors,
        )
        files = closure.get("files") if isinstance(closure, dict) else None
        if not isinstance(files, list):
            errors.append(f"{closure_name}.files must be a list")
        else:
            for index, row in enumerate(files):
                _require_exact_fields(
                    row, {"role", "path", "sha256"}, f"{closure_name}.files[{index}]", errors
                )


def _validate_boundary_shapes(document: dict[str, Any], errors: list[str]) -> None:
    _require_exact_fields(
        document.get("receipt_verification"),
        {
            "performed_by",
            "verifier_source_path",
            "risc0_zkvm_version",
            "all_receipts_seal_verified",
            "all_expected_image_ids_verified",
            "exact_aggregate_journals_recomposed",
            "python_checker_verifies_seal",
            "python_checker_scope",
        },
        "receipt_verification",
        errors,
    )
    controls = document.get("negative_controls")
    if not isinstance(controls, list) or len(controls) != 3:
        errors.append("negative_controls must contain exactly three rows")
    else:
        for index, control in enumerate(controls):
            _require_exact_fields(
                control,
                {"id", "passed", "expected_program_role", "status", "transcript"},
                f"negative_controls[{index}]",
                errors,
            )
            if isinstance(control, dict):
                _require_exact_fields(
                    control.get("transcript"),
                    {"artifact_path", "sha256", "size_bytes"},
                    f"negative_controls[{index}].transcript",
                    errors,
                )
    _require_exact_fields(
        document.get("prover_execution"),
        {
            "performed_by",
            "receipt_generation_completed",
            "executed_harness_source_closure_attested",
            "current_source_matches_executed",
            "source_drift_reason",
            "executed_binary_sha256",
            "executed_binary_size_bytes",
        },
        "prover_execution",
        errors,
    )
    _require_exact_fields(
        document.get("verifier_replay"),
        {
            "status",
            "current_source_closure_attested",
            "executed_binary_sha256",
            "executed_binary_size_bytes",
            "transcript",
        },
        "verifier_replay",
        errors,
    )
    replay = document.get("verifier_replay")
    if isinstance(replay, dict):
        _require_exact_fields(
            replay.get("transcript"),
            {"artifact_path", "sha256", "size_bytes"},
            "verifier_replay.transcript",
            errors,
        )


def _validate_header(document: dict[str, Any], errors: list[str]) -> None:
    if document.get("schema") != EXPECTED_SCHEMA:
        errors.append("manifest schema mismatch")
    if type(document.get("version")) is not int or document.get("version") != 1:
        errors.append("manifest version mismatch")
    if document.get("scope") != "four_leaf_two_level_zrpf_v3_structural_tree":
        errors.append("manifest scope mismatch")
    if document.get("status") != "temporary_local_structural_tree_receipt_evidence":
        errors.append("manifest status mismatch")
    if document.get("sanitization") != {
        "absolute_paths_included": False,
        "private_project_names_included": False,
        "public_safe_record": True,
    }:
        errors.append("sanitization assertions mismatch")
    if document.get("build_scope") != {
        "compiler_visible_path_stable": False,
        "cross_host_reproduced": False,
        "release_authority": False,
    }:
        errors.append("temporary build scope mismatch")
    if document.get("tree_profile") != {
        "journal_schema": "zenodex.zrpf.node_journal.v3",
        "aggregate_profile": "zrpf_v3_structural_aggregate_v1",
        "count_unit": "source_transition_receipt",
        "receipt_kind": "succinct",
        "fanout_limit": 8,
        "depth_limit": 2,
        "observed_leaf_count": 4,
        "observed_node_count": 7,
    }:
        errors.append("tree profile facts mismatch")


def _validate_programs(programs: Any, errors: list[str]) -> None:
    if not isinstance(programs, list):
        return
    roles = [row.get("role") if isinstance(row, dict) else None for row in programs]
    if roles != list(EXPECTED_PROGRAMS):
        errors.append("program roles or order mismatch")
    for row in programs:
        if not isinstance(row, dict):
            continue
        role = row.get("role")
        if not isinstance(role, str):
            errors.append("program role must be a string")
            continue
        expected = EXPECTED_PROGRAMS.get(role)
        if expected is None:
            continue
        image_id = row.get("image_id")
        words = row.get("image_id_words")
        elf = row.get("elf")
        if image_id != expected["image_id"]:
            errors.append(f"program image ID mismatch: {role}")
        if (
            not isinstance(words, list)
            or len(words) != 8
            or any(type(word) is not int or word < 0 or word > 0xFFFFFFFF for word in words)
        ):
            errors.append(f"program image words are invalid: {role}")
        elif b"".join(word.to_bytes(4, "little") for word in words).hex() != image_id:
            errors.append(f"program image words do not encode image ID: {role}")
        if not isinstance(elf, dict) or elf != {
            "sha256": expected["elf_sha256"],
            "size_bytes": expected["elf_size_bytes"],
        }:
            errors.append(f"program ELF facts mismatch: {role}")


def _validate_nodes(nodes: Any, errors: list[str]) -> dict[str, dict[str, Any]]:
    if not isinstance(nodes, list):
        return {}
    ids = [row.get("id") if isinstance(row, dict) else None for row in nodes]
    if ids != EXPECTED_NODE_ORDER:
        errors.append("node IDs or order mismatch")
    if any(not isinstance(node_id, str) for node_id in ids):
        errors.append("node IDs must be strings")
    elif len(ids) != len(set(ids)):
        errors.append("node IDs must be unique")
    indexed: dict[str, dict[str, Any]] = {}
    for row in nodes:
        if not isinstance(row, dict) or not isinstance(row.get("id"), str):
            continue
        node_id = row["id"]
        indexed[node_id] = row
        expected = EXPECTED_NODES.get(node_id)
        if expected is not None:
            _validate_node_against_expected(row, expected, errors)
    return indexed


def _validate_node_against_expected(
    row: dict[str, Any],
    expected: dict[str, Any],
    errors: list[str],
) -> None:
    node_id = row.get("id")
    for field in ("role", "parent_id", "child_ids", "artifact_path", "program_role"):
        if row.get(field) != expected[field]:
            errors.append(f"node {field} mismatch: {node_id}")
    receipt = row.get("receipt")
    if not isinstance(receipt, dict) or receipt != {
        "kind": "succinct",
        "sha256": expected["receipt_sha256"],
        "size_bytes": expected["receipt_size_bytes"],
    }:
        errors.append(f"node receipt facts mismatch: {node_id}")
    journal = row.get("journal")
    if not isinstance(journal, dict) or journal != {
        "protocol_hash": expected["journal_protocol_hash"],
        "sha256": expected["journal_sha256"],
        "size_bytes": 1547,
    }:
        errors.append(f"node journal facts mismatch: {node_id}")
    topology = row.get("topology")
    topology_tuple = (
        tuple(
            topology.get(field)
            for field in (
                "level",
                "child_count",
                "leaf_count",
                "operation_count",
                "subtree_node_count",
                "partition_start",
                "partition_end",
            )
        )
        if isinstance(topology, dict)
        else ()
    )
    if topology_tuple != expected["topology"]:
        errors.append(f"node topology facts mismatch: {node_id}")


def _validate_tree(nodes: dict[str, dict[str, Any]], errors: list[str]) -> None:
    if set(nodes) != set(EXPECTED_NODES):
        return
    roots = [node_id for node_id, row in nodes.items() if row.get("parent_id") is None]
    if roots != ["l2-root"]:
        errors.append("tree must have exactly the expected root")
    for node_id, row in nodes.items():
        topology = row.get("topology")
        child_ids = row.get("child_ids")
        if not isinstance(topology, dict) or not isinstance(child_ids, list):
            continue
        if any(not isinstance(child_id, str) for child_id in child_ids):
            errors.append(f"tree child IDs must be strings: {node_id}")
            continue
        topology_fields = (
            "level",
            "child_count",
            "leaf_count",
            "operation_count",
            "subtree_node_count",
            "partition_start",
            "partition_end",
        )
        if any(type(topology.get(field)) is not int for field in topology_fields):
            errors.append(f"tree topology values must be integers: {node_id}")
            continue
        if topology.get("child_count") != len(child_ids):
            errors.append(f"tree child count mismatch: {node_id}")
        if not child_ids:
            continue
        children = [nodes.get(child_id) for child_id in child_ids]
        if any(child is None for child in children):
            errors.append(f"tree child reference missing: {node_id}")
            continue
        raw_child_topologies = [
            child.get("topology") for child in children if child is not None
        ]
        if any(not isinstance(child, dict) for child in raw_child_topologies):
            continue
        child_topologies = [
            child for child in raw_child_topologies if isinstance(child, dict)
        ]
        first = child_topologies[0]
        last = child_topologies[-1]
        if topology.get("partition_start") != first.get("partition_start"):
            errors.append(f"tree partition start mismatch: {node_id}")
        if topology.get("partition_end") != last.get("partition_end"):
            errors.append(f"tree partition end mismatch: {node_id}")
        for left, right in zip(child_topologies, child_topologies[1:]):
            if left.get("partition_end") != right.get("partition_start"):
                errors.append(f"tree child partitions are not dense: {node_id}")
        for sum_field in ("leaf_count", "operation_count"):
            if topology.get(sum_field) != sum(child.get(sum_field, -1) for child in child_topologies):
                errors.append(f"tree {sum_field} does not sum: {node_id}")
        expected_nodes = 1 + sum(child.get("subtree_node_count", -1) for child in child_topologies)
        if topology.get("subtree_node_count") != expected_nodes:
            errors.append(f"tree subtree node count does not sum: {node_id}")
        for child_id, child in zip(child_ids, children):
            if child is not None and child.get("parent_id") != node_id:
                errors.append(f"tree parent link mismatch: {child_id}")


def _validate_verification_boundary(document: dict[str, Any], errors: list[str]) -> None:
    verification = document.get("receipt_verification")
    if isinstance(verification, dict):
        expected = {
            "performed_by": "Rust RISC0 verifier-only harness",
            "verifier_source_path": "zk/zrpf_risc0/harness/src/bin/verify_structural_tree.rs",
            "risc0_zkvm_version": "3.0.5",
            "all_receipts_seal_verified": True,
            "all_expected_image_ids_verified": True,
            "exact_aggregate_journals_recomposed": True,
            "python_checker_verifies_seal": False,
            "python_checker_scope": [
                "strict_manifest_schema",
                "reviewed_manifest_digest",
                "relative_source_sha256",
                "optional_receipt_and_journal_byte_hashes",
                "optional_transcript_byte_hashes",
                "bounded_tree_topology",
            ],
        }
        if verification != expected:
            errors.append("receipt-verification boundary facts mismatch")
    controls = document.get("negative_controls")
    expected_controls = [
        {
            "id": "missing_child_assumption_rejected",
            "passed": True,
            "expected_program_role": "structural_l1",
            "status": "structural_l1_missing_child_assumption_rejected",
            "transcript": {
                "artifact_path": "structural-tree/missing-child-assumption-transcript.json",
                "sha256": "3fbbf303f3cc6f0e7c996731b2b68ba4f8f059064595647faf6f83b09b6ca521",
                "size_bytes": 159,
            },
        },
        {
            "id": "swapped_level_one_receipts_rejected",
            "passed": True,
            "expected_program_role": "structural_l1",
            "status": "swapped_level_one_receipts_rejected",
            "transcript": {
                "artifact_path": "structural-tree/swapped-level-one-transcript.json",
                "sha256": "901ad867adee829d6da910b2ddc5915b4c116c0a22a30b5111d24e9be29d80fa",
                "size_bytes": 274,
            },
        },
        {
            "id": "wrong_image_receipt_rejected",
            "passed": True,
            "expected_program_role": "structural_l1",
            "status": "wrong_image_receipt_rejected",
            "transcript": {
                "artifact_path": "structural-tree/wrong-image-transcript.json",
                "sha256": "8233da84919f833ae678706f89f35a8aef4a05aacca91fdbb7f4335d0b953a31",
                "size_bytes": 267,
            },
        },
    ]
    if not isinstance(controls, list) or controls != expected_controls:
        errors.append("negative-control facts mismatch")
    prover = document.get("prover_execution")
    if isinstance(prover, dict) and prover != {
        "performed_by": "Rust RISC0 proving harness",
        "receipt_generation_completed": True,
        "executed_harness_source_closure_attested": False,
        "current_source_matches_executed": False,
        "source_drift_reason": "post_run_checkpoint_patch_changed_proving_harness_source",
        "executed_binary_sha256": "5a8d767d7ea4b335116b51480880072dd7518de63245507f2eb9a9b454d80615",
        "executed_binary_size_bytes": 9976088,
    }:
        errors.append("prover-execution provenance facts mismatch")
    replay = document.get("verifier_replay")
    if isinstance(replay, dict):
        transcript = replay.get("transcript")
        if replay.get("status") != "persisted_four_leaf_two_level_structural_tree_verified":
            errors.append("verifier replay status mismatch")
        if replay.get("current_source_closure_attested") is not True:
            errors.append("verifier replay source closure is not attested")
        if replay.get("executed_binary_sha256") != (
            "b55f992f5d71d1f72eaf9e108126866b00a6374ca2af5bcb83ff2a3457a138c6"
        ):
            errors.append("verifier replay binary SHA-256 mismatch")
        if replay.get("executed_binary_size_bytes") != 2584232:
            errors.append("verifier replay binary size mismatch")
        if not isinstance(transcript, dict):
            errors.append("verifier replay transcript facts missing")
        elif transcript != {
            "artifact_path": "structural-tree/verifier-replay-transcript.json",
            "sha256": "d9f05bb36f9e6c8666561b9f805f433048657805a75d9c34217479172ef42d0e",
            "size_bytes": 295,
        }:
            errors.append("verifier replay transcript facts mismatch")
    if document.get("claims") != EXPECTED_CLAIMS:
        errors.append("claim boundary mismatch")
    if document.get("non_claims") != EXPECTED_NON_CLAIMS:
        errors.append("required non-claims mismatch")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--artifact-root",
        type=Path,
        help="optional local root containing seven receipts and four transcripts",
    )
    args = parser.parse_args()

    document, load_errors = load_manifest(args.manifest)
    if load_errors:
        report = _report(load_errors, 0, "")
    else:
        report = validate_manifest(document)

    checked_artifacts = 0
    if args.artifact_root is not None and isinstance(document, dict):
        nodes = document.get("nodes")
        if isinstance(nodes, list):
            for node in nodes:
                if isinstance(node, dict):
                    report["errors"].extend(
                        support.verify_receipt_artifact(args.artifact_root, node)
                    )
                    checked_artifacts += 1
        controls = document.get("negative_controls")
        if isinstance(controls, list):
            for index, control in enumerate(controls):
                transcript = control.get("transcript") if isinstance(control, dict) else None
                if isinstance(transcript, dict):
                    report["errors"].extend(
                        support.verify_transcript_artifact(
                            args.artifact_root, transcript, f"negative-control transcript {index}"
                        )
                    )
                    checked_artifacts += 1
        replay = document.get("verifier_replay")
        transcript = replay.get("transcript") if isinstance(replay, dict) else None
        if isinstance(transcript, dict):
            report["errors"].extend(
                support.verify_transcript_artifact(
                    args.artifact_root, transcript, "verifier replay transcript"
                )
            )
            checked_artifacts += 1
    report["facts"]["optional_artifacts_checked"] = checked_artifacts
    report["errors"] = list(dict.fromkeys(report["errors"]))
    report["ok"] = not report["errors"]
    report["facts"]["evidence_ready"] = report["ok"]
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
