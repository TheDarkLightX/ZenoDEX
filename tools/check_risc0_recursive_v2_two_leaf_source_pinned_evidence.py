#!/usr/bin/env python3
"""Replay the claim-limited recursive-v2 source-pinned two-leaf evidence.

The committed manifest and v2 rebuild reference are fixed trust inputs. Live
artifact paths are caller supplied, bounded, hash checked, and never become
trust-root inputs.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
import stat
import subprocess
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from tools.check_risc0_recursive_v2_rebuild_evidence import (
        EvidenceError,
        FileDigest,
    )

_MODULE_PREFIX = "tools." if __package__ else ""
v2 = importlib.import_module(
    f"{_MODULE_PREFIX}check_risc0_recursive_v2_rebuild_evidence"
)


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PATH = (
    ROOT / "docs/research/RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json"
)
HISTORICAL_PATH = ROOT / "docs/research/RECURSIVE_STARK_V2_TWO_LEAF_EXPERIMENT_20260710.json"
TOOLCHAIN_LOCK_PATH = ROOT / "config/proof_profiles/risc0_recursive_toolchain_lock.json"

EVIDENCE_SCHEMA = "zenodex/recursive_stark_v2_two_leaf_source_pinned_evidence/v1"
REPORT_SCHEMA = "zenodex/recursive_stark_v2_two_leaf_source_pinned_evidence_check/v1"
EXPECTED_STATUS = "same_host_source_frozen_two_leaf_receipts_regenerated_and_verified"
ACCEPTED_STATUS = "source_pinned_two_leaf_evidence_replayed"
EXPECTED_EVIDENCE_FILE_SHA256 = "9a98b947f76a599109f5238861d010fd3dbb8a8299ef6e3f03685b3cac51ad74"
EXPECTED_EVIDENCE_CANONICAL_SHA256 = (
    "56a821441a4d89228347a2ad6e4659c3d0a8c7b32130cbba8bec6749141b97f5"
)
EXPECTED_HISTORICAL_FILE_SHA256 = "c225841cff999b30d0b076845a76b6c0a1ee95127a62504dc2d7c0f49280b73d"
EXPECTED_REFERENCE_FILE_SHA256 = "fe044c8fdef2f8e32e788c8d8d07bf2b82a77666bfb186f86e43f827db0dffec"

MAX_MANIFEST_BYTES = 1024 * 1024
MAX_LEAF_BYTES = 16 * 1024 * 1024
MAX_NODE_BYTES = 16 * 1024 * 1024
MAX_EXECUTABLE_BYTES = 256 * 1024 * 1024
MAX_COMMAND_OUTPUT_BYTES = 64 * 1024
COMMAND_TIMEOUT_SECONDS = 120

ROOT_KEYS = frozenset(
    {
        "aggregate_v2",
        "claims",
        "cross_run_comparison",
        "date",
        "leaf_claims",
        "nonclaims",
        "regenerated_proof_pair",
        "schema",
        "source_frozen_build",
        "status",
        "verification",
        "version",
    }
)

EXPECTED_CLAIMS = {
    "bounded_host_fanout_constructor_source_pinned": True,
    "current_image_two_leaf_receipts_regenerated": True,
    "current_image_two_leaf_fixed_height_receipt_integrity": True,
    "exact_leaf_and_node_binding_verified": True,
    "same_host_source_frozen_build": True,
    "arbitrary_depth_recursion": False,
    "cross_environment_reproducibility": False,
    "data_availability_verified": False,
    "durable_atomic_admission": False,
    "general_multi_leaf_profile_promoted": False,
    "governed_statement_authority": False,
    "nonempty_receipt_partition_merge_cryptographically_exercised": False,
    "privacy": False,
    "production_ready": False,
    "public_claim_allowed": False,
    "public_replay_available": False,
    "release_authority": False,
    "same_profile_verifier_set_cryptographically_exercised": False,
    "settlement_authorization": False,
    "throughput_claim_allowed": False,
    "v1_outer_envelope_canonicality_verified": False,
}

EXPECTED_NONCLAIMS = (
    "This evidence covers one same-host spot-plus-zUSD fanout-two fixed-height run; it does not establish all supported fanouts or arbitrary depth.",
    "The source-frozen build constrains and observes the build pipeline. Source-to-binary cryptographic attestation and cross-host reproducibility remain absent.",
    "Fresh receipts authenticate the same journals as the historical run. The receipt bytes differ, so proof-byte determinism is not established.",
    "The repository-pinned specialized two-leaf verifier shares the RISC0 and recursive-v2 libraries with the prover and is not an independent proof implementation.",
    "Both leaves have empty receipt-ID partitions, so nonempty accepted and rejected receipt-set composition remains unverified.",
    "The zUSD evidence covers DepositMint only; repay, redeem, burn, liquidation, and stability-pool lifecycle coverage remain absent.",
    "The generated node artifacts retain the historical one-leaf throughput nonclaim string and require this manifest for accurate standalone interpretation.",
    "The V1 outer envelope does not yet reject duplicate keys or unknown nested fields.",
    "Schedule, data-availability, and carry fields remain commitment-only for this profile.",
    "No durable atomic ZenoLedger admission path consumed these receipts.",
    "RISC0 receipt verification establishes computational integrity for the authenticated journals; it does not establish witness privacy or zero knowledge.",
    "This evidence grants no release, governance, settlement, throughput, public replay, or production authority.",
)


def _reject(code: str, detail: str) -> EvidenceError:
    return v2.EvidenceError(code, detail)


def _mapping(value: object, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise _reject("EVIDENCE_SCHEMA", f"{label} must be an object")
    return value


def _canonical_sha256(value: object) -> str:
    return hashlib.sha256(v2._canonical_json_bytes(value)).hexdigest()


def _check_mapping_shape(value: object, template: object, *, path: str = "evidence") -> None:
    if isinstance(template, Mapping):
        current = _mapping(value, path)
        if frozenset(current) != frozenset(template):
            raise _reject("EVIDENCE_SCHEMA", f"{path} keys mismatch")
        for key, child in template.items():
            _check_mapping_shape(current[key], child, path=f"{path}.{key}")
    elif isinstance(template, list) and isinstance(value, list):
        for index, (current, expected) in enumerate(zip(value, template, strict=False)):
            _check_mapping_shape(current, expected, path=f"{path}[{index}]")


def _load_fixed_json(path: Path, *, label: str, expected_sha256: str) -> Mapping[str, Any]:
    digest = v2._read_regular(path, label=label, max_bytes=MAX_MANIFEST_BYTES)
    if digest.sha256 != expected_sha256:
        raise _reject(f"{label}_DIGEST_MISMATCH", digest.sha256)
    return _mapping(v2._parse_json(digest.raw, label=label), label)


def load_evidence() -> Mapping[str, Any]:
    evidence = _load_fixed_json(
        EVIDENCE_PATH,
        label="TWO_LEAF_EVIDENCE",
        expected_sha256=EXPECTED_EVIDENCE_FILE_SHA256,
    )
    canonical = _canonical_sha256(evidence)
    if canonical != EXPECTED_EVIDENCE_CANONICAL_SHA256:
        raise _reject("EVIDENCE_CANONICAL_DIGEST_MISMATCH", canonical)
    return evidence


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


def validate_evidence(
    evidence: Mapping[str, Any],
    reference: Mapping[str, Any],
    historical: Mapping[str, Any],
) -> None:
    if frozenset(evidence) != ROOT_KEYS:
        raise _reject("EVIDENCE_SCHEMA", "root keys mismatch")
    _check_mapping_shape(evidence, load_evidence())
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

    build = _mapping(evidence["source_frozen_build"], "source_frozen_build")
    link = _mapping(build.get("reference"), "source_frozen_build.reference")
    reference_digest = v2._read_regular(
        v2.REFERENCE_PATH,
        label="reference",
        max_bytes=v2.MAX_REFERENCE_BYTES,
    )
    if reference_digest.sha256 != EXPECTED_REFERENCE_FILE_SHA256:
        raise _reject("REFERENCE_FILE_DIGEST_MISMATCH", reference_digest.sha256)
    if link != {
        "path": "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json",
        "file_sha256": reference_digest.sha256,
        "canonical_json_sha256": v2.reference_canonical_sha256(reference),
    }:
        raise _reject("EVIDENCE_REFERENCE_BINDING", "reference link mismatch")

    aggregate = _mapping(evidence["aggregate_v2"], "aggregate_v2")
    program = _mapping(reference["program"], "reference.program")
    if aggregate != {
        "sdk_version": reference["sdk_version"],
        "image_id": program["image_id"],
        "program_sha256": program["program_sha256"],
        "program_size_bytes": program["program_bytes"],
        "raw_elf_sha256": program["raw_elf"]["sha256"],
        "raw_elf_size_bytes": program["raw_elf"]["size_bytes"],
    }:
        raise _reject("EVIDENCE_PROGRAM_BINDING", "aggregate program mismatch")

    source = _mapping(reference["source_compile"], "reference.source_compile")
    source_evidence = _mapping(build.get("source_closure"), "source_closure")
    main_row = next(
        (
            row
            for row in source["files"]
            if row["path"] == "zk/recursive_stark_v2_risc0/harness/src/main.rs"
        ),
        None,
    )
    if main_row is None:
        raise _reject("EVIDENCE_SOURCE_BINDING", "harness main absent")
    if source_evidence != {
        "file_count": source["file_count"],
        "root_sha256": source["root_sha256"],
        "total_bytes": sum(int(row["size_bytes"]) for row in source["files"]),
        "harness_main_sha256": main_row["sha256"],
        "harness_main_size_bytes": main_row["size_bytes"],
    }:
        raise _reject("EVIDENCE_SOURCE_BINDING", "source closure mismatch")
    if build.get("source_to_binary_cryptographic_attestation") is not False:
        raise _reject("EVIDENCE_CLAIMS", "source attestation must remain false")
    if build.get("cross_environment_reproducibility") is not False:
        raise _reject("EVIDENCE_CLAIMS", "cross-environment claim must remain false")
    if build.get("build_pipeline_constrained") is not True:
        raise _reject("EVIDENCE_CLAIMS", "build pipeline constraint must remain true")
    registry = _mapping(build.get("registry_source_closure"), "registry source closure")
    reference_registry = _mapping(
        source.get("registry_source_closure"), "reference registry source closure"
    )
    if registry != {
        "package_count": reference_registry["package_count"],
        "root_sha256": reference_registry["root_sha256"],
        "verified_source_bytes": 175405359,
    }:
        raise _reject("EVIDENCE_SOURCE_BINDING", "registry source closure mismatch")
    clean_report = _mapping(build.get("clean_rebuild_report"), "clean rebuild report")
    if clean_report.get("status") != reference["claims"]["accepted_clean_rebuild_status"]:
        raise _reject("EVIDENCE_SOURCE_BINDING", "clean rebuild status mismatch")

    leaves = evidence.get("leaf_claims")
    old_leaves = historical.get("leaf_claims")
    if not isinstance(leaves, list) or len(leaves) != 2 or not isinstance(old_leaves, list):
        raise _reject("EVIDENCE_LEAVES", "expected two leaf rows")
    expected_roles = ("spot", "zusd_deposit_mint")
    expected_profiles = ("recursive_spot_leaf_v1", "recursive_zusd_leaf_v1")
    for index, (leaf, old_leaf) in enumerate(zip(leaves, old_leaves, strict=True)):
        row = _mapping(leaf, f"leaf[{index}]")
        old = _mapping(old_leaf, f"historical leaf[{index}]")
        if (
            row.get("role") != expected_roles[index]
            or row.get("profile") != expected_profiles[index]
        ):
            raise _reject("EVIDENCE_LEAVES", f"leaf role/profile {index}")
        for key in (
            "proof_type",
            "profile",
            "lane_id",
            "image_id",
            "artifact_file_sha256",
            "artifact_size_bytes",
            "receipt_sha256",
        ):
            if row.get(key) != old.get(key):
                raise _reject("EVIDENCE_LEAVES", f"historical leaf mismatch {index}:{key}")

    pair = _mapping(evidence["regenerated_proof_pair"], "regenerated_proof_pair")
    old_pair = _mapping(historical["proof_pair"], "historical proof_pair")
    for role, topology in (("inner", (2, 2, 1, 3)), ("root", (1, 2, 2, 4))):
        node = _mapping(pair[role], role)
        old_node = _mapping(old_pair[role], f"historical {role}")
        observed = (
            node.get("immediate_child_count"),
            node.get("flat_leaf_count"),
            node.get("tree_height"),
            node.get("subtree_node_count"),
        )
        if observed != topology:
            raise _reject("EVIDENCE_TOPOLOGY", f"{role}:{observed}")
        for key in ("journal_sha256", "protocol_journal_hash", "profile"):
            if node.get(key) != old_node.get(key):
                raise _reject("EVIDENCE_CROSS_RUN", f"{role}:{key}")
        if node.get("receipt_sha256") == old_node.get("receipt_sha256"):
            raise _reject("EVIDENCE_CROSS_RUN", f"{role}:receipt unexpectedly reused")
    if pair.get("shared_authenticated_roots") != old_pair.get("shared_authenticated_roots"):
        raise _reject("EVIDENCE_CROSS_RUN", "shared authenticated roots mismatch")
    comparison = _mapping(evidence["cross_run_comparison"], "cross_run_comparison")
    if (
        comparison.get("historical_experiment_manifest_sha256") != EXPECTED_HISTORICAL_FILE_SHA256
        or comparison.get("receipt_bytes_reproduced") is not False
        or comparison.get("proof_regeneration_determinism") is not False
        or comparison.get("authenticated_inner_journal_reproduced") is not True
        or comparison.get("authenticated_root_journal_reproduced") is not True
    ):
        raise _reject("EVIDENCE_CROSS_RUN", "cross-run policy mismatch")

    verification = _mapping(evidence["verification"], "verification")
    specialized = _mapping(verification["specialized_host_verifier"], "specialized verifier")
    if specialized.get("repository_source_pinned") is not True:
        raise _reject("EVIDENCE_CLAIMS", "specialized verifier source pin required")
    if specialized.get("independent_proof_implementation") is not False:
        raise _reject("EVIDENCE_CLAIMS", "independent implementation must remain false")
    source_path = "zk/recursive_stark_v2_risc0/harness/src/bin/verify_recursive_v2_two_leaf_pair.rs"
    source_row = next(
        (row for row in source["files"] if row.get("path") == source_path),
        None,
    )
    if source_row is None or specialized.get("source_path") != source_path:
        raise _reject("EVIDENCE_VERIFIER_BINDING", "two-leaf verifier source path mismatch")
    if specialized.get("source_sha256") != source_row.get("sha256"):
        raise _reject("EVIDENCE_VERIFIER_BINDING", "two-leaf verifier source hash mismatch")
    two_leaf_binary = reference["proof_pair"]["two_leaf_static_verifier"]
    if (
        specialized.get("binary_sha256") != two_leaf_binary["sha256"]
        or specialized.get("binary_size_bytes") != two_leaf_binary["size_bytes"]
    ):
        raise _reject("EVIDENCE_VERIFIER_BINDING", "two-leaf verifier binary mismatch")
    one_leaf = _mapping(verification["source_pinned_one_leaf_verifier_control"], "one-leaf control")
    if one_leaf.get("binary_sha256") != reference["proof_pair"]["static_verifier"]["sha256"]:
        raise _reject("EVIDENCE_VERIFIER_BINDING", "one-leaf verifier hash mismatch")
    missing = _mapping(verification["missing_child_assumption_control"], "missing assumption")
    if (
        missing.get("transcript_sha256")
        != reference["proof_pair"]["missing_assumption_output"]["sha256"]
        or missing.get("status") != "missing_child_assumption_rejected"
    ):
        raise _reject("EVIDENCE_MISSING_ASSUMPTION", "transcript mismatch")


def load_trust_roots() -> tuple[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]]:
    evidence = load_evidence()
    reference = v2.load_reference()
    historical = _load_fixed_json(
        HISTORICAL_PATH,
        label="TWO_LEAF_HISTORICAL",
        expected_sha256=EXPECTED_HISTORICAL_FILE_SHA256,
    )
    validate_evidence(evidence, reference, historical)
    return evidence, reference, historical


def _verify_file(
    path: Path,
    *,
    label: str,
    expected_sha256: str,
    expected_size: int | None,
    max_bytes: int,
    executable: bool = False,
) -> FileDigest:
    digest = v2._read_regular(path, label=label, max_bytes=max_bytes)
    if digest.sha256 != expected_sha256:
        raise _reject("LIVE_FILE_SHA256", label)
    if expected_size is not None and digest.size_bytes != expected_size:
        raise _reject("LIVE_FILE_SIZE", label)
    absolute = v2._canonical_path(path, label=label, directory=False)
    mode = absolute.stat(follow_symlinks=False).st_mode
    if executable and (not stat.S_ISREG(mode) or mode & 0o111 == 0):
        raise _reject("LIVE_EXECUTABLE", label)
    return digest


def _run(
    command: Sequence[str], *, env: Mapping[str, str] | None = None
) -> subprocess.CompletedProcess[bytes]:
    try:
        result = subprocess.run(
            list(command),
            cwd=ROOT,
            env=dict(env) if env is not None else None,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=COMMAND_TIMEOUT_SECONDS,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise _reject("LIVE_COMMAND", Path(command[0]).name) from exc
    if (
        len(result.stdout) > MAX_COMMAND_OUTPUT_BYTES
        or len(result.stderr) > MAX_COMMAND_OUTPUT_BYTES
    ):
        raise _reject("LIVE_COMMAND_OUTPUT", Path(command[0]).name)
    return result


def _stdout_json(result: subprocess.CompletedProcess[bytes], *, label: str) -> Mapping[str, Any]:
    if result.returncode != 0 or result.stderr:
        raise _reject("LIVE_COMMAND_REJECT", f"{label}:{result.returncode}")
    return _mapping(v2._parse_json(result.stdout, label=label), label)


def _validate_dry_run(report: Mapping[str, Any], evidence: Mapping[str, Any]) -> None:
    pair = evidence["regenerated_proof_pair"]
    leaves = evidence["leaf_claims"]
    if (
        report.get("ok") is not True
        or report.get("dry_run") is not True
        or report.get("aggregate_v2_image_id") != evidence["aggregate_v2"]["image_id"]
        or report.get("input_leaf_count") != 2
        or report.get("input_leaf_receipt_sha256s")
        != [leaves[0]["receipt_sha256"], leaves[1]["receipt_sha256"]]
    ):
        raise _reject("LIVE_DRY_RUN", "header mismatch")
    shared = pair["shared_authenticated_roots"]
    for role, output_key in (("inner", "inner"), ("root", "epoch_root")):
        observed = _mapping(report.get(output_key), f"dry-run {output_key}")
        expected = pair[role]
        for key in (
            "journal_sha256",
            "protocol_journal_hash",
            "profile",
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


def _expected_verifier_output(evidence: Mapping[str, Any]) -> Mapping[str, Any]:
    leaves = evidence["leaf_claims"]
    pair = evidence["regenerated_proof_pair"]
    return {
        "aggregate_v2_image_id": evidence["aggregate_v2"]["image_id"],
        "inner_receipt_sha256": pair["inner"]["receipt_sha256"],
        "leaf_receipt_sha256s": [leaves[0]["receipt_sha256"], leaves[1]["receipt_sha256"]],
        "ok": True,
        "root_receipt_sha256": pair["root"]["receipt_sha256"],
        "status": "recursive_v2_two_leaf_pair_verified",
    }


def _load_r0vm_policy(reference: Mapping[str, Any]) -> Mapping[str, Any]:
    lock_digest = v2._read_regular(
        TOOLCHAIN_LOCK_PATH,
        label="toolchain lock",
        max_bytes=v2.MAX_REFERENCE_BYTES,
    )
    lock = _mapping(v2._parse_json(lock_digest.raw, label="TOOLCHAIN_LOCK"), "toolchain lock")
    if (
        v2.toolchain_lock._canonical_manifest_sha256(lock)
        != reference["build_policy"]["toolchain_lock_canonical_sha256"]
    ):
        raise _reject("TOOLCHAIN_LOCK_DIGEST", "canonical digest mismatch")
    rows = lock.get("installed_artifacts")
    if not isinstance(rows, list):
        raise _reject("TOOLCHAIN_LOCK_SCHEMA", "installed_artifacts")
    row = next(
        (item for item in rows if isinstance(item, Mapping) and item.get("id") == "r0vm"), None
    )
    if row is None:
        raise _reject("TOOLCHAIN_LOCK_SCHEMA", "r0vm absent")
    return row


def check_live(
    *,
    spot_leaf: Path,
    zusd_leaf: Path,
    inner_artifact: Path,
    root_artifact: Path,
    release_harness: Path,
    one_leaf_verifier: Path,
    two_leaf_verifier: Path,
    r0vm: Path,
) -> dict[str, Any]:
    evidence, reference, _ = load_trust_roots()
    leaves = evidence["leaf_claims"]
    pair = evidence["regenerated_proof_pair"]
    verification = evidence["verification"]
    r0vm_policy = _load_r0vm_policy(reference)

    for path, row, label, bound in (
        (spot_leaf, leaves[0], "spot leaf", MAX_LEAF_BYTES),
        (zusd_leaf, leaves[1], "zUSD leaf", MAX_LEAF_BYTES),
        (inner_artifact, pair["inner"], "inner artifact", MAX_NODE_BYTES),
        (root_artifact, pair["root"], "root artifact", MAX_NODE_BYTES),
    ):
        _verify_file(
            path,
            label=label,
            expected_sha256=row["artifact_file_sha256"],
            expected_size=row["artifact_size_bytes"],
            max_bytes=bound,
        )
    _verify_file(
        release_harness,
        label="release harness",
        expected_sha256=evidence["source_frozen_build"]["release_harness_binary"]["sha256"],
        expected_size=evidence["source_frozen_build"]["release_harness_binary"]["size_bytes"],
        max_bytes=MAX_EXECUTABLE_BYTES,
        executable=True,
    )
    _verify_file(
        one_leaf_verifier,
        label="one-leaf verifier",
        expected_sha256=verification["source_pinned_one_leaf_verifier_control"]["binary_sha256"],
        expected_size=reference["proof_pair"]["static_verifier"]["size_bytes"],
        max_bytes=MAX_EXECUTABLE_BYTES,
        executable=True,
    )
    _verify_file(
        two_leaf_verifier,
        label="two-leaf verifier",
        expected_sha256=verification["specialized_host_verifier"]["binary_sha256"],
        expected_size=reference["proof_pair"]["two_leaf_static_verifier"]["size_bytes"],
        max_bytes=MAX_EXECUTABLE_BYTES,
        executable=True,
    )
    _verify_file(
        r0vm,
        label="r0vm",
        expected_sha256=r0vm_policy["sha256"],
        expected_size=r0vm_policy["size_bytes"],
        max_bytes=r0vm_policy["max_size_bytes"],
        executable=True,
    )

    clean_env = {
        "HOME": os.environ.get("HOME", "/nonexistent"),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "RISC0_DEV_MODE": "0",
        "RISC0_PROVER": "ipc",
        "RISC0_SERVER_PATH": str(v2._canonical_path(r0vm, label="r0vm", directory=False)),
        "TZ": "UTC",
    }
    harness = str(v2._canonical_path(release_harness, label="release harness", directory=False))
    spot = str(v2._canonical_path(spot_leaf, label="spot leaf", directory=False))
    zusd = str(v2._canonical_path(zusd_leaf, label="zUSD leaf", directory=False))
    inner = str(v2._canonical_path(inner_artifact, label="inner artifact", directory=False))
    root = str(v2._canonical_path(root_artifact, label="root artifact", directory=False))
    verifier2 = str(
        v2._canonical_path(two_leaf_verifier, label="two-leaf verifier", directory=False)
    )
    verifier1 = str(
        v2._canonical_path(one_leaf_verifier, label="one-leaf verifier", directory=False)
    )

    dry_forward = _stdout_json(
        _run([harness, spot, zusd, "--dry-run"], env=clean_env), label="DRY_RUN_FORWARD"
    )
    dry_reverse = _stdout_json(
        _run([harness, zusd, spot, "--dry-run"], env=clean_env), label="DRY_RUN_REVERSE"
    )
    _validate_dry_run(dry_forward, evidence)
    _validate_dry_run(dry_reverse, evidence)
    if dry_forward != dry_reverse:
        raise _reject("LIVE_ORDER_INVARIANCE", "dry-run output mismatch")

    expected_verifier = _expected_verifier_output(evidence)
    verified_forward = _stdout_json(
        _run([verifier2, spot, zusd, inner, root], env=clean_env), label="VERIFY_FORWARD"
    )
    verified_reverse = _stdout_json(
        _run([verifier2, zusd, spot, inner, root], env=clean_env), label="VERIFY_REVERSE"
    )
    if verified_forward != expected_verifier or verified_reverse != expected_verifier:
        raise _reject("LIVE_TWO_LEAF_VERIFIER", "verifier output mismatch")

    duplicate_leaf_result = _run([verifier2, spot, spot, inner, root], env=clean_env)
    if (
        duplicate_leaf_result.returncode != 1
        or duplicate_leaf_result.stdout
        or duplicate_leaf_result.stderr
        != b"duplicate authenticated leaf lane ID\n"
    ):
        raise _reject("LIVE_DUPLICATE_LEAF_POLICY", "control mismatch")

    swapped_nodes_result = _run([verifier2, spot, zusd, root, inner], env=clean_env)
    if (
        swapped_nodes_result.returncode != 1
        or swapped_nodes_result.stdout
        or swapped_nodes_result.stderr != b"two-leaf pair shape mismatch\n"
    ):
        raise _reject("LIVE_SWAPPED_NODE_POLICY", "control mismatch")

    one_leaf_result = _run([verifier1, inner, root], env=clean_env)
    one_leaf_policy = verification["source_pinned_one_leaf_verifier_control"]
    if (
        one_leaf_result.returncode != one_leaf_policy["exit_code"]
        or one_leaf_result.stdout
        or one_leaf_result.stderr != (one_leaf_policy["reject"] + "\n").encode("utf-8")
        or hashlib.sha256(one_leaf_result.stderr).hexdigest() != one_leaf_policy["stderr_sha256"]
    ):
        raise _reject("LIVE_ONE_LEAF_POLICY", "control mismatch")

    missing_result = _run(
        [harness, spot, zusd, "--expect-missing-assumption-reject"], env=clean_env
    )
    missing_report = _stdout_json(missing_result, label="MISSING_ASSUMPTION")
    missing_policy = verification["missing_child_assumption_control"]
    if (
        missing_report.get("status") != missing_policy["status"]
        or missing_report.get("ok") is not True
        or hashlib.sha256(missing_result.stdout).hexdigest() != missing_policy["transcript_sha256"]
        or len(missing_result.stdout) != missing_policy["transcript_size_bytes"]
    ):
        raise _reject("LIVE_MISSING_ASSUMPTION", "control mismatch")

    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": ACCEPTED_STATUS,
        "evidence_file_sha256": EXPECTED_EVIDENCE_FILE_SHA256,
        "aggregate_v2_image_id": evidence["aggregate_v2"]["image_id"],
        "source_root_sha256": evidence["source_frozen_build"]["source_closure"]["root_sha256"],
        "leaf_receipt_sha256s": expected_verifier["leaf_receipt_sha256s"],
        "inner_receipt_sha256": expected_verifier["inner_receipt_sha256"],
        "root_receipt_sha256": expected_verifier["root_receipt_sha256"],
        "dry_run_order_invariant": True,
        "duplicate_leaf_reject_verified": True,
        "specialized_verifier_repository_source_pinned": True,
        "specialized_verifier_order_invariant": True,
        "swapped_node_reject_verified": True,
        "one_leaf_policy_reject_verified": True,
        "missing_assumption_reject_verified": True,
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


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spot-leaf", type=Path, required=True)
    parser.add_argument("--zusd-leaf", type=Path, required=True)
    parser.add_argument("--inner-artifact", type=Path, required=True)
    parser.add_argument("--root-artifact", type=Path, required=True)
    parser.add_argument("--release-harness", type=Path, required=True)
    parser.add_argument("--one-leaf-verifier", type=Path, required=True)
    parser.add_argument("--two-leaf-verifier", type=Path, required=True)
    parser.add_argument("--r0vm", type=Path, required=True)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        report = check_live(
            spot_leaf=args.spot_leaf,
            zusd_leaf=args.zusd_leaf,
            inner_artifact=args.inner_artifact,
            root_artifact=args.root_artifact,
            release_harness=args.release_harness,
            one_leaf_verifier=args.one_leaf_verifier,
            two_leaf_verifier=args.two_leaf_verifier,
            r0vm=args.r0vm,
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
            print(f"two-leaf evidence rejected: {exc}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print(f"two-leaf evidence: {report['status']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
