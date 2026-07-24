#!/usr/bin/env python3
"""Check narrowly scoped retained V6 program-binary byte-identity evidence.

The record separates publisher-reported retained output bytes from live,
HEAD-only Git observations. It does not bind an output to a source root or
build execution and therefore cannot establish build reproducibility.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import selectors
import stat
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVIDENCE = (
    REPO_ROOT
    / "docs/research/"
    "ZRPF_SOURCE_OPENED_SPOT_V6_SAME_HOST_REPRODUCIBILITY_20260713.json"
)
EVIDENCE_SCHEMA = (
    "zenodex/zrpf_source_opened_spot_v6_retained_output_identity/v2"
)
REPORT_SCHEMA = (
    "zenodex/zrpf_source_opened_spot_v6_retained_output_identity_check/v2"
)
LIVE_RETAINED_OUTPUT_IDENTITY_FIELD = (
    "three_live_retained_output_sets_byte_identity_observed"
)
EXPECTED_EVIDENCE_SHA256 = (
    "0a4096119ed5d4e2258d209e1f58fd0cb015ad8d210af1770367743c564c73ae"
)
RECORDED_AT = "2026-07-13"
SCOPE = "retained_v6_program_binary_byte_identity_comparison"
ARTIFACT_SET_DOMAIN = b"zenodex.zrpf.source_opened_spot_v6.artifact_set.v1\0"
ARTIFACT_SET_DOMAIN_LABEL = "zenodex.zrpf.source_opened_spot_v6.artifact_set.v1"
EXPECTED_ARTIFACT_SET_SHA256 = (
    "0075441f70fa7b5f16b5b0282cdb4a765d0b1107740bfbac3d29ef7ae6bc41a3"
)
MAX_EVIDENCE_BYTES = 64 * 1024
MAX_ARTIFACT_BYTES = 8 * 1024 * 1024
MAX_JSON_DEPTH = 12
MAX_JSON_NODES = 512
MAX_JSON_STRING_BYTES = 1024
MAX_JSON_INTEGER_DIGITS = 19
MAX_JSON_INTEGER_ABS = (1 << 63) - 1
MAX_GIT_STDOUT_BYTES = 4 * 1024
MAX_GIT_STDERR_BYTES = 4 * 1024
GIT_INSPECTION_TIMEOUT_SECONDS = 20
OUTPUT_LABELS = ("build_a", "build_b", "path4")
SOURCE_HEAD_OBSERVATION_LABELS = OUTPUT_LABELS
EQUAL_HEAD_COMMIT_TREE_PAIR = ("build_a", "build_b")
EXPECTED_SOURCE_HEAD_OBSERVATIONS = {
    "build_a": (
        "87c7a5b1146482d7a55428179ed6d3453b43a7e7",
        "25299d0dc26ec9cf7e7ae4ea664e4c9d8278b820",
    ),
    "build_b": (
        "87c7a5b1146482d7a55428179ed6d3453b43a7e7",
        "25299d0dc26ec9cf7e7ae4ea664e4c9d8278b820",
    ),
    "path4": (
        "2e1e77c2ad6603ae798d9a39e0f65f1ddc5c2d9f",
        "786edac523b9f802575e5ced642ea1f256c90cfb",
    ),
}


@dataclass(frozen=True)
class ArtifactSpec:
    stage: str
    artifact_file: str
    size_bytes: int
    sha256: str
    image_id_hex: str


@dataclass(frozen=True)
class BoundedGitResult:
    returncode: int
    stdout: bytes
    stderr: bytes


ARTIFACT_SPECS = (
    ArtifactSpec(
        "spot_value_leaf_v6",
        "spot_value_leaf_v6.bin",
        1_191_196,
        "28e6ed98c89f62a4439a1e63c6c5173c927209923f1f24733d0f67d155d0da74",
        "67494a413c729cbb4b6095036425ba0b86edcc30625c19b525409f8e8ff022d1",
    ),
    ArtifactSpec(
        "spot_value_aggregate_l1_v6",
        "spot_value_aggregate_l1_v6.bin",
        635_236,
        "2368aa13b18398e49460067f6907e30339b856e8439a464b4ddb4e7a9970a1f9",
        "a2b4c32ef76c0a81643f1758c476fc21f6a7c2afd11d2a6e08fae022418e2e15",
    ),
    ArtifactSpec(
        "spot_value_aggregate_l2_v6",
        "spot_value_aggregate_l2_v6.bin",
        546_376,
        "3439541629e1c0376cea111061cadd2594218c501cc8485249ef2a50ff824908",
        "5c8f94b4ada70ad5ba0d6ac6bd6b0055a9e148c329372e7b24a81249ff07a76f",
    ),
    ArtifactSpec(
        "source_opened_spot_settlement_v6",
        "source_opened_spot_settlement_v6.bin",
        2_039_876,
        "dc192506cf8ff97824aa98b90eb8b62bd43ece5ccb1af7d2ba085e5faf865309",
        "73a1c5c275d85f39443f68803932df9caac670b420b9948b7e7b2dffe1f2e98d",
    ),
)

PUBLISHER_REPORTED_TRUE_OBSERVATIONS = {
    "a_b_head_commit_tree_identity_observed",
    "output_roots_pairwise_distinct",
    "three_retained_output_sets_byte_identical",
}
FALSE_CLAIMS = {
    "same_host_build_reproducibility_verified",
    "source_to_output_provenance_verified",
    "complete_build_input_closure_verified",
    "cross_host_reproducibility_verified",
    "image_ids_recomputed_in_this_comparison",
    "path4_exact_source_equivalence_verified",
    "proofs_regenerated",
    "release_authority",
    "settlement_authority",
    "production_authority",
}
EXPECTED_NONCLAIMS = [
    "retained output byte identity does not establish source-to-output "
    "provenance or a build execution",
    "publisher-reported observations are historical records and are not live "
    "verification",
    "build host identity and build execution transcripts are not committed",
    "live source inspection observes only HEAD commit/tree; working-tree "
    "contents, cleanliness, index flags, and compiler-visible input closure "
    "are not inspected",
    "live output and source rechecks are sequential observations, not atomic "
    "filesystem snapshots",
    "build_a and build_b HEAD commit/tree equality is independent of retained "
    "output bytes",
    "path4 records a distinct HEAD commit/tree and is only a third retained "
    "output byte-identity comparison",
    "no complete build-input closure, same-host build reproducibility, or "
    "cross-host reproducibility claim",
    "image IDs, proofs, and receipts were not recomputed or regenerated in "
    "this comparison",
    "no release, settlement, ledger-admission, or production authority",
]
REPORT_FIELDS = frozenset(
    {
        "ok",
        "schema",
        "errors",
        "evidence_sha256",
        "governed_anchor_checked",
        "static_artifact_records_checked",
        "live_output_sets_checked",
        "live_artifact_files_checked",
        "live_output_roots_pairwise_distinct",
        "live_source_head_observations_checked",
        "live_a_b_head_commit_tree_identity_observed",
        LIVE_RETAINED_OUTPUT_IDENTITY_FIELD,
        "same_host_build_reproducibility_verified",
        "source_to_output_provenance_verified",
        "complete_build_input_closure_verified",
        "image_ids_recomputed_in_this_comparison",
        "build_host_identifier_committed",
        "build_execution_transcripts_committed",
        "path4_exact_source_equivalence_verified",
        "cross_host_reproducibility_verified",
        "proofs_regenerated",
        "release_authority",
        "settlement_authority",
        "production_authority",
        "nonclaims",
    }
)


class RetainedOutputEvidenceError(ValueError):
    """Stable fail-closed evidence rejection."""


def _reject_float(_value: str) -> NoReturn:
    raise RetainedOutputEvidenceError("floating-point JSON numbers are forbidden")


def _parse_bounded_int(value: str) -> int:
    digits = value[1:] if value.startswith("-") else value
    if len(digits) > MAX_JSON_INTEGER_DIGITS:
        raise RetainedOutputEvidenceError("JSON integer exceeds governed bound")
    try:
        parsed = int(value, 10)
    except ValueError as exc:
        raise RetainedOutputEvidenceError("JSON integer is malformed") from exc
    if abs(parsed) > MAX_JSON_INTEGER_ABS:
        raise RetainedOutputEvidenceError("JSON integer exceeds governed bound")
    return parsed


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RetainedOutputEvidenceError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def canonical_bytes(document: Any) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=False) + "\n").encode("utf-8")


def _stable_path_bytes(path: Path, maximum: int, label: str) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise RetainedOutputEvidenceError(f"{label} unavailable") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RetainedOutputEvidenceError(f"{label} must be a regular file")
        if before.st_size <= 0 or before.st_size > maximum:
            raise RetainedOutputEvidenceError(f"{label} byte length is unsupported")
        raw = _read_exact_fd(descriptor, before.st_size, label)
        after = os.fstat(descriptor)
        if _stable_identity(before) != _stable_identity(after):
            raise RetainedOutputEvidenceError(f"{label} changed during read")
        return raw
    finally:
        os.close(descriptor)


def _read_exact_fd(descriptor: int, size: int, label: str) -> bytes:
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        try:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
        except BlockingIOError as exc:
            raise RetainedOutputEvidenceError(f"{label} read would block") from exc
        if not chunk:
            raise RetainedOutputEvidenceError(
                f"{label} ended before its recorded size"
            )
        chunks.append(chunk)
        remaining -= len(chunk)
    if os.read(descriptor, 1):
        raise RetainedOutputEvidenceError(f"{label} exceeds its recorded size")
    return b"".join(chunks)


def _stable_identity(value: os.stat_result) -> tuple[int, ...]:
    return (
        value.st_dev,
        value.st_ino,
        value.st_mode,
        value.st_nlink,
        value.st_size,
        value.st_mtime_ns,
        value.st_ctime_ns,
    )


def load_evidence(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = _stable_path_bytes(path, MAX_EVIDENCE_BYTES, "evidence")
    try:
        document = json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_int=_parse_bounded_int,
            parse_constant=_reject_float,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        OverflowError,
        RecursionError,
        RetainedOutputEvidenceError,
        ValueError,
    ) as exc:
        raise RetainedOutputEvidenceError(f"evidence JSON rejected: {exc}") from exc
    _validate_json_shape(document)
    if type(document) is not dict:
        raise RetainedOutputEvidenceError("evidence root must be an object")
    if canonical_bytes(document) != raw:
        raise RetainedOutputEvidenceError("evidence bytes are noncanonical")
    return document, raw


def _validate_json_shape(document: Any) -> None:
    stack: list[tuple[Any, int]] = [(document, 1)]
    nodes = 0
    while stack:
        value, depth = stack.pop()
        nodes += 1
        if nodes > MAX_JSON_NODES:
            raise RetainedOutputEvidenceError("evidence JSON has too many nodes")
        if depth > MAX_JSON_DEPTH:
            raise RetainedOutputEvidenceError("evidence JSON is nested too deeply")
        if type(value) is dict:
            for key, child in value.items():
                if type(key) is not str:
                    raise RetainedOutputEvidenceError(
                        "evidence JSON key is unsupported"
                    )
                _require_bounded_utf8(key, "evidence JSON key")
                stack.append((child, depth + 1))
        elif type(value) is list:
            stack.extend((child, depth + 1) for child in value)
        elif type(value) is str:
            _require_bounded_utf8(value, "evidence JSON string")
        elif type(value) not in {bool, int}:
            raise RetainedOutputEvidenceError(
                "evidence JSON value type is unsupported"
            )


def _require_bounded_utf8(value: str, label: str) -> None:
    try:
        encoded = value.encode("utf-8", errors="strict")
    except UnicodeEncodeError as exc:
        raise RetainedOutputEvidenceError(
            f"{label} contains invalid Unicode"
        ) from exc
    if len(encoded) > MAX_JSON_STRING_BYTES:
        raise RetainedOutputEvidenceError(f"{label} is too long")


def validate_evidence(
    document: dict[str, Any],
    raw: bytes,
    *,
    output_directories: Mapping[str, Path] | None = None,
    source_directories: Mapping[str, Path] | None = None,
    require_anchor: bool = True,
) -> dict[str, Any]:
    evidence = _exact_object(
        document,
        {
            "schema",
            "recorded_at",
            "scope",
            "comparison_profile",
            "publisher_reported_observations",
            "artifacts",
            "claims",
            "nonclaims",
        },
        "evidence",
    )
    _require_equal(evidence["schema"], EVIDENCE_SCHEMA, "evidence.schema")
    _require_equal(evidence["recorded_at"], RECORDED_AT, "evidence.recorded_at")
    _require_equal(evidence["scope"], SCOPE, "evidence.scope")
    observed_sha256 = hashlib.sha256(raw).hexdigest()
    if require_anchor and observed_sha256 != EXPECTED_EVIDENCE_SHA256:
        raise RetainedOutputEvidenceError(
            "evidence SHA-256 differs from the governed checker anchor"
        )
    _validate_comparison_profile(evidence["comparison_profile"])
    _validate_publisher_reported_observations(
        evidence["publisher_reported_observations"]
    )
    _validate_artifacts(evidence["artifacts"])
    _validate_claims(evidence["claims"])
    if evidence["nonclaims"] != EXPECTED_NONCLAIMS:
        raise RetainedOutputEvidenceError("evidence.nonclaims mismatch")

    outputs_checked = 0
    artifact_files_checked = 0
    output_roots_distinct = False
    if output_directories is not None:
        outputs_checked, artifact_files_checked = _validate_live_outputs(
            output_directories
        )
        output_roots_distinct = outputs_checked == len(OUTPUT_LABELS)

    source_head_observations_checked = 0
    a_b_head_commit_tree_identity_observed = False
    if source_directories is not None:
        source_head_observations_checked = _validate_live_sources(
            source_directories
        )
        a_b_head_commit_tree_identity_observed = (
            source_head_observations_checked
            == len(SOURCE_HEAD_OBSERVATION_LABELS)
        )

    retained_output_identity_verified = (
        require_anchor
        and outputs_checked == len(OUTPUT_LABELS)
        and artifact_files_checked == len(OUTPUT_LABELS) * len(ARTIFACT_SPECS)
        and output_roots_distinct
    )
    return _report(
        ok=True,
        errors=[],
        evidence_sha256=observed_sha256,
        governed_anchor_checked=require_anchor,
        static_artifact_records_checked=len(ARTIFACT_SPECS),
        live_output_sets_checked=outputs_checked,
        live_artifact_files_checked=artifact_files_checked,
        live_output_roots_pairwise_distinct=output_roots_distinct,
        live_source_head_observations_checked=source_head_observations_checked,
        live_a_b_head_commit_tree_identity_observed=(
            a_b_head_commit_tree_identity_observed
        ),
        live_retained_output_identity_observed=retained_output_identity_verified,
    )


def _validate_comparison_profile(value: Any) -> None:
    profile = _exact_object(
        value,
        {
            "output_labels",
            "source_head_observation_labels",
            "equal_head_commit_tree_pair",
            "distinct_head_commit_tree_label",
            "artifact_set_domain",
            "build_host_identifier_committed",
            "build_execution_transcripts_committed",
            "source_to_output_provenance_verified",
        },
        "comparison_profile",
    )
    if profile["output_labels"] != list(OUTPUT_LABELS):
        raise RetainedOutputEvidenceError("comparison_profile.output_labels mismatch")
    if profile["source_head_observation_labels"] != list(
        SOURCE_HEAD_OBSERVATION_LABELS
    ):
        raise RetainedOutputEvidenceError(
            "comparison_profile.source_head_observation_labels mismatch"
        )
    if profile["equal_head_commit_tree_pair"] != list(
        EQUAL_HEAD_COMMIT_TREE_PAIR
    ):
        raise RetainedOutputEvidenceError(
            "comparison_profile.equal_head_commit_tree_pair mismatch"
        )
    _require_equal(
        profile["distinct_head_commit_tree_label"],
        "path4",
        "comparison_profile.distinct_head_commit_tree_label",
    )
    _require_equal(
        profile["artifact_set_domain"],
        ARTIFACT_SET_DOMAIN_LABEL,
        "comparison_profile.artifact_set_domain",
    )
    _require_exact_bool(
        profile["build_host_identifier_committed"],
        False,
        "comparison_profile.build_host_identifier_committed",
    )
    _require_exact_bool(
        profile["build_execution_transcripts_committed"],
        False,
        "comparison_profile.build_execution_transcripts_committed",
    )
    _require_exact_bool(
        profile["source_to_output_provenance_verified"],
        False,
        "comparison_profile.source_to_output_provenance_verified",
    )


def _validate_publisher_reported_observations(value: Any) -> None:
    observations = _exact_object(
        value,
        PUBLISHER_REPORTED_TRUE_OBSERVATIONS
        | {"retained_output_sets", "source_head_commit_tree_observations"},
        "publisher_reported_observations",
    )
    for field in sorted(PUBLISHER_REPORTED_TRUE_OBSERVATIONS):
        _require_exact_bool(
            observations[field],
            True,
            f"publisher_reported_observations.{field}",
        )
    _validate_retained_output_sets(observations["retained_output_sets"])
    _validate_source_head_observations(
        observations["source_head_commit_tree_observations"]
    )


def _validate_retained_output_sets(value: Any) -> None:
    if type(value) is not list or len(value) != len(OUTPUT_LABELS):
        raise RetainedOutputEvidenceError(
            "retained_output_sets must contain three entries"
        )
    for index, label in enumerate(OUTPUT_LABELS):
        item = _exact_object(
            value[index],
            {
                "output_label",
                "artifact_set_sha256",
            },
            f"retained_output_sets[{index}]",
        )
        _require_equal(
            item["output_label"],
            label,
            f"retained_output_sets[{index}].output_label",
        )
        _require_equal(
            item["artifact_set_sha256"],
            EXPECTED_ARTIFACT_SET_SHA256,
            f"retained_output_sets[{index}].artifact_set_sha256",
        )


def _validate_source_head_observations(value: Any) -> None:
    if type(value) is not list or len(value) != len(
        SOURCE_HEAD_OBSERVATION_LABELS
    ):
        raise RetainedOutputEvidenceError(
            "source_head_commit_tree_observations must contain three entries"
        )
    for index, label in enumerate(SOURCE_HEAD_OBSERVATION_LABELS):
        item = _exact_object(
            value[index],
            {"source_label", "repository_commit", "repository_tree"},
            f"source_head_commit_tree_observations[{index}]",
        )
        _require_equal(
            item["source_label"],
            label,
            f"source_head_commit_tree_observations[{index}].source_label",
        )
        expected_commit, expected_tree = EXPECTED_SOURCE_HEAD_OBSERVATIONS[label]
        _require_equal(
            item["repository_commit"],
            expected_commit,
            f"source_head_commit_tree_observations[{index}].repository_commit",
        )
        _require_equal(
            item["repository_tree"],
            expected_tree,
            f"source_head_commit_tree_observations[{index}].repository_tree",
        )
    if (
        EXPECTED_SOURCE_HEAD_OBSERVATIONS["build_a"]
        != EXPECTED_SOURCE_HEAD_OBSERVATIONS["build_b"]
    ):
        raise RetainedOutputEvidenceError("checker exact-source pair is inconsistent")
    if (
        EXPECTED_SOURCE_HEAD_OBSERVATIONS["path4"]
        == EXPECTED_SOURCE_HEAD_OBSERVATIONS["build_a"]
    ):
        raise RetainedOutputEvidenceError("checker path4 distinction is inconsistent")


def _validate_artifacts(value: Any) -> None:
    if type(value) is not list or len(value) != len(ARTIFACT_SPECS):
        raise RetainedOutputEvidenceError("artifacts field has the wrong length")
    for index, spec in enumerate(ARTIFACT_SPECS):
        item = _exact_object(
            value[index],
            {"stage", "artifact_file", "size_bytes", "sha256", "image_id_hex"},
            f"artifacts[{index}]",
        )
        expected = {
            "stage": spec.stage,
            "artifact_file": spec.artifact_file,
            "size_bytes": spec.size_bytes,
            "sha256": spec.sha256,
            "image_id_hex": spec.image_id_hex,
        }
        if item != expected:
            raise RetainedOutputEvidenceError(f"artifacts[{index}] mismatch")


def _validate_claims(value: Any) -> None:
    claims = _exact_object(value, FALSE_CLAIMS, "claims")
    for field in sorted(FALSE_CLAIMS):
        _require_exact_bool(claims[field], False, f"claims.{field}")


def _open_directory(path: Path, label: str) -> int:
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise RetainedOutputEvidenceError(f"{label} directory unavailable") from exc
    observed = os.fstat(descriptor)
    if not stat.S_ISDIR(observed.st_mode):
        os.close(descriptor)
        raise RetainedOutputEvidenceError(f"{label} must be a directory")
    return descriptor


def _validated_directory_fds(
    directories: Mapping[str, Path], label: str
) -> dict[str, int]:
    if type(directories) is not dict or set(directories) != set(OUTPUT_LABELS):
        raise RetainedOutputEvidenceError(
            f"{label} roots must provide the exact retained labels"
        )
    opened: dict[str, int] = {}
    try:
        for entry_label in OUTPUT_LABELS:
            opened[entry_label] = _open_directory(
                directories[entry_label], f"{label}.{entry_label}"
            )
        identities = {
            (os.fstat(descriptor).st_dev, os.fstat(descriptor).st_ino)
            for descriptor in opened.values()
        }
        if len(identities) != len(OUTPUT_LABELS):
            raise RetainedOutputEvidenceError(
                f"{label} roots are not pairwise distinct"
            )
        return opened
    except Exception:
        for descriptor in opened.values():
            os.close(descriptor)
        raise


def _stable_artifact_bytes(
    directory_fd: int, spec: ArtifactSpec, label: str
) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(spec.artifact_file, flags, dir_fd=directory_fd)
    except OSError as exc:
        raise RetainedOutputEvidenceError(f"{label} unavailable") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RetainedOutputEvidenceError(f"{label} must be a regular file")
        if before.st_size != spec.size_bytes or before.st_size > MAX_ARTIFACT_BYTES:
            raise RetainedOutputEvidenceError(f"{label} size mismatch")
        raw = _read_exact_fd(descriptor, before.st_size, label)
        after = os.fstat(descriptor)
        if _stable_identity(before) != _stable_identity(after):
            raise RetainedOutputEvidenceError(f"{label} changed during read")
        if hashlib.sha256(raw).hexdigest() != spec.sha256:
            raise RetainedOutputEvidenceError(f"{label} SHA-256 mismatch")
        return raw
    finally:
        os.close(descriptor)


def _artifact_set_sha256(artifacts: Mapping[str, bytes]) -> str:
    hasher = hashlib.sha256()
    hasher.update(ARTIFACT_SET_DOMAIN)
    for artifact_file in sorted(artifacts):
        name = artifact_file.encode("utf-8")
        raw = artifacts[artifact_file]
        hasher.update(len(name).to_bytes(4, "big"))
        hasher.update(name)
        hasher.update(len(raw).to_bytes(8, "big"))
        hasher.update(raw)
    return hasher.hexdigest()


def _bounded_directory_inventory(
    directory_fd: int, maximum_entries: int, label: str
) -> set[str]:
    names: set[str] = set()
    entries_seen = 0
    try:
        with os.scandir(directory_fd) as entries:
            for entry in entries:
                if entries_seen >= maximum_entries:
                    raise RetainedOutputEvidenceError(
                        f"{label} inventory exceeds governed bound"
                    )
                entries_seen += 1
                names.add(entry.name)
    except OSError as exc:
        raise RetainedOutputEvidenceError(f"{label} inventory unavailable") from exc
    return names


def _observe_output_set(
    directory_fd: int, output_label: str, expected_inventory: set[str]
) -> tuple[dict[str, bytes], tuple[int, ...]]:
    label = f"output.{output_label}"
    directory_before = os.fstat(directory_fd)
    inventory_before = _bounded_directory_inventory(
        directory_fd, len(expected_inventory), label
    )
    if inventory_before != expected_inventory:
        raise RetainedOutputEvidenceError(f"{label} inventory mismatch")
    observed = {
        spec.artifact_file: _stable_artifact_bytes(
            directory_fd, spec, f"{label}.{spec.artifact_file}"
        )
        for spec in ARTIFACT_SPECS
    }
    inventory_after = _bounded_directory_inventory(
        directory_fd, len(expected_inventory), label
    )
    directory_after = os.fstat(directory_fd)
    if (
        inventory_after != inventory_before
        or _stable_identity(directory_after) != _stable_identity(directory_before)
    ):
        raise RetainedOutputEvidenceError(f"{label} changed during observation")
    if _artifact_set_sha256(observed) != EXPECTED_ARTIFACT_SET_SHA256:
        raise RetainedOutputEvidenceError(f"{label} artifact-set SHA-256 mismatch")
    return observed, _stable_identity(directory_after)


def _validate_live_outputs(directories: Mapping[str, Path]) -> tuple[int, int]:
    opened = _validated_directory_fds(directories, "output")
    try:
        expected_inventory = {spec.artifact_file for spec in ARTIFACT_SPECS}
        initial: dict[str, tuple[dict[str, bytes], tuple[int, ...]]] = {}
        baseline: dict[str, bytes] | None = None
        for output_label in OUTPUT_LABELS:
            observation = _observe_output_set(
                opened[output_label], output_label, expected_inventory
            )
            initial[output_label] = observation
            observed, _directory_identity = observation
            if baseline is None:
                baseline = observed
            elif observed != baseline:
                raise RetainedOutputEvidenceError(
                    f"output.{output_label} is not byte-identical to build_a"
                )

        # Re-read all retained roots while every directory FD remains open. This
        # catches mutation of an earlier root during observation of later roots.
        for output_label in OUTPUT_LABELS:
            final = _observe_output_set(
                opened[output_label], output_label, expected_inventory
            )
            if final != initial[output_label]:
                raise RetainedOutputEvidenceError(
                    f"output.{output_label} changed after initial observation"
                )
        return len(OUTPUT_LABELS), len(OUTPUT_LABELS) * len(ARTIFACT_SPECS)
    finally:
        for descriptor in opened.values():
            os.close(descriptor)


def _git_environment() -> dict[str, str]:
    return {
        "PATH": "/usr/bin:/bin",
        "HOME": "/nonexistent",
        "LANG": "C",
        "LC_ALL": "C",
        "TZ": "UTC",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_OPTIONAL_LOCKS": "0",
    }


def _kill_and_wait(process: subprocess.Popen[bytes]) -> None:
    if process.poll() is None:
        process.kill()
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def _run_git_bounded(
    directory_fd: int, arguments: Sequence[str], label: str
) -> BoundedGitResult:
    process: subprocess.Popen[bytes] | None = None
    selector = selectors.DefaultSelector()
    streams: list[Any] = []
    stdout = bytearray()
    stderr = bytearray()
    try:
        process = subprocess.Popen(
            [
                "/usr/bin/git",
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.untrackedCache=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-C",
                f"/proc/self/fd/{directory_fd}",
                *arguments,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=_git_environment(),
            pass_fds=(directory_fd,),
        )
        if process.stdout is None or process.stderr is None:
            raise RetainedOutputEvidenceError(f"{label} Git inspection failed")
        streams = [process.stdout, process.stderr]
        selector.register(
            process.stdout,
            selectors.EVENT_READ,
            (stdout, MAX_GIT_STDOUT_BYTES, "stdout"),
        )
        selector.register(
            process.stderr,
            selectors.EVENT_READ,
            (stderr, MAX_GIT_STDERR_BYTES, "stderr"),
        )
        deadline = time.monotonic() + GIT_INSPECTION_TIMEOUT_SECONDS
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise RetainedOutputEvidenceError(
                    f"{label} Git inspection timed out"
                )
            for key, _events in selector.select(remaining):
                buffer, maximum, stream_label = key.data
                try:
                    chunk = os.read(key.fd, min(64 * 1024, maximum - len(buffer) + 1))
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                buffer.extend(chunk)
                if len(buffer) > maximum:
                    raise RetainedOutputEvidenceError(
                        f"{label} Git {stream_label} exceeds governed bound"
                    )
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise RetainedOutputEvidenceError(f"{label} Git inspection timed out")
        try:
            returncode = process.wait(timeout=remaining)
        except subprocess.TimeoutExpired as exc:
            raise RetainedOutputEvidenceError(
                f"{label} Git inspection timed out"
            ) from exc
        return BoundedGitResult(returncode, bytes(stdout), bytes(stderr))
    except RetainedOutputEvidenceError:
        if process is not None:
            _kill_and_wait(process)
        raise
    except (OSError, ValueError) as exc:
        if process is not None:
            _kill_and_wait(process)
        raise RetainedOutputEvidenceError(f"{label} Git inspection failed") from exc
    finally:
        selector.close()
        for stream in streams:
            stream.close()


def _git_stdout(directory_fd: int, arguments: Sequence[str], label: str) -> str:
    completed = _run_git_bounded(directory_fd, arguments, label)
    if completed.returncode != 0 or completed.stderr:
        raise RetainedOutputEvidenceError(f"{label} Git inspection failed")
    try:
        return completed.stdout.decode("ascii", errors="strict").strip()
    except UnicodeDecodeError as exc:
        raise RetainedOutputEvidenceError(f"{label} Git output is not ASCII") from exc


def _git_head_commit_tree_observation(
    directory_fd: int, label: str
) -> tuple[str, str]:
    output = _git_stdout(
        directory_fd,
        ("rev-parse", "HEAD^{commit}", "HEAD^{tree}"),
        label,
    )
    values = output.splitlines()
    if len(values) != 2 or any(
        len(value) != 40
        or any(character not in "0123456789abcdef" for character in value)
        for value in values
    ):
        raise RetainedOutputEvidenceError(f"{label} Git identity is malformed")
    return values[0], values[1]


def _observe_source_head(
    directory_fd: int, source_label: str
) -> tuple[tuple[str, str], tuple[int, ...]]:
    label = f"source.{source_label}"
    directory_before = os.fstat(directory_fd)
    observed_before = _git_head_commit_tree_observation(directory_fd, label)
    observed_after = _git_head_commit_tree_observation(directory_fd, label)
    directory_after = os.fstat(directory_fd)
    if (
        observed_after != observed_before
        or _stable_identity(directory_before) != _stable_identity(directory_after)
    ):
        raise RetainedOutputEvidenceError(f"{label} changed during observation")
    return observed_after, _stable_identity(directory_after)


def _validate_live_sources(directories: Mapping[str, Path]) -> int:
    opened = _validated_directory_fds(directories, "source")
    try:
        initial: dict[str, tuple[tuple[str, str], tuple[int, ...]]] = {}
        for source_label in SOURCE_HEAD_OBSERVATION_LABELS:
            observation = _observe_source_head(opened[source_label], source_label)
            if observation[0] != EXPECTED_SOURCE_HEAD_OBSERVATIONS[source_label]:
                raise RetainedOutputEvidenceError(
                    f"source.{source_label} HEAD commit/tree mismatch"
                )
            initial[source_label] = observation

        # A second complete pass detects an earlier HEAD change while a later
        # repository was being observed. No working-tree cleanliness is claimed.
        for source_label in SOURCE_HEAD_OBSERVATION_LABELS:
            final = _observe_source_head(opened[source_label], source_label)
            if final != initial[source_label]:
                raise RetainedOutputEvidenceError(
                    f"source.{source_label} HEAD commit/tree changed after initial "
                    "observation"
                )
        return len(SOURCE_HEAD_OBSERVATION_LABELS)
    finally:
        for descriptor in opened.values():
            os.close(descriptor)


def _exact_object(value: Any, expected: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise RetainedOutputEvidenceError(f"{label} must be an object")
    observed = set(value)
    if observed != expected:
        raise RetainedOutputEvidenceError(
            f"{label} field set mismatch: missing={sorted(expected - observed)}, "
            f"unknown={sorted(observed - expected)}"
        )
    return value


def _require_equal(value: Any, expected: str, label: str) -> None:
    if type(value) is not str or value != expected:
        raise RetainedOutputEvidenceError(f"{label} mismatch")


def _require_exact_bool(value: Any, expected: bool, label: str) -> None:
    if type(value) is not bool or value is not expected:
        raise RetainedOutputEvidenceError(f"{label} must be exactly {expected}")


def _report(
    *,
    ok: bool,
    errors: Sequence[str],
    evidence_sha256: str = "",
    governed_anchor_checked: bool = False,
    static_artifact_records_checked: int = 0,
    live_output_sets_checked: int = 0,
    live_artifact_files_checked: int = 0,
    live_output_roots_pairwise_distinct: bool = False,
    live_source_head_observations_checked: int = 0,
    live_a_b_head_commit_tree_identity_observed: bool = False,
    live_retained_output_identity_observed: bool = False,
) -> dict[str, Any]:
    report = {
        "ok": ok,
        "schema": REPORT_SCHEMA,
        "errors": list(errors),
        "evidence_sha256": evidence_sha256,
        "governed_anchor_checked": governed_anchor_checked,
        "static_artifact_records_checked": static_artifact_records_checked,
        "live_output_sets_checked": live_output_sets_checked,
        "live_artifact_files_checked": live_artifact_files_checked,
        "live_output_roots_pairwise_distinct": (
            live_output_roots_pairwise_distinct
        ),
        "live_source_head_observations_checked": (
            live_source_head_observations_checked
        ),
        "live_a_b_head_commit_tree_identity_observed": (
            live_a_b_head_commit_tree_identity_observed
        ),
        LIVE_RETAINED_OUTPUT_IDENTITY_FIELD: (
            live_retained_output_identity_observed
        ),
        "same_host_build_reproducibility_verified": False,
        "source_to_output_provenance_verified": False,
        "complete_build_input_closure_verified": False,
        "image_ids_recomputed_in_this_comparison": False,
        "build_host_identifier_committed": False,
        "build_execution_transcripts_committed": False,
        "path4_exact_source_equivalence_verified": False,
        "cross_host_reproducibility_verified": False,
        "proofs_regenerated": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
        "nonclaims": list(EXPECTED_NONCLAIMS),
    }
    if set(report) != REPORT_FIELDS:
        raise RuntimeError("internal report schema mismatch")
    return report


def check_evidence(
    path: Path = DEFAULT_EVIDENCE,
    *,
    output_directories: Mapping[str, Path] | None = None,
    source_directories: Mapping[str, Path] | None = None,
    require_retained_output_identity: bool = False,
) -> dict[str, Any]:
    try:
        document, raw = load_evidence(path)
        report = validate_evidence(
            document,
            raw,
            output_directories=output_directories,
            source_directories=source_directories,
        )
        if require_retained_output_identity and not report[
            LIVE_RETAINED_OUTPUT_IDENTITY_FIELD
        ]:
            raise RetainedOutputEvidenceError(
                "retained output byte identity is not established"
            )
        return report
    except (OSError, RetainedOutputEvidenceError) as exc:
        return _report(ok=False, errors=[str(exc)])


def _optional_roots(
    arguments: argparse.Namespace, suffix: str
) -> dict[str, Path] | None:
    values = {
        "build_a": getattr(arguments, f"build_a_{suffix}"),
        "build_b": getattr(arguments, f"build_b_{suffix}"),
        "path4": getattr(arguments, f"path4_{suffix}"),
    }
    present = sum(value is not None for value in values.values())
    if present == 0:
        return None
    if present != len(values):
        raise RetainedOutputEvidenceError(
            f"all three --*-{suffix.replace('_', '-')} arguments are required together"
        )
    return {label: value for label, value in values.items() if value is not None}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path, default=DEFAULT_EVIDENCE)
    for label in OUTPUT_LABELS:
        option = label.replace("_", "-")
        parser.add_argument(f"--{option}-output", type=Path)
        parser.add_argument(f"--{option}-source", type=Path)
    parser.add_argument("--require-retained-output-identity", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    try:
        output_directories = _optional_roots(arguments, "output")
        source_directories = _optional_roots(arguments, "source")
        report = check_evidence(
            arguments.evidence,
            output_directories=output_directories,
            source_directories=source_directories,
            require_retained_output_identity=(
                arguments.require_retained_output_identity
            ),
        )
    except RetainedOutputEvidenceError as exc:
        report = _report(ok=False, errors=[str(exc)])
    if arguments.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("accepted" if report["ok"] else "rejected")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
