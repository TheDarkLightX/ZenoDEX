#!/usr/bin/env python3
"""Fail-closed checker for the source-opened Spot V6 build record.

The governed record binds one publisher report, an exact local Cargo path
dependency graph, and four RISC0 combined program-binary identities. Optional
live artifact verification rechecks those four binaries with the checker-owned
RISC0 tool identity. It does not establish build execution, source-to-binary
provenance, proof generation, reproducibility, or release authority.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import selectors
import stat
import subprocess
import time
import tomllib
from dataclasses import dataclass
from datetime import date
from pathlib import Path, PurePosixPath
from typing import Any, Callable, NoReturn, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = (
    REPO_ROOT
    / "docs/research/ZRPF_SOURCE_OPENED_SPOT_V6_BUILD_RECORD_20260712.json"
)
RECORD_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record/v3"
REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record_check/v3"
MAX_RECORD_BYTES = 256 * 1024
MAX_JSON_INTEGER_DIGITS = 19
MAX_JSON_INTEGER_ABS = (1 << 63) - 1
MAX_JSON_DEPTH = 16
MAX_JSON_NODES = 2_048
MAX_JSON_STRING_CHARS = 1_024
MAX_ARTIFACT_BYTES = 64 * 1024 * 1024
MAX_R0VM_BYTES = 256 * 1024 * 1024
MAX_CARGO_MANIFEST_BYTES = 256 * 1024
MAX_LOCAL_PATH_CRATES = 64
MAX_SOURCE_FILES = 4_096
MAX_SOURCE_FILE_BYTES = 4 * 1024 * 1024
MAX_SOURCE_BYTES = 32 * 1024 * 1024
MAX_SOURCE_PATH_BYTES = 512
MAX_SOURCE_INVENTORY_NODES = 16_384
MAX_GIT_REQUEST_BYTES = 2 * 1024 * 1024
MAX_GIT_STDOUT_BYTES = 36 * 1024 * 1024
MAX_GIT_STDERR_BYTES = 64 * 1024
GIT_TIMEOUT_SECONDS = 30
MEMFD_SEALS = (
    fcntl.F_SEAL_SEAL
    | fcntl.F_SEAL_SHRINK
    | fcntl.F_SEAL_GROW
    | fcntl.F_SEAL_WRITE
)

# Updating this hash is a governance change. Candidate builders cannot supply
# or override it.
GOVERNED_RECORD_SHA256 = (
    "2dd7ccf63e35e26949eb3ebaa543cb6560821bfb57dd498580335fe5f1abaf7a"
)
OFFICIAL_RUSTC_VERSION = "rustc 1.94.1-dev (06e01cb0d 2026-04-09)"
OFFICIAL_CARGO_VERSION = "cargo 1.94.1-dev (29ea6fb6a 2026-03-24)"
OFFICIAL_R0VM_VERSION = "risc0-r0vm 3.0.5"
OFFICIAL_R0VM_SHA256 = (
    "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b"
)
OFFICIAL_CARGO_RISCZERO_VERSION = "cargo-risczero 3.0.5"
OFFICIAL_CARGO_RISCZERO_SHA256 = (
    "45aba69689cef25d81237f3ff62456fc96ff1e23f75adfcd16f7c8b8c1606619"
)
OFFICIAL_RISC0_ZKVM_VERSION = "3.0.5"
OFFICIAL_RISC0_TARGET = "riscv32im-risc0-zkvm-elf"
OFFICIAL_BUILD_JOBS = 2

SOURCE_SPOT_IMAGE_ID = "1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403"
ADAPTER_IMAGE_ID = "4caf9aa0a1ed0e1f08d43549bafd0f25a2e75125862cd7e31edbbfa520cd8760"
LEAF_IMAGE_ID = "67494a413c729cbb4b6095036425ba0b86edcc30625c19b525409f8e8ff022d1"
L1_IMAGE_ID = "a2b4c32ef76c0a81643f1758c476fc21f6a7c2afd11d2a6e08fae022418e2e15"
L2_IMAGE_ID = "5c8f94b4ada70ad5ba0d6ac6bd6b0055a9e148c329372e7b24a81249ff07a76f"
SETTLEMENT_IMAGE_ID = "73a1c5c275d85f39443f68803932df9caac670b420b9948b7e7b2dffe1f2e98d"

PROGRAM_SPECS = (
    (
        "spot_value_leaf_v6",
        "zenodex-zrpf-risc0-spot-value-leaf-v6",
        "spot_value_leaf_v6.bin",
        LEAF_IMAGE_ID,
        "adapter_v3",
        ADAPTER_IMAGE_ID,
    ),
    (
        "spot_value_aggregate_l1_v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l1-v6",
        "spot_value_aggregate_l1_v6.bin",
        L1_IMAGE_ID,
        "spot_value_leaf_v6",
        LEAF_IMAGE_ID,
    ),
    (
        "spot_value_aggregate_l2_v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l2-v6",
        "spot_value_aggregate_l2_v6.bin",
        L2_IMAGE_ID,
        "spot_value_aggregate_l1_v6",
        L1_IMAGE_ID,
    ),
    (
        "source_opened_spot_settlement_v6",
        "zenodex-zrpf-risc0-source-opened-spot-settlement-v6",
        "source_opened_spot_settlement_v6.bin",
        SETTLEMENT_IMAGE_ID,
        "spot_value_aggregate_l2_v6",
        L2_IMAGE_ID,
    ),
)

POLICY_SPECS = (
    (
        "zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs",
        "PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID",
        ADAPTER_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_value_aggregate_l1_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6",
        LEAF_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_value_aggregate_l2_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6",
        L1_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_value_aggregate_root_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6",
        L2_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_settlement_root_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6",
        SETTLEMENT_IMAGE_ID,
    ),
)

CARGO_LOCK_RELATIVE = "zk/zrpf_risc0/Cargo.lock"
BUILD_ORCHESTRATOR_DIRECTORY = "zk/zrpf_risc0/spot_v6_methods"
GOVERNED_GUEST_CRATE_DIRECTORIES = (
    "zk/zrpf_risc0/methods/spot_value_leaf_v6",
    "zk/zrpf_risc0/methods/spot_value_aggregate_l1_v6",
    "zk/zrpf_risc0/methods/spot_value_aggregate_l2_v6",
    "zk/zrpf_risc0/methods/source_opened_spot_settlement_v6",
)
GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES = frozenset(
    {
        "zk/state_proof_risc0/shared",
        "zk/zrpf_protocol/protocol",
        "zk/zrpf_risc0/aggregate_shared",
        "zk/zrpf_risc0/shared",
        "zk/zrpf_risc0/semantic_shared",
        "zk/zrpf_risc0/spot_settlement_v6_shared",
        "zk/zrpf_risc0/spot_value_aggregate_l1_policy_v6",
        "zk/zrpf_risc0/spot_value_aggregate_l2_policy_v6",
        "zk/zrpf_risc0/spot_value_aggregate_root_policy_v6",
        "zk/zrpf_risc0/spot_value_leaf_v6_shared",
        "zk/zrpf_risc0/value_aggregate_shared",
        *GOVERNED_GUEST_CRATE_DIRECTORIES,
    }
)
SOURCE_CLOSURE_EXTRA_DIRECTORIES = frozenset(
    {
        BUILD_ORCHESTRATOR_DIRECTORY,
        "zk/zrpf_risc0/spot_settlement_root_policy_v6",
    }
)
SOURCE_CLOSURE_FILES = (
    "zk/zrpf_risc0/.cargo/config.toml",
    CARGO_LOCK_RELATIVE,
    "zk/zrpf_risc0/Cargo.toml",
)
SOURCE_CLOSURE_FILENAMES = {"Cargo.lock", "Cargo.toml", "build.rs"}
SOURCE_CLOSURE_SUFFIXES = {".rs"}
SOURCE_CLOSURE_DOMAIN = b"zenodex.zrpf.source_opened_spot_v6.repository_source_closure.v2\0"

PUBLISHER_REPORTED_COMMAND_FIELDS = {
    "artifact_hashes_recorded",
    "cargo_build_locked",
    "clean_external_target_verified",
    "image_ids_recomputed_from_program_binaries",
    "policy_dependencies_compiled",
    "risc0_guests_built",
    "source_snapshot_captured",
}
TRUE_CLAIMS = {
    "four_guest_program_binary_identities_recorded",
    "local_path_dependency_graph_complete",
    "selected_source_closure_matches_commit",
}
FALSE_CLAIMS = {
    "complete_build_input_closure_verified",
    "cross_host_reproducible_build",
    "durable_atomic_admission_verified",
    "global_worktree_cleanliness_verified",
    "historical_build_commands_independently_verified",
    "proofs_generated",
    "release_authority",
    "settlement_authority",
    "source_to_program_binary_provenance_verified",
    "production_authority",
}

# Compatibility alias for proof-evidence code that has not yet migrated. The
# record schema uses the explicitly qualified publisher field below.
EXECUTED_COMMAND_FIELDS = PUBLISHER_REPORTED_COMMAND_FIELDS


class BuildRecordError(ValueError):
    """Stable fail-closed build-record rejection."""


@dataclass(frozen=True)
class SourceValidation:
    cargo_lock_sha256: str
    closure: tuple[str, int, int]
    local_path_crates: int


@dataclass(frozen=True)
class BoundedCommandResult:
    returncode: int
    stdout: bytes
    stderr: bytes


def _reject_float(_value: str) -> NoReturn:
    raise BuildRecordError("floating-point JSON numbers are forbidden")


def _parse_bounded_int(value: str) -> int:
    digits = value[1:] if value.startswith("-") else value
    if not digits or len(digits) > MAX_JSON_INTEGER_DIGITS:
        raise BuildRecordError("JSON integer exceeds bound")
    parsed = int(value, 10)
    if abs(parsed) > MAX_JSON_INTEGER_ABS:
        raise BuildRecordError("JSON integer exceeds bound")
    return parsed


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BuildRecordError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def canonical_bytes(document: Any) -> bytes:
    return (
        json.dumps(document, allow_nan=False, indent=2, sort_keys=False) + "\n"
    ).encode("utf-8")


def _read_bounded_regular_file(
    path: Path,
    *,
    label: str,
    maximum_bytes: int,
    executable: bool = False,
) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    flags |= getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise BuildRecordError(f"{label} is unavailable") from exc
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > maximum_bytes
            or (executable and before.st_mode & 0o111 == 0)
        ):
            raise BuildRecordError(f"{label} is not a bounded regular file")
        chunks: list[bytes] = []
        total = 0
        while chunk := os.read(
            descriptor,
            min(1 << 20, maximum_bytes + 1 - total),
        ):
            total += len(chunk)
            if total > maximum_bytes:
                raise BuildRecordError(f"{label} exceeds its byte bound")
            chunks.append(chunk)
        after = os.fstat(descriptor)
    except OSError as exc:
        raise BuildRecordError(f"{label} read failed") from exc
    finally:
        os.close(descriptor)
    if (
        total != before.st_size
        or (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
        != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
    ):
        raise BuildRecordError(f"{label} changed during read")
    return b"".join(chunks)


def _require_unicode_scalars(value: str) -> None:
    if any(0xD800 <= ord(character) <= 0xDFFF for character in value):
        raise BuildRecordError("build record JSON contains a non-Unicode scalar")


def _validate_json_shape(document: Any) -> None:
    nodes = 0
    pending: list[tuple[Any, int]] = [(document, 1)]
    while pending:
        value, depth = pending.pop()
        nodes += 1
        if nodes > MAX_JSON_NODES:
            raise BuildRecordError("build record JSON node count exceeds bound")
        if depth > MAX_JSON_DEPTH:
            raise BuildRecordError("build record JSON depth exceeds bound")
        if type(value) is str:
            if len(value) > MAX_JSON_STRING_CHARS:
                raise BuildRecordError("build record JSON string exceeds bound")
            _require_unicode_scalars(value)
        elif type(value) is dict:
            for key, child in value.items():
                if type(key) is not str:
                    raise BuildRecordError("build record JSON object key is not text")
                if len(key) > MAX_JSON_STRING_CHARS:
                    raise BuildRecordError("build record JSON string exceeds bound")
                _require_unicode_scalars(key)
                pending.append((child, depth + 1))
        elif type(value) is list:
            pending.extend((child, depth + 1) for child in value)
        elif type(value) not in {bool, int, type(None)}:
            raise BuildRecordError("build record JSON contains an unsupported value")


def load_record(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = _read_bounded_regular_file(
        path,
        label="build record",
        maximum_bytes=MAX_RECORD_BYTES,
    )
    try:
        text = raw.decode("utf-8", errors="strict")
        document = json.loads(
            text,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_int=_parse_bounded_int,
            parse_constant=_reject_float,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        BuildRecordError,
        RecursionError,
        ValueError,
    ) as exc:
        raise BuildRecordError(f"build record JSON rejected: {exc}") from exc
    if type(document) is not dict:
        raise BuildRecordError("build record root must be an object")
    _validate_json_shape(document)
    if canonical_bytes(document) != raw:
        raise BuildRecordError("build record bytes are noncanonical")
    return document, raw


def validate_record(
    document: dict[str, Any],
    raw: bytes,
    *,
    repo_root: Path = REPO_ROOT,
    artifact_directory: Path | None = None,
    r0vm_path: Path | None = None,
    expected_record_sha256: str | None = None,
) -> dict[str, Any]:
    """Validate the checker-governed record and optional live artifacts.

    ``expected_record_sha256`` is only an additional caller cross-check. It
    cannot replace or override ``GOVERNED_RECORD_SHA256``.
    """

    return _validate_record(
        document,
        raw,
        repo_root=repo_root,
        artifact_directory=artifact_directory,
        r0vm_path=r0vm_path,
        governed=True,
        additional_expected_sha256=expected_record_sha256,
    )


def validate_candidate_record(
    document: dict[str, Any],
    raw: bytes,
    *,
    repo_root: Path = REPO_ROOT,
    artifact_directory: Path | None = None,
    r0vm_path: Path | None = None,
) -> dict[str, Any]:
    """Validate candidate facts without creating a governed observation."""

    return _validate_record(
        document,
        raw,
        repo_root=repo_root,
        artifact_directory=artifact_directory,
        r0vm_path=r0vm_path,
        governed=False,
        additional_expected_sha256=None,
    )


def _validate_record(
    document: dict[str, Any],
    raw: bytes,
    *,
    repo_root: Path,
    artifact_directory: Path | None,
    r0vm_path: Path | None,
    governed: bool,
    additional_expected_sha256: str | None,
) -> dict[str, Any]:
    _require_canonical_document_bytes(document, raw)
    record = _exact_object(
        document,
        {
            "schema",
            "recorded_at",
            "source_observation",
            "toolchain",
            "programs",
            "publisher_reported_observations",
            "claims",
        },
        "record",
    )
    _require_equal(record["schema"], RECORD_SCHEMA, "record.schema")
    _require_date(record["recorded_at"], "record.recorded_at")
    observed_record_sha256 = hashlib.sha256(raw).hexdigest()
    if governed and observed_record_sha256 != GOVERNED_RECORD_SHA256:
        raise BuildRecordError("build record SHA-256 differs from governed record SHA-256")
    if additional_expected_sha256 is not None:
        _require_hash(additional_expected_sha256, "expected_record_sha256")
        if observed_record_sha256 != additional_expected_sha256:
            raise BuildRecordError(
                "build record SHA-256 differs from additional caller cross-check"
            )

    source_validation = _validate_source_observation(
        record["source_observation"],
        repo_root,
    )
    _validate_toolchain(
        record["toolchain"],
        expected_cargo_lock_sha256=source_validation.cargo_lock_sha256,
    )
    _validate_programs(record["programs"])
    _validate_publisher_reported_observations(
        record["publisher_reported_observations"]
    )
    _validate_claims(record["claims"])
    _validate_policy_sources(repo_root)
    artifacts_checked = 0
    image_ids_recomputed = 0
    if artifact_directory is not None:
        artifacts_checked, image_ids_recomputed = _validate_external_artifacts(
            artifact_directory,
            record["programs"],
            r0vm_path=r0vm_path,
            expected_r0vm_sha256=OFFICIAL_R0VM_SHA256,
        )
    final_closure = compute_source_closure(repo_root)
    if final_closure != source_validation.closure:
        raise BuildRecordError(
            "current source closure changed after initial observation"
        )
    live_observation = (
        governed
        and artifacts_checked == len(PROGRAM_SPECS)
        and image_ids_recomputed == len(PROGRAM_SPECS)
    )
    return {
        "ok": True,
        "schema": REPORT_SCHEMA,
        "record_sha256": observed_record_sha256,
        "candidate_record_validated": True,
        "governed_record_anchor_checked": governed,
        "policy_dependencies_checked": len(POLICY_SPECS),
        "local_path_dependency_crates_checked": source_validation.local_path_crates,
        "source_closure_final_recheck": True,
        "external_artifact_files_checked": artifacts_checked,
        "program_image_ids_recomputed": image_ids_recomputed,
        "live_governed_artifact_set_observed": live_observation,
        "leaf_image_id": LEAF_IMAGE_ID,
        "level_one_image_id": L1_IMAGE_ID,
        "level_two_image_id": L2_IMAGE_ID,
        "settlement_image_id": SETTLEMENT_IMAGE_ID,
        "global_worktree_cleanliness_verified": False,
        "historical_build_commands_independently_verified": False,
        "source_to_program_binary_provenance_verified": False,
        "proofs_generated": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }


def _require_canonical_document_bytes(document: Any, raw: Any) -> None:
    if type(raw) is not bytes or not raw or len(raw) > MAX_RECORD_BYTES:
        raise BuildRecordError("build record canonical raw bytes are invalid")
    _validate_json_shape(document)
    try:
        encoded = canonical_bytes(document)
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as exc:
        raise BuildRecordError(
            "build record document cannot be represented as canonical raw bytes"
        ) from exc
    if encoded != raw:
        raise BuildRecordError(
            "build record document differs from canonical raw bytes"
        )


def _validate_source_observation(value: Any, repo_root: Path) -> SourceValidation:
    source = _exact_object(
        value,
        {
            "repository_commit",
            "repository_tree",
            "source_root_sha256",
            "source_file_count",
            "source_bytes",
        },
        "record.source_observation",
    )
    _require_hex(source["repository_commit"], 40, "repository_commit")
    _require_hex(source["repository_tree"], 40, "repository_tree")
    _require_hash(source["source_root_sha256"], "source_root_sha256")
    _require_positive_int(source["source_file_count"], "source_file_count")
    _require_positive_int(source["source_bytes"], "source_bytes")
    _validate_git_tree(
        repo_root,
        source["repository_commit"],
        source["repository_tree"],
    )
    committed = compute_git_source_closure(
        repo_root,
        source["repository_commit"],
    )
    observed = compute_source_closure(repo_root)
    expected = (
        source["source_root_sha256"],
        source["source_file_count"],
        source["source_bytes"],
    )
    if committed != expected:
        raise BuildRecordError(
            "recorded source closure differs from the recorded Git commit"
        )
    if observed != committed:
        raise BuildRecordError(
            "current selected source closure differs from the recorded Git commit"
        )
    return SourceValidation(
        cargo_lock_sha256=_verified_cargo_lock_sha256(
            repo_root,
            source["repository_commit"],
        ),
        closure=committed,
        local_path_crates=len(GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES),
    )


def _validate_publisher_reported_observations(value: Any) -> None:
    observations = _exact_object(
        value,
        {
            "commands_reported_executed",
            "same_host_current_v6_images_built",
        },
        "record.publisher_reported_observations",
    )
    _require_true_fields(
        observations["commands_reported_executed"],
        PUBLISHER_REPORTED_COMMAND_FIELDS,
        "record.publisher_reported_observations.commands_reported_executed",
    )
    _require_exact_bool(
        observations["same_host_current_v6_images_built"],
        "record.publisher_reported_observations.same_host_current_v6_images_built",
        expected=True,
    )


def _verified_cargo_lock_sha256(repo_root: Path, commit: str) -> str:
    root = repo_root.resolve(strict=True)
    committed = _git_source_files(
        root,
        commit,
        {CARGO_LOCK_RELATIVE},
        _git_environment(),
    )[CARGO_LOCK_RELATIVE]
    current = _stable_source_bytes(root, CARGO_LOCK_RELATIVE)
    if current != committed:
        raise BuildRecordError(
            "current Cargo.lock differs from the recorded Git source closure"
        )
    return hashlib.sha256(committed).hexdigest()


def derive_local_path_dependency_directories(repo_root: Path) -> frozenset[str]:
    root = repo_root.resolve(strict=True)
    return _derive_local_path_dependency_directories(
        lambda relative: _stable_source_bytes(root, relative)
    )


def derive_git_local_path_dependency_directories(
    repo_root: Path,
    commit: str,
) -> frozenset[str]:
    root = repo_root.resolve(strict=True)
    environment = _git_environment()
    return _derive_local_path_dependency_directories(
        lambda relative: _git_source_files(
            root,
            commit,
            {relative},
            environment,
        )[relative]
    )


def _derive_local_path_dependency_directories(
    read_bytes: Callable[[str], bytes],
) -> frozenset[str]:
    orchestrator = _load_cargo_manifest(BUILD_ORCHESTRATOR_DIRECTORY, read_bytes)
    workspace = _load_cargo_manifest("zk/zrpf_risc0", read_bytes)
    _require_no_unmodeled_cargo_path_overrides(workspace, read_bytes)
    roots = _orchestrated_guest_directories(orchestrator)
    orchestrator_dependencies = _local_dependency_directories(
        BUILD_ORCHESTRATOR_DIRECTORY,
        orchestrator,
    )
    pending = list(reversed((*roots, *sorted(orchestrator_dependencies))))
    observed: set[str] = set()
    while pending:
        directory = pending.pop()
        if directory in observed:
            continue
        observed.add(directory)
        if len(observed) > MAX_LOCAL_PATH_CRATES:
            raise BuildRecordError("local Cargo path dependency graph exceeds bound")
        manifest = _load_cargo_manifest(directory, read_bytes)
        for dependency in sorted(_local_dependency_directories(directory, manifest)):
            if dependency not in observed:
                pending.append(dependency)
    return frozenset(observed)


def _load_cargo_manifest(
    directory: str,
    read_bytes: Callable[[str], bytes],
) -> dict[str, Any]:
    relative = f"{directory}/Cargo.toml"
    raw = read_bytes(relative)
    if not raw or len(raw) > MAX_CARGO_MANIFEST_BYTES:
        raise BuildRecordError(f"Cargo manifest byte length unsupported: {relative}")
    try:
        text = raw.decode("utf-8", errors="strict")
        document = tomllib.loads(text)
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise BuildRecordError(f"Cargo manifest rejected: {relative}") from exc
    if type(document) is not dict:
        raise BuildRecordError(f"Cargo manifest root is not a table: {relative}")
    return document


def _require_no_unmodeled_cargo_path_overrides(
    workspace: dict[str, Any],
    read_bytes: Callable[[str], bytes],
) -> None:
    if workspace.get("patch") is not None or workspace.get("replace") is not None:
        raise BuildRecordError("Cargo workspace path overrides are unsupported")
    relative = "zk/zrpf_risc0/.cargo/config.toml"
    raw = read_bytes(relative)
    if not raw or len(raw) > MAX_CARGO_MANIFEST_BYTES:
        raise BuildRecordError(f"Cargo config byte length unsupported: {relative}")
    try:
        config = tomllib.loads(raw.decode("utf-8", errors="strict"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise BuildRecordError(f"Cargo config rejected: {relative}") from exc
    if config.get("paths") not in (None, []):
        raise BuildRecordError("Cargo config path overrides are unsupported")


def _orchestrated_guest_directories(document: dict[str, Any]) -> tuple[str, ...]:
    try:
        methods = document["package"]["metadata"]["risc0"]["methods"]
    except (KeyError, TypeError) as exc:
        raise BuildRecordError("Spot V6 build orchestrator methods are unavailable") from exc
    if type(methods) is not list or len(methods) != len(
        GOVERNED_GUEST_CRATE_DIRECTORIES
    ):
        raise BuildRecordError("Spot V6 build orchestrator method set mismatch")
    observed = tuple(
        _resolve_local_dependency_directory(BUILD_ORCHESTRATOR_DIRECTORY, method)
        for method in methods
    )
    if observed != GOVERNED_GUEST_CRATE_DIRECTORIES:
        raise BuildRecordError("Spot V6 build orchestrator method order mismatch")
    return observed


def _local_dependency_directories(
    manifest_directory: str,
    document: dict[str, Any],
) -> set[str]:
    tables: list[Any] = [
        document.get("dependencies"),
        document.get("build-dependencies"),
    ]
    target = document.get("target")
    if target is not None:
        if type(target) is not dict:
            raise BuildRecordError("Cargo target dependency table is malformed")
        for target_table in target.values():
            if type(target_table) is not dict:
                raise BuildRecordError("Cargo target dependency table is malformed")
            tables.extend(
                (
                    target_table.get("dependencies"),
                    target_table.get("build-dependencies"),
                )
            )
    result: set[str] = set()
    for table in tables:
        if table is None:
            continue
        if type(table) is not dict:
            raise BuildRecordError("Cargo dependency table is malformed")
        for specification in table.values():
            if type(specification) is not dict:
                continue
            if specification.get("workspace") is True:
                raise BuildRecordError(
                    "workspace-inherited Cargo dependencies are unsupported"
                )
            if "path" in specification:
                result.add(
                    _resolve_local_dependency_directory(
                        manifest_directory,
                        specification["path"],
                    )
                )
    return result


def _resolve_local_dependency_directory(base: str, value: Any) -> str:
    if (
        type(value) is not str
        or not value
        or len(value.encode("utf-8", errors="strict")) > MAX_SOURCE_PATH_BYTES
        or "\\" in value
        or any(character in value for character in "\r\n\0")
    ):
        raise BuildRecordError("local Cargo dependency path is malformed")
    relative = PurePosixPath(value)
    if relative.is_absolute():
        raise BuildRecordError("local Cargo dependency path must be repository-relative")
    parts = list(PurePosixPath(base).parts)
    for part in relative.parts:
        if part in {"", "."}:
            continue
        if part == "..":
            if not parts:
                raise BuildRecordError("local Cargo dependency escapes repository")
            parts.pop()
        else:
            parts.append(part)
    if not parts:
        raise BuildRecordError("local Cargo dependency escapes repository")
    return "/".join(parts)


def _require_governed_dependency_graph(directories: frozenset[str]) -> None:
    if directories != GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES:
        missing = sorted(GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES - directories)
        unknown = sorted(directories - GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES)
        raise BuildRecordError(
            "local Cargo path dependency graph differs from governed graph: "
            f"missing={missing}, unknown={unknown}"
        )


def source_closure_directories(repo_root: Path) -> frozenset[str]:
    dependencies = derive_local_path_dependency_directories(repo_root)
    _require_governed_dependency_graph(dependencies)
    return dependencies | SOURCE_CLOSURE_EXTRA_DIRECTORIES


def _git_source_closure_directories(repo_root: Path, commit: str) -> frozenset[str]:
    dependencies = derive_git_local_path_dependency_directories(repo_root, commit)
    _require_governed_dependency_graph(dependencies)
    return dependencies | SOURCE_CLOSURE_EXTRA_DIRECTORIES


def compute_source_closure(repo_root: Path) -> tuple[str, int, int]:
    root = repo_root.resolve(strict=True)
    directories = source_closure_directories(root)
    relative_paths = _current_source_inventory(root, directories)
    return _hash_source_closure(
        relative_paths,
        lambda relative: _stable_source_bytes(root, relative),
    )


def _current_source_inventory(
    root: Path,
    directories: frozenset[str],
) -> set[str]:
    relative_paths = set(SOURCE_CLOSURE_FILES)
    nodes = 0
    for directory_name in sorted(directories):
        directory = root.joinpath(*PurePosixPath(directory_name).parts)
        try:
            facts = directory.stat(follow_symlinks=False)
        except OSError as exc:
            raise BuildRecordError(
                f"source closure directory unavailable: {directory_name}"
            ) from exc
        if directory.is_symlink() or not stat.S_ISDIR(facts.st_mode):
            raise BuildRecordError(
                f"source closure directory unavailable: {directory_name}"
            )
        pending = [directory]
        while pending:
            current = pending.pop()
            try:
                iterator = os.scandir(current)
            except OSError as exc:
                raise BuildRecordError(
                    f"source inventory failed: {directory_name}"
                ) from exc
            try:
                for entry in iterator:
                    nodes += 1
                    if nodes > MAX_SOURCE_INVENTORY_NODES:
                        raise BuildRecordError("source inventory exceeds bound")
                    if entry.is_symlink():
                        raise BuildRecordError(
                            f"source closure symlink rejected: {entry.path}"
                        )
                    if entry.is_dir(follow_symlinks=False):
                        pending.append(Path(entry.path))
                        continue
                    if not entry.is_file(follow_symlinks=False):
                        raise BuildRecordError(
                            f"source closure special file rejected: {entry.path}"
                        )
                    candidate = Path(entry.path)
                    if (
                        candidate.name in SOURCE_CLOSURE_FILENAMES
                        or candidate.suffix in SOURCE_CLOSURE_SUFFIXES
                    ):
                        relative_paths.add(candidate.relative_to(root).as_posix())
            except OSError as exc:
                raise BuildRecordError(
                    f"source inventory failed: {directory_name}"
                ) from exc
            finally:
                iterator.close()
    _validate_source_paths(relative_paths)
    return relative_paths


def compute_git_source_closure(
    repo_root: Path,
    commit: str,
) -> tuple[str, int, int]:
    root = repo_root.resolve(strict=True)
    directories = _git_source_closure_directories(root, commit)
    pathspecs = [*SOURCE_CLOSURE_FILES, *sorted(directories)]
    completed = _run_git_bounded(
        root,
        ["ls-tree", "-r", "--name-only", "-z", commit, "--", *pathspecs],
        "source snapshot inventory",
    )
    if completed.returncode != 0 or completed.stderr:
        raise BuildRecordError("source snapshot Git inventory failed")
    if completed.stdout and not completed.stdout.endswith(b"\0"):
        raise BuildRecordError("source snapshot Git inventory framing is invalid")
    try:
        decoded = [
            item.decode("utf-8", errors="strict")
            for item in completed.stdout.split(b"\0")
            if item
        ]
    except UnicodeDecodeError as exc:
        raise BuildRecordError("source snapshot Git inventory is not UTF-8") from exc
    if len(decoded) != len(set(decoded)):
        raise BuildRecordError("source snapshot Git inventory contains duplicates")
    if len(decoded) > MAX_SOURCE_INVENTORY_NODES:
        raise BuildRecordError("source snapshot Git inventory exceeds bound")
    relative_paths = {
        relative
        for relative in decoded
        if _is_source_closure_path(relative, directories)
    }
    missing = set(SOURCE_CLOSURE_FILES) - relative_paths
    if missing:
        raise BuildRecordError(
            f"source snapshot Git closure misses required files: {sorted(missing)}"
        )
    _validate_source_paths(relative_paths)
    source_bytes = _git_source_files(
        root,
        commit,
        relative_paths,
        _git_environment(),
    )
    return _hash_source_closure(relative_paths, source_bytes.__getitem__)


def _is_source_closure_path(
    relative: str,
    directories: frozenset[str] | None = None,
) -> bool:
    if relative in SOURCE_CLOSURE_FILES:
        return True
    if directories is None:
        directories = (
            GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES
            | SOURCE_CLOSURE_EXTRA_DIRECTORIES
        )
    pure = PurePosixPath(relative)
    if (
        pure.is_absolute()
        or ".." in pure.parts
        or any(character in relative for character in "\r\n\0")
    ):
        return False
    in_directory = any(
        relative.startswith(f"{directory}/") for directory in directories
    )
    return in_directory and (
        pure.name in SOURCE_CLOSURE_FILENAMES
        or pure.suffix in SOURCE_CLOSURE_SUFFIXES
    )


def _validate_source_paths(relative_paths: set[str]) -> None:
    if not relative_paths or len(relative_paths) > MAX_SOURCE_FILES:
        raise BuildRecordError("source file inventory exceeds bound")
    for relative in relative_paths:
        try:
            encoded = relative.encode("utf-8", errors="strict")
        except UnicodeEncodeError as exc:
            raise BuildRecordError("source path is not UTF-8") from exc
        pure = PurePosixPath(relative)
        if (
            not encoded
            or len(encoded) > MAX_SOURCE_PATH_BYTES
            or pure.is_absolute()
            or ".." in pure.parts
            or any(character in relative for character in "\r\n\0")
        ):
            raise BuildRecordError(f"source closure path is invalid: {relative}")


def _hash_source_closure(
    relative_paths: set[str],
    read_bytes: Callable[[str], bytes],
) -> tuple[str, int, int]:
    _validate_source_paths(relative_paths)
    hasher = hashlib.sha256()
    hasher.update(SOURCE_CLOSURE_DOMAIN)
    total_bytes = 0
    for relative in sorted(relative_paths):
        path_bytes = relative.encode("utf-8")
        raw = read_bytes(relative)
        if type(raw) is not bytes or not raw or len(raw) > MAX_SOURCE_FILE_BYTES:
            raise BuildRecordError(
                f"source closure file byte length unsupported: {relative}"
            )
        total_bytes += len(raw)
        if total_bytes > MAX_SOURCE_BYTES:
            raise BuildRecordError("source closure total bytes exceed bound")
        hasher.update(len(path_bytes).to_bytes(4, "big"))
        hasher.update(path_bytes)
        hasher.update(len(raw).to_bytes(8, "big"))
        hasher.update(raw)
    return hasher.hexdigest(), len(relative_paths), total_bytes


def _git_source_files(
    root: Path,
    commit: str,
    relative_paths: set[str],
    environment: dict[str, str],
) -> dict[str, bytes]:
    _validate_source_paths(relative_paths)
    ordered = sorted(relative_paths)
    request = b"".join(
        f"{commit}:{relative}\n".encode("utf-8") for relative in ordered
    )
    if not request or len(request) > MAX_GIT_REQUEST_BYTES:
        raise BuildRecordError("source snapshot Git request exceeds bound")
    completed = _run_git_bounded(
        root,
        ["cat-file", "--batch"],
        "source snapshot file batch read",
        input_bytes=request,
        environment=environment,
    )
    if completed.returncode != 0 or completed.stderr:
        raise BuildRecordError("source snapshot Git file batch read failed")
    output = completed.stdout
    cursor = 0
    total_bytes = 0
    files: dict[str, bytes] = {}
    for relative in ordered:
        line_end = output.find(b"\n", cursor)
        if line_end < 0:
            raise BuildRecordError(
                f"source snapshot Git object header unavailable: {relative}"
            )
        header = output[cursor:line_end].split()
        cursor = line_end + 1
        if len(header) != 3 or header[1] != b"blob" or not header[2].isdigit():
            raise BuildRecordError(
                f"source snapshot Git object is not a blob: {relative}"
            )
        if len(header[2]) > MAX_JSON_INTEGER_DIGITS:
            raise BuildRecordError(
                f"source snapshot Git blob size exceeds bound: {relative}"
            )
        size = int(header[2])
        total_bytes += size
        end = cursor + size
        if (
            size <= 0
            or size > MAX_SOURCE_FILE_BYTES
            or total_bytes > MAX_SOURCE_BYTES
            or end >= len(output)
            or output[end : end + 1] != b"\n"
        ):
            raise BuildRecordError(
                f"source snapshot Git blob framing is invalid: {relative}"
            )
        files[relative] = output[cursor:end]
        cursor = end + 1
    if cursor != len(output):
        raise BuildRecordError("source snapshot Git batch output has trailing bytes")
    return files


def _stable_source_bytes(root: Path, relative: str) -> bytes:
    _validate_source_paths({relative})
    pure = PurePosixPath(relative)
    return _read_bounded_regular_file(
        root.joinpath(*pure.parts),
        label=f"source closure file {relative}",
        maximum_bytes=MAX_SOURCE_FILE_BYTES,
    )


def _validate_git_tree(repo_root: Path, commit: str, expected_tree: str) -> None:
    completed = _run_git_bounded(
        repo_root.resolve(strict=True),
        ["rev-parse", f"{commit}^{{tree}}"],
        "source snapshot tree lookup",
    )
    try:
        observed = completed.stdout[:-1].decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise BuildRecordError("source snapshot Git tree output is malformed") from exc
    if (
        completed.returncode != 0
        or completed.stderr
        or len(completed.stdout) != 41
        or not completed.stdout.endswith(b"\n")
        or observed != expected_tree
    ):
        raise BuildRecordError("repository_tree does not match repository_commit")


def _run_git_bounded(
    root: Path,
    arguments: Sequence[str],
    label: str,
    *,
    input_bytes: bytes | None = None,
    environment: dict[str, str] | None = None,
) -> BoundedCommandResult:
    process: subprocess.Popen[bytes] | None = None
    selector = selectors.DefaultSelector()
    streams: list[Any] = []
    root_descriptor: int | None = None
    input_descriptor: int | None = None
    stdout = bytearray()
    stderr = bytearray()
    try:
        root_descriptor = os.open(
            root,
            os.O_RDONLY
            | getattr(os, "O_DIRECTORY", 0)
            | getattr(os, "O_NOFOLLOW", 0),
        )
        if input_bytes is not None:
            if not hasattr(os, "memfd_create"):
                raise BuildRecordError(f"{label} Git bounded input is unavailable")
            if len(input_bytes) > MAX_GIT_REQUEST_BYTES:
                raise BuildRecordError(f"{label} Git request exceeds bound")
            input_descriptor = os.memfd_create("zrpf-v6-git-input", os.MFD_CLOEXEC)
            pending = memoryview(input_bytes)
            while pending:
                written = os.write(input_descriptor, pending)
                if written <= 0:
                    raise BuildRecordError(f"{label} Git request write failed")
                pending = pending[written:]
            os.lseek(input_descriptor, 0, os.SEEK_SET)
        process = subprocess.Popen(
            [
                "/usr/bin/git",
                "--literal-pathspecs",
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.untrackedCache=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-C",
                f"/proc/self/fd/{root_descriptor}",
                *arguments,
            ],
            stdin=input_descriptor if input_descriptor is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment or _git_environment(),
            pass_fds=tuple(
                descriptor
                for descriptor in (root_descriptor, input_descriptor)
                if descriptor is not None
            ),
        )
        if process.stdout is None or process.stderr is None:
            raise BuildRecordError(f"{label} Git inspection failed")
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
        deadline = time.monotonic() + GIT_TIMEOUT_SECONDS
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise BuildRecordError(f"{label} Git inspection timed out")
            for key, _events in selector.select(remaining):
                buffer, maximum, stream_label = key.data
                try:
                    chunk = os.read(
                        key.fd,
                        min(64 * 1024, maximum - len(buffer) + 1),
                    )
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                buffer.extend(chunk)
                if len(buffer) > maximum:
                    raise BuildRecordError(
                        f"{label} Git {stream_label} exceeds bound"
                    )
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise BuildRecordError(f"{label} Git inspection timed out")
        try:
            returncode = process.wait(timeout=remaining)
        except subprocess.TimeoutExpired as exc:
            raise BuildRecordError(f"{label} Git inspection timed out") from exc
        return BoundedCommandResult(returncode, bytes(stdout), bytes(stderr))
    except BuildRecordError:
        if process is not None:
            _kill_and_wait(process)
        raise
    except (OSError, ValueError) as exc:
        if process is not None:
            _kill_and_wait(process)
        raise BuildRecordError(f"{label} Git inspection failed") from exc
    finally:
        selector.close()
        for stream in streams:
            stream.close()
        if input_descriptor is not None:
            os.close(input_descriptor)
        if root_descriptor is not None:
            os.close(root_descriptor)


def _kill_and_wait(process: subprocess.Popen[bytes]) -> None:
    if process.poll() is None:
        process.kill()
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def _git_environment() -> dict[str, str]:
    return {
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_TERMINAL_PROMPT": "0",
        "HOME": "/nonexistent",
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }


def _validate_toolchain(
    value: Any,
    *,
    expected_cargo_lock_sha256: str,
) -> None:
    toolchain = _exact_object(
        value,
        {
            "rustc",
            "cargo",
            "r0vm",
            "cargo_risczero",
            "risc0_zkvm",
            "cargo_lock_sha256",
            "target",
            "build_jobs",
            "offline",
            "locked",
        },
        "record.toolchain",
    )
    exact_text = {
        "rustc": OFFICIAL_RUSTC_VERSION,
        "cargo": OFFICIAL_CARGO_VERSION,
        "r0vm": f"{OFFICIAL_R0VM_VERSION} sha256:{OFFICIAL_R0VM_SHA256}",
        "cargo_risczero": (
            f"{OFFICIAL_CARGO_RISCZERO_VERSION} "
            f"sha256:{OFFICIAL_CARGO_RISCZERO_SHA256}"
        ),
        "risc0_zkvm": OFFICIAL_RISC0_ZKVM_VERSION,
        "target": OFFICIAL_RISC0_TARGET,
    }
    for field, expected in exact_text.items():
        _require_equal(toolchain[field], expected, f"toolchain.{field}")
    _require_hash(toolchain["cargo_lock_sha256"], "toolchain.cargo_lock_sha256")
    if toolchain["cargo_lock_sha256"] != expected_cargo_lock_sha256:
        raise BuildRecordError(
            "toolchain.cargo_lock_sha256 differs from the verified source closure"
        )
    if type(toolchain["build_jobs"]) is not int or toolchain[
        "build_jobs"
    ] != OFFICIAL_BUILD_JOBS:
        raise BuildRecordError(
            f"toolchain.build_jobs must be exactly {OFFICIAL_BUILD_JOBS}"
        )
    _require_exact_bool(toolchain["offline"], "toolchain.offline", expected=True)
    _require_exact_bool(toolchain["locked"], "toolchain.locked", expected=True)


def _validate_programs(value: Any) -> None:
    if type(value) is not list or len(value) != len(PROGRAM_SPECS):
        raise BuildRecordError("record.programs must contain the four ordered V6 programs")
    for index, (row, spec) in enumerate(zip(value, PROGRAM_SPECS, strict=True)):
        stage, package, artifact_file, image_id, child_stage, child_image_id = spec
        program = _exact_object(
            row,
            {
                "stage",
                "package",
                "artifact_file",
                "program_binary_bytes",
                "program_binary_sha256",
                "image_id_hex",
                "image_id_words_le",
                "verified_child_stage",
                "verified_child_image_id",
            },
            f"record.programs[{index}]",
        )
        for field, expected in (
            ("stage", stage),
            ("package", package),
            ("artifact_file", artifact_file),
            ("image_id_hex", image_id),
            ("verified_child_stage", child_stage),
            ("verified_child_image_id", child_image_id),
        ):
            _require_equal(program[field], expected, f"programs[{index}].{field}")
        _require_positive_int(
            program["program_binary_bytes"],
            f"programs[{index}].program_binary_bytes",
        )
        if program["program_binary_bytes"] > MAX_ARTIFACT_BYTES:
            raise BuildRecordError(
                f"programs[{index}].program_binary_bytes exceeds bound"
            )
        _require_hash(
            program["program_binary_sha256"],
            f"programs[{index}].program_binary_sha256",
        )
        if program["program_binary_sha256"] == "0" * 64:
            raise BuildRecordError(
                f"programs[{index}].program_binary_sha256 is zero"
            )
        expected_words = _image_words_le(image_id)
        if program["image_id_words_le"] != expected_words:
            raise BuildRecordError(f"programs[{index}].image_id_words_le mismatch")


def _validate_claims(value: Any) -> None:
    claims = _exact_object(value, TRUE_CLAIMS | FALSE_CLAIMS, "record.claims")
    for field in TRUE_CLAIMS:
        _require_exact_bool(claims[field], f"claims.{field}", expected=True)
    for field in FALSE_CLAIMS:
        _require_exact_bool(claims[field], f"claims.{field}", expected=False)


def _validate_policy_sources(repo_root: Path) -> None:
    for relative, symbol, expected_image in POLICY_SPECS:
        raw = _read_bounded_regular_file(
            repo_root / relative,
            label=f"policy source {relative}",
            maximum_bytes=256 * 1024,
        )
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise BuildRecordError(f"policy source is not UTF-8: {relative}") from exc
        pattern = re.compile(
            rf"pub const {re.escape(symbol)}: \[u32; 8\] = \[(.*?)\];",
            re.DOTALL,
        )
        match = pattern.search(text)
        if match is None:
            raise BuildRecordError(f"policy symbol is unavailable: {symbol}")
        numbers = [
            int(value.replace("_", ""))
            for value in re.findall(r"[0-9][0-9_]*", match.group(1))
        ]
        if len(numbers) != 8 or any(value > 0xFFFF_FFFF for value in numbers):
            raise BuildRecordError(f"policy image words malformed: {symbol}")
        observed = b"".join(value.to_bytes(4, "little") for value in numbers).hex()
        if observed != expected_image:
            raise BuildRecordError(f"policy image mismatch: {symbol}")


def _validate_external_artifacts(
    directory: Path,
    programs: Any,
    *,
    r0vm_path: Path | None,
    expected_r0vm_sha256: str,
) -> tuple[int, int]:
    root = directory.resolve(strict=True)
    if not root.is_dir():
        raise BuildRecordError("artifact directory is not a directory")
    checked = 0
    recomputed = 0
    r0vm_descriptor: int | None = None
    if r0vm_path is not None:
        r0vm_descriptor = _open_verified_r0vm(r0vm_path, expected_r0vm_sha256)
    try:
        for row in programs:
            filename = row["artifact_file"]
            path = _resolve_artifact(root, filename)
            program_descriptor, size, digest = _open_stable_program_binary(path)
            try:
                if (
                    size != row["program_binary_bytes"]
                    or digest != row["program_binary_sha256"]
                ):
                    raise BuildRecordError(
                        f"external artifact identity mismatch: {filename}"
                    )
                if r0vm_descriptor is not None:
                    observed_image = _compute_program_image_id(
                        r0vm_descriptor,
                        program_descriptor,
                    )
                    if observed_image != row["image_id_hex"]:
                        raise BuildRecordError(
                            f"program image ID differs from retained binary: {filename}"
                        )
                    recomputed += 1
                checked += 1
            finally:
                os.close(program_descriptor)
    finally:
        if r0vm_descriptor is not None:
            os.close(r0vm_descriptor)
    return checked, recomputed


def _open_verified_r0vm(path: Path, expected_sha256: str) -> int:
    if not path.is_absolute() or path.is_symlink():
        raise BuildRecordError("r0vm must be an absolute non-symlink path")
    descriptor, _size, digest, _prefix = _sealed_file_snapshot(
        path,
        label="r0vm executable",
        maximum_bytes=MAX_R0VM_BYTES,
        executable=True,
    )
    if digest != expected_sha256:
        os.close(descriptor)
        raise BuildRecordError("r0vm executable identity mismatch")
    return descriptor


def _compute_program_image_id(r0vm_descriptor: int, program_descriptor: int) -> str:
    environment = {
        "HOME": "/nonexistent",
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    try:
        completed = subprocess.run(
            [
                f"/proc/self/fd/{r0vm_descriptor}",
                "--elf",
                f"/proc/self/fd/{program_descriptor}",
                "--id",
            ],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            pass_fds=(r0vm_descriptor, program_descriptor),
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise BuildRecordError("r0vm image-ID computation failed") from exc
    output = completed.stdout
    if (
        completed.returncode != 0
        or completed.stderr
        or not output.endswith(b"\n")
        or output.count(b"\n") != 1
    ):
        raise BuildRecordError("r0vm image-ID computation failed")
    try:
        image_id = output[:-1].decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise BuildRecordError("r0vm image ID is not ASCII") from exc
    _require_hash(image_id, "r0vm image ID")
    return image_id


def _open_stable_program_binary(path: Path) -> tuple[int, int, str]:
    descriptor, size, digest, prefix = _sealed_file_snapshot(
        path,
        label=f"artifact {path.name}",
        maximum_bytes=MAX_ARTIFACT_BYTES,
        executable=False,
    )
    if size <= 8 or len(prefix) != 8 or prefix[:4] != b"R0BF":
        os.close(descriptor)
        raise BuildRecordError(
            f"artifact is not a stable RISC0 program binary: {path.name}"
        )
    return descriptor, size, digest


def _sealed_file_snapshot(
    path: Path,
    *,
    label: str,
    maximum_bytes: int,
    executable: bool,
) -> tuple[int, int, str, bytes]:
    if not hasattr(os, "memfd_create"):
        raise BuildRecordError("sealed memfd snapshots are unavailable")
    source = os.open(
        path,
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_CLOEXEC", 0),
    )
    snapshot: int | None = None
    try:
        before = os.fstat(source)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > maximum_bytes
            or (executable and before.st_mode & 0o111 == 0)
        ):
            raise BuildRecordError(f"{label} is not a bounded regular file")
        snapshot = os.memfd_create(
            "zrpf-v6-sealed-snapshot",
            os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
        )
        hasher = hashlib.sha256()
        prefix = b""
        total = 0
        while chunk := os.read(source, min(1 << 20, maximum_bytes + 1 - total)):
            if len(prefix) < 8:
                prefix += chunk[: 8 - len(prefix)]
            total += len(chunk)
            if total > maximum_bytes:
                raise BuildRecordError(f"{label} exceeds its byte bound")
            hasher.update(chunk)
            pending = memoryview(chunk)
            while pending:
                written = os.write(snapshot, pending)
                if written <= 0:
                    raise BuildRecordError(f"{label} snapshot write failed")
                pending = pending[written:]
        after = os.fstat(source)
        if (
            (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
            != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
            or total != before.st_size
        ):
            raise BuildRecordError(f"{label} changed during snapshot capture")
        os.fchmod(snapshot, 0o500 if executable else 0o400)
        os.lseek(snapshot, 0, os.SEEK_SET)
        fcntl.fcntl(snapshot, fcntl.F_ADD_SEALS, MEMFD_SEALS)
        if fcntl.fcntl(snapshot, fcntl.F_GET_SEALS) != MEMFD_SEALS:
            raise BuildRecordError(f"{label} snapshot seals are incomplete")
        snap = os.fstat(snapshot)
        if not stat.S_ISREG(snap.st_mode) or snap.st_size != total:
            raise BuildRecordError(f"{label} snapshot identity mismatch")
        result = snapshot
        snapshot = None
        return result, total, hasher.hexdigest(), prefix
    finally:
        os.close(source)
        if snapshot is not None:
            os.close(snapshot)


def _require_risc0_program_binary(path: Path) -> None:
    descriptor = os.open(
        path,
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        before = os.fstat(descriptor)
        prefix = os.read(descriptor, 8)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (
        (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
        != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
        or len(prefix) != 8
        or prefix[:4] != b"R0BF"
    ):
        raise BuildRecordError(
            f"artifact is not a stable RISC0 program binary: {path.name}"
        )


def _resolve_artifact(root: Path, relative: str) -> Path:
    if type(relative) is not str:
        raise BuildRecordError("artifact path must be a string")
    pure = PurePosixPath(relative)
    if pure.is_absolute() or len(pure.parts) != 1 or pure.name in {"", ".", ".."}:
        raise BuildRecordError(f"artifact path is not one bounded filename: {relative}")
    candidate = root / pure.name
    if candidate.is_symlink():
        raise BuildRecordError(f"artifact symlink rejected: {relative}")
    return candidate


def _stable_file_facts(path: Path) -> tuple[int, str]:
    before = path.stat(follow_symlinks=False)
    if (
        not stat.S_ISREG(before.st_mode)
        or before.st_size <= 0
        or before.st_size > MAX_ARTIFACT_BYTES
    ):
        raise BuildRecordError(f"artifact is not a bounded regular file: {path.name}")
    hasher = hashlib.sha256()
    descriptor = os.open(
        path,
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        opened = os.fstat(descriptor)
        if (opened.st_dev, opened.st_ino, opened.st_size) != (
            before.st_dev,
            before.st_ino,
            before.st_size,
        ):
            raise BuildRecordError(f"artifact changed before read: {path.name}")
        total = 0
        while chunk := os.read(descriptor, min(1 << 20, MAX_ARTIFACT_BYTES + 1 - total)):
            total += len(chunk)
            if total > MAX_ARTIFACT_BYTES:
                raise BuildRecordError(f"artifact exceeds bound: {path.name}")
            hasher.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns) != (
        opened.st_dev,
        opened.st_ino,
        opened.st_size,
        opened.st_mtime_ns,
    ) or total != opened.st_size:
        raise BuildRecordError(f"artifact changed during read: {path.name}")
    return total, hasher.hexdigest()


def _exact_object(value: Any, fields: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise BuildRecordError(f"{label} must be an object")
    observed = set(value)
    if observed != fields:
        raise BuildRecordError(
            f"{label} field set mismatch: missing={sorted(fields - observed)}, "
            f"unknown={sorted(observed - fields)}"
        )
    return value


def _require_true_fields(value: Any, fields: set[str], label: str) -> None:
    obj = _exact_object(value, fields, label)
    for field in fields:
        _require_exact_bool(obj[field], f"{label}.{field}", expected=True)


def _require_exact_bool(value: Any, label: str, *, expected: bool | None = None) -> None:
    if type(value) is not bool or (expected is not None and value is not expected):
        suffix = "a Boolean" if expected is None else f"exactly {expected}"
        raise BuildRecordError(f"{label} must be {suffix}")


def _require_positive_int(value: Any, label: str) -> None:
    if type(value) is not int or value <= 0:
        raise BuildRecordError(f"{label} must be a positive integer")


def _require_text(value: Any, label: str) -> None:
    if (
        type(value) is not str
        or not value
        or len(value) > 256
        or any(character in value for character in "\r\n\0")
    ):
        raise BuildRecordError(f"{label} must be bounded single-line text")


def _tool_sha256(value: Any, label: str) -> str:
    _require_text(value, f"toolchain.{label}")
    match = re.fullmatch(r"[A-Za-z0-9._-]+ 3\.0\.5 sha256:([0-9a-f]{64})", value)
    if match is None:
        raise BuildRecordError(
            f"toolchain.{label} must include an exact 3.0.5 executable SHA-256"
        )
    return match.group(1)


def _require_equal(value: Any, expected: str, label: str) -> None:
    if type(value) is not str or value != expected:
        raise BuildRecordError(f"{label} mismatch")


def _require_hash(value: Any, label: str) -> None:
    _require_hex(value, 64, label)


def _require_hex(value: Any, length: int, label: str) -> None:
    if type(value) is not str or len(value) != length or re.fullmatch(r"[0-9a-f]+", value) is None:
        raise BuildRecordError(f"{label} must be {length} lowercase hexadecimal characters")


def _require_date(value: Any, label: str) -> None:
    if type(value) is not str:
        raise BuildRecordError(f"{label} must be an ISO date")
    try:
        parsed = date.fromisoformat(value)
    except ValueError as exc:
        raise BuildRecordError(f"{label} must be an ISO date") from exc
    if parsed.isoformat() != value:
        raise BuildRecordError(f"{label} must be a canonical ISO date")


def _image_words_le(image_id: str) -> list[int]:
    raw = bytes.fromhex(image_id)
    return [int.from_bytes(raw[offset : offset + 4], "little") for offset in range(0, 32, 4)]


def check_record(
    path: Path = DEFAULT_RECORD,
    *,
    artifact_directory: Path | None = None,
    r0vm_path: Path | None = None,
    expected_record_sha256: str | None = None,
    require_live_artifact_observation: bool = False,
    require_scoped_claim: bool = False,
) -> dict[str, Any]:
    try:
        document, raw = load_record(path)
        report = validate_record(
            document,
            raw,
            artifact_directory=artifact_directory,
            r0vm_path=r0vm_path,
            expected_record_sha256=expected_record_sha256,
        )
        if (
            require_live_artifact_observation or require_scoped_claim
        ) and not report["live_governed_artifact_set_observed"]:
            raise BuildRecordError(
                "live governed artifact-set observation is not established"
            )
        return report
    except (OSError, BuildRecordError) as exc:
        return {
            "ok": False,
            "schema": REPORT_SCHEMA,
            "errors": [str(exc)],
            "candidate_record_validated": False,
            "governed_record_anchor_checked": False,
            "local_path_dependency_crates_checked": 0,
            "source_closure_final_recheck": False,
            "external_artifact_files_checked": 0,
            "program_image_ids_recomputed": 0,
            "live_governed_artifact_set_observed": False,
            "global_worktree_cleanliness_verified": False,
            "historical_build_commands_independently_verified": False,
            "source_to_program_binary_provenance_verified": False,
            "proofs_generated": False,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD)
    parser.add_argument("--artifact-directory", type=Path)
    parser.add_argument("--r0vm", type=Path)
    parser.add_argument("--expected-record-sha256")
    parser.add_argument("--require-live-artifact-observation", action="store_true")
    parser.add_argument("--require-scoped-claim", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    report = check_record(
        arguments.record,
        artifact_directory=arguments.artifact_directory,
        r0vm_path=arguments.r0vm,
        expected_record_sha256=arguments.expected_record_sha256,
        require_live_artifact_observation=(
            arguments.require_live_artifact_observation
        ),
        require_scoped_claim=arguments.require_scoped_claim,
    )
    if arguments.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("accepted" if report["ok"] else "rejected")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
