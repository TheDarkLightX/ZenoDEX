#!/usr/bin/env python3
"""Check byte-pinned rebuild artifacts for the recursive RISC0 workspace.

The checker is intentionally standard-library-only and self-contained so its
trust root, bounded filesystem reads, schema checks, and CLI remain one audited
boundary.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import copy
import hashlib
import io
import json
import os
import re
import stat
import sys
import tarfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REFERENCE_PATH = ROOT / "config/proof_profiles/risc0_recursive_rebuild_reference.json"

REFERENCE_SCHEMA = "zenodex/risc0_recursive_rebuild_reference/v2"
REPORT_SCHEMA = "zenodex/risc0_recursive_rebuild_evidence_check/v2"
ARTIFACT_REPORT_SCHEMA = "zenodex/risc0_recursive_embedded_artifacts/v1"
MALFORMED_PROOF_REJECT_SCHEMA = "zenodex/risc0_recursive_malformed_proof_reject/v1"
MALFORMED_PROOF_MUTATION_KIND = "succinct_seal_word_xor_lsb_v1"
CRYPTOGRAPHIC_INVALID_ERROR = "receipt verification failed: verification indicates proof is invalid"
ACCEPTED_STATUS = "pinned_rebuild_artifact_match"
SDK_VERSION = "3.0.5"
WORKSPACE_IDENTITY_PREFIX = "zk/state_proof_risc0"
SOURCE_ROOT_ALGORITHM = "sha256(sorted(path_utf8 || nul || file_sha256_ascii || nul))"
PROGRAM_FORMAT = "risc0_program_binary_v1compat_v3"
EXPECTED_PROGRAM_NAMES = (
    "aggregate",
    "guest",
    "perps_np_leaf",
    "spot_leaf",
    "summary_leaf",
    "zusd_leaf",
)
EXPECTED_REFERENCE_CANONICAL_SHA256 = (
    "7c6016e43f80b1b1f4af15a34ed990085e8676edf9f95a2e5b48e65f0173839f"
)

EXPECTED_CLAIMS = {
    "accepted_status": ACCEPTED_STATUS,
    "build_command_authenticated": False,
    "build_environment_authenticated": False,
    "clean_target_verified": False,
    "cross_environment_reproducibility": False,
    "independent_rebuild": False,
    "production_ready": False,
    "public_claim_allowed": False,
    "public_replay": False,
    "reproducible_release": False,
    "settlement_authorization": False,
    "same_host_clean_rebuild": False,
    "source_archive_provenance_authenticated": False,
    "toolchain_execution_authenticated": False,
}

REFERENCE_KEYS = frozenset(
    {
        "artifact_report",
        "claims",
        "malformed_proof_reject",
        "positive_verify_request",
        "programs",
        "root_proof",
        "schema",
        "sdk_version",
        "source_compile",
        "static_verifier",
        "verified_transcript",
        "version",
        "workspace_archive",
    }
)
SOURCE_COMPILE_KEYS = frozenset(
    {
        "file_count",
        "files",
        "root_algorithm",
        "root_sha256",
        "workspace_identity_prefix",
    }
)
SOURCE_FILE_KEYS = frozenset({"path", "sha256", "size_bytes"})
PROGRAM_KEYS = frozenset(
    {
        "artifact",
        "generated_image_id_words",
        "image_id",
        "name",
        "program_bytes",
        "program_sha256",
    }
)
BLOB_KEYS = frozenset({"sha256", "size_bytes"})
MALFORMED_PROOF_REJECT_KEYS = frozenset(
    {
        "expected_error",
        "expected_process_exit_code",
        "mutated_root_proof",
        "mutation_kind",
        "reject_transcript",
        "schema",
        "seal_word_index",
        "seal_word_mutated",
        "seal_word_original",
        "source_root_proof_sha256",
        "verify_request",
    }
)
ROOT_PROOF_ARTIFACT_KEYS = frozenset(
    {"meta", "proof", "proof_type", "schema", "schema_version", "state_hash"}
)
VERIFY_REQUEST_KEYS = frozenset(
    {
        "proof",
        "recursive_expectations",
        "recursive_input",
        "schema",
        "schema_version",
        "state_hash",
    }
)
ARCHIVE_KEYS = frozenset({"format", "sha256", "size_bytes"})
ARTIFACT_REPORT_REF_KEYS = frozenset({"schema", "sha256", "size_bytes"})
ARTIFACT_REPORT_KEYS = frozenset({"method_count", "methods", "schema", "sdk_version"})
ARTIFACT_METHOD_KEYS = PROGRAM_KEYS | {"program_format"}

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
MAX_REFERENCE_BYTES = 1024 * 1024
MAX_SOURCE_FILE_BYTES = 16 * 1024 * 1024
MAX_SOURCE_TOTAL_BYTES = 64 * 1024 * 1024
MAX_SOURCE_FILES = 128
MAX_DISCOVERY_ENTRIES = 4096
MAX_DISCOVERY_DEPTH = 16
MAX_ARTIFACT_REPORT_BYTES = 1024 * 1024
MAX_JSON_DEPTH = 64
MAX_JSON_ITEMS = 20_000
MAX_RECEIPT_JSON_ITEMS = 100_000
MAX_JSON_INTEGER_CHARS = 20
MAX_RECEIPT_SEAL_WORDS = 65_536
MAX_PROGRAM_BYTES = 64 * 1024 * 1024
MAX_WORKSPACE_ARCHIVE_BYTES = 64 * 1024 * 1024
MAX_STATIC_VERIFIER_BYTES = 64 * 1024 * 1024
MAX_PROOF_BYTES = 32 * 1024 * 1024
MAX_TRANSCRIPT_BYTES = 4 * 1024 * 1024
MAX_VERIFY_REQUEST_BYTES = 4 * 1024 * 1024
READ_CHUNK_BYTES = 1024 * 1024


class EvidenceError(ValueError):
    """Stable rejection at the rebuild-evidence boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class FileDigest:
    raw: bytes
    sha256: str
    size_bytes: int


@dataclass(frozen=True)
class RebuildEvidencePaths:
    workspace_root: Path
    workspace_archive: Path
    artifact_report: Path
    program_directory: Path
    static_verifier: Path
    root_proof: Path
    positive_verify_request: Path
    verified_transcript: Path
    malformed_root_proof: Path
    malformed_verify_request: Path
    malformed_reject_transcript: Path


@dataclass(frozen=True)
class MalformedProofEvidenceFiles:
    positive_verify_request: FileDigest
    mutated_root_proof: FileDigest
    mutated_verify_request: FileDigest
    reject_transcript: FileDigest


def _reject(code: str, detail: str) -> EvidenceError:
    return EvidenceError(code, detail)


def _required_flag(name: str) -> int:
    value = getattr(os, name, None)
    if not isinstance(value, int):
        raise _reject("PLATFORM_UNSUPPORTED", f"missing {name}")
    return value


def _absolute_path(path: Path, *, code: str, label: str) -> Path:
    try:
        raw_path = os.fspath(path)
        if "\x00" in raw_path:
            raise ValueError("path contains NUL")
        os.fsencode(raw_path)
        return Path(os.path.abspath(raw_path))
    except (OSError, TypeError, UnicodeError, ValueError) as exc:
        raise _reject(code, label) from exc


def _close_descriptors(
    file_descriptor: int | None,
    directory_descriptors: list[int],
    *,
    label: str,
) -> None:
    first_error: OSError | None = None
    descriptors = ([] if file_descriptor is None else [file_descriptor]) + list(
        reversed(directory_descriptors)
    )
    for descriptor in descriptors:
        try:
            os.close(descriptor)
        except OSError as exc:
            if first_error is None:
                first_error = exc
    if first_error is not None:
        raise _reject("FILE_CLOSE_FAILED", label) from first_error


def _canonical_directory(path: Path, *, label: str) -> Path:
    absolute = _absolute_path(path, code="DIRECTORY_INVALID", label=label)
    try:
        resolved = absolute.resolve(strict=True)
    except (OSError, RuntimeError, UnicodeError, ValueError) as exc:
        raise _reject("DIRECTORY_INVALID", label) from exc
    if resolved != absolute:
        raise _reject("SYMLINK_FORBIDDEN", label)

    current = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        current /= part
        try:
            mode = os.lstat(current).st_mode
        except OSError as exc:
            raise _reject("DIRECTORY_INVALID", label) from exc
        if stat.S_ISLNK(mode):
            raise _reject("SYMLINK_FORBIDDEN", label)
    if not absolute.is_dir():
        raise _reject("DIRECTORY_INVALID", label)
    return absolute


def _canonical_relative_path(value: object, *, code: str, prefix: str = "") -> str:
    if not isinstance(value, str) or not value or "\x00" in value or "\\" in value:
        raise _reject(code, str(value))
    try:
        value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise _reject(code, "path must be ASCII") from exc
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise _reject(code, value)
    if path.as_posix() != value:
        raise _reject(code, value)
    if prefix and not value.startswith(prefix + "/"):
        raise _reject(code, value)
    return value


def _relative_parts(value: str) -> tuple[str, ...]:
    canonical = _canonical_relative_path(value, code="UNSAFE_PATH")
    return PurePosixPath(canonical).parts


def _read_regular_under_root(
    root: Path,
    relative_path: str,
    *,
    label: str,
    max_bytes: int,
) -> FileDigest:
    parts = _relative_parts(relative_path)
    directory_flags = (
        os.O_RDONLY
        | _required_flag("O_DIRECTORY")
        | _required_flag("O_NOFOLLOW")
        | getattr(os, "O_CLOEXEC", 0)
    )
    file_flags = os.O_RDONLY | _required_flag("O_NOFOLLOW") | getattr(os, "O_CLOEXEC", 0)
    directory_descriptors: list[int] = []
    file_descriptor: int | None = None
    try:
        directory_descriptors.append(os.open(root, directory_flags))
        current_descriptor = directory_descriptors[0]
        for part in parts[:-1]:
            entry = os.stat(part, dir_fd=current_descriptor, follow_symlinks=False)
            if stat.S_ISLNK(entry.st_mode):
                raise _reject("SYMLINK_FORBIDDEN", label)
            if not stat.S_ISDIR(entry.st_mode):
                raise _reject("FILE_PATH_INVALID", label)
            next_descriptor = os.open(
                part,
                directory_flags,
                dir_fd=current_descriptor,
            )
            directory_descriptors.append(next_descriptor)
            current_descriptor = next_descriptor

        leaf = parts[-1]
        entry = os.stat(leaf, dir_fd=current_descriptor, follow_symlinks=False)
        if stat.S_ISLNK(entry.st_mode):
            raise _reject("SYMLINK_FORBIDDEN", label)
        if not stat.S_ISREG(entry.st_mode):
            raise _reject("FILE_NOT_REGULAR", label)
        file_descriptor = os.open(leaf, file_flags, dir_fd=current_descriptor)
        before = os.fstat(file_descriptor)
        if (entry.st_dev, entry.st_ino) != (before.st_dev, before.st_ino):
            raise _reject("FILE_CHANGED_DURING_OPEN", label)
        if before.st_size > max_bytes:
            raise _reject("FILE_SIZE_LIMIT", label)

        digest = hashlib.sha256()
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(file_descriptor, min(READ_CHUNK_BYTES, max_bytes + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise _reject("FILE_SIZE_LIMIT", label)
            digest.update(chunk)
            chunks.append(chunk)

        after = os.fstat(file_descriptor)
        before_identity = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
        after_identity = (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
        if total != before.st_size or before_identity != after_identity:
            raise _reject("FILE_CHANGED_DURING_READ", label)
        return FileDigest(
            raw=b"".join(chunks),
            sha256=digest.hexdigest(),
            size_bytes=total,
        )
    except EvidenceError:
        raise
    except FileNotFoundError as exc:
        raise _reject("FILE_MISSING", label) from exc
    except OSError as exc:
        raise _reject("FILE_OPEN_FAILED", label) from exc
    finally:
        _close_descriptors(
            file_descriptor,
            directory_descriptors,
            label=label,
        )


def _read_regular_path(path: Path, *, label: str, max_bytes: int) -> FileDigest:
    absolute = _absolute_path(path, code="FILE_PATH_INVALID", label=label)
    parent = _canonical_directory(absolute.parent, label=f"{label}.parent")
    if not absolute.name:
        raise _reject("FILE_PATH_INVALID", label)
    return _read_regular_under_root(
        parent,
        absolute.name,
        label=label,
        max_bytes=max_bytes,
    )


def _parse_json(
    raw: bytes,
    *,
    label: str,
    require_canonical: bool = False,
    max_items: int = MAX_JSON_ITEMS,
) -> object:
    def reject_duplicates(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise _reject(f"{label}_JSON_DUPLICATE_KEY", key)
            result[key] = value
        return result

    def reject_float(value: str) -> object:
        raise _reject(f"{label}_JSON_FLOAT", value)

    def bounded_integer(value: str) -> int:
        if len(value.removeprefix("-")) > MAX_JSON_INTEGER_CHARS:
            raise _reject(f"{label}_JSON_INTEGER_LIMIT", str(MAX_JSON_INTEGER_CHARS))
        return int(value)

    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise _reject(f"{label}_JSON_ENCODING", "UTF-8 required") from exc
    try:
        parsed = json.loads(
            text,
            object_pairs_hook=reject_duplicates,
            parse_int=bounded_integer,
            parse_float=reject_float,
            parse_constant=reject_float,
        )
    except EvidenceError:
        raise
    except (json.JSONDecodeError, RecursionError) as exc:
        raise _reject(f"{label}_JSON_INVALID", str(exc)) from exc
    _validate_json_shape(parsed, label=label, max_items=max_items)
    if require_canonical and raw != _canonical_json_bytes(parsed) + b"\n":
        raise _reject(f"{label}_JSON_NONCANONICAL", "canonical JSON plus newline required")
    return parsed


def _validate_json_shape(
    value: object,
    *,
    label: str,
    max_items: int = MAX_JSON_ITEMS,
) -> None:
    stack: list[tuple[object, int]] = [(value, 1)]
    items = 0
    while stack:
        current, depth = stack.pop()
        items += 1
        if items > max_items:
            raise _reject(f"{label}_JSON_ITEM_LIMIT", str(max_items))
        if depth > MAX_JSON_DEPTH:
            raise _reject(f"{label}_JSON_DEPTH_LIMIT", str(MAX_JSON_DEPTH))
        if isinstance(current, Mapping):
            for key, child in current.items():
                if not isinstance(key, str):
                    raise _reject(f"{label}_JSON_KEY_TYPE", str(type(key)))
                stack.append((child, depth + 1))
        elif isinstance(current, list):
            stack.extend((child, depth + 1) for child in current)
        elif current is not None and not isinstance(current, (bool, int, str)):
            raise _reject(f"{label}_JSON_VALUE_TYPE", str(type(current)))


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")


def reference_canonical_sha256(reference: Mapping[str, Any]) -> str:
    """Return the semantic digest used to authenticate a reference manifest."""

    return hashlib.sha256(_canonical_json_bytes(reference)).hexdigest()


def _mapping(value: object, *, code: str, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise _reject(code, f"{label} must be an object")
    return value


def _exact_keys(value: Mapping[str, Any], expected: frozenset[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = ",".join(sorted(expected - actual))
        extra = ",".join(sorted(actual - expected))
        raise _reject("REFERENCE_SCHEMA", f"{label}:missing={missing}:extra={extra}")


def _positive_int(value: object, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise _reject("REFERENCE_SCHEMA", f"{label} must be a positive integer")
    return value


def _nonnegative_int(value: object, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise _reject("REFERENCE_SCHEMA", f"{label} must be a nonnegative integer")
    return value


def _u32(value: object, *, label: str) -> int:
    parsed = _nonnegative_int(value, label=label)
    if parsed > 0xFFFF_FFFF:
        raise _reject("REFERENCE_SCHEMA", f"{label} exceeds u32")
    return parsed


def _sha256(value: object, *, label: str) -> str:
    if not isinstance(value, str) or SHA256_RE.fullmatch(value) is None:
        raise _reject("REFERENCE_SCHEMA", f"{label} must be lowercase SHA-256")
    return value


def _validate_blob_reference(value: object, *, label: str) -> Mapping[str, Any]:
    blob = _mapping(value, code="REFERENCE_SCHEMA", label=label)
    _exact_keys(blob, BLOB_KEYS, label=label)
    _sha256(blob.get("sha256"), label=f"{label}.sha256")
    _positive_int(blob.get("size_bytes"), label=f"{label}.size_bytes")
    return blob


def _validate_malformed_proof_reference(value: object) -> Mapping[str, Any]:
    reject = _mapping(
        value,
        code="REFERENCE_SCHEMA",
        label="malformed_proof_reject",
    )
    _exact_keys(
        reject,
        MALFORMED_PROOF_REJECT_KEYS,
        label="malformed_proof_reject",
    )
    if reject.get("schema") != MALFORMED_PROOF_REJECT_SCHEMA:
        raise _reject("REFERENCE_SCHEMA", "malformed proof reject schema mismatch")
    if reject.get("mutation_kind") != MALFORMED_PROOF_MUTATION_KIND:
        raise _reject("REFERENCE_SCHEMA", "malformed proof mutation kind mismatch")
    if reject.get("expected_error") != CRYPTOGRAPHIC_INVALID_ERROR:
        raise _reject("REFERENCE_SCHEMA", "malformed proof expected error mismatch")
    if reject.get("expected_process_exit_code") != 0:
        raise _reject(
            "REFERENCE_SCHEMA",
            "handled verifier reject must record process exit code zero",
        )
    _sha256(
        reject.get("source_root_proof_sha256"),
        label="malformed_proof_reject.source_root_proof_sha256",
    )
    index = _nonnegative_int(
        reject.get("seal_word_index"),
        label="malformed_proof_reject.seal_word_index",
    )
    if index >= MAX_RECEIPT_SEAL_WORDS:
        raise _reject("REFERENCE_SCHEMA", "malformed proof seal index exceeds bound")
    original = _u32(
        reject.get("seal_word_original"),
        label="malformed_proof_reject.seal_word_original",
    )
    mutated = _u32(
        reject.get("seal_word_mutated"),
        label="malformed_proof_reject.seal_word_mutated",
    )
    if mutated != (original ^ 1):
        raise _reject("REFERENCE_SCHEMA", "seal mutation must flip exactly the low bit")
    _validate_blob_reference(
        reject.get("mutated_root_proof"),
        label="malformed_proof_reject.mutated_root_proof",
    )
    _validate_blob_reference(
        reject.get("verify_request"),
        label="malformed_proof_reject.verify_request",
    )
    _validate_blob_reference(
        reject.get("reject_transcript"),
        label="malformed_proof_reject.reject_transcript",
    )
    return reject


def _validate_programs(value: object) -> list[Mapping[str, Any]]:
    if not isinstance(value, list) or len(value) != len(EXPECTED_PROGRAM_NAMES):
        raise _reject("REFERENCE_PROGRAMS", "expected six programs")
    programs: list[Mapping[str, Any]] = []
    observed_names: list[str] = []
    observed_artifacts: set[str] = set()
    for index, raw_program in enumerate(value):
        program = _mapping(
            raw_program,
            code="REFERENCE_PROGRAMS",
            label=f"programs[{index}]",
        )
        _exact_keys(program, PROGRAM_KEYS, label=f"programs[{index}]")
        name = program.get("name")
        artifact = program.get("artifact")
        if not isinstance(name, str) or not isinstance(artifact, str):
            raise _reject("REFERENCE_PROGRAMS", f"programs[{index}] names")
        _canonical_relative_path(artifact, code="REFERENCE_PROGRAMS")
        if "/" in artifact or artifact in observed_artifacts:
            raise _reject("REFERENCE_PROGRAMS", f"programs[{index}].artifact")
        observed_names.append(name)
        observed_artifacts.add(artifact)
        _positive_int(program.get("program_bytes"), label=f"programs[{index}].program_bytes")
        _sha256(program.get("program_sha256"), label=f"programs[{index}].program_sha256")
        image_id = _sha256(program.get("image_id"), label=f"programs[{index}].image_id")
        words = program.get("generated_image_id_words")
        if not isinstance(words, list) or len(words) != 8:
            raise _reject("REFERENCE_PROGRAMS", f"programs[{index}].generated_image_id_words")
        encoded = bytearray()
        for word in words:
            if not isinstance(word, int) or isinstance(word, bool) or not 0 <= word <= 0xFFFF_FFFF:
                raise _reject("REFERENCE_PROGRAMS", f"programs[{index}].image word")
            encoded.extend(word.to_bytes(4, "little"))
        if encoded.hex() != image_id:
            raise _reject("REFERENCE_PROGRAMS", f"programs[{index}].image encoding")
        programs.append(program)
    if tuple(observed_names) != EXPECTED_PROGRAM_NAMES:
        raise _reject("REFERENCE_PROGRAMS", "program order or names mismatch")
    return programs


def _validate_source_compile(value: object) -> Mapping[str, Any]:
    source = _mapping(value, code="REFERENCE_SOURCE", label="source_compile")
    _exact_keys(source, SOURCE_COMPILE_KEYS, label="source_compile")
    if source.get("root_algorithm") != SOURCE_ROOT_ALGORITHM:
        raise _reject("REFERENCE_SOURCE", "root algorithm mismatch")
    if source.get("workspace_identity_prefix") != WORKSPACE_IDENTITY_PREFIX:
        raise _reject("REFERENCE_SOURCE", "workspace identity prefix mismatch")
    _sha256(source.get("root_sha256"), label="source_compile.root_sha256")
    raw_files = source.get("files")
    if not isinstance(raw_files, list) or not 0 < len(raw_files) <= MAX_SOURCE_FILES:
        raise _reject("REFERENCE_SOURCE", "invalid source file list")
    if source.get("file_count") != len(raw_files):
        raise _reject("REFERENCE_SOURCE", "source file_count mismatch")

    observed_paths: list[str] = []
    for index, raw_file in enumerate(raw_files):
        entry = _mapping(
            raw_file,
            code="REFERENCE_SOURCE",
            label=f"source_compile.files[{index}]",
        )
        _exact_keys(entry, SOURCE_FILE_KEYS, label=f"source_compile.files[{index}]")
        path = _canonical_relative_path(
            entry.get("path"),
            code="REFERENCE_SOURCE",
            prefix=WORKSPACE_IDENTITY_PREFIX,
        )
        observed_paths.append(path)
        size = _positive_int(
            entry.get("size_bytes"),
            label=f"source_compile.files[{index}].size_bytes",
        )
        if size > MAX_SOURCE_FILE_BYTES:
            raise _reject("REFERENCE_SOURCE", f"source file too large: {path}")
        _sha256(entry.get("sha256"), label=f"source_compile.files[{index}].sha256")
    if observed_paths != sorted(observed_paths) or len(observed_paths) != len(set(observed_paths)):
        raise _reject("REFERENCE_SOURCE", "source paths must be sorted and unique")
    return source


def validate_reference(reference: object) -> Mapping[str, Any]:
    manifest = _mapping(reference, code="REFERENCE_SCHEMA", label="reference")
    _exact_keys(manifest, REFERENCE_KEYS, label="reference")
    if manifest.get("schema") != REFERENCE_SCHEMA or manifest.get("version") != 2:
        raise _reject("REFERENCE_SCHEMA", "schema or version mismatch")
    if manifest.get("sdk_version") != SDK_VERSION:
        raise _reject("REFERENCE_SCHEMA", "sdk version mismatch")
    if manifest.get("claims") != EXPECTED_CLAIMS:
        raise _reject("REFERENCE_CLAIMS", "claim scope mismatch")

    _validate_source_compile(manifest.get("source_compile"))
    _validate_programs(manifest.get("programs"))
    _validate_blob_reference(manifest.get("root_proof"), label="root_proof")
    _validate_blob_reference(
        manifest.get("positive_verify_request"),
        label="positive_verify_request",
    )
    malformed = _validate_malformed_proof_reference(manifest.get("malformed_proof_reject"))
    root_proof = _mapping(
        manifest.get("root_proof"),
        code="REFERENCE_SCHEMA",
        label="root_proof",
    )
    if malformed.get("source_root_proof_sha256") != root_proof.get("sha256"):
        raise _reject("REFERENCE_SCHEMA", "malformed proof source root mismatch")
    _validate_blob_reference(manifest.get("static_verifier"), label="static_verifier")
    _validate_blob_reference(manifest.get("verified_transcript"), label="verified_transcript")

    archive = _mapping(
        manifest.get("workspace_archive"),
        code="REFERENCE_SCHEMA",
        label="workspace_archive",
    )
    _exact_keys(archive, ARCHIVE_KEYS, label="workspace_archive")
    if archive.get("format") != "normalized_gnu_tar_v1":
        raise _reject("REFERENCE_SCHEMA", "workspace archive format mismatch")
    _sha256(archive.get("sha256"), label="workspace_archive.sha256")
    _positive_int(archive.get("size_bytes"), label="workspace_archive.size_bytes")

    report = _mapping(
        manifest.get("artifact_report"),
        code="REFERENCE_SCHEMA",
        label="artifact_report",
    )
    _exact_keys(report, ARTIFACT_REPORT_REF_KEYS, label="artifact_report")
    if report.get("schema") != ARTIFACT_REPORT_SCHEMA:
        raise _reject("REFERENCE_SCHEMA", "artifact report schema mismatch")
    _sha256(report.get("sha256"), label="artifact_report.sha256")
    _positive_int(report.get("size_bytes"), label="artifact_report.size_bytes")
    return manifest


def _decode_succinct_receipt(
    proof: Mapping[str, Any],
    *,
    label: str,
) -> tuple[bytes, Mapping[str, Any], list[object]]:
    encoded = proof.get("proof")
    if not isinstance(encoded, str) or not encoded:
        raise _reject("MALFORMED_PROOF_EVIDENCE", f"{label}.proof must be base64")
    try:
        raw = base64.b64decode(encoded.encode("ascii"), validate=True)
    except (UnicodeEncodeError, binascii.Error, ValueError) as exc:
        raise _reject("MALFORMED_PROOF_EVIDENCE", f"{label}.proof base64") from exc
    if base64.b64encode(raw).decode("ascii") != encoded:
        raise _reject("MALFORMED_PROOF_EVIDENCE", f"{label}.proof base64 noncanonical")
    if not raw or len(raw) > MAX_PROOF_BYTES:
        raise _reject("MALFORMED_PROOF_EVIDENCE", f"{label}.receipt size")
    receipt = _mapping(
        _parse_json(
            raw,
            label=f"{label}_RECEIPT",
            max_items=MAX_RECEIPT_JSON_ITEMS,
        ),
        code="MALFORMED_PROOF_EVIDENCE",
        label=f"{label}.receipt",
    )
    inner = _mapping(
        receipt.get("inner"),
        code="MALFORMED_PROOF_EVIDENCE",
        label=f"{label}.receipt.inner",
    )
    if set(inner) != {"Succinct"}:
        raise _reject("MALFORMED_PROOF_EVIDENCE", f"{label}.receipt kind")
    succinct = _mapping(
        inner.get("Succinct"),
        code="MALFORMED_PROOF_EVIDENCE",
        label=f"{label}.receipt.inner.Succinct",
    )
    seal = succinct.get("seal")
    if not isinstance(seal, list) or not 0 < len(seal) <= MAX_RECEIPT_SEAL_WORDS:
        raise _reject("MALFORMED_PROOF_EVIDENCE", f"{label}.receipt seal")
    return raw, receipt, seal


def _parse_bound_proof_pair(
    root_proof: FileDigest,
    mutated_root_proof: FileDigest,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    root = _mapping(
        _parse_json(root_proof.raw, label="ROOT_PROOF"),
        code="MALFORMED_PROOF_EVIDENCE",
        label="root proof",
    )
    mutated = _mapping(
        _parse_json(
            mutated_root_proof.raw,
            label="MUTATED_ROOT_PROOF",
            require_canonical=True,
        ),
        code="MALFORMED_PROOF_EVIDENCE",
        label="mutated root proof",
    )
    _exact_keys(root, ROOT_PROOF_ARTIFACT_KEYS, label="root proof")
    _exact_keys(mutated, ROOT_PROOF_ARTIFACT_KEYS, label="mutated root proof")
    root_without_receipt = dict(root)
    mutated_without_receipt = dict(mutated)
    root_without_receipt.pop("proof", None)
    mutated_without_receipt.pop("proof", None)
    if root_without_receipt != mutated_without_receipt:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "proof envelope fields changed")
    return root, mutated


def _validate_single_seal_word_mutation(
    root: Mapping[str, Any],
    mutated: Mapping[str, Any],
    mutation: Mapping[str, Any],
) -> None:
    root_receipt_raw, root_receipt, root_seal = _decode_succinct_receipt(
        root,
        label="root proof",
    )
    mutated_receipt_raw, mutated_receipt, mutated_seal = _decode_succinct_receipt(
        mutated,
        label="mutated root proof",
    )
    index = mutation.get("seal_word_index")
    if not isinstance(index, int) or isinstance(index, bool) or not 0 <= index < len(root_seal):
        raise _reject("MALFORMED_PROOF_EVIDENCE", "seal word index out of range")
    original_word = mutation.get("seal_word_original")
    mutated_word = mutation.get("seal_word_mutated")
    if root_seal[index] != original_word or mutated_seal[index] != mutated_word:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "seal mutation words mismatch")
    expected_receipt = copy.deepcopy(root_receipt)
    expected_inner = _mapping(
        expected_receipt.get("inner"),
        code="MALFORMED_PROOF_EVIDENCE",
        label="expected receipt inner",
    )
    expected_succinct = _mapping(
        expected_inner.get("Succinct"),
        code="MALFORMED_PROOF_EVIDENCE",
        label="expected receipt Succinct",
    )
    expected_seal = expected_succinct.get("seal")
    if not isinstance(expected_seal, list):
        raise _reject("MALFORMED_PROOF_EVIDENCE", "expected receipt seal")
    expected_seal[index] = mutated_word
    if expected_receipt != mutated_receipt:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "mutation changed more than one seal word")
    byte_differences = sum(
        left != right for left, right in zip(root_receipt_raw, mutated_receipt_raw, strict=False)
    )
    if len(root_receipt_raw) != len(mutated_receipt_raw) or byte_differences != 1:
        raise _reject(
            "MALFORMED_PROOF_EVIDENCE",
            "encoded receipt must differ by exactly one byte",
        )


def _validate_verify_request_parity(
    root: Mapping[str, Any],
    mutated: Mapping[str, Any],
    positive_verify_request: FileDigest,
    mutated_verify_request: FileDigest,
) -> None:
    positive_request = _mapping(
        _parse_json(positive_verify_request.raw, label="POSITIVE_VERIFY_REQUEST"),
        code="MALFORMED_PROOF_EVIDENCE",
        label="positive verify request",
    )
    malformed_request = _mapping(
        _parse_json(
            mutated_verify_request.raw,
            label="MALFORMED_VERIFY_REQUEST",
            require_canonical=True,
        ),
        code="MALFORMED_PROOF_EVIDENCE",
        label="malformed verify request",
    )
    _exact_keys(positive_request, VERIFY_REQUEST_KEYS, label="positive verify request")
    _exact_keys(malformed_request, VERIFY_REQUEST_KEYS, label="malformed verify request")
    if positive_request.get("proof") != root:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "positive request root proof mismatch")
    if malformed_request.get("proof") != mutated:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "malformed request proof mismatch")
    expected_request = dict(copy.deepcopy(positive_request))
    expected_request["proof"] = mutated
    if expected_request != malformed_request:
        raise _reject(
            "MALFORMED_PROOF_EVIDENCE",
            "verify request changed outside the proof artifact",
        )


def _validate_reject_transcript(
    mutation: Mapping[str, Any],
    reject_transcript: FileDigest,
) -> None:
    transcript = _parse_json(
        reject_transcript.raw,
        label="MALFORMED_REJECT_TRANSCRIPT",
        require_canonical=True,
    )
    expected_transcript = {
        "process_exit_code": mutation.get("expected_process_exit_code"),
        "response": {
            "error": mutation.get("expected_error"),
            "ok": False,
        },
        "stderr": "",
    }
    if transcript != expected_transcript:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "cryptographic reject transcript mismatch")


def _validate_malformed_proof_evidence(
    reference: Mapping[str, Any],
    *,
    root_proof: FileDigest,
    positive_verify_request: FileDigest,
    mutated_root_proof: FileDigest,
    mutated_verify_request: FileDigest,
    reject_transcript: FileDigest,
) -> None:
    mutation = _mapping(
        reference.get("malformed_proof_reject"),
        code="REFERENCE_SCHEMA",
        label="malformed_proof_reject",
    )
    if mutation.get("source_root_proof_sha256") != root_proof.sha256:
        raise _reject("MALFORMED_PROOF_EVIDENCE", "source root proof digest mismatch")
    root, mutated = _parse_bound_proof_pair(root_proof, mutated_root_proof)
    _validate_single_seal_word_mutation(root, mutated, mutation)
    _validate_verify_request_parity(
        root,
        mutated,
        positive_verify_request,
        mutated_verify_request,
    )
    _validate_reject_transcript(mutation, reject_transcript)


def _load_malformed_proof_evidence_files(
    reference: Mapping[str, Any],
    paths: RebuildEvidencePaths,
) -> MalformedProofEvidenceFiles:
    positive_request = _check_expected_file(
        paths.positive_verify_request,
        _mapping(
            reference["positive_verify_request"],
            code="REFERENCE_SCHEMA",
            label="positive_verify_request",
        ),
        label="positive_verify_request",
        mismatch_prefix="POSITIVE_VERIFY_REQUEST",
        max_bytes=MAX_VERIFY_REQUEST_BYTES,
    )
    malformed = _mapping(
        reference["malformed_proof_reject"],
        code="REFERENCE_SCHEMA",
        label="malformed_proof_reject",
    )
    proof = _check_expected_file(
        paths.malformed_root_proof,
        _mapping(
            malformed["mutated_root_proof"],
            code="REFERENCE_SCHEMA",
            label="malformed_proof_reject.mutated_root_proof",
        ),
        label="malformed_root_proof",
        mismatch_prefix="MALFORMED_ROOT_PROOF",
        max_bytes=MAX_PROOF_BYTES,
    )
    request = _check_expected_file(
        paths.malformed_verify_request,
        _mapping(
            malformed["verify_request"],
            code="REFERENCE_SCHEMA",
            label="malformed_proof_reject.verify_request",
        ),
        label="malformed_verify_request",
        mismatch_prefix="MALFORMED_VERIFY_REQUEST",
        max_bytes=MAX_VERIFY_REQUEST_BYTES,
    )
    transcript = _check_expected_file(
        paths.malformed_reject_transcript,
        _mapping(
            malformed["reject_transcript"],
            code="REFERENCE_SCHEMA",
            label="malformed_proof_reject.reject_transcript",
        ),
        label="malformed_reject_transcript",
        mismatch_prefix="MALFORMED_REJECT_TRANSCRIPT",
        max_bytes=MAX_TRANSCRIPT_BYTES,
    )
    return MalformedProofEvidenceFiles(positive_request, proof, request, transcript)


def _discover_source_paths(workspace: Path) -> list[str]:
    directory_flags = (
        os.O_RDONLY
        | _required_flag("O_DIRECTORY")
        | _required_flag("O_NOFOLLOW")
        | getattr(os, "O_CLOEXEC", 0)
    )
    root_descriptor = os.open(workspace, directory_flags)
    entries_seen = 0
    discovered: list[str] = []

    def visit(descriptor: int, relative_parts: tuple[str, ...], depth: int) -> None:
        nonlocal entries_seen
        if depth > MAX_DISCOVERY_DEPTH:
            raise _reject("SOURCE_DISCOVERY_LIMIT", "depth")
        try:
            entries = sorted(os.scandir(descriptor), key=lambda item: item.name)
        except OSError as exc:
            raise _reject("SOURCE_DISCOVERY_FAILED", "/".join(relative_parts)) from exc
        for entry in entries:
            entries_seen += 1
            if entries_seen > MAX_DISCOVERY_ENTRIES:
                raise _reject("SOURCE_DISCOVERY_LIMIT", "entries")
            relative = "/".join((*relative_parts, entry.name))
            if entry.is_symlink():
                raise _reject("SYMLINK_FORBIDDEN", relative)
            if entry.is_dir(follow_symlinks=False):
                if entry.name == "target":
                    raise _reject("SOURCE_TARGET_PRESENT", relative)
                child = os.open(entry.name, directory_flags, dir_fd=descriptor)
                try:
                    visit(child, (*relative_parts, entry.name), depth + 1)
                finally:
                    os.close(child)
                continue
            if not entry.is_file(follow_symlinks=False):
                raise _reject("SOURCE_ENTRY_INVALID", relative)
            discovered.append(f"{WORKSPACE_IDENTITY_PREFIX}/{relative}")

    try:
        visit(root_descriptor, (), 0)
    finally:
        os.close(root_descriptor)
    return discovered


def _source_root(rows: Sequence[Mapping[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in sorted(rows, key=lambda item: str(item["path"])):
        digest.update(str(row["path"]).encode("ascii"))
        digest.update(b"\x00")
        digest.update(str(row["sha256"]).encode("ascii"))
        digest.update(b"\x00")
    return digest.hexdigest()


def _check_source_workspace(
    workspace_root: Path,
    source_reference: Mapping[str, Any],
) -> tuple[str, list[dict[str, Any]]]:
    workspace = _canonical_directory(workspace_root, label="workspace_root")
    expected_files = source_reference["files"]
    if not isinstance(expected_files, list):
        raise _reject("REFERENCE_SOURCE", "files must be a list")
    expected_by_path = {
        str(entry["path"]): entry for entry in expected_files if isinstance(entry, Mapping)
    }
    actual_paths = _discover_source_paths(workspace)
    missing = sorted(set(expected_by_path) - set(actual_paths))
    extra = sorted(set(actual_paths) - set(expected_by_path))
    if missing:
        raise _reject("SOURCE_FILE_MISSING", ",".join(missing))
    if extra:
        raise _reject("SOURCE_FILE_EXTRA", ",".join(extra))

    rows: list[dict[str, Any]] = []
    total_bytes = 0
    for canonical_path in sorted(actual_paths):
        relative = canonical_path.removeprefix(WORKSPACE_IDENTITY_PREFIX + "/")
        expected = expected_by_path[canonical_path]
        actual = _read_regular_under_root(
            workspace,
            relative,
            label=canonical_path,
            max_bytes=MAX_SOURCE_FILE_BYTES,
        )
        if actual.size_bytes != expected["size_bytes"]:
            raise _reject("SOURCE_SIZE_MISMATCH", canonical_path)
        if actual.sha256 != expected["sha256"]:
            raise _reject("SOURCE_SHA256_MISMATCH", canonical_path)
        total_bytes += actual.size_bytes
        if total_bytes > MAX_SOURCE_TOTAL_BYTES:
            raise _reject("SOURCE_TOTAL_SIZE_LIMIT", str(total_bytes))
        rows.append(
            {
                "path": canonical_path,
                "sha256": actual.sha256,
                "size_bytes": actual.size_bytes,
            }
        )
    root = _source_root(rows)
    if root != source_reference["root_sha256"]:
        raise _reject("SOURCE_ROOT_MISMATCH", root)
    return root, rows


def _check_expected_file(
    path: Path,
    reference: Mapping[str, Any],
    *,
    label: str,
    mismatch_prefix: str,
    max_bytes: int,
) -> FileDigest:
    actual = _read_regular_path(path, label=label, max_bytes=max_bytes)
    if actual.size_bytes != reference["size_bytes"]:
        raise _reject(f"{mismatch_prefix}_SIZE_MISMATCH", label)
    if actual.sha256 != reference["sha256"]:
        raise _reject(f"{mismatch_prefix}_SHA256_MISMATCH", label)
    return actual


def _check_workspace_archive_sources(
    raw: bytes,
    source_rows: Sequence[Mapping[str, Any]],
) -> str:
    expected: dict[str, Mapping[str, Any]] = {}
    prefix = WORKSPACE_IDENTITY_PREFIX + "/"
    for row in source_rows:
        canonical = str(row["path"])
        if not canonical.startswith(prefix):
            raise _reject("WORKSPACE_ARCHIVE_SOURCE_PATH", canonical)
        expected[canonical.removeprefix(prefix)] = row

    observed: dict[str, tuple[str, int]] = {}
    names: set[str] = set()
    total_bytes = 0
    try:
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
            members = archive.getmembers()
            if len(members) > MAX_DISCOVERY_ENTRIES:
                raise _reject("WORKSPACE_ARCHIVE_ENTRY_LIMIT", str(len(members)))
            for member in members:
                name = member.name
                if name in names:
                    raise _reject("WORKSPACE_ARCHIVE_DUPLICATE", name)
                names.add(name)
                if name == ".":
                    relative = ""
                elif name.startswith("./"):
                    relative = name[2:]
                else:
                    raise _reject("WORKSPACE_ARCHIVE_PATH", name)
                if relative:
                    parsed = PurePosixPath(relative)
                    if (
                        parsed.is_absolute()
                        or any(part in ("", ".", "..") for part in parsed.parts)
                        or parsed.as_posix() != relative
                    ):
                        raise _reject("WORKSPACE_ARCHIVE_PATH", name)
                if (
                    member.uid != 0
                    or member.gid != 0
                    or member.mtime != 0
                    or member.uname
                    or member.gname
                    or member.pax_headers
                ):
                    raise _reject("WORKSPACE_ARCHIVE_METADATA", name)
                if member.isdir():
                    if member.size != 0 or member.mode != 0o775:
                        raise _reject("WORKSPACE_ARCHIVE_METADATA", name)
                    continue
                if not member.isfile() or not relative or member.mode != 0o664:
                    raise _reject("WORKSPACE_ARCHIVE_ENTRY_TYPE", name)
                if member.size < 0 or member.size > MAX_SOURCE_FILE_BYTES:
                    raise _reject("WORKSPACE_ARCHIVE_FILE_LIMIT", name)
                stream = archive.extractfile(member)
                if stream is None:
                    raise _reject("WORKSPACE_ARCHIVE_READ", name)
                payload = stream.read(MAX_SOURCE_FILE_BYTES + 1)
                if len(payload) != member.size:
                    raise _reject("WORKSPACE_ARCHIVE_READ", name)
                total_bytes += len(payload)
                if total_bytes > MAX_SOURCE_TOTAL_BYTES:
                    raise _reject("WORKSPACE_ARCHIVE_TOTAL_LIMIT", str(total_bytes))
                observed[relative] = (hashlib.sha256(payload).hexdigest(), len(payload))
    except EvidenceError:
        raise
    except (OSError, tarfile.TarError) as exc:
        raise _reject("WORKSPACE_ARCHIVE_INVALID", "tar parse failed") from exc

    missing = sorted(set(expected) - set(observed))
    extra = sorted(set(observed) - set(expected))
    if missing:
        raise _reject("WORKSPACE_ARCHIVE_SOURCE_MISSING", missing[0])
    if extra:
        raise _reject("WORKSPACE_ARCHIVE_SOURCE_EXTRA", extra[0])
    for relative, row in expected.items():
        observed_sha256, observed_size = observed[relative]
        if observed_size != row["size_bytes"]:
            raise _reject("WORKSPACE_ARCHIVE_SOURCE_SIZE_MISMATCH", relative)
        if observed_sha256 != row["sha256"]:
            raise _reject("WORKSPACE_ARCHIVE_SOURCE_SHA256_MISMATCH", relative)
    return _source_root(source_rows)


def _program_directory_names(program_directory: Path) -> tuple[Path, list[str]]:
    directory = _canonical_directory(program_directory, label="program_directory")
    try:
        entries = sorted(os.scandir(directory), key=lambda item: item.name)
    except OSError as exc:
        raise _reject("PROGRAM_DIRECTORY_INVALID", "cannot scan") from exc
    names: list[str] = []
    for entry in entries:
        if entry.is_symlink():
            raise _reject("SYMLINK_FORBIDDEN", f"program_directory/{entry.name}")
        if not entry.is_file(follow_symlinks=False):
            raise _reject("PROGRAM_DIRECTORY_ENTRY_UNEXPECTED", entry.name)
        names.append(entry.name)
    return directory, names


def _check_programs(
    program_directory: Path,
    program_reference: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    directory, actual_names = _program_directory_names(program_directory)
    expected_by_artifact = {str(program["artifact"]): program for program in program_reference}
    missing = sorted(set(expected_by_artifact) - set(actual_names))
    extra = sorted(set(actual_names) - set(expected_by_artifact))
    if missing:
        raise _reject("PROGRAM_ARTIFACT_MISSING", ",".join(missing))
    if extra:
        raise _reject("PROGRAM_ARTIFACT_EXTRA", ",".join(extra))

    checked: list[dict[str, Any]] = []
    for artifact in sorted(actual_names):
        expected = expected_by_artifact[artifact]
        actual = _read_regular_under_root(
            directory,
            artifact,
            label=f"program.{artifact}",
            max_bytes=MAX_PROGRAM_BYTES,
        )
        if actual.size_bytes != expected["program_bytes"]:
            raise _reject("PROGRAM_SIZE_MISMATCH", artifact)
        if actual.sha256 != expected["program_sha256"]:
            raise _reject("PROGRAM_SHA256_MISMATCH", artifact)
        checked.append(
            {
                "artifact": artifact,
                "image_id": expected["image_id"],
                "name": expected["name"],
                "program_bytes": actual.size_bytes,
                "program_sha256": actual.sha256,
            }
        )
    checked.sort(key=lambda item: EXPECTED_PROGRAM_NAMES.index(str(item["name"])))
    return checked


def _validate_artifact_report(
    raw: bytes,
    reference_programs: Sequence[Mapping[str, Any]],
) -> None:
    parsed = _parse_json(raw, label="ARTIFACT_REPORT", require_canonical=True)
    report = _mapping(parsed, code="ARTIFACT_REPORT_SCHEMA", label="artifact report")
    if set(report) != ARTIFACT_REPORT_KEYS:
        raise _reject("ARTIFACT_REPORT_SCHEMA", "top-level keys mismatch")
    if report.get("schema") != ARTIFACT_REPORT_SCHEMA or report.get("sdk_version") != SDK_VERSION:
        raise _reject("ARTIFACT_REPORT_SCHEMA", "schema or SDK mismatch")
    methods = report.get("methods")
    if not isinstance(methods, list) or report.get("method_count") != len(methods):
        raise _reject("ARTIFACT_REPORT_SCHEMA", "method count mismatch")
    if len(methods) != len(reference_programs):
        raise _reject("ARTIFACT_REPORT_MISMATCH", "method cardinality")
    for index, (raw_method, expected) in enumerate(zip(methods, reference_programs, strict=True)):
        method = _mapping(
            raw_method,
            code="ARTIFACT_REPORT_SCHEMA",
            label=f"methods[{index}]",
        )
        if set(method) != ARTIFACT_METHOD_KEYS:
            raise _reject("ARTIFACT_REPORT_SCHEMA", f"methods[{index}] keys")
        expected_method = {**expected, "program_format": PROGRAM_FORMAT}
        if dict(method) != expected_method:
            raise _reject("ARTIFACT_REPORT_MISMATCH", str(expected.get("name")))


def _failure_report(error: EvidenceError, report: dict[str, Any]) -> dict[str, Any]:
    return {
        **report,
        "error_codes": [error.code],
        "errors": [str(error)],
        "ok": False,
        "same_host_clean_rebuild": False,
        "status": "rejected",
    }


def _base_report() -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "claim_scope": ACCEPTED_STATUS,
        "evidence_basis": (
            "code_pinned_reference_candidate_byte_equality_and_malformed_proof_semantics"
        ),
        "independent_image_id_rerun": {
            "attempted": False,
            "matched": False,
            "reason": "no hash-pinned r0vm was supplied for execution",
        },
        "build_command_authenticated": False,
        "build_environment_authenticated": False,
        "clean_target_verified": False,
        "cross_environment_reproducibility": False,
        "independent_rebuild": False,
        "malformed_proof_reject_verified": False,
        "production_ready": False,
        "public_claim_allowed": False,
        "public_replay": False,
        "pinned_rebuild_artifact_match": False,
        "reproducible_release": False,
        "same_host_clean_rebuild": False,
        "settlement_authorization": False,
        "source_archive_provenance_authenticated": False,
        "toolchain_execution_authenticated": False,
    }


def check_risc0_recursive_rebuild_evidence(
    paths: RebuildEvidencePaths,
) -> dict[str, Any]:
    """Validate one candidate against the compiled-in artifact reference."""

    report = _base_report()
    try:
        reference_file = _read_regular_path(
            REFERENCE_PATH,
            label="reference",
            max_bytes=MAX_REFERENCE_BYTES,
        )
        parsed_reference = _parse_json(reference_file.raw, label="REFERENCE")
        reference = validate_reference(parsed_reference)
        actual_reference_digest = reference_canonical_sha256(reference)
        report["reference_canonical_sha256"] = actual_reference_digest
        if actual_reference_digest != EXPECTED_REFERENCE_CANONICAL_SHA256:
            raise _reject("REFERENCE_DIGEST_MISMATCH", actual_reference_digest)

        source_reference = _mapping(
            reference["source_compile"],
            code="REFERENCE_SOURCE",
            label="source_compile",
        )
        source_root, source_rows = _check_source_workspace(paths.workspace_root, source_reference)
        report["source_compile_root_sha256"] = source_root
        report["source_file_count"] = len(source_rows)

        archive_reference = _mapping(
            reference["workspace_archive"],
            code="REFERENCE_SCHEMA",
            label="workspace_archive",
        )
        archive = _check_expected_file(
            paths.workspace_archive,
            archive_reference,
            label="workspace_archive",
            mismatch_prefix="WORKSPACE_ARCHIVE",
            max_bytes=MAX_WORKSPACE_ARCHIVE_BYTES,
        )
        report["workspace_archive_sha256"] = archive.sha256
        report["workspace_archive_source_root_sha256"] = _check_workspace_archive_sources(
            archive.raw,
            source_rows,
        )

        raw_programs = reference["programs"]
        if not isinstance(raw_programs, list):
            raise _reject("REFERENCE_PROGRAMS", "programs must be a list")
        program_references = [
            _mapping(program, code="REFERENCE_PROGRAMS", label="program")
            for program in raw_programs
        ]
        artifact_report_reference = _mapping(
            reference["artifact_report"],
            code="REFERENCE_SCHEMA",
            label="artifact_report",
        )
        artifact_report = _check_expected_file(
            paths.artifact_report,
            artifact_report_reference,
            label="artifact_report",
            mismatch_prefix="ARTIFACT_REPORT",
            max_bytes=MAX_ARTIFACT_REPORT_BYTES,
        )
        _validate_artifact_report(artifact_report.raw, program_references)
        report["artifact_report_sha256"] = artifact_report.sha256
        report["programs"] = _check_programs(paths.program_directory, program_references)

        verifier_reference = _mapping(
            reference["static_verifier"],
            code="REFERENCE_SCHEMA",
            label="static_verifier",
        )
        verifier = _check_expected_file(
            paths.static_verifier,
            verifier_reference,
            label="static_verifier",
            mismatch_prefix="STATIC_VERIFIER",
            max_bytes=MAX_STATIC_VERIFIER_BYTES,
        )
        report["static_verifier_sha256"] = verifier.sha256

        proof_reference = _mapping(
            reference["root_proof"],
            code="REFERENCE_SCHEMA",
            label="root_proof",
        )
        proof = _check_expected_file(
            paths.root_proof,
            proof_reference,
            label="root_proof",
            mismatch_prefix="ROOT_PROOF",
            max_bytes=MAX_PROOF_BYTES,
        )
        report["root_proof_sha256"] = proof.sha256

        transcript_reference = _mapping(
            reference["verified_transcript"],
            code="REFERENCE_SCHEMA",
            label="verified_transcript",
        )
        transcript = _check_expected_file(
            paths.verified_transcript,
            transcript_reference,
            label="verified_transcript",
            mismatch_prefix="VERIFIED_TRANSCRIPT",
            max_bytes=MAX_TRANSCRIPT_BYTES,
        )
        report["verified_transcript_sha256"] = transcript.sha256

        malformed = _load_malformed_proof_evidence_files(reference, paths)
        _validate_malformed_proof_evidence(
            reference,
            root_proof=proof,
            positive_verify_request=malformed.positive_verify_request,
            mutated_root_proof=malformed.mutated_root_proof,
            mutated_verify_request=malformed.mutated_verify_request,
            reject_transcript=malformed.reject_transcript,
        )
        report["positive_verify_request_sha256"] = malformed.positive_verify_request.sha256
        report["malformed_root_proof_sha256"] = malformed.mutated_root_proof.sha256
        report["malformed_verify_request_sha256"] = malformed.mutated_verify_request.sha256
        report["malformed_reject_transcript_sha256"] = malformed.reject_transcript.sha256
        report["malformed_proof_reject_verified"] = True
    except EvidenceError as error:
        return _failure_report(error, report)

    return {
        **report,
        "error_codes": [],
        "errors": [],
        "ok": True,
        "pinned_rebuild_artifact_match": True,
        "status": ACCEPTED_STATUS,
    }


def _print_human(report: Mapping[str, Any]) -> None:
    if report.get("ok") is True:
        print(
            f"ok: {ACCEPTED_STATUS} {report['source_compile_root_sha256']}; "
            "command and environment provenance unauthenticated; "
            "cross-environment and release claims false"
        )
        return
    print("error: recursive RISC0 rebuild evidence rejected", file=sys.stderr)
    for error in report.get("errors", []):
        print(f"  - {error}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace-root", type=Path, required=True)
    parser.add_argument("--workspace-archive", type=Path, required=True)
    parser.add_argument("--artifact-report", type=Path, required=True)
    parser.add_argument("--program-directory", type=Path, required=True)
    parser.add_argument("--static-verifier", type=Path, required=True)
    parser.add_argument("--root-proof", type=Path, required=True)
    parser.add_argument("--positive-verify-request", type=Path, required=True)
    parser.add_argument("--verified-transcript", type=Path, required=True)
    parser.add_argument("--malformed-root-proof", type=Path, required=True)
    parser.add_argument("--malformed-verify-request", type=Path, required=True)
    parser.add_argument("--malformed-reject-transcript", type=Path, required=True)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    report = check_risc0_recursive_rebuild_evidence(
        RebuildEvidencePaths(
            workspace_root=args.workspace_root,
            workspace_archive=args.workspace_archive,
            artifact_report=args.artifact_report,
            program_directory=args.program_directory,
            static_verifier=args.static_verifier,
            root_proof=args.root_proof,
            positive_verify_request=args.positive_verify_request,
            verified_transcript=args.verified_transcript,
            malformed_root_proof=args.malformed_root_proof,
            malformed_verify_request=args.malformed_verify_request,
            malformed_reject_transcript=args.malformed_reject_transcript,
        )
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
