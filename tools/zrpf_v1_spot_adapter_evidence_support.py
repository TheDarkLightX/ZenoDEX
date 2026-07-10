"""Schema constants and bounded byte checks for ZRPF adapter evidence."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = (
    REPO_ROOT
    / "docs/research/ZRPF_V1_SPOT_ADAPTER_TEMPORARY_LOCAL_EVIDENCE_20260710.json"
)
REPORT_SCHEMA = "zenodex/zrpf_v1_spot_adapter_temporary_local_evidence_check/v1"
EXPECTED_SCHEMA = "zenodex/zrpf_v1_spot_adapter_temporary_local_evidence/v1"

# Reviewed after one stable guest rebuild, verification run, and source snapshot.
EXPECTED_FINAL_CANONICAL_SHA256 = (
    "7e4c1f9b23ac6e62836a94ff99de344f66aef7c53d859ef98521138c26dde791"
)
MAX_MANIFEST_BYTES = 128 * 1024
MAX_SOURCE_BYTES = 16 * 1024 * 1024
HEX_DIGEST = re.compile(r"[0-9a-f]{64}")
ABSOLUTE_POSIX_PATH = re.compile(r"(?:^|[\s\"'(])/(?:[^/\s]+/)*[^/\s]+")
ABSOLUTE_WINDOWS_PATH = re.compile(r"(?:^|[\s\"'(])[A-Za-z]:[\\/]")

# A public checker must not embed hashes of private low-entropy names because
# guessed-name dictionaries could confirm them. Publication runs apply their
# private denylist outside the repository. Tests inject synthetic token hashes
# to preserve the deterministic redaction-path regression.
PRIVATE_NAME_TOKEN_HASHES: frozenset[str] = frozenset()

EXPECTED_FIELDS: dict[tuple[str, ...], set[str]] = {
    (): {
        "schema",
        "version",
        "evidence_date",
        "scope",
        "status",
        "sanitization",
        "build_scope",
        "toolchain",
        "adapter",
        "source_receipt",
        "receipt_verification",
        "negative_controls",
        "evidence_build_sources",
        "verification_sources",
        "claims",
        "non_claims",
    },
    ("sanitization",): {
        "absolute_paths_included",
        "private_project_names_included",
        "public_safe_record",
    },
    ("build_scope",): {
        "compiler_visible_path_stable",
        "cross_host_reproduced",
        "release_authority",
    },
    ("toolchain",): {
        "risc0_zkvm_version",
        "rustc_version",
        "rustc_commit",
        "cargo_version",
        "cargo_commit",
    },
    ("adapter",): {
        "profile",
        "source_kind",
        "image_id",
        "image_id_words",
        "elf",
        "receipt",
        "journal",
    },
    ("adapter", "elf"): {"sha256", "size_bytes"},
    ("adapter", "receipt"): {"kind", "sha256", "size_bytes"},
    ("adapter", "journal"): {"protocol_hash", "sha256"},
    ("source_receipt",): {
        "proof_type",
        "image_id",
        "proof_artifact_sha256",
        "proof_artifact_size_bytes",
        "receipt_sha256",
    },
    ("receipt_verification",): {
        "performed_by",
        "risc0_zkvm_version",
        "source_receipt_verified",
        "adapter_receipt_verified",
        "python_checker_verifies_seal",
        "python_checker_scope",
    },
    ("evidence_build_sources",): {
        "scope",
        "finalized",
        "definition",
        "file_count",
        "sha256",
        "files",
    },
    ("verification_sources",): {
        "scope",
        "finalized",
        "definition",
        "file_count",
        "sha256",
        "files",
    },
    ("claims",): {
        "rust_harness_verified_receipt_cryptography",
        "temporary_local_computational_integrity_evidence",
        "release_backed",
        "public_replay",
        "recursive_aggregate_evidence",
        "full_zenodex_semantic_composition",
        "ledger_or_settlement_admission_authority",
    },
}
EXPECTED_CONTROL_FIELDS = (
    {"id", "passed"},
    {"id", "passed"},
    {
        "id",
        "passed",
        "control_receipt_sha256",
        "substituted_adapter_image_id",
    },
)
EXPECTED_SOURCE_FIELDS = {"role", "path", "sha256"}
EXPECTED_NON_CLAIMS = [
    "pending_rebuild_no_current_adapter_evidence_claim",
    "no_release_or_cross_host_reproducibility_claim",
    "no_public_replay_claim",
    "no_recursive_aggregate_claim",
    "no_full_zenodex_semantic_composition_claim",
    "no_zenoledger_or_settlement_admission_claim",
]
EXPECTED_ARTIFACTS = {
    "adapter_receipt": {
        "sha256": "cc65e529bd881b331531aa615298e46471e31a36d3b8d57af2290031969dda61",
        "size_bytes": 593505,
    },
    "source_proof": {
        "sha256": "4ce7db31e6ae5e5af53b4ef67fb0cd6ebb1dcae9cf05ee9f73b4511c10db20b9",
        "size_bytes": 784225,
    },
    "elf": {
        "sha256": "545c832d0dbe54ed2379f7fa423e490177cf4e3475c208ce5edf2d6bd4cb9797",
        "size_bytes": 255660,
    },
}


@dataclass(frozen=True)
class _SourceClosureContext:
    root: Path
    hasher: Any
    allow_pending: bool
    errors: list[str]


def validate_redaction(document: dict[str, Any], errors: list[str]) -> None:
    for label, value in walk_strings(document):
        if (
            ABSOLUTE_POSIX_PATH.search(value)
            or ABSOLUTE_WINDOWS_PATH.search(value)
            or value.startswith("\\\\")
            or "file://" in value.casefold()
        ):
            errors.append(f"absolute path detected at {label}")
        for token in re.findall(r"[a-z0-9]+", value.casefold()):
            token_hash = hashlib.sha256(token.encode("utf-8")).hexdigest()
            if token_hash in PRIVATE_NAME_TOKEN_HASHES:
                errors.append(f"private project name token detected at {label}")


def walk_strings(value: Any, label: str = "manifest") -> list[tuple[str, str]]:
    found: list[tuple[str, str]] = []
    if isinstance(value, str):
        found.append((label, value))
    elif isinstance(value, dict):
        for key, child in value.items():
            found.extend(walk_strings(child, f"{label}.{key}"))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(walk_strings(child, f"{label}[{index}]"))
    return found


def validate_source_closure(
    closure: Any,
    repo_root: Path,
    errors: list[str],
    *,
    allow_pending: bool,
) -> int:
    if not isinstance(closure, dict):
        return 0
    files = closure.get("files")
    if not isinstance(files, list):
        return 0
    _validate_closure_header(closure, files, allow_pending, errors)
    if not _paths_are_canonical(files, errors):
        return 0

    checked = 0
    closure_hasher = hashlib.sha256()
    context = _SourceClosureContext(
        root=repo_root.resolve(),
        hasher=closure_hasher,
        allow_pending=allow_pending,
        errors=errors,
    )
    for index, row in enumerate(files):
        checked += _validate_source_row(row, index, context)
    if not allow_pending and closure_hasher.hexdigest() != closure.get("sha256"):
        errors.append("source closure SHA-256 mismatch")
    return checked


def _validate_closure_header(
    closure: dict[str, Any],
    files: list[Any],
    allow_pending: bool,
    errors: list[str],
) -> None:
    if type(closure.get("file_count")) is not int or closure.get("file_count") != len(files):
        errors.append("source_closure.file_count mismatch")
    finalized = closure.get("finalized")
    if allow_pending:
        if finalized is not False or closure.get("sha256") is not None:
            errors.append("pending source closure must remain unfinalized")
    elif finalized is not True or not is_digest(closure.get("sha256")):
        errors.append("final source closure is incomplete")


def _paths_are_canonical(files: list[Any], errors: list[str]) -> bool:
    raw_paths = [row.get("path") if isinstance(row, dict) else None for row in files]
    if any(not isinstance(path, str) for path in raw_paths):
        errors.append("every source closure path must be a string")
        return False
    paths = [path for path in raw_paths if isinstance(path, str)]
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        errors.append("source closure paths must be unique and sorted")
    return True


def _validate_source_row(
    row: Any,
    index: int,
    context: _SourceClosureContext,
) -> int:
    if not isinstance(row, dict):
        return 0
    role = row.get("role")
    relative = row.get("path")
    expected_sha256 = row.get("sha256")
    if not isinstance(role, str) or not role:
        context.errors.append(f"source_closure.files[{index}].role is invalid")
        return 0
    if not isinstance(relative, str) or not is_safe_relative_path(relative):
        context.errors.append(f"source_closure.files[{index}].path is not a safe relative path")
        return 0
    if context.allow_pending and expected_sha256 is None:
        return 0
    if not isinstance(expected_sha256, str) or not is_digest(expected_sha256):
        context.errors.append(f"source_closure.files[{index}].sha256 is invalid")
        return 0
    _update_closure_hash(context.hasher, role, relative, expected_sha256)
    return _verify_source_file(
        context.root,
        relative,
        expected_sha256,
        context.errors,
    )


def _update_closure_hash(hasher: Any, role: str, relative: str, digest: str) -> None:
    hasher.update(role.encode("utf-8"))
    hasher.update(b"\0")
    hasher.update(relative.encode("utf-8"))
    hasher.update(b"\0")
    hasher.update(digest.encode("ascii"))
    hasher.update(b"\n")


def _verify_source_file(
    root: Path,
    relative: str,
    expected_sha256: str,
    errors: list[str],
) -> int:
    candidate = root / relative
    try:
        resolved = candidate.resolve(strict=True)
        if not resolved.is_relative_to(root) or candidate.is_symlink() or not resolved.is_file():
            errors.append(f"source path escapes the repository or is not a regular file: {relative}")
            return 0
        if resolved.stat().st_size > MAX_SOURCE_BYTES:
            errors.append(f"source file exceeds byte cap: {relative}")
            return 0
        actual_sha256 = sha256_file(resolved)
    except OSError:
        errors.append(f"source file read failed: {relative}")
        return 0
    if actual_sha256 != expected_sha256:
        errors.append(f"source SHA-256 mismatch: {relative}")
        return 0
    return 1


def is_safe_relative_path(value: Any) -> bool:
    if not isinstance(value, str) or not value or "\\" in value:
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and ".." not in path.parts and str(path) == value


def verify_optional_artifact(path: Path, label: str) -> list[str]:
    expected = EXPECTED_ARTIFACTS[label]
    if expected["sha256"] is None or expected["size_bytes"] is None:
        return [f"{label} expectation is pending final rebuild"]
    try:
        if path.is_symlink() or not path.is_file():
            return [f"{label} is not a regular file"]
        if path.stat().st_size != expected["size_bytes"]:
            return [f"{label} size mismatch"]
        actual_sha256 = sha256_file(path)
    except OSError:
        return [f"{label} read failed"]
    if actual_sha256 != expected["sha256"]:
        return [f"{label} SHA-256 mismatch"]
    return []


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def canonical_sha256(document: Any) -> str:
    encoded = json.dumps(
        document,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def is_digest(value: Any) -> bool:
    return isinstance(value, str) and HEX_DIGEST.fullmatch(value) is not None
