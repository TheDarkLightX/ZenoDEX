"""Bounded byte and source checks for temporary ZRPF structural-tree evidence."""

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
    / "docs/research/ZRPF_V3_STRUCTURAL_TREE_TEMPORARY_LOCAL_EVIDENCE_20260710.json"
)
REPORT_SCHEMA = "zenodex/zrpf_v3_structural_tree_temporary_local_evidence_check/v1"
EXPECTED_SCHEMA = "zenodex/zrpf_v3_structural_tree_temporary_local_evidence/v1"

# Reviewed after the current verifier-only replay and negative controls passed.
EXPECTED_MANIFEST_CANONICAL_SHA256 = (
    "e28b80256092df69dcc201c39b51fc81340da1b1c8aba858e6b9e49c001e4a8a"
)
MAX_MANIFEST_BYTES = 256 * 1024
MAX_SOURCE_BYTES = 16 * 1024 * 1024
MAX_RECEIPT_BYTES = 16 * 1024 * 1024
MAX_TRANSCRIPT_BYTES = 64 * 1024
HEX_DIGEST = re.compile(r"[0-9a-f]{64}")
ABSOLUTE_POSIX_PATH = re.compile(r"(?:^|[\s\"'(])/(?:[^/\s]+/)*[^/\s]+")
ABSOLUTE_WINDOWS_PATH = re.compile(r"(?:^|[\s\"'(])[A-Za-z]:[\\/]")

# A public checker must not embed hashes of private low-entropy names because
# guessed-name dictionaries could confirm them. Publication runs apply their
# private denylist outside the repository. Tests inject synthetic token hashes
# to preserve the deterministic redaction-path regression.
PRIVATE_NAME_TOKEN_HASHES: frozenset[str] = frozenset()


@dataclass(frozen=True)
class SourceClosureContext:
    root: Path
    hasher: Any
    errors: list[str]


def canonical_sha256(document: Any) -> str:
    encoded = json.dumps(
        document,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def is_digest(value: Any) -> bool:
    return isinstance(value, str) and HEX_DIGEST.fullmatch(value) is not None


def is_safe_relative_path(value: Any) -> bool:
    if not isinstance(value, str) or not value or "\\" in value:
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and ".." not in path.parts and str(path) == value


def walk_strings(value: Any, label: str = "manifest") -> list[tuple[str, str]]:
    found: list[tuple[str, str]] = []
    if isinstance(value, str):
        found.append((label, value))
    elif isinstance(value, dict):
        for key, child in value.items():
            found.append((f"{label}.<key>", str(key)))
            found.extend(walk_strings(child, f"{label}.{key}"))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(walk_strings(child, f"{label}[{index}]"))
    return found


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


def validate_source_closure(
    closure: Any,
    repo_root: Path,
    errors: list[str],
) -> int:
    if not isinstance(closure, dict):
        return 0
    files = closure.get("files")
    if not isinstance(files, list):
        return 0
    if type(closure.get("file_count")) is not int or closure.get("file_count") != len(files):
        errors.append("source_closure.file_count mismatch")
    if closure.get("finalized") is not True or not is_digest(closure.get("sha256")):
        errors.append("source closure is not finalized")

    raw_paths = [row.get("path") if isinstance(row, dict) else None for row in files]
    if any(not isinstance(path, str) for path in raw_paths):
        errors.append("every source closure path must be a string")
        return 0
    paths = [path for path in raw_paths if isinstance(path, str)]
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        errors.append("source closure paths must be unique and sorted")

    closure_hasher = hashlib.sha256()
    context = SourceClosureContext(
        root=repo_root.resolve(),
        hasher=closure_hasher,
        errors=errors,
    )
    checked = 0
    for index, row in enumerate(files):
        checked += _validate_source_row(row, index, context)
    if closure_hasher.hexdigest() != closure.get("sha256"):
        errors.append("source closure SHA-256 mismatch")
    return checked


def _validate_source_row(
    row: Any,
    index: int,
    context: SourceClosureContext,
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
    if not isinstance(expected_sha256, str) or not is_digest(expected_sha256):
        context.errors.append(f"source_closure.files[{index}].sha256 is invalid")
        return 0

    context.hasher.update(role.encode("utf-8"))
    context.hasher.update(b"\0")
    context.hasher.update(relative.encode("utf-8"))
    context.hasher.update(b"\0")
    context.hasher.update(expected_sha256.encode("ascii"))
    context.hasher.update(b"\n")
    return _verify_file(
        context.root,
        relative,
        expected_sha256,
        MAX_SOURCE_BYTES,
        "source",
        context.errors,
    )


def _resolve_regular_file(root: Path, relative: str, label: str) -> tuple[Path | None, list[str]]:
    errors: list[str] = []
    if not is_safe_relative_path(relative):
        return None, [f"{label} path is not a safe relative path"]
    try:
        resolved_root = root.resolve(strict=True)
        candidate = resolved_root / relative
        resolved = candidate.resolve(strict=True)
        if (
            root.is_symlink()
            or candidate.is_symlink()
            or not resolved.is_relative_to(resolved_root)
            or not resolved.is_file()
        ):
            errors.append(f"{label} path escapes its root or is not a regular file")
            return None, errors
    except OSError:
        return None, [f"{label} read failed"]
    return resolved, errors


def _verify_file(
    root: Path,
    relative: str,
    expected_sha256: str,
    max_bytes: int,
    label: str,
    errors: list[str],
) -> int:
    path, path_errors = _resolve_regular_file(root, relative, label)
    errors.extend(path_errors)
    if path is None:
        return 0
    try:
        size = path.stat().st_size
        if size <= 0 or size > max_bytes:
            errors.append(f"{label} byte length is empty or exceeds the cap")
            return 0
        actual = sha256_file(path)
    except OSError:
        errors.append(f"{label} read failed")
        return 0
    if actual != expected_sha256:
        errors.append(f"{label} SHA-256 mismatch: {relative}")
        return 0
    return 1


def verify_receipt_artifact(
    artifact_root: Path,
    node: dict[str, Any],
) -> list[str]:
    errors: list[str] = []
    relative = node.get("artifact_path")
    receipt = node.get("receipt")
    journal = node.get("journal")
    if not isinstance(receipt, dict) or not isinstance(journal, dict):
        return ["node receipt or journal facts are malformed"]
    if not isinstance(relative, str):
        return ["receipt artifact path is not a string"]
    path, path_errors = _resolve_regular_file(artifact_root, relative, "receipt artifact")
    errors.extend(path_errors)
    if path is None:
        return errors
    try:
        raw = path.read_bytes()
    except OSError:
        return errors + ["receipt artifact read failed"]
    if len(raw) != receipt.get("size_bytes"):
        errors.append(f"receipt artifact size mismatch: {relative}")
    if len(raw) > MAX_RECEIPT_BYTES:
        errors.append(f"receipt artifact exceeds byte cap: {relative}")
        return errors
    if hashlib.sha256(raw).hexdigest() != receipt.get("sha256"):
        errors.append(f"receipt artifact SHA-256 mismatch: {relative}")
        return errors

    try:
        document = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_json_object,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        errors.append(f"receipt artifact JSON rejected: {exc}")
        return errors
    if not isinstance(document, dict) or set(document) != {"inner", "journal", "metadata"}:
        errors.append(f"receipt artifact outer fields mismatch: {relative}")
        return errors
    inner = document.get("inner")
    if not isinstance(inner, dict) or set(inner) != {"Succinct"}:
        errors.append(f"receipt artifact is not structurally labeled Succinct: {relative}")
    journal_object = document.get("journal")
    if not isinstance(journal_object, dict) or set(journal_object) != {"bytes"}:
        errors.append(f"receipt artifact journal envelope mismatch: {relative}")
        return errors
    journal_values = journal_object.get("bytes")
    if (
        not isinstance(journal_values, list)
        or any(type(value) is not int or value < 0 or value > 255 for value in journal_values)
    ):
        errors.append(f"receipt artifact journal bytes are invalid: {relative}")
        return errors
    journal_bytes = bytes(journal_values)
    if len(journal_bytes) != journal.get("size_bytes"):
        errors.append(f"receipt journal size mismatch: {relative}")
    if hashlib.sha256(journal_bytes).hexdigest() != journal.get("sha256"):
        errors.append(f"receipt journal SHA-256 mismatch: {relative}")
    return errors


def verify_transcript_artifact(
    artifact_root: Path,
    transcript: dict[str, Any],
    label: str,
) -> list[str]:
    errors: list[str] = []
    relative = transcript.get("artifact_path")
    if not isinstance(relative, str):
        return [f"{label} path is not a string"]
    path, path_errors = _resolve_regular_file(artifact_root, relative, label)
    errors.extend(path_errors)
    if path is None:
        return errors
    try:
        raw = path.read_bytes()
    except OSError:
        return errors + [f"{label} read failed"]
    if len(raw) != transcript.get("size_bytes"):
        errors.append(f"{label} size mismatch")
    if not raw or len(raw) > MAX_TRANSCRIPT_BYTES:
        errors.append(f"{label} byte length is empty or exceeds the cap")
    if hashlib.sha256(raw).hexdigest() != transcript.get("sha256"):
        errors.append(f"{label} SHA-256 mismatch")
    return errors


def _unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number: {value}")
