#!/usr/bin/env python3
"""Audit every reviewed ZenoDEX RISC0 lockfile under one exact policy."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_POLICY = ROOT / "config/proof_profiles/risc0_dependency_audit_policy_v2.json"
DEFAULT_ADVISORY_DB = Path.home() / ".cargo/advisory-db"
POLICY_SCHEMA = "zenodex/risc0-dependency-audit-policy/v2"
REPORT_SCHEMA = "zenodex/risc0-dependency-audit-check/v2"
EXPECTED_CLAIM_SCOPE = "experimental_risc0_dependency_audit_only"
MAX_POLICY_BYTES = 1024 * 1024
MAX_LOCK_BYTES = 32 * 1024 * 1024
MAX_REFERENCE_BYTES = 2 * 1024 * 1024
MAX_SCANNED_SOURCE_BYTES = 16 * 1024 * 1024
MAX_AUDIT_OUTPUT_BYTES = 16 * 1024 * 1024
AUDIT_TIMEOUT_SECONDS = 180
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_REVISION_RE = re.compile(r"^[0-9a-f]{40}$")


@dataclass(frozen=True)
class WorkspaceSpec:
    workspace_id: str
    relative_path: str
    lockfile: str


@dataclass(frozen=True)
class UnsoundBoundary:
    lockfile_sha256: str
    reference_path: str
    reference_file_sha256: str
    source_roots: tuple[str, ...]


REVIEWED_WORKSPACES: tuple[WorkspaceSpec, ...] = (
    WorkspaceSpec(
        "state_proof_risc0",
        "zk/state_proof_risc0",
        "zk/state_proof_risc0/Cargo.lock",
    ),
    WorkspaceSpec(
        "recursive_stark_v2_risc0",
        "zk/recursive_stark_v2_risc0",
        "zk/recursive_stark_v2_risc0/Cargo.lock",
    ),
    WorkspaceSpec(
        "zrpf_risc0",
        "zk/zrpf_risc0",
        "zk/zrpf_risc0/Cargo.lock",
    ),
    WorkspaceSpec(
        "zrpf_protocol",
        "zk/zrpf_protocol",
        "zk/zrpf_protocol/Cargo.lock",
    ),
)
RISC0_WORKSPACE_IDS = frozenset(spec.workspace_id for spec in REVIEWED_WORKSPACES[:3])
DispositionKey = tuple[str, str, str, str, str]
PERMITTED_DISPOSITION_KEYS: frozenset[DispositionKey] = frozenset(
    (workspace_id, "vulnerability", advisory_id, package, version)
    for workspace_id in RISC0_WORKSPACE_IDS
    for advisory_id, package, version in (
        ("RUSTSEC-2023-0071", "rsa", "0.9.10"),
        ("RUSTSEC-2025-0055", "tracing-subscriber", "0.2.25"),
    )
) | frozenset(
    {
        (
            "state_proof_risc0",
            "unsound",
            "RUSTSEC-2026-0190",
            "anyhow",
            "1.0.100",
        ),
        (
            "recursive_stark_v2_risc0",
            "unsound",
            "RUSTSEC-2026-0190",
            "anyhow",
            "1.0.102",
        ),
    }
)
KNOWN_WARNING_CATEGORIES = frozenset({"unmaintained", "unsound", "yanked"})
DENIED_WARNING_CATEGORIES = frozenset({"unsound", "yanked"})
UNSOUND_BOUNDARIES: Mapping[str, UnsoundBoundary] = {
    "state_proof_risc0": UnsoundBoundary(
        lockfile_sha256=(
            "f7d854a75aea4d9626719587bb8870d67a7891c9dfb93a28842df09bf934c4b1"
        ),
        reference_path="config/proof_profiles/risc0_recursive_rebuild_reference.json",
        reference_file_sha256=(
            "ab6d7e6752d120571c14a76ef981f789179b25a4a989687edd04574cd1740283"
        ),
        source_roots=("zk/state_proof_risc0",),
    ),
    "recursive_stark_v2_risc0": UnsoundBoundary(
        lockfile_sha256=(
            "8fb6d7f66790920e44278d56e33cff1c344dd15ca6c3f96f4abf2a727a7e9f23"
        ),
        reference_path=(
            "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json"
        ),
        reference_file_sha256=(
            "fe044c8fdef2f8e32e788c8d8d07bf2b82a77666bfb186f86e43f827db0dffec"
        ),
        source_roots=(
            "zk/recursive_stark_v2_risc0",
            "zk/state_proof_risc0/shared",
        ),
    ),
}
POLICY_FIELDS = frozenset(
    {
        "cargo_audit_version",
        "claim_scope",
        "dispositions",
        "nonclaims",
        "policy_id",
        "production_authority",
        "schema",
        "warning_policy",
        "workspaces",
    }
)
DISPOSITION_FIELDS = frozenset(
    {
        "advisory_id",
        "category",
        "dependency_path",
        "no_raw_untrusted_terminal_logging",
        "no_secret_input",
        "package",
        "production_authority",
        "reachability",
        "scope",
        "version",
        "workspace_id",
    }
)
UNSOUND_DISPOSITION_FIELDS = frozenset(
    {
        "affected_function",
        "affected_function_callers_found",
        "lockfile_sha256",
        "new_proof_generation_authority",
        "reference_file_sha256",
        "reference_path",
        "retained_identity_only",
    }
)


class AuditInputError(ValueError):
    """A local policy, lockfile, database, or cargo-audit report is unsafe."""


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise AuditInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(value: str) -> object:
    raise AuditInputError(f"floating-point JSON value is forbidden: {value}")


def _parse_json(raw: bytes, *, label: str) -> Mapping[str, Any]:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AuditInputError(f"{label} is invalid JSON: {exc}") from exc
    if not isinstance(value, Mapping):
        raise AuditInputError(f"{label} must be an object")
    return value


def _read_regular(path: Path, *, max_bytes: int, label: str) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise AuditInputError("O_NOFOLLOW is required for dependency-audit inputs")
    descriptor: int | None = None
    try:
        descriptor = os.open(path, flags | nofollow)
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise AuditInputError(f"{label} is not a regular file")
        if before.st_size > max_bytes:
            raise AuditInputError(f"{label} exceeds size limit")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, max_bytes + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise AuditInputError(f"{label} exceeds size limit")
            chunks.append(chunk)
        after = os.fstat(descriptor)
    except OSError as exc:
        raise AuditInputError(f"cannot safely read {label}") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    before_identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    after_identity = (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if total != before.st_size or before_identity != after_identity:
        raise AuditInputError(f"{label} changed while it was read")
    return b"".join(chunks)


def _exact_fields(value: object, expected: frozenset[str], *, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or set(value) != expected:
        raise AuditInputError(f"{label} fields mismatch")
    return value


def _nonempty_ascii(value: object, *, label: str, max_chars: int = 1024) -> str:
    if not isinstance(value, str) or not value or len(value) > max_chars:
        raise AuditInputError(f"{label} must be a bounded nonempty string")
    try:
        value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise AuditInputError(f"{label} must contain ASCII only") from exc
    return value


def _workspace_rows() -> list[dict[str, str]]:
    return [
        {"id": spec.workspace_id, "lockfile": spec.lockfile, "path": spec.relative_path}
        for spec in REVIEWED_WORKSPACES
    ]


def _validate_policy_header(policy: Mapping[str, Any]) -> None:
    _exact_fields(policy, POLICY_FIELDS, label="policy")
    if policy.get("schema") != POLICY_SCHEMA:
        raise AuditInputError("policy schema mismatch")
    _nonempty_ascii(policy.get("policy_id"), label="policy id", max_chars=128)
    if policy.get("claim_scope") != EXPECTED_CLAIM_SCOPE:
        raise AuditInputError("policy claim scope mismatch")
    if policy.get("production_authority") is not False:
        raise AuditInputError("policy production authority must remain false")
    version = _nonempty_ascii(
        policy.get("cargo_audit_version"), label="cargo-audit version", max_chars=32
    )
    if version != "0.22.1":
        raise AuditInputError("cargo-audit version policy mismatch")
    if policy.get("workspaces") != _workspace_rows():
        raise AuditInputError("reviewed workspace registry mismatch")
    warning_policy = _exact_fields(
        policy.get("warning_policy"),
        frozenset({"denied_categories", "recorded_categories"}),
        label="warning policy",
    )
    if warning_policy.get("denied_categories") != sorted(DENIED_WARNING_CATEGORIES):
        raise AuditInputError("denied warning categories mismatch")
    if warning_policy.get("recorded_categories") != ["unmaintained"]:
        raise AuditInputError("recorded warning categories mismatch")
    nonclaims = policy.get("nonclaims")
    if not isinstance(nonclaims, list) or not nonclaims:
        raise AuditInputError("policy nonclaims must be a nonempty array")
    for index, nonclaim in enumerate(nonclaims):
        _nonempty_ascii(nonclaim, label=f"policy nonclaim[{index}]", max_chars=128)


def _validate_disposition(
    raw: object,
    *,
    index: int,
) -> DispositionKey:
    if not isinstance(raw, Mapping):
        raise AuditInputError(f"disposition[{index}] fields mismatch")
    category = _nonempty_ascii(
        raw.get("category"), label=f"disposition[{index}] category", max_chars=32
    )
    expected_fields = (
        DISPOSITION_FIELDS | UNSOUND_DISPOSITION_FIELDS
        if category == "unsound"
        else DISPOSITION_FIELDS
    )
    row = _exact_fields(raw, expected_fields, label=f"disposition[{index}]")
    workspace_id = _nonempty_ascii(
        row.get("workspace_id"), label=f"disposition[{index}] workspace", max_chars=64
    )
    advisory_id = _nonempty_ascii(
        row.get("advisory_id"), label=f"disposition[{index}] advisory", max_chars=64
    )
    package = _nonempty_ascii(
        row.get("package"), label=f"disposition[{index}] package", max_chars=128
    )
    package_version = _nonempty_ascii(
        row.get("version"), label=f"disposition[{index}] version", max_chars=64
    )
    if category not in {"vulnerability", "unsound"}:
        raise AuditInputError("disposition category is not permitted")
    if row.get("scope") != EXPECTED_CLAIM_SCOPE:
        raise AuditInputError("disposition scope mismatch")
    if row.get("no_secret_input") is not True:
        raise AuditInputError("disposition must prohibit secret input")
    if row.get("no_raw_untrusted_terminal_logging") is not True:
        raise AuditInputError("disposition must prohibit raw untrusted terminal logging")
    if row.get("production_authority") is not False:
        raise AuditInputError("disposition production authority must remain false")
    _nonempty_ascii(row.get("dependency_path"), label=f"disposition[{index}] dependency path")
    _nonempty_ascii(row.get("reachability"), label=f"disposition[{index}] reachability")
    key = (workspace_id, category, advisory_id, package, package_version)
    if key not in PERMITTED_DISPOSITION_KEYS:
        raise AuditInputError("dependency-audit disposition identity is not permitted")
    if category == "unsound":
        boundary = UNSOUND_BOUNDARIES.get(workspace_id)
        if boundary is None:
            raise AuditInputError("unsound disposition workspace is not governed")
        if row.get("affected_function") != "anyhow::Error::downcast_mut":
            raise AuditInputError("unsound disposition affected function mismatch")
        if row.get("affected_function_callers_found") is not False:
            raise AuditInputError("unsound disposition must record zero affected callers")
        if row.get("new_proof_generation_authority") is not False:
            raise AuditInputError("unsound disposition cannot authorize new proof generation")
        if row.get("retained_identity_only") is not True:
            raise AuditInputError("unsound disposition must remain retained-identity-only")
        if row.get("lockfile_sha256") != boundary.lockfile_sha256:
            raise AuditInputError("unsound disposition lockfile identity mismatch")
        if row.get("reference_path") != boundary.reference_path:
            raise AuditInputError("unsound disposition reference path mismatch")
        if row.get("reference_file_sha256") != boundary.reference_file_sha256:
            raise AuditInputError("unsound disposition reference identity mismatch")
    return key


def _validate_policy(policy: Mapping[str, Any]) -> None:
    _validate_policy_header(policy)
    rows = policy.get("dispositions")
    if not isinstance(rows, list):
        raise AuditInputError("policy dispositions must be an array")
    observed: set[DispositionKey] = set()
    for index, raw in enumerate(rows):
        key = _validate_disposition(raw, index=index)
        if key in observed:
            raise AuditInputError("duplicate dependency-audit disposition")
        observed.add(key)
    if observed != PERMITTED_DISPOSITION_KEYS:
        raise AuditInputError("dependency-audit disposition set mismatch")


def load_policy(path: Path = DEFAULT_POLICY) -> tuple[Mapping[str, Any], str]:
    raw = _read_regular(path, max_bytes=MAX_POLICY_BYTES, label="dependency-audit policy")
    policy = _parse_json(raw, label="dependency-audit policy")
    _validate_policy(policy)
    return policy, hashlib.sha256(raw).hexdigest()


def _disposition_keys(policy: Mapping[str, Any]) -> frozenset[DispositionKey]:
    rows = policy["dispositions"]
    return frozenset(
        (
            str(row["workspace_id"]),
            str(row["category"]),
            str(row["advisory_id"]),
            str(row["package"]),
            str(row["version"]),
        )
        for row in rows
    )


def _finding(
    entry: object,
    *,
    category: str,
    advisory_required: bool,
    label: str,
) -> dict[str, Any]:
    if not isinstance(entry, Mapping):
        raise AuditInputError(f"{label} must be an object")
    package_value = entry.get("package")
    if not isinstance(package_value, Mapping):
        raise AuditInputError(f"{label} package must be an object")
    package = _nonempty_ascii(package_value.get("name"), label=f"{label} package name")
    version = _nonempty_ascii(package_value.get("version"), label=f"{label} package version")
    advisory_value = entry.get("advisory")
    advisory_id = ""
    if advisory_value is not None:
        if not isinstance(advisory_value, Mapping):
            raise AuditInputError(f"{label} advisory must be an object")
        advisory_id = _nonempty_ascii(
            advisory_value.get("id"), label=f"{label} advisory id", max_chars=64
        )
    if advisory_required and not advisory_id:
        raise AuditInputError(f"{label} advisory id is required")
    return {
        "advisory_id": advisory_id,
        "category": category,
        "package": package,
        "version": version,
    }


def _validate_database(payload: Mapping[str, Any], errors: list[str]) -> None:
    database = payload.get("database")
    if not isinstance(database, Mapping):
        errors.append("cargo-audit report database must be an object")
        return
    advisory_count = database.get("advisory-count")
    if type(advisory_count) is not int or advisory_count < 1:
        errors.append("cargo-audit advisory count must be a positive integer")


def _evaluate_vulnerabilities(
    vulnerabilities: object,
    *,
    workspace_id: str,
    dispositions: frozenset[DispositionKey],
) -> tuple[list[dict[str, Any]], set[DispositionKey], list[str]]:
    findings: list[dict[str, Any]] = []
    applied: set[DispositionKey] = set()
    errors: list[str] = []
    if not isinstance(vulnerabilities, Mapping):
        return findings, applied, ["cargo-audit vulnerabilities must be an object"]
    entries = vulnerabilities.get("list")
    found = vulnerabilities.get("found")
    count = vulnerabilities.get("count")
    if not isinstance(entries, list):
        errors.append("cargo-audit vulnerability list must be an array")
        entries = []
    if type(found) is not bool:
        errors.append("cargo-audit vulnerability found flag must be boolean")
    if type(count) is not int or count < 0:
        errors.append("cargo-audit vulnerability count must be a nonnegative integer")
    if type(count) is int and count != len(entries):
        errors.append("cargo-audit vulnerability count mismatch")
    if type(found) is bool and found is not bool(entries):
        errors.append("cargo-audit vulnerability found flag mismatch")
    for index, entry in enumerate(entries):
        try:
            finding = _finding(
                entry,
                category="vulnerability",
                advisory_required=True,
                label=f"vulnerability[{index}]",
            )
        except AuditInputError as exc:
            errors.append(str(exc))
            continue
        key = (
            workspace_id,
            "vulnerability",
            finding["advisory_id"],
            finding["package"],
            finding["version"],
        )
        finding["disposition_applied"] = key in dispositions
        findings.append(finding)
        if key in dispositions:
            applied.add(key)
        else:
            errors.append(
                "undisposed vulnerability: "
                f"{finding['advisory_id']} {finding['package']} {finding['version']}"
            )
    return findings, applied, errors


def _evaluate_warnings(
    warnings: object,
    *,
    workspace_id: str,
    dispositions: frozenset[DispositionKey],
) -> tuple[list[dict[str, Any]], set[DispositionKey], list[str]]:
    findings: list[dict[str, Any]] = []
    applied: set[DispositionKey] = set()
    errors: list[str] = []
    if not isinstance(warnings, Mapping):
        return findings, applied, ["cargo-audit warnings must be an object"]
    for category, entries in sorted(warnings.items(), key=lambda item: str(item[0])):
        if not isinstance(category, str) or category not in KNOWN_WARNING_CATEGORIES:
            errors.append(f"unknown cargo-audit warning category: {category!r}")
            continue
        if not isinstance(entries, list):
            errors.append(f"cargo-audit {category} warnings must be an array")
            continue
        for index, entry in enumerate(entries):
            try:
                finding = _finding(
                    entry,
                    category=category,
                    advisory_required=category != "yanked",
                    label=f"warning[{category}][{index}]",
                )
            except AuditInputError as exc:
                errors.append(str(exc))
                continue
            key = (
                workspace_id,
                category,
                finding["advisory_id"],
                finding["package"],
                finding["version"],
            )
            finding["disposition_applied"] = key in dispositions
            findings.append(finding)
            if key in dispositions:
                applied.add(key)
            elif category in DENIED_WARNING_CATEGORIES:
                identity = finding["advisory_id"] or "no-advisory-id"
                errors.append(
                    f"denied {category} warning: "
                    f"{identity} {finding['package']} {finding['version']}"
                )
    return findings, applied, errors


def evaluate_audit_payload(
    payload: object,
    *,
    workspace_id: str,
    dispositions: frozenset[DispositionKey],
) -> dict[str, Any]:
    if not isinstance(payload, Mapping):
        return {
            "applied_dispositions": [],
            "errors": ["cargo-audit report must be an object"],
            "ok": False,
            "vulnerabilities": [],
            "warnings": [],
        }
    errors: list[str] = []
    _validate_database(payload, errors)
    vulnerabilities, applied, vulnerability_errors = _evaluate_vulnerabilities(
        payload.get("vulnerabilities"),
        workspace_id=workspace_id,
        dispositions=dispositions,
    )
    warnings, warning_applied, warning_errors = _evaluate_warnings(
        payload.get("warnings"),
        workspace_id=workspace_id,
        dispositions=dispositions,
    )
    applied.update(warning_applied)
    errors.extend(vulnerability_errors)
    errors.extend(warning_errors)
    vulnerabilities.sort(
        key=lambda item: (item["advisory_id"], item["package"], item["version"])
    )
    warnings.sort(
        key=lambda item: (
            item["category"],
            item["advisory_id"],
            item["package"],
            item["version"],
        )
    )
    return {
        "applied_dispositions": [list(key) for key in sorted(applied)],
        "errors": list(dict.fromkeys(errors)),
        "ok": not errors,
        "vulnerabilities": vulnerabilities,
        "warnings": warnings,
    }


def _discover_workspace_locks(root: Path) -> list[str]:
    zk_root = root / "zk"
    if not zk_root.is_dir():
        raise AuditInputError("zk workspace root is missing")
    paths: list[str] = []
    for entry in sorted(zk_root.iterdir(), key=lambda path: path.name):
        lockfile = entry / "Cargo.lock"
        try:
            lock_stat = lockfile.lstat()
        except FileNotFoundError:
            continue
        except OSError as exc:
            raise AuditInputError("cannot inspect workspace lockfile inventory") from exc
        if not stat.S_ISREG(lock_stat.st_mode):
            raise AuditInputError(f"workspace lockfile is not regular: {lockfile.relative_to(root)}")
        paths.append(lockfile.relative_to(root).as_posix())
    return paths


def _unsound_boundary_errors(
    spec: WorkspaceSpec,
    *,
    root: Path,
    lockfile_sha256: str,
    dispositions: frozenset[DispositionKey],
) -> tuple[list[str], bool]:
    boundary = UNSOUND_BOUNDARIES.get(spec.workspace_id)
    if boundary is None:
        return [], False
    unsound_keys = [
        key
        for key in dispositions
        if key[0] == spec.workspace_id and key[1] == "unsound"
    ]
    if len(unsound_keys) != 1:
        return ["workspace unsound disposition cardinality mismatch"], False
    errors: list[str] = []
    if lockfile_sha256 != boundary.lockfile_sha256:
        errors.append("unsound disposition lockfile bytes drifted")
    try:
        reference = _read_regular(
            root / boundary.reference_path,
            max_bytes=MAX_REFERENCE_BYTES,
            label=boundary.reference_path,
        )
    except AuditInputError as exc:
        errors.append(str(exc))
    else:
        if hashlib.sha256(reference).hexdigest() != boundary.reference_file_sha256:
            errors.append("unsound disposition rebuild reference drifted")
        else:
            try:
                reference_document = _parse_json(
                    reference,
                    label=boundary.reference_path,
                )
                errors.extend(_reference_source_closure_errors(reference_document, root))
            except AuditInputError as exc:
                errors.append(str(exc))
    source_count = 0
    for relative_root in boundary.source_roots:
        source_root = root / relative_root
        try:
            metadata = source_root.lstat()
        except OSError:
            errors.append("unsound disposition source root is unavailable")
            continue
        if source_root.is_symlink() or not stat.S_ISDIR(metadata.st_mode):
            errors.append("unsound disposition source root is not a real directory")
            continue
        for source in sorted(source_root.rglob("*.rs")):
            relative = source.relative_to(root)
            if "target" in relative.parts:
                continue
            source_count += 1
            try:
                raw = _read_regular(
                    source,
                    max_bytes=MAX_SCANNED_SOURCE_BYTES,
                    label=relative.as_posix(),
                )
            except AuditInputError as exc:
                errors.append(str(exc))
                continue
            if b"downcast_mut" in raw:
                errors.append(
                    "affected anyhow::Error::downcast_mut token entered governed source"
                )
    if source_count == 0:
        errors.append("unsound disposition source scan was empty")
    return list(dict.fromkeys(errors)), not errors


def _reference_source_closure_errors(
    reference: Mapping[str, Any],
    root: Path,
) -> list[str]:
    source_compile = reference.get("source_compile")
    if not isinstance(source_compile, Mapping):
        return ["unsound disposition reference source closure is absent"]
    files = source_compile.get("files")
    expected_root = source_compile.get("root_sha256")
    if not isinstance(files, list) or not files or not isinstance(expected_root, str):
        return ["unsound disposition reference source closure is malformed"]
    rows: list[tuple[str, str, int]] = []
    errors: list[str] = []
    for index, raw in enumerate(files):
        try:
            row = _exact_fields(
                raw,
                frozenset({"path", "sha256", "size_bytes"}),
                label=f"reference source file[{index}]",
            )
            relative = _nonempty_ascii(
                row.get("path"),
                label=f"reference source file[{index}] path",
            )
            pure = PurePosixPath(relative)
            if (
                pure.is_absolute()
                or ".." in pure.parts
                or not pure.parts
                or str(pure) != relative
            ):
                raise AuditInputError("reference source path is unsafe")
            digest = _nonempty_ascii(
                row.get("sha256"),
                label=f"reference source file[{index}] SHA-256",
                max_chars=64,
            )
            if SHA256_RE.fullmatch(digest) is None:
                raise AuditInputError("reference source SHA-256 is malformed")
            size = row.get("size_bytes")
            if type(size) is not int or size <= 0 or size > MAX_SCANNED_SOURCE_BYTES:
                raise AuditInputError("reference source size is out of bounds")
            rows.append((relative, digest, size))
        except AuditInputError as exc:
            errors.append(str(exc))
    if errors:
        return errors
    if [row[0] for row in rows] != sorted({row[0] for row in rows}):
        return ["reference source paths are not sorted and unique"]
    closure = hashlib.sha256()
    for relative, expected_digest, expected_size in rows:
        try:
            raw = _read_regular(
                root / relative,
                max_bytes=MAX_SCANNED_SOURCE_BYTES,
                label=relative,
            )
        except AuditInputError as exc:
            errors.append(str(exc))
            continue
        actual_digest = hashlib.sha256(raw).hexdigest()
        if len(raw) != expected_size or actual_digest != expected_digest:
            errors.append(f"unsound disposition source closure drifted: {relative}")
            continue
        closure.update(relative.encode("utf-8"))
        closure.update(b"\0")
        closure.update(actual_digest.encode("ascii"))
        closure.update(b"\0")
    if not errors and closure.hexdigest() != expected_root:
        errors.append("unsound disposition source closure root mismatch")
    return errors


def _workspace_report(
    spec: WorkspaceSpec,
    *,
    payload: object,
    root: Path,
    dispositions: frozenset[DispositionKey],
) -> tuple[dict[str, Any], set[DispositionKey]]:
    errors: list[str] = []
    lock_sha256 = ""
    lock_size_bytes = 0
    try:
        lock_raw = _read_regular(
            root / spec.lockfile,
            max_bytes=MAX_LOCK_BYTES,
            label=spec.lockfile,
        )
        lock_sha256 = hashlib.sha256(lock_raw).hexdigest()
        lock_size_bytes = len(lock_raw)
    except AuditInputError as exc:
        errors.append(str(exc))
    boundary_errors, boundary_verified = _unsound_boundary_errors(
        spec,
        root=root,
        lockfile_sha256=lock_sha256,
        dispositions=dispositions,
    )
    errors.extend(boundary_errors)
    evaluation = evaluate_audit_payload(
        payload,
        workspace_id=spec.workspace_id,
        dispositions=dispositions,
    )
    errors.extend(evaluation["errors"])
    applied = {tuple(row) for row in evaluation["applied_dispositions"]}
    return (
        {
            "applied_dispositions": evaluation["applied_dispositions"],
            "errors": list(dict.fromkeys(errors)),
            "lockfile": spec.lockfile,
            "lockfile_sha256": lock_sha256,
            "lockfile_size_bytes": lock_size_bytes,
            "ok": not errors,
            "retained_unsound_boundary_verified": boundary_verified,
            "vulnerabilities": evaluation["vulnerabilities"],
            "warnings": evaluation["warnings"],
            "workspace": spec.relative_path,
            "workspace_id": spec.workspace_id,
        },
        applied,
    )


def check_audit_payloads(
    payloads: Mapping[str, object],
    *,
    advisory_database_revision: str,
    root: Path = ROOT,
    policy_path: Path = DEFAULT_POLICY,
    cargo_audit_version: str = "cargo-audit-audit 0.22.1",
) -> dict[str, Any]:
    policy, policy_sha256 = load_policy(policy_path)
    errors: list[str] = []
    expected_locks = sorted(spec.lockfile for spec in REVIEWED_WORKSPACES)
    discovered_locks = _discover_workspace_locks(root)
    if discovered_locks != expected_locks:
        errors.append("reviewed workspace lockfile inventory mismatch")
    expected_workspace_ids = {spec.workspace_id for spec in REVIEWED_WORKSPACES}
    if set(payloads) != expected_workspace_ids:
        errors.append("cargo-audit payload workspace set mismatch")
    if GIT_REVISION_RE.fullmatch(advisory_database_revision) is None:
        errors.append("advisory database revision must be lowercase Git SHA-1")
    expected_version = str(policy["cargo_audit_version"])
    if re.search(rf"(?<![0-9.]){re.escape(expected_version)}(?![0-9.])", cargo_audit_version) is None:
        errors.append("cargo-audit executable version mismatch")

    dispositions = _disposition_keys(policy)
    applied_dispositions: set[DispositionKey] = set()
    workspace_reports: list[dict[str, Any]] = []
    for spec in REVIEWED_WORKSPACES:
        report, applied = _workspace_report(
            spec,
            payload=payloads.get(spec.workspace_id),
            root=root,
            dispositions=dispositions,
        )
        workspace_reports.append(report)
        applied_dispositions.update(applied)
    unused_dispositions = sorted(dispositions - applied_dispositions)
    if unused_dispositions:
        errors.append("policy contains stale or unreachable vulnerability dispositions")
    all_ok = not errors and all(report["ok"] for report in workspace_reports)
    return {
        "advisory_database_revision": advisory_database_revision,
        "cargo_audit_version": cargo_audit_version,
        "claim_scope": policy["claim_scope"],
        "errors": errors,
        "ok": all_ok,
        "policy_id": policy["policy_id"],
        "policy_sha256": policy_sha256,
        "production_authority": False,
        "schema": REPORT_SCHEMA,
        "status": "accepted" if all_ok else "rejected",
        "unused_dispositions": [list(key) for key in unused_dispositions],
        "workspaces": workspace_reports,
    }


def _run_command(command: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    try:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            check=False,
            capture_output=True,
            text=True,
            timeout=AUDIT_TIMEOUT_SECONDS,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise AuditInputError(f"dependency-audit command failed to run: {command[0]}") from exc
    if len(completed.stdout.encode("utf-8")) > MAX_AUDIT_OUTPUT_BYTES:
        raise AuditInputError("dependency-audit stdout exceeds byte cap")
    if len(completed.stderr.encode("utf-8")) > MAX_AUDIT_OUTPUT_BYTES:
        raise AuditInputError("dependency-audit stderr exceeds byte cap")
    return completed


def _cargo_audit_version(root: Path) -> str:
    completed = _run_command(["cargo", "audit", "--version"], cwd=root)
    if completed.returncode != 0 or not completed.stdout.strip():
        raise AuditInputError("cargo-audit version command failed")
    return completed.stdout.strip()


def _advisory_database_revision(advisory_db: Path, *, root: Path) -> str:
    completed = _run_command(
        ["git", "-C", str(advisory_db), "rev-parse", "--verify", "HEAD"],
        cwd=root,
    )
    revision = completed.stdout.strip()
    if completed.returncode != 0 or GIT_REVISION_RE.fullmatch(revision) is None:
        raise AuditInputError("advisory database revision is unavailable")
    return revision


def _run_cargo_audit(
    lockfile: Path,
    *,
    advisory_db: Path,
    root: Path,
    no_fetch: bool,
) -> Mapping[str, Any]:
    command = [
        "cargo",
        "audit",
        "--json",
        "--db",
        str(advisory_db),
        "--file",
        str(lockfile),
    ]
    if no_fetch:
        command.append("--no-fetch")
    completed = _run_command(command, cwd=root)
    if completed.returncode not in {0, 1}:
        raise AuditInputError("cargo-audit returned an operational failure")
    if not completed.stdout.strip():
        raise AuditInputError("cargo-audit produced no JSON output")
    return _parse_json(completed.stdout.encode("utf-8"), label="cargo-audit report")


def run_registered_audits(
    *,
    root: Path = ROOT,
    policy_path: Path = DEFAULT_POLICY,
    advisory_db: Path = DEFAULT_ADVISORY_DB,
    no_fetch: bool = False,
) -> dict[str, Any]:
    load_policy(policy_path)
    version = _cargo_audit_version(root)
    payloads: dict[str, object] = {}
    for index, spec in enumerate(REVIEWED_WORKSPACES):
        payloads[spec.workspace_id] = _run_cargo_audit(
            root / spec.lockfile,
            advisory_db=advisory_db,
            root=root,
            no_fetch=no_fetch or index > 0,
        )
        if index == 0:
            revision = _advisory_database_revision(advisory_db, root=root)
    final_revision = _advisory_database_revision(advisory_db, root=root)
    if final_revision != revision:
        raise AuditInputError("advisory database changed during the audit")
    return check_audit_payloads(
        payloads,
        advisory_database_revision=revision,
        root=root,
        policy_path=policy_path,
        cargo_audit_version=version,
    )


def _failure_report(error: Exception) -> dict[str, Any]:
    return {
        "errors": [str(error)],
        "ok": False,
        "production_authority": False,
        "schema": REPORT_SCHEMA,
        "status": "operational_error",
        "workspaces": [],
    }


def _emit_report(report: Mapping[str, Any], output: Path | None) -> None:
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY)
    parser.add_argument("--advisory-db", type=Path, default=DEFAULT_ADVISORY_DB)
    parser.add_argument("--no-fetch", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = run_registered_audits(
            policy_path=args.policy,
            advisory_db=args.advisory_db,
            no_fetch=args.no_fetch,
        )
    except (AuditInputError, OSError, ValueError) as exc:
        report = _failure_report(exc)
    _emit_report(report, args.output)
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
