#!/usr/bin/env python3
"""Check or reconstruct the pinned recursive-v2 RISC0 evidence boundary."""

from __future__ import annotations

import argparse
import base64
import hashlib
import io
import json
import os
import re
import signal
import stat
import subprocess
import tarfile
import tomllib
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

try:
    from . import check_risc0_recursive_toolchain_lock as toolchain_lock
except ImportError:  # Direct script execution.
    import check_risc0_recursive_toolchain_lock as toolchain_lock


ROOT = Path(__file__).resolve().parents[1]
REFERENCE_PATH = ROOT / "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json"

REFERENCE_SCHEMA = "zenodex/risc0_recursive_v2_rebuild_reference/v1"
REPORT_SCHEMA = "zenodex/risc0_recursive_v2_rebuild_evidence_check/v1"
SDK_VERSION = "3.0.5"
EXPECTED_REFERENCE_CANONICAL_SHA256 = (
    "de542c96cca4f516bb481843d81bc0bc4dce94870f22ae8163908e1e16534823"
)
SOURCE_ROOT_ALGORITHM = "sha256(sorted(path_utf8 || nul || file_sha256_ascii || nul))"
REGISTRY_ROOT_ALGORITHM = "sha256(sorted(package_dir_utf8 || nul || lock_checksum_ascii || nul))"
EXPECTED_SOURCE_SCOPES = (
    "zk/recursive_stark_v2_risc0",
    "zk/state_proof_risc0/shared",
)
EXPECTED_NONCLAIMS = (
    "migration profile: the transition leaf still uses the authenticated v1 leaf journal",
    "the harness-local v1 image allowlist has no release or registry authority",
    "one-leaf smoke does not establish production throughput or proving-cost bounds",
    "this harness does not grant release, settlement, or ledger-admission authority",
    "schedule and data-availability fields remain commitment-only in this profile",
    "strict closed subtrees do not support cross-subtree value or message flows",
    "this local run does not establish cross-host reproducibility or privacy",
)
EXPECTED_CLAIMS = {
    "accepted_candidate_status": "pinned_recursive_v2_artifact_match",
    "accepted_clean_rebuild_status": "same_host_clean_recursive_v2_rebuild_match",
    "arbitrary_depth_recursion": False,
    "cross_environment_reproducibility": False,
    "data_availability_verified": False,
    "multi_leaf_fanout": False,
    "privacy": False,
    "production_ready": False,
    "public_claim_allowed": False,
    "reproducible_release": False,
    "settlement_authorization": False,
}

MAX_REFERENCE_BYTES = 1024 * 1024
MAX_SOURCE_FILE_BYTES = 16 * 1024 * 1024
MAX_SOURCE_TOTAL_BYTES = 128 * 1024 * 1024
MAX_SOURCE_FILES = 128
MAX_DISCOVERY_ENTRIES = 16_384
MAX_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_METHODS_BYTES = 64 * 1024
MAX_PROGRAM_BYTES = 64 * 1024 * 1024
MAX_VERIFIER_BYTES = 64 * 1024 * 1024
MAX_TRANSCRIPT_BYTES = 1024 * 1024
MAX_JSON_DEPTH = 128
MAX_JSON_ITEMS = 100_000
MAX_JSON_INTEGER_CHARS = 20
MAX_COMMAND_OUTPUT_BYTES = 1024 * 1024
MAX_BUILD_LOG_BYTES = 64 * 1024 * 1024
MAX_DEP_INFO_BYTES = 8 * 1024 * 1024
MAX_CRATE_ARCHIVE_BYTES = 64 * 1024 * 1024
MAX_CRATE_MEMBER_BYTES = 32 * 1024 * 1024
MAX_REGISTRY_SOURCE_BYTES = 2 * 1024 * 1024 * 1024
BUILD_TIMEOUT_SECONDS = 3600
COMMAND_TIMEOUT_SECONDS = 60
READ_CHUNK_BYTES = 1024 * 1024

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
METHOD_ELF_RE = re.compile(
    r"^pub const TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF: &\[u8\] = "
    r'include_bytes!\("([^"\\\n]+)"\);$',
    re.MULTILINE,
)
METHOD_PATH_RE = re.compile(
    r"^pub const TAU_STATE_PROOF_RISC0_AGGREGATE_V2_PATH: &str = "
    r'"([^"\\\n]+)";$',
    re.MULTILINE,
)
METHOD_ID_RE = re.compile(
    r"^pub const TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID: \[u32; 8\] = "
    r"\[([0-9, ]+)\];$",
    re.MULTILINE,
)

REFERENCE_KEYS = frozenset(
    {
        "build_policy",
        "claims",
        "program",
        "proof_pair",
        "schema",
        "sdk_version",
        "source_compile",
        "version",
    }
)
SOURCE_KEYS = frozenset(
    {"file_count", "files", "registry_source_closure", "root_algorithm", "root_sha256", "scopes"}
)
SOURCE_FILE_KEYS = frozenset({"path", "sha256", "size_bytes"})
REGISTRY_KEYS = frozenset({"package_count", "root_algorithm", "root_sha256", "verification"})
PROGRAM_KEYS = frozenset(
    {
        "artifact_name",
        "generated_image_id_words",
        "image_id",
        "name",
        "program_bytes",
        "program_sha256",
        "raw_elf",
    }
)
RAW_ELF_KEYS = frozenset({"artifact_name", "sha256", "size_bytes"})
ARTIFACT_KEYS = frozenset(
    {
        "file_sha256",
        "flat_leaf_count",
        "immediate_child_count",
        "journal_sha256",
        "level",
        "profile",
        "protocol_journal_hash",
        "receipt_bytes",
        "receipt_sha256",
        "size_bytes",
        "subtree_node_count",
        "tree_height",
    }
)
ARTIFACT_CONTRACT_KEYS = frozenset(
    {"proof_type", "receipt_codec", "receipt_kind", "schema", "schema_version"}
)
RECEIPT_SECURITY_KEYS = frozenset({"control_id", "hashfn", "verifier_parameters"})
BLOB_VALUE_KEYS = frozenset({"sha256", "size_bytes", "value"})
STATIC_VERIFIER_KEYS = frozenset({"artifact_name", "sha256", "size_bytes"})
PROOF_PAIR_KEYS = frozenset(
    {
        "inner",
        "missing_assumption_output",
        "nonclaims",
        "pair_verifier_output",
        "receipt_artifact_contract",
        "receipt_security",
        "root",
        "static_verifier",
        "two_leaf_static_verifier",
    }
)


class EvidenceError(ValueError):
    """Stable fail-closed rejection at the recursive-v2 evidence boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class FileDigest:
    raw: bytes
    sha256: str
    size_bytes: int


def _reject(code: str, detail: str) -> EvidenceError:
    return EvidenceError(code, detail)


def _canonical_path(path: Path, *, label: str, directory: bool) -> Path:
    absolute = Path(os.path.abspath(os.fspath(path)))
    try:
        resolved = absolute.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise _reject("PATH_INVALID", label) from exc
    if resolved != absolute:
        raise _reject("SYMLINK_FORBIDDEN", label)
    expected = resolved.is_dir() if directory else resolved.is_file()
    if not expected:
        raise _reject("PATH_TYPE", label)
    return resolved


def _canonical_new_path(path: Path, *, label: str) -> Path:
    absolute = Path(os.path.abspath(os.fspath(path)))
    if absolute.exists() or absolute.is_symlink():
        raise _reject("CLEAN_TARGET_EXISTS", label)
    parent = _canonical_path(absolute.parent, label=f"{label} parent", directory=True)
    if absolute.parent != parent:
        raise _reject("SYMLINK_FORBIDDEN", f"{label} parent")
    return absolute


def _read_regular(path: Path, *, label: str, max_bytes: int) -> FileDigest:
    absolute = _canonical_path(path, label=label, directory=False)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if not isinstance(nofollow, int):
        raise _reject("PLATFORM_UNSUPPORTED", "O_NOFOLLOW")
    descriptor = os.open(absolute, flags | nofollow)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size < 0 or before.st_size > max_bytes:
            raise _reject("FILE_BOUNDS", label)
        chunks: list[bytes] = []
        total = 0
        digest = hashlib.sha256()
        while True:
            chunk = os.read(descriptor, min(READ_CHUNK_BYTES, max_bytes + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise _reject("FILE_BOUNDS", label)
            digest.update(chunk)
            chunks.append(chunk)
        after = os.fstat(descriptor)
        if _stat_identity(before) != _stat_identity(after) or total != before.st_size:
            raise _reject("FILE_CHANGED", label)
        return FileDigest(b"".join(chunks), digest.hexdigest(), total)
    finally:
        os.close(descriptor)


def _stat_identity(value: os.stat_result) -> tuple[int, int, int, int, int]:
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size, value.st_mtime_ns)


def _parse_json(raw: bytes, *, label: str) -> object:
    def reject_duplicates(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise _reject(f"{label}_JSON_DUPLICATE_KEY", key)
            result[key] = value
        return result

    def reject_float(value: str) -> object:
        raise _reject(f"{label}_JSON_FLOAT", value)

    def bounded_int(value: str) -> int:
        if len(value.removeprefix("-")) > MAX_JSON_INTEGER_CHARS:
            raise _reject(f"{label}_JSON_INTEGER_LIMIT", value)
        return int(value)

    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise _reject(f"{label}_JSON_ENCODING", "UTF-8 required") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=reject_duplicates,
            parse_int=bounded_int,
            parse_float=reject_float,
            parse_constant=reject_float,
        )
    except EvidenceError:
        raise
    except (json.JSONDecodeError, RecursionError) as exc:
        raise _reject(f"{label}_JSON_INVALID", str(exc)) from exc
    _validate_json_shape(value, label=label)
    return value


def _validate_json_shape(value: object, *, label: str) -> None:
    stack: list[tuple[object, int]] = [(value, 1)]
    items = 0
    while stack:
        current, depth = stack.pop()
        items += 1
        if items > MAX_JSON_ITEMS:
            raise _reject(f"{label}_JSON_ITEM_LIMIT", str(MAX_JSON_ITEMS))
        if depth > MAX_JSON_DEPTH:
            raise _reject(f"{label}_JSON_DEPTH_LIMIT", str(MAX_JSON_DEPTH))
        if isinstance(current, Mapping):
            for key, child in current.items():
                if not isinstance(key, str):
                    raise _reject(f"{label}_JSON_KEY_TYPE", repr(key))
                stack.append((child, depth + 1))
        elif isinstance(current, list):
            stack.extend((child, depth + 1) for child in current)
        elif current is not None and not isinstance(current, (bool, int, str)):
            raise _reject(f"{label}_JSON_VALUE_TYPE", str(type(current)))


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
        "ascii"
    )


def reference_canonical_sha256(value: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _mapping(value: object, *, code: str, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise _reject(code, f"{label} must be an object")
    return value


def _exact_keys(value: Mapping[str, Any], expected: frozenset[str], *, label: str) -> None:
    observed = frozenset(value)
    if observed != expected:
        missing = sorted(expected - observed)
        extra = sorted(observed - expected)
        raise _reject("REFERENCE_SCHEMA", f"{label}:missing={missing}:extra={extra}")


def _positive_int(value: object, *, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise _reject("REFERENCE_SCHEMA", f"{label} must be a positive integer")
    return value


def _sha256(value: object, *, label: str) -> str:
    if not isinstance(value, str) or SHA256_RE.fullmatch(value) is None:
        raise _reject("REFERENCE_SCHEMA", f"{label} must be lowercase SHA-256")
    return value


def _relative_path(value: object, *, label: str) -> str:
    if not isinstance(value, str) or not value or "\x00" in value or "\\" in value:
        raise _reject("REFERENCE_SCHEMA", f"{label} invalid")
    try:
        value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise _reject("REFERENCE_SCHEMA", f"{label} must be ASCII") from exc
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or path.as_posix() != value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise _reject("REFERENCE_SCHEMA", f"{label} invalid")
    return value


def load_reference() -> Mapping[str, Any]:
    digest = _read_regular(REFERENCE_PATH, label="reference", max_bytes=MAX_REFERENCE_BYTES)
    value = validate_reference(_parse_json(digest.raw, label="REFERENCE"))
    canonical = reference_canonical_sha256(value)
    if canonical != EXPECTED_REFERENCE_CANONICAL_SHA256:
        raise _reject("REFERENCE_DIGEST_MISMATCH", canonical)
    return value


def validate_reference(value: object) -> Mapping[str, Any]:
    reference = _mapping(value, code="REFERENCE_SCHEMA", label="reference")
    _exact_keys(reference, REFERENCE_KEYS, label="reference")
    if reference.get("schema") != REFERENCE_SCHEMA or reference.get("version") != 1:
        raise _reject("REFERENCE_SCHEMA", "schema or version mismatch")
    if reference.get("sdk_version") != SDK_VERSION:
        raise _reject("REFERENCE_SCHEMA", "SDK version mismatch")
    if reference.get("claims") != EXPECTED_CLAIMS:
        raise _reject("REFERENCE_CLAIMS", "claim policy mismatch")
    _validate_build_policy(reference.get("build_policy"))
    _validate_source_compile(reference.get("source_compile"))
    _validate_program(reference.get("program"))
    _validate_proof_pair(reference.get("proof_pair"))
    return reference


def _validate_build_policy(value: object) -> None:
    policy = _mapping(value, code="REFERENCE_SCHEMA", label="build_policy")
    required = {
        "cargo_arguments",
        "cargo_home_policy",
        "clean_target_required",
        "effective_cargo_configs",
        "environment",
        "guest_target",
        "host_target",
        "nested_cargo_policy",
        "offline_config_path",
        "offline_config_sha256",
        "outer_cargo_relative_path",
        "r0vm_relative_path",
        "risc0_home_policy",
        "rustc_relative_path",
        "toolchain_lock_canonical_sha256",
        "toolchain_lock_path",
    }
    _exact_keys(policy, frozenset(required), label="build_policy")
    expected_args = [
        "build",
        "--frozen",
        "--release",
        "--target",
        "x86_64-unknown-linux-gnu",
        "-p",
        "tau-state-proof-risc0-recursive-v2-harness",
        "--bins",
    ]
    if policy.get("cargo_arguments") != expected_args:
        raise _reject("REFERENCE_BUILD_POLICY", "Cargo arguments mismatch")
    expected_environment = {
        "CARGO_INCREMENTAL": "0",
        "LANG": "C",
        "LC_ALL": "C",
        "RISC0_BUILD_LOCKED": "1",
        "RISC0_FORCE_BUILD": "1",
        "SOURCE_DATE_EPOCH": "0",
        "TZ": "UTC",
        "ZERO_AR_DATE": "1",
    }
    if policy.get("environment") != expected_environment:
        raise _reject("REFERENCE_BUILD_POLICY", "environment mismatch")
    fixed = {
        "cargo_home_policy": "home_relative_dot_cargo",
        "clean_target_required": True,
        "guest_target": "riscv32im-risc0-zkvm-elf",
        "host_target": "x86_64-unknown-linux-gnu",
        "nested_cargo_policy": "path_first_observer_execs_exact_pinned_cargo",
        "risc0_home_policy": "home_relative_dot_risc0",
        "toolchain_lock_canonical_sha256": toolchain_lock.EXPECTED_CANONICAL_LOCK_SHA256,
        "toolchain_lock_path": "config/proof_profiles/risc0_recursive_toolchain_lock.json",
    }
    for key, expected in fixed.items():
        if policy.get(key) != expected:
            raise _reject("REFERENCE_BUILD_POLICY", key)
    for key in (
        "offline_config_path",
        "outer_cargo_relative_path",
        "r0vm_relative_path",
        "rustc_relative_path",
    ):
        _relative_path(policy.get(key), label=f"build_policy.{key}")
    _sha256(policy.get("offline_config_sha256"), label="offline config SHA-256")
    configs = policy.get("effective_cargo_configs")
    if not isinstance(configs, list) or len(configs) != 2:
        raise _reject("REFERENCE_BUILD_POLICY", "effective Cargo configs")
    for index, config in enumerate(configs):
        item = _mapping(config, code="REFERENCE_BUILD_POLICY", label=f"config[{index}]")
        _exact_keys(
            item, frozenset({"location", "path", "sha256", "size_bytes"}), label=f"config[{index}]"
        )
        if item.get("location") not in {"workspace", "cargo_home"}:
            raise _reject("REFERENCE_BUILD_POLICY", "Cargo config location")
        _relative_path(item.get("path"), label=f"config[{index}].path")
        _sha256(item.get("sha256"), label=f"config[{index}].sha256")
        _positive_int(item.get("size_bytes"), label=f"config[{index}].size_bytes")


def _validate_source_compile(value: object) -> None:
    source = _mapping(value, code="REFERENCE_SOURCE", label="source_compile")
    _exact_keys(source, SOURCE_KEYS, label="source_compile")
    if source.get("root_algorithm") != SOURCE_ROOT_ALGORITHM:
        raise _reject("REFERENCE_SOURCE", "source root algorithm")
    if tuple(source.get("scopes", ())) != EXPECTED_SOURCE_SCOPES:
        raise _reject("REFERENCE_SOURCE", "source scopes")
    _sha256(source.get("root_sha256"), label="source root")
    files = source.get("files")
    count = _positive_int(source.get("file_count"), label="source file_count")
    if not isinstance(files, list) or len(files) != count or count > MAX_SOURCE_FILES:
        raise _reject("REFERENCE_SOURCE", "source files")
    paths: list[str] = []
    for index, row_value in enumerate(files):
        row = _mapping(row_value, code="REFERENCE_SOURCE", label=f"files[{index}]")
        _exact_keys(row, SOURCE_FILE_KEYS, label=f"files[{index}]")
        path = _relative_path(row.get("path"), label=f"files[{index}].path")
        if not any(
            path == scope or path.startswith(scope + "/") for scope in EXPECTED_SOURCE_SCOPES
        ):
            raise _reject("REFERENCE_SOURCE", path)
        _sha256(row.get("sha256"), label=f"files[{index}].sha256")
        if (
            _positive_int(row.get("size_bytes"), label=f"files[{index}].size_bytes")
            > MAX_SOURCE_FILE_BYTES
        ):
            raise _reject("REFERENCE_SOURCE", "source file too large")
        paths.append(path)
    if paths != sorted(set(paths)):
        raise _reject("REFERENCE_SOURCE", "source paths must be sorted unique")
    registry = _mapping(
        source.get("registry_source_closure"), code="REFERENCE_SOURCE", label="registry"
    )
    _exact_keys(registry, REGISTRY_KEYS, label="registry")
    if (
        registry.get("root_algorithm") != REGISTRY_ROOT_ALGORITHM
        or registry.get("verification")
        != "lock_checksum_plus_cached_crate_and_extracted_tree_equality"
    ):
        raise _reject("REFERENCE_SOURCE", "registry policy")
    _positive_int(registry.get("package_count"), label="registry package_count")
    _sha256(registry.get("root_sha256"), label="registry root")


def _validate_program(value: object) -> None:
    program = _mapping(value, code="REFERENCE_PROGRAM", label="program")
    _exact_keys(program, PROGRAM_KEYS, label="program")
    if (
        program.get("name") != "aggregate_v2"
        or program.get("artifact_name") != "tau-state-proof-risc0-aggregate-v2.bin"
    ):
        raise _reject("REFERENCE_PROGRAM", "program identity")
    words = program.get("generated_image_id_words")
    if (
        not isinstance(words, list)
        or len(words) != 8
        or any(
            isinstance(word, bool) or not isinstance(word, int) or not 0 <= word <= 0xFFFF_FFFF
            for word in words
        )
    ):
        raise _reject("REFERENCE_PROGRAM", "image words")
    image_id = _sha256(program.get("image_id"), label="program image ID")
    if b"".join(word.to_bytes(4, "little") for word in words).hex() != image_id:
        raise _reject("REFERENCE_PROGRAM", "image word encoding")
    _sha256(program.get("program_sha256"), label="program SHA-256")
    _positive_int(program.get("program_bytes"), label="program bytes")
    raw = _mapping(program.get("raw_elf"), code="REFERENCE_PROGRAM", label="raw ELF")
    _exact_keys(raw, RAW_ELF_KEYS, label="raw ELF")
    if raw.get("artifact_name") != "tau-state-proof-risc0-aggregate-v2":
        raise _reject("REFERENCE_PROGRAM", "raw ELF name")
    _sha256(raw.get("sha256"), label="raw ELF SHA-256")
    _positive_int(raw.get("size_bytes"), label="raw ELF bytes")


def _validate_proof_pair(value: object) -> None:
    pair = _mapping(value, code="REFERENCE_PROOF", label="proof_pair")
    _exact_keys(pair, PROOF_PAIR_KEYS, label="proof_pair")
    if tuple(pair.get("nonclaims", ())) != EXPECTED_NONCLAIMS:
        raise _reject("REFERENCE_CLAIMS", "artifact nonclaims")
    for role in ("inner", "root"):
        artifact = _mapping(pair.get(role), code="REFERENCE_PROOF", label=role)
        _exact_keys(artifact, ARTIFACT_KEYS, label=role)
        for key in ("file_sha256", "journal_sha256", "protocol_journal_hash", "receipt_sha256"):
            _sha256(artifact.get(key), label=f"{role}.{key}")
        for key in (
            "flat_leaf_count",
            "immediate_child_count",
            "receipt_bytes",
            "size_bytes",
            "subtree_node_count",
            "tree_height",
        ):
            _positive_int(artifact.get(key), label=f"{role}.{key}")
        if not isinstance(artifact.get("level"), str) or not isinstance(
            artifact.get("profile"), str
        ):
            raise _reject("REFERENCE_PROOF", f"{role} level/profile")
    contract = _mapping(
        pair.get("receipt_artifact_contract"), code="REFERENCE_PROOF", label="receipt contract"
    )
    _exact_keys(contract, ARTIFACT_CONTRACT_KEYS, label="receipt contract")
    security = _mapping(
        pair.get("receipt_security"), code="REFERENCE_PROOF", label="receipt security"
    )
    _exact_keys(security, RECEIPT_SECURITY_KEYS, label="receipt security")
    if security.get("hashfn") != "poseidon2":
        raise _reject("REFERENCE_PROOF", "receipt hash function")
    _sha256(security.get("control_id"), label="control ID")
    _sha256(security.get("verifier_parameters"), label="verifier parameters")
    for field, label in (
        ("static_verifier", "static verifier"),
        ("two_leaf_static_verifier", "two-leaf static verifier"),
    ):
        verifier = _mapping(pair.get(field), code="REFERENCE_PROOF", label=label)
        _exact_keys(verifier, STATIC_VERIFIER_KEYS, label=label)
        _sha256(verifier.get("sha256"), label=f"{label} SHA-256")
        _positive_int(verifier.get("size_bytes"), label=f"{label} bytes")
    for label in ("pair_verifier_output", "missing_assumption_output"):
        transcript = _mapping(pair.get(label), code="REFERENCE_PROOF", label=label)
        _exact_keys(transcript, BLOB_VALUE_KEYS, label=label)
        _sha256(transcript.get("sha256"), label=f"{label}.sha256")
        _positive_int(transcript.get("size_bytes"), label=f"{label}.size_bytes")
        _mapping(transcript.get("value"), code="REFERENCE_PROOF", label=f"{label}.value")


def _discover_source_paths(repository_root: Path) -> list[str]:
    found: list[str] = []
    entries = 0
    for scope in EXPECTED_SOURCE_SCOPES:
        scope_path = repository_root.joinpath(*PurePosixPath(scope).parts)
        if not scope_path.is_dir() or scope_path.is_symlink():
            raise _reject("SOURCE_SCOPE_INVALID", scope)
        for directory, dirnames, filenames in os.walk(scope_path, followlinks=False):
            entries += len(dirnames) + len(filenames)
            if entries > MAX_DISCOVERY_ENTRIES:
                raise _reject("SOURCE_DISCOVERY_LIMIT", str(MAX_DISCOVERY_ENTRIES))
            base = Path(directory)
            kept: list[str] = []
            for name in sorted(dirnames):
                child = base / name
                if child.is_symlink():
                    raise _reject("SYMLINK_FORBIDDEN", str(child))
                if name == "target":
                    raise _reject("SOURCE_TARGET_PRESENT", str(child))
                kept.append(name)
            dirnames[:] = kept
            for name in sorted(filenames):
                child = base / name
                if child.is_symlink():
                    raise _reject("SYMLINK_FORBIDDEN", str(child))
                if not child.is_file():
                    raise _reject("SOURCE_ENTRY_INVALID", str(child))
                found.append(child.relative_to(repository_root).as_posix())
    return sorted(found)


def _check_source(reference: Mapping[str, Any], repository_root: Path) -> dict[str, Any]:
    source = reference["source_compile"]
    rows = source["files"]
    expected_paths = [row["path"] for row in rows]
    observed_paths = _discover_source_paths(repository_root)
    missing = sorted(set(expected_paths) - set(observed_paths))
    extra = sorted(set(observed_paths) - set(expected_paths))
    if missing:
        raise _reject("SOURCE_FILE_MISSING", missing[0])
    if extra:
        raise _reject("SOURCE_FILE_EXTRA", extra[0])
    checked: list[dict[str, Any]] = []
    total = 0
    for row in rows:
        path = repository_root.joinpath(*PurePosixPath(row["path"]).parts)
        digest = _read_regular(path, label=row["path"], max_bytes=MAX_SOURCE_FILE_BYTES)
        if digest.size_bytes != row["size_bytes"]:
            raise _reject("SOURCE_SIZE_MISMATCH", row["path"])
        if digest.sha256 != row["sha256"]:
            raise _reject("SOURCE_SHA256_MISMATCH", row["path"])
        total += digest.size_bytes
        if total > MAX_SOURCE_TOTAL_BYTES:
            raise _reject("SOURCE_TOTAL_LIMIT", str(MAX_SOURCE_TOTAL_BYTES))
        checked.append(row)
    root = _source_root(checked)
    if root != source["root_sha256"]:
        raise _reject("SOURCE_ROOT_MISMATCH", root)
    return {"file_count": len(checked), "root_sha256": root, "total_bytes": total}


def _source_root(rows: Sequence[Mapping[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in sorted(rows, key=lambda item: str(item["path"])):
        digest.update(str(row["path"]).encode("ascii"))
        digest.update(b"\x00")
        digest.update(str(row["sha256"]).encode("ascii"))
        digest.update(b"\x00")
    return digest.hexdigest()


def _check_effective_cargo_configs(
    reference: Mapping[str, Any], repository_root: Path, cargo_home: Path
) -> None:
    policy = reference["build_policy"]
    expected: dict[Path, Mapping[str, Any]] = {}
    for row in policy["effective_cargo_configs"]:
        if row["location"] == "workspace":
            path = repository_root.joinpath(*PurePosixPath(row["path"]).parts)
        else:
            path = cargo_home.joinpath(*PurePosixPath(row["path"]).parts)
        expected[path] = row
    workspace = repository_root / "zk/recursive_stark_v2_risc0"
    discovered: set[Path] = set()
    current = workspace
    while True:
        for name in ("config", "config.toml"):
            candidate = current / ".cargo" / name
            if candidate.exists() or candidate.is_symlink():
                discovered.add(candidate)
        if current.parent == current:
            break
        current = current.parent
    for name in ("config", "config.toml"):
        candidate = cargo_home / name
        if candidate.exists() or candidate.is_symlink():
            discovered.add(candidate)
    if discovered != set(expected):
        raise _reject("CARGO_CONFIG_SET_MISMATCH", str(sorted(map(str, discovered))))
    for path, row in expected.items():
        digest = _read_regular(path, label="Cargo config", max_bytes=1024 * 1024)
        if digest.sha256 != row["sha256"] or digest.size_bytes != row["size_bytes"]:
            raise _reject("CARGO_CONFIG_MISMATCH", row["path"])
    offline = repository_root.joinpath(*PurePosixPath(policy["offline_config_path"]).parts)
    parsed = tomllib.loads(
        _read_regular(offline, label="offline config", max_bytes=1024 * 1024).raw.decode("utf-8")
    )
    if parsed.get("net", {}).get("offline") is not True:
        raise _reject("CARGO_OFFLINE_POLICY", "workspace net.offline must be true")


def _check_blob(
    path: Path, reference: Mapping[str, Any], *, code: str, max_bytes: int
) -> FileDigest:
    digest = _read_regular(path, label=code, max_bytes=max_bytes)
    if digest.size_bytes != reference["size_bytes"]:
        raise _reject(f"{code}_SIZE_MISMATCH", str(digest.size_bytes))
    if digest.sha256 != reference["sha256"]:
        raise _reject(f"{code}_SHA256_MISMATCH", digest.sha256)
    return digest


def _target_artifacts(target_root: Path) -> dict[str, Path]:
    guest = (
        target_root
        / "riscv-guest/tau-state-proof-risc0-recursive-v2-methods/tau-state-proof-risc0-aggregate-v2/riscv32im-risc0-zkvm-elf/release"
    )
    host = target_root / "x86_64-unknown-linux-gnu/release"
    methods = sorted(host.glob("build/tau-state-proof-risc0-recursive-v2-methods-*/out/methods.rs"))
    if len(methods) != 1:
        raise _reject("GENERATED_METHODS_COUNT", str(len(methods)))
    return {
        "program": guest / "tau-state-proof-risc0-aggregate-v2.bin",
        "raw_elf": guest / "tau-state-proof-risc0-aggregate-v2",
        "verifier": host / "verify_recursive_v2_pair",
        "two_leaf_verifier": host / "verify_recursive_v2_two_leaf_pair",
        "methods": methods[0],
    }


def _check_program_and_methods(reference: Mapping[str, Any], target_root: Path) -> dict[str, Any]:
    paths = _target_artifacts(target_root)
    program_ref = reference["program"]
    program = _read_regular(paths["program"], label="combined program", max_bytes=MAX_PROGRAM_BYTES)
    if (
        program.sha256 != program_ref["program_sha256"]
        or program.size_bytes != program_ref["program_bytes"]
    ):
        raise _reject("PROGRAM_MISMATCH", program.sha256)
    raw = _check_blob(
        paths["raw_elf"], program_ref["raw_elf"], code="RAW_ELF", max_bytes=MAX_PROGRAM_BYTES
    )
    methods = _read_regular(
        paths["methods"], label="generated methods", max_bytes=MAX_METHODS_BYTES
    )
    try:
        text = methods.raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("GENERATED_METHODS_INVALID", "ASCII required") from exc
    elf_match = METHOD_ELF_RE.findall(text)
    path_match = METHOD_PATH_RE.findall(text)
    id_match = METHOD_ID_RE.findall(text)
    if len(elf_match) != 1 or len(path_match) != 1 or len(id_match) != 1:
        raise _reject("GENERATED_METHODS_INVALID", "constant surface")
    included = Path(elf_match[0])
    declared = Path(path_match[0])
    expected_program = _canonical_path(paths["program"], label="combined program", directory=False)
    if (
        _canonical_path(included, label="methods include", directory=False) != expected_program
        or _canonical_path(declared, label="methods path", directory=False) != expected_program
    ):
        raise _reject("GENERATED_METHODS_PATH_MISMATCH", str(included))
    if not expected_program.is_relative_to(target_root):
        raise _reject("GENERATED_METHODS_PATH_MISMATCH", "program outside target")
    words = [int(item.strip()) for item in id_match[0].split(",") if item.strip()]
    if words != program_ref["generated_image_id_words"]:
        raise _reject("GENERATED_IMAGE_ID_MISMATCH", str(words))
    return {
        "program_path": paths["program"],
        "program_sha256": program.sha256,
        "program_bytes": program.size_bytes,
        "raw_elf_sha256": raw.sha256,
        "raw_elf_bytes": raw.size_bytes,
        "verifier_path": paths["verifier"],
        "two_leaf_verifier_path": paths["two_leaf_verifier"],
        "methods_path": paths["methods"],
    }


def _u32_digest_hex(value: object, *, label: str) -> str:
    if (
        not isinstance(value, list)
        or len(value) != 8
        or any(
            isinstance(item, bool) or not isinstance(item, int) or not 0 <= item <= 0xFFFF_FFFF
            for item in value
        )
    ):
        raise _reject("ARTIFACT_RECEIPT_SECURITY", label)
    return b"".join(item.to_bytes(4, "little") for item in value).hex()


def _check_receipt_artifact(
    reference: Mapping[str, Any], path: Path, *, role: str
) -> dict[str, Any]:
    pair = reference["proof_pair"]
    role_ref = pair[role]
    digest = _read_regular(path, label=f"{role} artifact", max_bytes=MAX_ARTIFACT_BYTES)
    if digest.sha256 != role_ref["file_sha256"] or digest.size_bytes != role_ref["size_bytes"]:
        raise _reject(f"{role.upper()}_ARTIFACT_MISMATCH", digest.sha256)
    value = _mapping(
        _parse_json(digest.raw, label=f"{role.upper()}_ARTIFACT"),
        code="ARTIFACT_SCHEMA",
        label=role,
    )
    expected_keys = frozenset(
        {
            "journal",
            "journal_sha256",
            "nonclaims",
            "proof",
            "proof_type",
            "protocol_journal_hash",
            "receipt_codec",
            "receipt_kind",
            "receipt_sha256",
            "risc0_image_id",
            "schema",
            "schema_version",
        }
    )
    if frozenset(value) != expected_keys:
        raise _reject("ARTIFACT_SCHEMA", role)
    contract = pair["receipt_artifact_contract"]
    for key, expected in contract.items():
        if value.get(key) != expected:
            raise _reject("ARTIFACT_HEADER_MISMATCH", f"{role}.{key}")
    program = reference["program"]
    if (
        value.get("risc0_image_id") != program["image_id"]
        or tuple(value.get("nonclaims", ())) != EXPECTED_NONCLAIMS
    ):
        raise _reject("ARTIFACT_HEADER_MISMATCH", f"{role}.claim scope")
    for key in ("receipt_sha256", "journal_sha256", "protocol_journal_hash"):
        if value.get(key) != role_ref[key]:
            raise _reject("ARTIFACT_HEADER_MISMATCH", f"{role}.{key}")
    proof = value.get("proof")
    if not isinstance(proof, str) or len(proof) > MAX_ARTIFACT_BYTES * 2:
        raise _reject("ARTIFACT_RECEIPT_BOUNDS", role)
    try:
        receipt_bytes = base64.b64decode(proof.encode("ascii"), validate=True)
    except (UnicodeEncodeError, ValueError) as exc:
        raise _reject("ARTIFACT_RECEIPT_BASE64", role) from exc
    if base64.b64encode(receipt_bytes).decode("ascii") != proof:
        raise _reject("ARTIFACT_RECEIPT_BASE64", role)
    if (
        len(receipt_bytes) != role_ref["receipt_bytes"]
        or hashlib.sha256(receipt_bytes).hexdigest() != role_ref["receipt_sha256"]
    ):
        raise _reject("ARTIFACT_RECEIPT_MISMATCH", role)
    receipt = _mapping(
        _parse_json(receipt_bytes, label=f"{role.upper()}_RECEIPT"),
        code="ARTIFACT_RECEIPT_SCHEMA",
        label=role,
    )
    if frozenset(receipt) != frozenset({"inner", "journal", "metadata"}):
        raise _reject("ARTIFACT_RECEIPT_SCHEMA", role)
    inner = _mapping(receipt.get("inner"), code="ARTIFACT_RECEIPT_SCHEMA", label=f"{role}.inner")
    if frozenset(inner) != frozenset({"Succinct"}):
        raise _reject("ARTIFACT_RECEIPT_KIND", role)
    succinct = _mapping(inner["Succinct"], code="ARTIFACT_RECEIPT_SCHEMA", label=f"{role}.succinct")
    security = pair["receipt_security"]
    metadata = _mapping(
        receipt.get("metadata"), code="ARTIFACT_RECEIPT_SCHEMA", label=f"{role}.metadata"
    )
    if (
        succinct.get("hashfn") != security["hashfn"]
        or _u32_digest_hex(succinct.get("control_id"), label=f"{role}.control_id")
        != security["control_id"]
    ):
        raise _reject("ARTIFACT_RECEIPT_SECURITY", role)
    if (
        _u32_digest_hex(
            metadata.get("verifier_parameters"), label=f"{role}.metadata.verifier_parameters"
        )
        != security["verifier_parameters"]
        or _u32_digest_hex(
            succinct.get("verifier_parameters"), label=f"{role}.succinct.verifier_parameters"
        )
        != security["verifier_parameters"]
    ):
        raise _reject("ARTIFACT_RECEIPT_SECURITY", role)
    journal = _mapping(value.get("journal"), code="ARTIFACT_SCHEMA", label=f"{role}.journal")
    selected = (
        "level",
        "profile",
        "tree_height",
        "subtree_node_count",
        "immediate_child_count",
        "flat_leaf_count",
    )
    for key in selected:
        if journal.get(key) != role_ref[key]:
            raise _reject("ARTIFACT_JOURNAL_SURFACE", f"{role}.{key}")
    if journal.get("self_image_id") != program["generated_image_id_words"]:
        raise _reject("ARTIFACT_JOURNAL_SURFACE", f"{role}.self_image_id")
    return {
        "sha256": digest.sha256,
        "receipt_sha256": role_ref["receipt_sha256"],
        "receipt_bytes": len(receipt_bytes),
    }


def _check_transcript(path: Path, reference: Mapping[str, Any], *, label: str) -> None:
    digest = _read_regular(path, label=label, max_bytes=MAX_TRANSCRIPT_BYTES)
    if digest.sha256 != reference["sha256"] or digest.size_bytes != reference["size_bytes"]:
        raise _reject("TRANSCRIPT_MISMATCH", label)
    value = _parse_json(digest.raw, label=label.upper())
    if value != reference["value"]:
        raise _reject("TRANSCRIPT_VALUE_MISMATCH", label)


def _check_toolchain(risc0_home: Path, rustup_path: Path | None) -> Mapping[str, Any]:
    report = toolchain_lock.check_risc0_recursive_toolchain_lock(
        verify_installed=True,
        risc0_home=risc0_home,
        rustup_path=rustup_path,
    )
    if not report.get("ok"):
        raise _reject("TOOLCHAIN_LOCK_MISMATCH", ";".join(map(str, report.get("errors", ()))))
    return report


def _toolchain_artifact(
    reference: Mapping[str, Any], risc0_home: Path, artifact_id: str
) -> tuple[Path, Mapping[str, Any]]:
    manifest = toolchain_lock.load_lock_manifest()
    if (
        toolchain_lock._canonical_manifest_sha256(manifest)
        != reference["build_policy"]["toolchain_lock_canonical_sha256"]
    ):
        raise _reject("TOOLCHAIN_LOCK_MISMATCH", "manifest digest")
    artifact = next(
        (item for item in manifest["installed_artifacts"] if item["id"] == artifact_id), None
    )
    if artifact is None:
        raise _reject("TOOLCHAIN_LOCK_MISMATCH", artifact_id)
    path = risc0_home.joinpath(*PurePosixPath(artifact["relative_path"]).parts)
    return path, artifact


def _run_pinned(
    executable: Path,
    executable_ref: Mapping[str, Any],
    arguments: Sequence[tuple[Path | None, str]],
    *,
    env: Mapping[str, str],
    timeout: int,
) -> bytes:
    if not Path("/proc/self/fd").is_dir():
        raise _reject("PLATFORM_UNSUPPORTED", "/proc/self/fd")
    opened: list[tuple[int, os.stat_result]] = []
    try:
        input_paths = [
            executable,
            *(argument_path for argument_path, _ in arguments if argument_path is not None),
        ]
        for input_path in input_paths:
            absolute = _canonical_path(input_path, label="execution input", directory=False)
            fd = os.open(absolute, os.O_RDONLY | os.O_NOFOLLOW)
            before = os.fstat(fd)
            if not stat.S_ISREG(before.st_mode):
                raise _reject("EXECUTION_INPUT_INVALID", str(input_path))
            os.set_inheritable(fd, True)
            opened.append((fd, before))
        executable_fd = opened[0][0]
        executable_digest = _hash_open_descriptor(
            executable_fd,
            int(executable_ref.get("max_size_bytes", MAX_VERIFIER_BYTES)),
        )
        if (
            executable_digest.sha256 != executable_ref["sha256"]
            or executable_digest.size_bytes != executable_ref["size_bytes"]
        ):
            raise _reject("EXECUTABLE_MISMATCH", str(executable))
        data_index = 1
        argv = [f"/proc/self/fd/{executable_fd}"]
        for argument_path, literal in arguments:
            if argument_path is None:
                argv.append(literal)
            else:
                argv.append(f"/proc/self/fd/{opened[data_index][0]}")
                data_index += 1
        result = subprocess.run(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=dict(env),
            pass_fds=tuple(fd for fd, _ in opened),
            timeout=timeout,
            check=False,
        )
        if (
            len(result.stdout) > MAX_COMMAND_OUTPUT_BYTES
            or len(result.stderr) > MAX_COMMAND_OUTPUT_BYTES
        ):
            raise _reject("COMMAND_OUTPUT_LIMIT", str(executable))
        if result.returncode != 0:
            detail = result.stderr.decode("utf-8", errors="replace")[:4096]
            raise _reject("COMMAND_FAILED", f"{executable.name}:{detail}")
        for fd, before in opened:
            if _stat_identity(before) != _stat_identity(os.fstat(fd)):
                raise _reject("EXECUTION_INPUT_CHANGED", str(fd))
        return result.stdout
    except subprocess.TimeoutExpired as exc:
        raise _reject("COMMAND_TIMEOUT", executable.name) from exc
    finally:
        for fd, _ in opened:
            os.close(fd)


def _hash_open_descriptor(descriptor: int, max_bytes: int) -> FileDigest:
    before = os.fstat(descriptor)
    if before.st_size < 0 or before.st_size > max_bytes:
        raise _reject("FILE_BOUNDS", "open descriptor")
    digest = hashlib.sha256()
    offset = 0
    while offset < before.st_size:
        chunk = os.pread(descriptor, min(READ_CHUNK_BYTES, before.st_size - offset), offset)
        if not chunk:
            break
        digest.update(chunk)
        offset += len(chunk)
    after = os.fstat(descriptor)
    if offset != before.st_size or _stat_identity(before) != _stat_identity(after):
        raise _reject("FILE_CHANGED", "open descriptor")
    return FileDigest(b"", digest.hexdigest(), offset)


def _sanitized_execution_env(home: Path) -> dict[str, str]:
    return {"HOME": str(home), "LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin", "TZ": "UTC"}


def _run_live_verification(
    reference: Mapping[str, Any],
    program_path: Path,
    verifier_path: Path,
    inner_path: Path,
    root_path: Path,
    risc0_home: Path,
    home: Path,
) -> dict[str, Any]:
    r0vm_path, r0vm_ref = _toolchain_artifact(reference, risc0_home, "r0vm")
    image_stdout = _run_pinned(
        r0vm_path,
        r0vm_ref,
        [(None, "--id"), (None, "--elf"), (program_path, "")],
        env=_sanitized_execution_env(home),
        timeout=COMMAND_TIMEOUT_SECONDS,
    )
    try:
        image_id = image_stdout.decode("ascii").strip()
    except UnicodeDecodeError as exc:
        raise _reject("IMAGE_ID_OUTPUT", "non-ASCII") from exc
    if image_id != reference["program"]["image_id"]:
        raise _reject("IMAGE_ID_MISMATCH", image_id)
    verifier_ref = reference["proof_pair"]["static_verifier"]
    pair_stdout = _run_pinned(
        verifier_path,
        verifier_ref,
        [(inner_path, ""), (root_path, "")],
        env=_sanitized_execution_env(home),
        timeout=COMMAND_TIMEOUT_SECONDS,
    )
    expected = reference["proof_pair"]["pair_verifier_output"]
    if (
        hashlib.sha256(pair_stdout).hexdigest() != expected["sha256"]
        or len(pair_stdout) != expected["size_bytes"]
    ):
        raise _reject("PAIR_VERIFIER_OUTPUT_MISMATCH", hashlib.sha256(pair_stdout).hexdigest())
    if _parse_json(pair_stdout, label="PAIR_VERIFIER_OUTPUT") != expected["value"]:
        raise _reject("PAIR_VERIFIER_OUTPUT_MISMATCH", "value")
    return {"image_id": image_id, "pair_status": expected["value"]["status"]}


def _compiled_registry_packages(
    target_root: Path, cargo_home: Path, lock_path: Path
) -> list[tuple[str, str, str]]:
    registry_root = _canonical_path(
        cargo_home / "registry/src", label="registry source", directory=True
    )
    indices = sorted(
        path for path in registry_root.iterdir() if path.is_dir() and not path.is_symlink()
    )
    found: set[tuple[str, str]] = set()
    for dep_info in target_root.rglob("*.d"):
        digest = _read_regular(dep_info, label="dep-info", max_bytes=MAX_DEP_INFO_BYTES)
        text = digest.raw.decode("utf-8", errors="ignore")
        for registry_index_path in indices:
            pattern = re.compile(re.escape(str(registry_index_path)) + r"/([^/\\\s:]+)")
            found.update(
                (registry_index_path.name, match.group(1)) for match in pattern.finditer(text)
            )
    lock = tomllib.loads(
        _read_regular(lock_path, label="Cargo.lock", max_bytes=MAX_SOURCE_FILE_BYTES).raw.decode(
            "utf-8"
        )
    )
    packages = {
        f"{item['name']}-{item['version']}": str(item["checksum"])
        for item in lock.get("package", [])
        if str(item.get("source", "")).startswith("registry+")
        and isinstance(item.get("checksum"), str)
    }
    rows: list[tuple[str, str, str]] = []
    for index_name, package_dir in sorted(found):
        checksum = packages.get(package_dir)
        if checksum is None or SHA256_RE.fullmatch(checksum) is None:
            raise _reject("REGISTRY_PACKAGE_NOT_LOCKED", package_dir)
        rows.append((index_name, package_dir, checksum))
    if not rows:
        raise _reject("REGISTRY_SOURCE_EMPTY", "no compiled registry packages")
    return rows


def _registry_root(rows: Sequence[tuple[str, str, str]]) -> str:
    digest = hashlib.sha256()
    for _, package_dir, checksum in sorted(rows, key=lambda item: item[1]):
        digest.update(package_dir.encode("ascii"))
        digest.update(b"\x00")
        digest.update(checksum.encode("ascii"))
        digest.update(b"\x00")
    return digest.hexdigest()


def _check_registry_sources(
    reference: Mapping[str, Any], target_root: Path, cargo_home: Path, lock_path: Path
) -> dict[str, Any]:
    rows = _compiled_registry_packages(target_root, cargo_home, lock_path)
    expected = reference["source_compile"]["registry_source_closure"]
    root = _registry_root(rows)
    if len(rows) != expected["package_count"] or root != expected["root_sha256"]:
        raise _reject("REGISTRY_SOURCE_ROOT_MISMATCH", f"count={len(rows)}:root={root}")
    total = 0
    for index, package_dir, checksum in rows:
        source_dir = cargo_home / "registry/src" / index / package_dir
        archive = cargo_home / "registry/cache" / index / f"{package_dir}.crate"
        archive_digest = _read_regular(
            archive, label=f"crate archive {package_dir}", max_bytes=MAX_CRATE_ARCHIVE_BYTES
        )
        if archive_digest.sha256 != checksum:
            raise _reject("CRATE_ARCHIVE_MISMATCH", package_dir)
        expected_files = _crate_archive_files(archive_digest.raw, package_dir)
        observed_files: dict[str, str] = {}
        entries = 0
        for directory, dirnames, filenames in os.walk(source_dir, followlinks=False):
            entries += len(dirnames) + len(filenames)
            if entries > MAX_DISCOVERY_ENTRIES:
                raise _reject("REGISTRY_DISCOVERY_LIMIT", package_dir)
            base = Path(directory)
            for name in dirnames:
                if (base / name).is_symlink():
                    raise _reject("SYMLINK_FORBIDDEN", f"{package_dir}/{name}")
            for name in filenames:
                path = base / name
                if path.is_symlink():
                    raise _reject("SYMLINK_FORBIDDEN", str(path))
                relative = path.relative_to(source_dir).as_posix()
                if relative == ".cargo-ok":
                    continue
                file_digest = _read_regular(
                    path,
                    label=f"registry source {package_dir}/{relative}",
                    max_bytes=MAX_CRATE_MEMBER_BYTES,
                )
                total += file_digest.size_bytes
                if total > MAX_REGISTRY_SOURCE_BYTES:
                    raise _reject("REGISTRY_SOURCE_BYTES_LIMIT", str(total))
                observed_files[relative] = file_digest.sha256
        if observed_files != expected_files:
            raise _reject("REGISTRY_EXTRACTED_TREE_MISMATCH", package_dir)
    return {"package_count": len(rows), "root_sha256": root, "verified_source_bytes": total}


def _crate_archive_files(raw: bytes, package_dir: str) -> dict[str, str]:
    files: dict[str, str] = {}
    try:
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:gz") as archive:
            for member in archive:
                path = PurePosixPath(member.name)
                if (
                    not path.parts
                    or path.parts[0] != package_dir
                    or any(part in {"", ".", ".."} for part in path.parts)
                ):
                    raise _reject("CRATE_ARCHIVE_PATH", member.name)
                if member.isdir():
                    continue
                if not member.isfile() or member.size < 0 or member.size > MAX_CRATE_MEMBER_BYTES:
                    raise _reject("CRATE_ARCHIVE_MEMBER", member.name)
                relative = PurePosixPath(*path.parts[1:]).as_posix()
                if not relative or relative in files:
                    raise _reject("CRATE_ARCHIVE_PATH", member.name)
                extracted = archive.extractfile(member)
                if extracted is None:
                    raise _reject("CRATE_ARCHIVE_MEMBER", member.name)
                data = extracted.read(MAX_CRATE_MEMBER_BYTES + 1)
                if len(data) != member.size or len(data) > MAX_CRATE_MEMBER_BYTES:
                    raise _reject("CRATE_ARCHIVE_MEMBER", member.name)
                files[relative] = hashlib.sha256(data).hexdigest()
    except (tarfile.TarError, OSError) as exc:
        raise _reject("CRATE_ARCHIVE_INVALID", package_dir) from exc
    return files


def _base_report(mode: str) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": False,
        "mode": mode,
        "status": "rejected",
        "error_codes": [],
        "errors": [],
        "pinned_artifact_match": False,
        "same_host_clean_rebuild": False,
        "source_closure_exact": False,
        "registry_source_closure_exact": False,
        "effective_cargo_configs_exact": False,
        "pinned_toolchain_artifacts_matched": False,
        "build_command_constrained": False,
        "build_environment_constrained": False,
        "outer_cargo_constrained": False,
        "guest_build_nested_cargo_constrained_and_observed": False,
        "cargo_offline_enforced": False,
        "raw_elf_match": False,
        "combined_program_match": False,
        "independent_image_id_match": False,
        "live_pair_verification": False,
        "static_verifier_bytes_match": False,
        "two_leaf_static_verifier_bytes_match": False,
        "proxy_interpreter_authenticated": False,
        "source_archive_provenance_authenticated": False,
        "builder_identity_authenticated": False,
        "proof_regeneration_determinism": False,
        "whole_build_network_isolation": False,
        "full_toolchain_execution_authenticated": False,
        "runtime_rootfs_authenticated": False,
        "cross_environment_reproducibility": False,
        "production_ready": False,
        "public_claim_allowed": False,
        "settlement_authorization": False,
    }


def _failure(report: dict[str, Any], error: EvidenceError) -> dict[str, Any]:
    report["error_codes"] = [error.code]
    report["errors"] = [error.detail]
    return report


def check_candidate(
    *,
    repository_root: Path,
    build_target_root: Path,
    inner_artifact_path: Path,
    root_artifact_path: Path,
    missing_assumption_transcript_path: Path,
    risc0_home: Path,
    cargo_home: Path,
    rustup_path: Path | None,
    clean_observation: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    mode = "clean_rebuild" if clean_observation is not None else "candidate"
    report = _base_report(mode)
    try:
        reference = load_reference()
        repository = _canonical_path(repository_root, label="repository root", directory=True)
        target = _canonical_path(build_target_root, label="build target", directory=True)
        risc0 = _canonical_path(risc0_home, label="RISC0_HOME", directory=True)
        cargo = _canonical_path(cargo_home, label="CARGO_HOME", directory=True)
        home = _canonical_path(Path.home(), label="HOME", directory=True)
        if cargo != home / ".cargo" or risc0 != home / ".risc0":
            raise _reject("COMPILER_PATH_POLICY", "HOME-relative Cargo/RISC0 roots required")
        source = _check_source(reference, repository)
        report["source_closure_exact"] = True
        report["source"] = source
        _check_effective_cargo_configs(reference, repository, cargo)
        report["effective_cargo_configs_exact"] = True
        toolchain = _check_toolchain(risc0, rustup_path)
        report["pinned_toolchain_artifacts_matched"] = True
        report["toolchain_verified_artifacts"] = toolchain.get("verified_artifacts", [])
        program = _check_program_and_methods(reference, target)
        report["raw_elf_match"] = True
        report["combined_program_match"] = True
        _check_blob(
            program["verifier_path"],
            reference["proof_pair"]["static_verifier"],
            code="STATIC_VERIFIER",
            max_bytes=MAX_VERIFIER_BYTES,
        )
        report["static_verifier_bytes_match"] = True
        _check_blob(
            program["two_leaf_verifier_path"],
            reference["proof_pair"]["two_leaf_static_verifier"],
            code="TWO_LEAF_STATIC_VERIFIER",
            max_bytes=MAX_VERIFIER_BYTES,
        )
        report["two_leaf_static_verifier_bytes_match"] = True
        registry = _check_registry_sources(
            reference,
            target,
            cargo,
            repository / "zk/recursive_stark_v2_risc0/Cargo.lock",
        )
        report["registry_source_closure_exact"] = True
        report["registry_source"] = registry
        inner = _check_receipt_artifact(reference, inner_artifact_path, role="inner")
        root = _check_receipt_artifact(reference, root_artifact_path, role="root")
        _check_transcript(
            missing_assumption_transcript_path,
            reference["proof_pair"]["missing_assumption_output"],
            label="missing assumption transcript",
        )
        live = _run_live_verification(
            reference,
            program["program_path"],
            program["verifier_path"],
            inner_artifact_path,
            root_artifact_path,
            risc0,
            home,
        )
        report["independent_image_id_match"] = True
        report["live_pair_verification"] = True
        report["artifacts"] = {"inner": inner, "root": root}
        report["live"] = live
        report["pinned_artifact_match"] = True
        report["status"] = reference["claims"]["accepted_candidate_status"]
        if clean_observation is not None:
            _validate_clean_observation(clean_observation, reference, repository, target)
            report["same_host_clean_rebuild"] = True
            report["build_command_constrained"] = True
            report["build_environment_constrained"] = True
            report["outer_cargo_constrained"] = True
            report["guest_build_nested_cargo_constrained_and_observed"] = True
            report["cargo_offline_enforced"] = True
            report["status"] = reference["claims"]["accepted_clean_rebuild_status"]
        report["ok"] = True
    except EvidenceError as error:
        _failure(report, error)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        _failure(report, _reject("UNEXPECTED_ERROR", str(error)))
    return report


NESTED_CARGO_PROXY = r"""#!/usr/bin/python3
import hashlib
import json
import os
import stat
import sys

def fail(message):
    os.write(2, ("nested cargo proxy: " + message + "\n").encode("utf-8"))
    raise SystemExit(97)

required = [
    "ZENODEX_PINNED_CARGO",
    "ZENODEX_PINNED_CARGO_SHA256",
    "ZENODEX_NESTED_CARGO_LOG",
    "ZENODEX_CARGO_HOME",
    "ZENODEX_WORKSPACE",
    "ZENODEX_BUILD_TARGET",
    "ZENODEX_PINNED_RUSTC",
]
if any(name not in os.environ for name in required):
    fail("required environment missing")

cargo = os.path.realpath(os.environ["ZENODEX_PINNED_CARGO"])
fd = os.open(cargo, os.O_RDONLY | os.O_NOFOLLOW)
before = os.fstat(fd)
if not stat.S_ISREG(before.st_mode):
    fail("pinned cargo is not regular")
digest = hashlib.sha256()
offset = 0
while offset < before.st_size:
    chunk = os.pread(fd, min(1024 * 1024, before.st_size - offset), offset)
    if not chunk:
        break
    digest.update(chunk)
    offset += len(chunk)
after = os.fstat(fd)
if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns):
    fail("pinned cargo changed")
if offset != before.st_size or digest.hexdigest() != os.environ["ZENODEX_PINNED_CARGO_SHA256"]:
    fail("pinned cargo digest mismatch")

argv = sys.argv[1:]
workspace = os.path.realpath(os.environ["ZENODEX_WORKSPACE"])
cwd = os.path.realpath(os.getcwd())
if os.path.commonpath([workspace, cwd]) != workspace:
    fail("guest cargo cwd outside workspace")
if not argv or argv[0] != "build" or "--locked" not in argv or "--release" not in argv:
    fail("unexpected guest cargo operation")
if "--target" not in argv or argv[argv.index("--target") + 1] != "riscv32im-risc0-zkvm-elf":
    fail("unexpected guest target")
if "--manifest-path" not in argv or "--target-dir" not in argv:
    fail("guest manifest or target dir missing")
manifest = os.path.realpath(argv[argv.index("--manifest-path") + 1])
expected_manifest = os.path.join(workspace, "methods", "aggregate_v2", "Cargo.toml")
if manifest != expected_manifest:
    fail("unexpected guest manifest")
target = os.path.realpath(argv[argv.index("--target-dir") + 1])
build_target = os.path.realpath(os.environ["ZENODEX_BUILD_TARGET"])
if os.path.commonpath([build_target, target]) != build_target:
    fail("guest target directory outside clean target")
if any(value == "--config" or value.startswith("--config=") for value in argv):
    fail("guest Cargo config override forbidden")
if os.environ.get("RUSTC") != os.environ["ZENODEX_PINNED_RUSTC"]:
    fail("guest rustc path mismatch")

record = {
    "argv": argv,
    "cargo_sha256": digest.hexdigest(),
    "cwd_relative": os.path.relpath(cwd, workspace),
    "manifest_relative": os.path.relpath(manifest, workspace),
    "rustc": os.environ.get("RUSTC"),
    "target_relative": os.path.relpath(target, build_target),
}
encoded = json.dumps(record, sort_keys=True, separators=(",", ":")).encode("ascii") + b"\n"
if len(encoded) > 16384:
    fail("record too large")
log_fd = os.open(os.environ["ZENODEX_NESTED_CARGO_LOG"], os.O_WRONLY | os.O_APPEND | os.O_CREAT | os.O_NOFOLLOW, 0o600)
if os.write(log_fd, encoded) != len(encoded):
    fail("short log write")
os.close(log_fd)

environment = dict(os.environ)
environment["CARGO_HOME"] = os.environ["ZENODEX_CARGO_HOME"]
environment["CARGO_NET_OFFLINE"] = "true"
os.set_inheritable(fd, True)
os.execve("/proc/self/fd/%d" % fd, [cargo, *argv], environment)
"""


def run_clean_rebuild(
    *,
    repository_root: Path,
    clean_root: Path,
    inner_artifact_path: Path,
    root_artifact_path: Path,
    missing_assumption_transcript_path: Path,
    risc0_home: Path,
    cargo_home: Path,
    rustup_path: Path | None,
) -> dict[str, Any]:
    report = _base_report("clean_rebuild")
    try:
        reference = load_reference()
        repository = _canonical_path(repository_root, label="repository root", directory=True)
        risc0 = _canonical_path(risc0_home, label="RISC0_HOME", directory=True)
        cargo = _canonical_path(cargo_home, label="CARGO_HOME", directory=True)
        home = _canonical_path(Path.home(), label="HOME", directory=True)
        if cargo != home / ".cargo" or risc0 != home / ".risc0":
            raise _reject("COMPILER_PATH_POLICY", "HOME-relative Cargo/RISC0 roots required")
        clean = _canonical_new_path(clean_root, label="clean rebuild root")
        _check_source(reference, repository)
        _check_effective_cargo_configs(reference, repository, cargo)
        _check_toolchain(risc0, rustup_path)
        outer_cargo, cargo_ref = _toolchain_artifact(reference, risc0, "cargo")
        rustc, _ = _toolchain_artifact(reference, risc0, "rustc")
        os.mkdir(clean, 0o700)
        proxy_dir = clean / "nested-cargo-proxy"
        tmp_dir = clean / "tmp"
        target = clean / "target"
        proxy_dir.mkdir(mode=0o700)
        tmp_dir.mkdir(mode=0o700)
        proxy = proxy_dir / "cargo"
        proxy.write_text(NESTED_CARGO_PROXY, encoding="ascii", newline="\n")
        proxy.chmod(0o700)
        nested_log = clean / "nested-cargo.jsonl"
        build_log = clean / "build.log"
        workspace = repository / "zk/recursive_stark_v2_risc0"
        policy = reference["build_policy"]
        environment = {
            "HOME": str(home),
            "CARGO_HOME": str(cargo),
            "CARGO_NET_OFFLINE": "true",
            "CARGO_TARGET_DIR": str(target),
            "PATH": f"{proxy_dir}:{outer_cargo.parent}:/usr/bin:/bin",
            "RISC0_HOME": str(risc0),
            "RUSTC": str(rustc),
            "TMPDIR": str(tmp_dir),
            **policy["environment"],
            "ZENODEX_BUILD_TARGET": str(target),
            "ZENODEX_CARGO_HOME": str(cargo),
            "ZENODEX_NESTED_CARGO_LOG": str(nested_log),
            "ZENODEX_PINNED_CARGO": str(outer_cargo),
            "ZENODEX_PINNED_CARGO_SHA256": str(cargo_ref["sha256"]),
            "ZENODEX_PINNED_RUSTC": str(rustc),
            "ZENODEX_WORKSPACE": str(workspace),
        }
        command = [str(outer_cargo), *policy["cargo_arguments"]]
        old_umask = os.umask(0o077)
        try:
            _run_build(command, workspace, environment, build_log)
        finally:
            os.umask(old_umask)
        build_digest = _read_regular(build_log, label="build log", max_bytes=MAX_BUILD_LOG_BYTES)
        nested = _read_nested_log(nested_log)
        observation = {
            "build_log_sha256": build_digest.sha256,
            "nested_cargo_events": nested,
            "outer_cargo_sha256": cargo_ref["sha256"],
            "pinned_rustc": str(rustc),
            "target_was_absent": True,
        }
        report = check_candidate(
            repository_root=repository,
            build_target_root=target,
            inner_artifact_path=inner_artifact_path,
            root_artifact_path=root_artifact_path,
            missing_assumption_transcript_path=missing_assumption_transcript_path,
            risc0_home=risc0,
            cargo_home=cargo,
            rustup_path=rustup_path,
            clean_observation=observation,
        )
        report["clean_rebuild_root"] = str(clean)
        report["build_log_sha256"] = build_digest.sha256
    except EvidenceError as error:
        _failure(report, error)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        _failure(report, _reject("UNEXPECTED_ERROR", str(error)))
    return report


def _run_build(command: Sequence[str], cwd: Path, env: Mapping[str, str], log_path: Path) -> None:
    with log_path.open("xb") as log:
        process = subprocess.Popen(
            list(command),
            cwd=cwd,
            env=dict(env),
            stdin=subprocess.DEVNULL,
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            returncode = process.wait(timeout=BUILD_TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired as exc:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise _reject("BUILD_TIMEOUT", str(BUILD_TIMEOUT_SECONDS)) from exc
    if returncode != 0:
        with log_path.open("rb") as log:
            log.seek(max(0, log_path.stat().st_size - 4096))
            tail = log.read(4096).decode("utf-8", errors="replace")
        raise _reject("BUILD_FAILED", tail)


def _read_nested_log(path: Path) -> list[Mapping[str, Any]]:
    digest = _read_regular(path, label="nested Cargo log", max_bytes=MAX_TRANSCRIPT_BYTES)
    lines = digest.raw.splitlines()
    if len(lines) != 1 or not lines[0]:
        raise _reject("NESTED_CARGO_EVENT_COUNT", str(len(lines)))
    event = _mapping(
        _parse_json(lines[0], label="NESTED_CARGO_EVENT"), code="NESTED_CARGO_EVENT", label="event"
    )
    expected_keys = frozenset(
        {"argv", "cargo_sha256", "cwd_relative", "manifest_relative", "rustc", "target_relative"}
    )
    if frozenset(event) != expected_keys:
        raise _reject("NESTED_CARGO_EVENT", "keys")
    return [event]


def _validate_clean_observation(
    observation: Mapping[str, Any],
    reference: Mapping[str, Any],
    repository: Path,
    target: Path,
) -> None:
    if observation.get("target_was_absent") is not True:
        raise _reject("CLEAN_TARGET_UNOBSERVED", "target")
    events = observation.get("nested_cargo_events")
    if not isinstance(events, list) or len(events) != 1:
        raise _reject(
            "NESTED_CARGO_EVENT_COUNT", str(len(events) if isinstance(events, list) else -1)
        )
    event = _mapping(events[0], code="NESTED_CARGO_EVENT", label="event")
    if event.get("cargo_sha256") != observation.get("outer_cargo_sha256"):
        raise _reject("NESTED_CARGO_BINARY_MISMATCH", str(event.get("cargo_sha256")))
    if event.get("manifest_relative") != "methods/aggregate_v2/Cargo.toml":
        raise _reject("NESTED_CARGO_MANIFEST", str(event.get("manifest_relative")))
    argv = event.get("argv")
    if not isinstance(argv, list) or argv.count("--locked") != 1 or argv.count("--release") != 1:
        raise _reject("NESTED_CARGO_ARGV", str(argv))
    if event.get("rustc") != observation.get("pinned_rustc"):
        raise _reject("NESTED_RUSTC_MISMATCH", str(event.get("rustc")))
    _check_source(reference, repository)
    _canonical_path(target, label="clean target", directory=True)


def _print_human(report: Mapping[str, Any]) -> None:
    print(f"recursive-v2 rebuild evidence: {report['status']}")
    if report.get("errors"):
        for code, detail in zip(report.get("error_codes", ()), report["errors"], strict=False):
            print(f"  {code}: {detail}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, default=ROOT)
    parser.add_argument("--build-target-root", type=Path)
    parser.add_argument("--clean-rebuild-root", type=Path)
    parser.add_argument("--inner-artifact", type=Path, required=True)
    parser.add_argument("--root-artifact", type=Path, required=True)
    parser.add_argument("--missing-assumption-transcript", type=Path, required=True)
    parser.add_argument("--risc0-home", type=Path, required=True)
    parser.add_argument("--cargo-home", type=Path, required=True)
    parser.add_argument("--rustup-path", type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    if (args.build_target_root is None) == (args.clean_rebuild_root is None):
        parser.error("exactly one of --build-target-root or --clean-rebuild-root is required")
    if args.clean_rebuild_root is not None:
        report = run_clean_rebuild(
            repository_root=args.repository_root,
            clean_root=args.clean_rebuild_root,
            inner_artifact_path=args.inner_artifact,
            root_artifact_path=args.root_artifact,
            missing_assumption_transcript_path=args.missing_assumption_transcript,
            risc0_home=args.risc0_home,
            cargo_home=args.cargo_home,
            rustup_path=args.rustup_path,
        )
    else:
        report = check_candidate(
            repository_root=args.repository_root,
            build_target_root=args.build_target_root,
            inner_artifact_path=args.inner_artifact,
            root_artifact_path=args.root_artifact,
            missing_assumption_transcript_path=args.missing_assumption_transcript,
            risc0_home=args.risc0_home,
            cargo_home=args.cargo_home,
            rustup_path=args.rustup_path,
        )
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
