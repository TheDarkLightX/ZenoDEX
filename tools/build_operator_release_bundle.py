#!/usr/bin/env python3
"""Refuse operator releases and build deterministic unadmitted candidates."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import secrets
import stat
import sys
import tarfile
import tempfile
import unicodedata
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, BinaryIO, Iterable, Iterator, cast

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.local_route_quarantine import (  # noqa: E402
    current_local_operator_release_admission_v1,
)

SCHEMA = "zenodex.operator_candidate_bundle.v1"
MAX_ARCHIVE_MEMBER_BYTES_V1 = 64 * 1024 * 1024
MAX_ARCHIVE_TOTAL_BYTES_V1 = 512 * 1024 * 1024
MAX_ARCHIVE_COMPRESSED_BYTES_V1 = MAX_ARCHIVE_TOTAL_BYTES_V1 + 16 * 1024 * 1024
MAX_ARCHIVE_MEMBERS_V1 = 50_000
MAX_ARCHIVE_UNCOMPRESSED_BYTES_V1 = (
    MAX_ARCHIVE_TOTAL_BYTES_V1 + (MAX_ARCHIVE_MEMBERS_V1 + 2) * 2048
)
MAX_MANIFEST_BYTES_V1 = 16 * 1024 * 1024
MAX_RELATIVE_PATH_BYTES_V1 = 1024
MAX_VERSION_BYTES_V1 = 64
MAX_MANIFEST_NESTING_V1 = 8
MAX_MANIFEST_NODES_V1 = MAX_ARCHIVE_MEMBERS_V1 * 5 + 32
CANONICAL_GZIP_HEADER_V1 = bytes.fromhex("1f8b08000000000002ff")
MANIFEST_KEYS_V1 = frozenset(
    {
        "archive_name",
        "archive_sha256",
        "file_count",
        "files",
        "schema",
        "total_size_bytes",
        "version",
    }
)
MANIFEST_FILE_KEYS_V1 = frozenset({"path", "sha256", "size_bytes"})

INCLUDE_PATHS = (
    "bin",
    "scripts",
    "src",
    "tools",
    "config",
    ".docker",
    ".github/workflows/release-integrity.yml",
    "Dockerfile",
    "Dockerfile.hashlocked",
    "Dockerfile.operator-tools",
    "Dockerfile.production-hashlocked",
    "docker-compose.yml",
    "docker-compose.local.yml",
    "docker-compose.local-testnet.yml",
    "docker-compose.two-node.yml",
    "docker-compose.multimachine.yml",
    "docker-compose.permissionless.yml",
    "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
    "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",
    "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
    "generated/perp_python/perp_epoch_isolated_v2_ref.py",
    "generated/perp_python/perp_epoch_isolated_v3_ref.py",
    "packages/zeno-proof-client",
    "requirements-core.lock.txt",
    "requirements-dev.lock.txt",
    "requirements-agents.lock.txt",
    "pyproject.toml",
    "pytest.ini",
    "README.md",
    "docs/DEPLOYMENT_QUICKSTART.md",
    "docs/DOCKER_HASHLOCKED_DEPLOYMENT.md",
    "docs/LOCAL_TESTNET_QUICKSTART.md",
    "docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md",
    "docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md",
    "docs/PUBLIC_TESTNET_V0_1_16.md",
    "docs/LATEST_TESTNET_CHECKPOINT.md",
    "docs/PERMISSIONLESS_HOSTING.md",
    "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md",
    "docs/KEYS_STANDALONE_APP_SPEC.md",
    "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json",
    "docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md",
    "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
    "docs/ZENODEX_LOCAL_SIGNER_SECURITY_MODEL.md",
    "docs/assurance",
    "docs/claims_registry.yaml",
    "docs/tau_supported_runtime_contract.json",
)

REQUIRED_OPERATOR_PATHS = frozenset(
    {
        # Review finding (grade B+ -> A-): archive verification used to prove
        # hash consistency only. An internally consistent operator bundle could
        # omit the production-promotion gate and still verify. These files are
        # the minimum release-evidence toolchain an operator must receive.
        "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md",
        "docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md",
        "docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md",
        "src/integration/production_promotion_evidence.py",
        "tools/autogovnext_governance_lane_assurance_manifest.json",
        "tools/build_app_root_jmt_evidence.py",
        "tools/build_autotrader_evidence.py",
        "tools/build_confidential_runtime_evidence.py",
        "tools/build_hardware_wallet_evidence.py",
        "tools/build_oracle_authority_evidence.py",
        "tools/build_production_promotion_evidence_manifest.py",
        "tools/build_zk_wrapping_evidence_from_risc0_bundle.py",
        "tools/check_production_promotion_evidence_manifest.py",
        "tools/check_autogovnext_governance_lane_assurance_manifest.py",
        "tools/production_promotion_evidence_manifest.json",
        "tools/run_autogovnext_governance_lane_assurance_gate.sh",
        "tools/run_production_promotion_evidence_gate.sh",
    }
)

EXCLUDED_PARTS = {
    ".git",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".tau_history",
    "__pycache__",
    "build",
    "dist",
    "external",
    "internal",
    "mutants",
    "node_modules",
    "runs",
    "target",
    "_secbin",
    ".venv",
    "venv",
}

EXCLUDED_SUFFIXES = (
    ".pyc",
    ".pyo",
    ".log",
    ".tmp",
    ".tau_history",
)


@dataclass(frozen=True)
class BundleFile:
    relative_path: str
    size_bytes: int
    sha256: str


@dataclass(frozen=True, slots=True)
class _CandidateManifestFileV1:
    path: str
    size_bytes: int
    sha256: str


@dataclass(frozen=True, slots=True)
class _CandidateManifestV1:
    version: str
    archive_sha256: str
    files: tuple[_CandidateManifestFileV1, ...]


@dataclass(frozen=True, slots=True)
class _FileIdentityV1:
    device: int
    inode: int
    size_bytes: int
    modified_ns: int
    changed_ns: int

    @classmethod
    def from_stat(cls, value: os.stat_result) -> _FileIdentityV1:
        return cls(
            device=value.st_dev,
            inode=value.st_ino,
            size_bytes=value.st_size,
            modified_ns=value.st_mtime_ns,
            changed_ns=value.st_ctime_ns,
        )


class _ArchiveResourceLimit(ValueError):
    """Raised before a hostile archive can exceed its decompression budget."""


class _BoundedReader(io.RawIOBase):
    """Expose only a fixed number of bytes from a readable binary stream."""

    def __init__(self, reader: Any, limit: int) -> None:
        super().__init__()
        self._reader = reader
        self._limit = limit
        self._consumed = 0

    def read(self, size: int = -1) -> bytes:
        remaining_with_probe = self._limit - self._consumed + 1
        if remaining_with_probe <= 0:
            raise _ArchiveResourceLimit("archive decompression ceiling exceeded")
        bounded_size = remaining_with_probe if size < 0 else min(size, remaining_with_probe)
        payload = self._reader.read(bounded_size)
        self._consumed += len(payload)
        if self._consumed > self._limit:
            raise _ArchiveResourceLimit("archive decompression ceiling exceeded")
        return payload

    def readable(self) -> bool:
        return True


@dataclass(frozen=True)
class OperatorReleaseAdmissionRejectV1(ValueError):
    """Fixed rejection while the current operator profile is ineligible."""

    profile_id: str
    blocker: str

    def __str__(self) -> str:
        return f"OPERATOR_RELEASE_BLOCKED:{self.profile_id}:{self.blocker}"


def build_operator_release_bundle(
    *,
    root: Path = ROOT,
    out_dir: Path,
    version: str,
) -> dict[str, Any]:
    """Refuse release-labelled output until a later profile adds admission."""

    _ = (root, out_dir, version)
    admission = current_local_operator_release_admission_v1()
    raise OperatorReleaseAdmissionRejectV1(
        profile_id=admission.profile_id,
        blocker=admission.blocker,
    )


def build_operator_candidate_bundle(
    *,
    root: Path = ROOT,
    out_dir: Path,
    version: str,
) -> dict[str, Any]:
    """Build a deterministic unadmitted candidate archive for format testing."""

    root = root.resolve()
    safe_version = _safe_version(version)
    archive_name = f"zenodex-operator-candidate-{safe_version}.tar.gz"
    archive_path = out_dir / archive_name
    manifest_path = out_dir / f"{archive_name}.manifest.json"
    with _open_directory_readonly(root) as source_root_fd:
        with _open_candidate_output_directory(out_dir) as output_directory_fd:
            files = _collect_bundle_files(root, source_root_fd=source_root_fd)
            _enforce_candidate_file_limits(files)
            _write_tar_gz(
                source_root_fd=source_root_fd,
                files=files,
                output_directory_fd=output_directory_fd,
                archive_name=archive_name,
                prefix=f"zenodex-operator-candidate-{safe_version}",
            )
            archive_sha256 = _candidate_archive_sha256(
                output_directory_fd,
                archive_name,
            )
            manifest_body = _candidate_manifest_body(
                version=version,
                archive_name=archive_name,
                archive_sha256=archive_sha256,
                files=files,
            )
            _write_candidate_manifest(
                output_directory_fd,
                manifest_path.name,
                manifest_body,
            )
    return {
        "schema": "zenodex.operator_candidate_bundle.build_report.v1",
        "ok": True,
        "status": "UNADMITTED_CANDIDATE_NO_RELEASE_AUTHORITY",
        "release_eligible": False,
        "authority": "NONE",
        "vm_gates_closed": [],
        "archive_path": str(archive_path),
        "manifest_path": str(manifest_path),
        "archive_sha256": archive_sha256,
        "file_count": len(files),
        "total_size_bytes": manifest_body["total_size_bytes"],
    }


def _enforce_candidate_file_limits(files: list[BundleFile]) -> None:
    if not files:
        raise ValueError("operator candidate bundle would be empty")
    if len(files) > MAX_ARCHIVE_MEMBERS_V1:
        raise ValueError("operator candidate bundle exceeds member-count ceiling")
    if any(item.size_bytes > MAX_ARCHIVE_MEMBER_BYTES_V1 for item in files):
        raise ValueError("operator candidate bundle contains an oversize member")
    if sum(item.size_bytes for item in files) > MAX_ARCHIVE_TOTAL_BYTES_V1:
        raise ValueError("operator candidate bundle exceeds payload ceiling")


def _candidate_manifest_body(
    *,
    version: str,
    archive_name: str,
    archive_sha256: str,
    files: list[BundleFile],
) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "version": version,
        "archive_name": archive_name,
        "archive_sha256": archive_sha256,
        "file_count": len(files),
        "total_size_bytes": sum(item.size_bytes for item in files),
        "files": [
            {
                "path": item.relative_path,
                "size_bytes": item.size_bytes,
                "sha256": item.sha256,
            }
            for item in files
        ],
    }


def _candidate_archive_sha256(directory_fd: int, archive_name: str) -> str:
    try:
        with _open_regular_readonly_at(directory_fd, archive_name) as opened:
            archive_file, identity, parent_fd, entry_name = opened
            digest = _sha256_file_bounded(
                archive_file,
                MAX_ARCHIVE_COMPRESSED_BYTES_V1,
            )
            if _opened_entry_status(
                archive_file, identity, parent_fd, entry_name
            ) != "stable":
                raise ValueError("archive changed while building manifest")
            return digest
    except OSError as exc:
        raise ValueError("candidate archive is not a stable regular file") from exc


def _write_candidate_manifest(
    directory_fd: int, name: str, manifest: dict[str, Any]
) -> None:
    payload = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if len(payload) > MAX_MANIFEST_BYTES_V1:
        raise ValueError("operator candidate manifest exceeds byte ceiling")
    _atomic_write_bytes_at(directory_fd, name, payload)


def verify_operator_candidate_manifest(*, manifest_path: Path, archive_path: Path | None = None) -> dict[str, Any]:
    """Verify candidate archive integrity without granting release authority."""
    manifest, errors = _load_candidate_manifest(manifest_path)
    if manifest is None:
        return _verify_report(errors)
    candidate, validation_errors = _validate_candidate_manifest(manifest)
    errors.extend(validation_errors)
    if errors:
        return _verify_report(errors)
    if candidate is None:
        return _verify_report(["manifest validation produced no owned value"])

    archive = archive_path or (
        manifest_path.parent / f"zenodex-operator-candidate-{candidate.version}.tar.gz"
    )
    try:
        with _open_regular_readonly(archive) as (archive_file, identity):
            with tempfile.TemporaryFile(mode="w+b") as snapshot:
                _copy_file_bounded(
                    source=archive_file,
                    destination=snapshot,
                    limit=MAX_ARCHIVE_COMPRESSED_BYTES_V1,
                )
                actual_sha = _sha256_file_bounded(
                    snapshot,
                    MAX_ARCHIVE_COMPRESSED_BYTES_V1,
                )
                source_status = _opened_path_status(archive, archive_file, identity)
                if source_status == "path_changed":
                    return _verify_report(["archive path changed during verification"])
                if source_status != "stable":
                    return _verify_report(["archive changed during verification"])
                if actual_sha != candidate.archive_sha256:
                    return _verify_report(["archive_sha256 mismatch"])
                if not _has_canonical_gzip_header(snapshot):
                    return _verify_report(["archive gzip header is non-canonical"])
                archive_errors = _verify_archive_file(
                    archive_file=snapshot,
                    manifest=candidate,
                )
                source_status = _opened_path_status(archive, archive_file, identity)
                if source_status == "path_changed":
                    return _verify_report(["archive path changed during verification"])
                if source_status != "stable":
                    return _verify_report(["archive changed during verification"])
    except (OSError, ValueError):
        return _verify_report(["archive cannot be read within resource ceiling"])
    return _verify_report(archive_errors)


def _load_candidate_manifest(manifest_path: Path) -> tuple[dict[str, Any] | None, list[str]]:
    try:
        manifest_bytes = _read_bounded(manifest_path, MAX_MANIFEST_BYTES_V1)
        decoded = json.loads(
            manifest_bytes.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_json_keys,
        )
    except RecursionError:
        return None, ["manifest cannot be parsed within structural resource ceiling"]
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError):
        return None, ["manifest cannot be parsed within resource ceiling"]
    if not isinstance(decoded, dict):
        return None, ["manifest must be a JSON object"]
    if not _json_structure_within_budget(decoded):
        return decoded, ["manifest exceeds structural resource ceiling"]
    canonical = (json.dumps(decoded, indent=2, sort_keys=True) + "\n").encode("utf-8")
    errors = [] if manifest_bytes == canonical else ["manifest encoding is non-canonical"]
    return decoded, errors


def _validate_candidate_manifest(
    manifest: dict[str, Any],
) -> tuple[_CandidateManifestV1 | None, list[str]]:
    errors: list[str] = []
    if set(manifest) != MANIFEST_KEYS_V1:
        errors.append("manifest fields mismatch")
    if manifest.get("schema") != SCHEMA:
        errors.append("manifest schema mismatch")

    version = manifest.get("version")
    try:
        safe_version = _safe_version(version)
    except (TypeError, ValueError):
        safe_version = None
        errors.append("manifest version is invalid")
    expected_archive_name = (
        f"zenodex-operator-candidate-{safe_version}.tar.gz"
        if safe_version is not None
        else None
    )
    archive_name = manifest.get("archive_name")
    if archive_name != expected_archive_name:
        errors.append("manifest archive_name mismatch")
    if not _looks_sha256(manifest.get("archive_sha256")):
        errors.append("manifest archive_sha256 is invalid")

    files, seen, total_size_bytes, file_errors = _validate_manifest_files(manifest)
    errors.extend(file_errors)
    manifest_total = manifest.get("total_size_bytes")
    if (
        type(manifest_total) is not int
        or manifest_total != total_size_bytes
        or manifest_total > MAX_ARCHIVE_TOTAL_BYTES_V1
    ):
        errors.append("manifest total_size_bytes mismatch")
    for required_path in sorted(REQUIRED_OPERATOR_PATHS - seen):
        errors.append(f"missing required operator file: {required_path}")
    if errors or safe_version is None:
        return None, errors
    return (
        _CandidateManifestV1(
            version=safe_version,
            archive_sha256=cast(str, manifest["archive_sha256"]),
            files=files,
        ),
        [],
    )


def _validate_manifest_files(
    manifest: dict[str, Any],
) -> tuple[tuple[_CandidateManifestFileV1, ...], set[str], int, list[str]]:
    errors: list[str] = []
    raw_files = manifest.get("files")
    files = raw_files if isinstance(raw_files, list) else []
    if not files:
        errors.append("manifest files must be a non-empty list")
    file_count = manifest.get("file_count")
    if (
        type(file_count) is not int
        or file_count != len(files)
        or file_count > MAX_ARCHIVE_MEMBERS_V1
    ):
        errors.append("manifest file_count mismatch")
    seen: set[str] = set()
    declared_paths: list[str] = []
    validated: list[_CandidateManifestFileV1] = []
    total_size_bytes = 0
    for index, item in enumerate(files):
        if not isinstance(item, dict):
            errors.append(f"files[{index}] must be an object")
            continue
        if set(item) != MANIFEST_FILE_KEYS_V1:
            errors.append(f"files[{index}] fields mismatch")
        relpath = _validated_manifest_path(item, index, errors)
        if relpath is None:
            continue
        if relpath in seen:
            errors.append(f"duplicate file path: {relpath}")
        seen.add(relpath)
        declared_paths.append(relpath)
        size_bytes = item.get("size_bytes")
        if (
            type(size_bytes) is not int
            or size_bytes < 0
            or size_bytes > MAX_ARCHIVE_MEMBER_BYTES_V1
        ):
            errors.append(f"invalid file size: {relpath}")
        else:
            total_size_bytes += size_bytes
        sha256 = item.get("sha256")
        if not _looks_sha256(sha256):
            errors.append(f"invalid file sha256: {relpath}")
        if (
            type(size_bytes) is int
            and 0 <= size_bytes <= MAX_ARCHIVE_MEMBER_BYTES_V1
            and _looks_sha256(sha256)
        ):
            validated.append(
                _CandidateManifestFileV1(
                    path=relpath,
                    size_bytes=size_bytes,
                    sha256=cast(str, sha256),
                )
            )
    if declared_paths != sorted(declared_paths):
        errors.append("manifest file rows are not in canonical order")
    return tuple(validated), seen, total_size_bytes, errors


def _validated_manifest_path(
    item: dict[str, Any], index: int, errors: list[str]
) -> str | None:
    relpath = item.get("path")
    if type(relpath) is not str or not relpath:
        errors.append(f"files[{index}].path must be non-empty")
        return None
    if not _is_safe_relative_path(relpath):
        errors.append(f"files[{index}].path is unsafe or non-canonical")
        return None
    return relpath


def _verify_report(errors: list[str]) -> dict[str, Any]:
    return {
        "schema": "zenodex.operator_candidate_bundle.verify_report.v1",
        "ok": not errors,
        "errors": errors,
    }


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _json_structure_within_budget(value: object) -> bool:
    stack: list[tuple[object, int]] = [(value, 1)]
    observed_nodes = 0
    while stack:
        current, depth = stack.pop()
        observed_nodes += 1
        if depth > MAX_MANIFEST_NESTING_V1 or observed_nodes > MAX_MANIFEST_NODES_V1:
            return False
        if isinstance(current, dict):
            stack.extend((item, depth + 1) for item in current.values())
        elif isinstance(current, list):
            stack.extend((item, depth + 1) for item in current)
    return True


def _collect_bundle_files(root: Path, *, source_root_fd: int) -> list[BundleFile]:
    relpaths: set[str] = set()
    for include in INCLUDE_PATHS:
        path = root / include
        if path.is_symlink():
            raise ValueError("bundle source must be a stable regular file")
        if path.is_file():
            relpaths.add(include)
        elif path.is_dir():
            for child in sorted(path.rglob("*")):
                if child.is_symlink():
                    raise ValueError("bundle source must be a stable regular file")
                if child.is_file():
                    rel = child.relative_to(root).as_posix()
                    if _include_file(rel):
                        relpaths.add(rel)

    return [
        _bundle_file_from_source(source_root_fd, relpath)
        for relpath in sorted(relpaths)
    ]


def _bundle_file_from_source(source_root_fd: int, relpath: str) -> BundleFile:
    try:
        with _open_regular_readonly_at(source_root_fd, relpath) as opened:
            source, identity, parent_fd, entry_name = opened
            if identity.size_bytes > MAX_ARCHIVE_MEMBER_BYTES_V1:
                raise ValueError("operator candidate bundle contains an oversize member")
            digest = _sha256_file_bounded(source, MAX_ARCHIVE_MEMBER_BYTES_V1)
            if _opened_entry_status(
                source, identity, parent_fd, entry_name
            ) != "stable":
                raise ValueError("bundle source changed while hashing")
            return BundleFile(
                relative_path=relpath,
                size_bytes=identity.size_bytes,
                sha256=digest,
            )
    except OSError as exc:
        raise ValueError("bundle source must be a stable regular file") from exc


def _include_file(relpath: str) -> bool:
    path = Path(relpath)
    if not _is_safe_relative_path(relpath):
        return False
    if any(part in EXCLUDED_PARTS for part in path.parts):
        return False
    if relpath.endswith(EXCLUDED_SUFFIXES):
        return False
    return True


def _is_safe_relative_path(relpath: str) -> bool:
    if type(relpath) is not str or not relpath:
        return False
    try:
        encoded_path = relpath.encode("utf-8")
    except UnicodeEncodeError:
        return False
    if (
        len(encoded_path) > MAX_RELATIVE_PATH_BYTES_V1
        or unicodedata.normalize("NFC", relpath) != relpath
        or any(unicodedata.category(char) in {"Cf", "Cs"} for char in relpath)
        or relpath.startswith("/")
        or "\\" in relpath
        or any(ord(char) < 32 or ord(char) == 127 for char in relpath)
    ):
        return False
    return all(part not in {"", ".", ".."} for part in relpath.split("/"))


@contextmanager
def _atomic_binary_output_at(directory_fd: int, final_name: str) -> Iterator[BinaryIO]:
    if not final_name or "/" in final_name or "\\" in final_name:
        raise ValueError("atomic output name must be one canonical path component")
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_EXCL
        | _no_follow_flag()
        | getattr(os, "O_CLOEXEC", 0)
    )
    fd = -1
    temp_name = ""
    for _attempt in range(16):
        temp_name = f".{final_name}.{secrets.token_hex(16)}.tmp"
        try:
            fd = os.open(temp_name, flags, 0o600, dir_fd=directory_fd)
            break
        except FileExistsError:
            continue
    if fd < 0:
        raise OSError("could not allocate an exclusive temporary output")
    try:
        raw = os.fdopen(fd, "wb")
        fd = -1
        with raw:
            yield raw
            raw.flush()
            os.fsync(raw.fileno())
        os.replace(
            temp_name,
            final_name,
            src_dir_fd=directory_fd,
            dst_dir_fd=directory_fd,
        )
    finally:
        if fd >= 0:
            os.close(fd)
        try:
            os.unlink(temp_name, dir_fd=directory_fd)
        except FileNotFoundError:
            pass


def _atomic_write_bytes_at(directory_fd: int, name: str, payload: bytes) -> None:
    with _atomic_binary_output_at(directory_fd, name) as output:
        output.write(payload)


def _write_tar_gz(
    *,
    source_root_fd: int,
    files: Iterable[BundleFile],
    output_directory_fd: int,
    archive_name: str,
    prefix: str,
) -> None:
    with _atomic_binary_output_at(output_directory_fd, archive_name) as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as tar:
                for item in files:
                    _add_bundle_member(
                        tar=tar,
                        source_root_fd=source_root_fd,
                        item=item,
                        prefix=prefix,
                    )


def _add_bundle_member(
    *, tar: tarfile.TarFile, source_root_fd: int, item: BundleFile, prefix: str
) -> None:
    try:
        with _open_regular_readonly_at(source_root_fd, item.relative_path) as opened:
            source, identity, parent_fd, entry_name = opened
            with tempfile.TemporaryFile(mode="w+b") as snapshot:
                copied = _copy_file_bounded(
                    source=source,
                    destination=snapshot,
                    limit=MAX_ARCHIVE_MEMBER_BYTES_V1,
                )
                digest = _sha256_file_bounded(snapshot, MAX_ARCHIVE_MEMBER_BYTES_V1)
                if (
                    copied != item.size_bytes
                    or digest != item.sha256
                    or _opened_entry_status(
                        source, identity, parent_fd, entry_name
                    )
                    != "stable"
                ):
                    raise ValueError("bundle source changed before archive capture")
                snapshot.seek(0)
                tar.addfile(_canonical_tar_info(item, prefix=prefix), snapshot)
    except OSError as exc:
        raise ValueError("bundle source must be a stable regular file") from exc


def _canonical_tar_info(item: BundleFile, *, prefix: str) -> tarfile.TarInfo:
    info = tarfile.TarInfo(f"{prefix}/{item.relative_path}")
    info.size = item.size_bytes
    info.mode = _canonical_archive_mode(item.relative_path)
    info.uid = 0
    info.gid = 0
    info.uname = ""
    info.gname = ""
    info.mtime = 0
    info.pax_headers = {}
    return info


def _canonical_archive_mode(relpath: str) -> int:
    return 0o755 if relpath.startswith("bin/") or relpath.endswith(".sh") else 0o644


def _verify_archive_members(*, archive: Path, manifest: _CandidateManifestV1) -> list[str]:
    try:
        with _open_regular_readonly(archive) as (archive_file, _identity):
            return _verify_archive_file(
                archive_file=archive_file,
                manifest=manifest,
            )
    except OSError:
        return ["archive cannot be parsed"]


def _verify_archive_file(
    *, archive_file: BinaryIO, manifest: _CandidateManifestV1
) -> list[str]:
    expected = {item.path: item for item in manifest.files}
    prefix = f"zenodex-operator-candidate-{manifest.version}/"
    try:
        archive_file.seek(0)
        with gzip.GzipFile(fileobj=archive_file, mode="rb") as decompressed:
            bounded = _BoundedReader(
                decompressed,
                MAX_ARCHIVE_UNCOMPRESSED_BYTES_V1,
            )
            with tarfile.open(fileobj=bounded, mode="r|") as tar:
                errors, observed, member_count = _verify_archive_stream_members(
                    tar=tar,
                    expected=expected,
                    expected_order=tuple(item.path for item in manifest.files),
                    prefix=prefix,
                )
    except (OSError, EOFError, tarfile.TarError):
        return ["archive cannot be parsed"]
    except _ArchiveResourceLimit:
        return ["archive decompression exceeds resource ceiling"]
    missing = sorted(set(expected) - observed)
    for relpath in missing:
        errors.append(f"archive missing manifest file: {relpath}")
    if member_count != len(expected):
        errors.append("archive member count differs from manifest")
    return errors


def _verify_archive_stream_members(
    *,
    tar: tarfile.TarFile,
    expected: dict[str, _CandidateManifestFileV1],
    expected_order: tuple[str, ...],
    prefix: str,
) -> tuple[list[str], set[str], int]:
    errors: list[str] = []
    observed: set[str] = set()
    member_names: set[str] = set()
    member_count = 0
    total_payload_bytes = 0
    for member in tar:
        member_count += 1
        if member_count > MAX_ARCHIVE_MEMBERS_V1:
            errors.append("archive member count exceeds resource ceiling")
            break
        if not member.isfile():
            errors.append(f"archive contains non-regular member: {member.name}")
            break
        if member.name in member_names:
            errors.append(f"archive contains duplicate member: {member.name}")
            break
        member_names.add(member.name)
        if not member.name.startswith(prefix):
            errors.append(f"archive member outside bundle prefix: {member.name}")
            break
        relpath = member.name[len(prefix) :]
        if not _is_safe_relative_path(relpath):
            errors.append(f"archive contains non-canonical member path: {relpath}")
            break
        if (
            member_count > len(expected_order)
            or relpath != expected_order[member_count - 1]
        ):
            errors.append("archive members are not in canonical manifest order")
            break
        if relpath in observed:
            errors.append(f"archive contains duplicate file: {relpath}")
            break
        observed.add(relpath)
        expected_item = expected.get(relpath)
        if expected_item is None:
            errors.append(f"archive contains unexpected file: {relpath}")
            break
        expected_size = expected_item.size_bytes
        if member.size != expected_size:
            errors.append(f"archive member size mismatch: {relpath}")
            break
        if member.size > MAX_ARCHIVE_MEMBER_BYTES_V1:
            errors.append(f"archive member exceeds resource ceiling: {relpath}")
            break
        if not _archive_member_metadata_is_canonical(member, relpath=relpath):
            errors.append(f"archive member metadata is non-canonical: {relpath}")
            break
        total_payload_bytes += member.size
        if total_payload_bytes > MAX_ARCHIVE_TOTAL_BYTES_V1:
            errors.append("archive payload exceeds resource ceiling")
            break
        extracted = tar.extractfile(member)
        if extracted is None:
            errors.append(f"archive member could not be read: {relpath}")
            break
        payload = extracted.read(expected_size + 1)
        if len(payload) != expected_size:
            errors.append(f"archive member size mismatch: {relpath}")
            break
        if hashlib.sha256(payload).hexdigest() != expected_item.sha256:
            errors.append(f"archive member sha256 mismatch: {relpath}")
            break
    return errors, observed, member_count


def _archive_member_metadata_is_canonical(
    member: tarfile.TarInfo, *, relpath: str
) -> bool:
    canonical_pax_headers: tuple[dict[str, str], ...] = (
        {},
        {"path": member.name},
    )
    return (
        member.mode == _canonical_archive_mode(relpath)
        and member.uid == 0
        and member.gid == 0
        and member.uname in {"", None}
        and member.gname in {"", None}
        and member.mtime == 0
        and member.pax_headers in canonical_pax_headers
    )


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_bounded(path: Path, limit: int) -> bytes:
    with path.open("rb") as fh:
        payload = fh.read(limit + 1)
    if len(payload) > limit:
        raise ValueError("input exceeds resource ceiling")
    return payload


def _sha256_file_bounded(file: BinaryIO, limit: int) -> str:
    digest = hashlib.sha256()
    consumed = 0
    file.seek(0)
    while chunk := file.read(min(1024 * 1024, limit - consumed + 1)):
        consumed += len(chunk)
        if consumed > limit:
            raise ValueError("input exceeds resource ceiling")
        digest.update(chunk)
    return digest.hexdigest()


def _copy_file_bounded(
    *, source: BinaryIO, destination: BinaryIO, limit: int
) -> int:
    source.seek(0)
    destination.seek(0)
    destination.truncate(0)
    copied = 0
    while chunk := source.read(min(1024 * 1024, limit - copied + 1)):
        copied += len(chunk)
        if copied > limit:
            raise ValueError("input exceeds resource ceiling")
        destination.write(chunk)
    destination.flush()
    return copied


def _has_canonical_gzip_header(file: BinaryIO) -> bool:
    file.seek(0)
    header = file.read(len(CANONICAL_GZIP_HEADER_V1))
    file.seek(0)
    return header == CANONICAL_GZIP_HEADER_V1


def _no_follow_flag() -> int:
    no_follow = getattr(os, "O_NOFOLLOW", None)
    if no_follow is None:
        raise OSError("no-follow file opens are unavailable")
    return no_follow


def _directory_open_flags() -> int:
    directory = getattr(os, "O_DIRECTORY", None)
    if directory is None:
        raise OSError("directory-only file opens are unavailable")
    return os.O_RDONLY | directory | _no_follow_flag() | getattr(os, "O_CLOEXEC", 0)


@contextmanager
def _open_directory_readonly(path: Path) -> Iterator[int]:
    fd = os.open(path, _directory_open_flags())
    try:
        if not stat.S_ISDIR(os.fstat(fd).st_mode):
            raise OSError("path is not a directory")
        yield fd
    finally:
        os.close(fd)


@contextmanager
def _open_candidate_output_directory(path: Path) -> Iterator[int]:
    path.mkdir(parents=True, exist_ok=True)
    try:
        fd = os.open(path, _directory_open_flags())
    except OSError as exc:
        raise ValueError("output directory must be a stable regular directory") from exc
    try:
        initial_stat = os.fstat(fd)
        if not stat.S_ISDIR(initial_stat.st_mode):
            raise ValueError("output directory must be a stable regular directory")
        yield fd
        try:
            current_path = os.stat(path, follow_symlinks=False)
        except OSError as exc:
            raise ValueError("output directory changed during candidate build") from exc
        if not stat.S_ISDIR(current_path.st_mode) or (
            current_path.st_dev,
            current_path.st_ino,
        ) != (initial_stat.st_dev, initial_stat.st_ino):
            raise ValueError("output directory changed during candidate build")
    finally:
        os.close(fd)


@contextmanager
def _open_regular_readonly(
    path: Path,
) -> Iterator[tuple[BinaryIO, _FileIdentityV1]]:
    flags = os.O_RDONLY | _no_follow_flag() | getattr(os, "O_CLOEXEC", 0)
    fd = os.open(path, flags)
    try:
        file_stat = os.fstat(fd)
        if not stat.S_ISREG(file_stat.st_mode):
            raise OSError("path is not a regular file")
        raw = os.fdopen(fd, "rb")
        fd = -1
        with raw:
            yield raw, _FileIdentityV1.from_stat(file_stat)
    finally:
        if fd >= 0:
            os.close(fd)


@contextmanager
def _open_regular_readonly_at(
    root_directory_fd: int,
    relpath: str,
) -> Iterator[tuple[BinaryIO, _FileIdentityV1, int, str]]:
    if not _is_safe_relative_path(relpath):
        raise OSError("relative file path is unsafe")
    parts = relpath.split("/")
    parent_fd = os.dup(root_directory_fd)
    file_fd = -1
    try:
        for part in parts[:-1]:
            next_fd = os.open(part, _directory_open_flags(), dir_fd=parent_fd)
            os.close(parent_fd)
            parent_fd = next_fd
        file_fd = os.open(
            parts[-1],
            os.O_RDONLY | _no_follow_flag() | getattr(os, "O_CLOEXEC", 0),
            dir_fd=parent_fd,
        )
        file_stat = os.fstat(file_fd)
        if not stat.S_ISREG(file_stat.st_mode):
            raise OSError("path is not a regular file")
        raw = os.fdopen(file_fd, "rb")
        file_fd = -1
        with raw:
            yield raw, _FileIdentityV1.from_stat(file_stat), parent_fd, parts[-1]
    finally:
        if file_fd >= 0:
            os.close(file_fd)
        os.close(parent_fd)


def _opened_entry_status(
    file: BinaryIO,
    identity: _FileIdentityV1,
    parent_directory_fd: int,
    entry_name: str,
) -> str:
    current_file = _FileIdentityV1.from_stat(os.fstat(file.fileno()))
    try:
        path_stat = os.stat(
            entry_name,
            dir_fd=parent_directory_fd,
            follow_symlinks=False,
        )
    except OSError:
        return "path_changed"
    if not stat.S_ISREG(path_stat.st_mode):
        return "path_changed"
    current_path = _FileIdentityV1.from_stat(path_stat)
    if (current_path.device, current_path.inode) != (identity.device, identity.inode):
        return "path_changed"
    return "stable" if current_file == identity and current_path == identity else "changed"


def _opened_path_status(
    path: Path,
    file: BinaryIO,
    identity: _FileIdentityV1,
) -> str:
    current_file = _FileIdentityV1.from_stat(os.fstat(file.fileno()))
    try:
        path_stat = os.stat(path, follow_symlinks=False)
    except OSError:
        return "path_changed"
    if not stat.S_ISREG(path_stat.st_mode):
        return "path_changed"
    current_path = _FileIdentityV1.from_stat(path_stat)
    if (current_path.device, current_path.inode) != (identity.device, identity.inode):
        return "path_changed"
    return "stable" if current_file == identity and current_path == identity else "changed"


def _looks_sha256(value: object) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(char in "0123456789abcdef" for char in value)


def _safe_version(version: object) -> str:
    allowed = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-"
    if (
        type(version) is not str
        or not version
        or len(version.encode("ascii", errors="ignore")) != len(version)
        or len(version) > MAX_VERSION_BYTES_V1
        or version[0] not in allowed[:62]
        or any(char not in allowed for char in version)
    ):
        raise ValueError("version must contain only ASCII letters, digits, dot, underscore, or dash")
    return version


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    build = sub.add_parser("build", help="refuse release output for the current profile")
    build.add_argument("--repo-root", type=Path, default=ROOT)
    build.add_argument("--out-dir", type=Path, required=True)
    build.add_argument("--version", default="dev")

    candidate = sub.add_parser(
        "candidate",
        help="build an unadmitted candidate archive with no release authority",
    )
    candidate.add_argument("--repo-root", type=Path, default=ROOT)
    candidate.add_argument("--out-dir", type=Path, required=True)
    candidate.add_argument("--version", default="dev")

    verify = sub.add_parser(
        "verify",
        help="verify an unadmitted operator candidate manifest",
    )
    verify.add_argument("--manifest", type=Path, required=True)
    verify.add_argument("--archive", type=Path)

    args = parser.parse_args(argv)
    if args.command == "build":
        try:
            build_operator_release_bundle(
                root=args.repo_root,
                out_dir=args.out_dir,
                version=args.version,
            )
        except OperatorReleaseAdmissionRejectV1 as exc:
            admission = current_local_operator_release_admission_v1()
            print(
                json.dumps(
                    {
                        "schema": "zenodex.operator_release_admission.v1",
                        "ok": False,
                        "status": "blocked_current_profile",
                        "code": "OPERATOR_RELEASE_BLOCKED",
                        "current_profile_id": exc.profile_id,
                        "current_release_eligible": False,
                        "authority": admission.authority,
                        "vm_gates_closed": list(admission.vm_gates_closed),
                        "release_blocker": exc.blocker,
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 2
        raise AssertionError("current release admission unexpectedly allowed output")
    if args.command == "candidate":
        report = build_operator_candidate_bundle(
            root=args.repo_root,
            out_dir=args.out_dir,
            version=args.version,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    if args.command == "verify":
        report = verify_operator_candidate_manifest(
            manifest_path=args.manifest,
            archive_path=args.archive,
        )
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0 if report["ok"] else 1
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
