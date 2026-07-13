"""Stable tool and bounded Cargo-registry identities for the V6 build runner.

The identities in this module detect persistent replacement or mutation between
runner checks. They do not claim resistance to a hostile process with the same
UID that mutates and restores bytes entirely between checks.
"""

from __future__ import annotations

import hashlib
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import ExecutionError

CARGO_REGISTRY_IDENTITY_SCHEMA = planner.CARGO_REGISTRY_IDENTITY_SCHEMA
CARGO_REGISTRY_ROOT_DOMAIN = b"zenodex.zrpf.bounded_cargo_registry.v1\0"
CARGO_REGISTRY_COMPONENTS = ("cache", "index", "src")
MAX_CARGO_REGISTRY_FILES = planner.MAX_CARGO_REGISTRY_FILES
MAX_CARGO_REGISTRY_BYTES = planner.MAX_CARGO_REGISTRY_BYTES
MAX_CARGO_REGISTRY_FILE_BYTES = planner.MAX_CARGO_REGISTRY_FILE_BYTES
MAX_PINNED_TOOL_BYTES = planner.MAX_PINNED_TOOL_BYTES


@dataclass(frozen=True)
class StableFileIdentity:
    """One path-bound file identity with deterministic public evidence."""

    device: int
    inode: int
    mode: int
    size: int
    modified_ns: int
    changed_ns: int
    sha256: str

    def evidence(self) -> dict[str, Any]:
        """Return the deterministic, host-independent evidence subset."""

        return {"sha256": self.sha256, "bytes": self.size}


@dataclass(frozen=True)
class CargoRegistryIdentity:
    """One bounded, deterministic identity for the mounted Cargo registry."""

    root_identity: tuple[int, int, int, int, int, int]
    component_identities: tuple[tuple[int, int, int, int, int, int], ...]
    root_sha256: str
    file_count: int
    total_bytes: int

    def evidence(self) -> dict[str, Any]:
        """Return the canonical host-independent registry identity."""

        return {
            "schema": CARGO_REGISTRY_IDENTITY_SCHEMA,
            "root_sha256": self.root_sha256,
            "file_count": self.file_count,
            "total_bytes": self.total_bytes,
            "components": list(CARGO_REGISTRY_COMPONENTS),
            "maximum_files": MAX_CARGO_REGISTRY_FILES,
            "maximum_total_bytes": MAX_CARGO_REGISTRY_BYTES,
            "maximum_file_bytes": MAX_CARGO_REGISTRY_FILE_BYTES,
        }


def capture_pinned_tool(
    path: Path,
    label: str,
    expected_sha256: str,
) -> StableFileIdentity:
    """Read and authenticate one canonical executable without following links."""

    if len(expected_sha256) != 64 or any(
        character not in "0123456789abcdef" for character in expected_sha256
    ):
        raise ExecutionError(f"{label} expected SHA-256 is malformed")
    raw, identity = _read_stable_regular(
        path,
        label,
        MAX_PINNED_TOOL_BYTES,
        allow_empty=False,
        executable=True,
    )
    digest = hashlib.sha256(raw).hexdigest()
    if digest != expected_sha256:
        raise ExecutionError(f"pinned tool SHA-256 mismatch: {label}")
    return StableFileIdentity(*identity, digest)


def capture_cargo_registry(registry: Path) -> CargoRegistryIdentity:
    """Hash the exact bounded regular-file inventory of a Cargo registry."""

    root = _canonical_owned_directory(registry, "Cargo registry")
    root_before = _directory_identity(root, "Cargo registry")
    component_paths = tuple(root / component for component in CARGO_REGISTRY_COMPONENTS)
    component_before = tuple(
        _directory_identity(
            _canonical_owned_directory(path, f"Cargo registry {path.name}"),
            f"Cargo registry {path.name}",
        )
        for path in component_paths
    )
    entries = _registry_file_paths(root, (root,))
    hasher = hashlib.sha256()
    hasher.update(CARGO_REGISTRY_ROOT_DOMAIN)
    total = 0
    for relative, path, inventoried_identity in entries:
        raw, identity = _read_stable_regular(
            path,
            f"Cargo registry file {relative}",
            MAX_CARGO_REGISTRY_FILE_BYTES,
            allow_empty=True,
            executable=False,
        )
        if identity != inventoried_identity:
            raise ExecutionError("Cargo registry entry changed after inventory")
        total += len(raw)
        if total > MAX_CARGO_REGISTRY_BYTES:
            raise ExecutionError("Cargo registry exceeds its total byte bound")
        encoded = relative.encode("utf-8", errors="strict")
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
        hasher.update(stat.S_IMODE(identity[2]).to_bytes(4, "big"))
        hasher.update(len(raw).to_bytes(8, "big"))
        hasher.update(hashlib.sha256(raw).digest())
    root_after = _directory_identity(root, "Cargo registry")
    component_after = tuple(
        _directory_identity(path, f"Cargo registry {path.name}") for path in component_paths
    )
    entries_after = _registry_file_paths(root, (root,))
    if root_before != root_after or component_before != component_after:
        raise ExecutionError("Cargo registry directories changed during identity capture")
    if tuple((relative, identity) for relative, _path, identity in entries) != tuple(
        (relative, identity) for relative, _path, identity in entries_after
    ):
        raise ExecutionError("Cargo registry inventory changed during identity capture")
    return CargoRegistryIdentity(
        root_identity=root_before,
        component_identities=component_before,
        root_sha256=hasher.hexdigest(),
        file_count=len(entries),
        total_bytes=total,
    )


def _registry_file_paths(
    root: Path,
    component_paths: tuple[Path, ...],
) -> tuple[tuple[str, Path, tuple[int, int, int, int, int, int]], ...]:
    entries: list[tuple[str, Path, tuple[int, int, int, int, int, int]]] = []
    for component in component_paths:
        for current, directories, files in os.walk(component, followlinks=False):
            directories.sort()
            files.sort()
            current_path = Path(current)
            _require_owned_directory(current_path, f"Cargo registry directory {current_path}")
            for name in directories:
                _require_owned_directory(
                    current_path / name,
                    f"Cargo registry directory {name}",
                )
            for name in files:
                path = current_path / name
                facts = _lstat(path, f"Cargo registry entry {name}")
                if not stat.S_ISREG(facts.st_mode) or stat.S_ISLNK(facts.st_mode):
                    raise ExecutionError("Cargo registry contains a non-regular entry")
                try:
                    relative = path.relative_to(root).as_posix()
                    relative.encode("utf-8", errors="strict")
                except (ValueError, UnicodeEncodeError) as exc:
                    raise ExecutionError("Cargo registry path is noncanonical") from exc
                entries.append((relative, path, _file_identity(facts)))
                if len(entries) > MAX_CARGO_REGISTRY_FILES:
                    raise ExecutionError("Cargo registry exceeds its file-count bound")
    entries.sort(key=lambda entry: entry[0])
    if not entries:
        raise ExecutionError("Cargo registry inventory is empty")
    if len({relative for relative, _path, _identity in entries}) != len(entries):
        raise ExecutionError("Cargo registry contains duplicate canonical paths")
    return tuple(entries)


def _read_stable_regular(
    path: Path,
    label: str,
    maximum: int,
    *,
    allow_empty: bool,
    executable: bool,
) -> tuple[bytes, tuple[int, int, int, int, int, int]]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ExecutionError(f"{label} is not a stable regular file") from exc
    try:
        before = os.fstat(descriptor)
        minimum_ok = before.st_size >= 0 if allow_empty else before.st_size > 0
        if (
            not stat.S_ISREG(before.st_mode)
            or not minimum_ok
            or before.st_size > maximum
            or before.st_uid != os.getuid()
            or (executable and stat.S_IMODE(before.st_mode) & 0o111 == 0)
        ):
            raise ExecutionError(f"{label} is not a stable regular file")
        chunks: list[bytes] = []
        total = 0
        while total <= maximum:
            chunk = os.read(descriptor, min(1 << 20, maximum + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
        after = os.fstat(descriptor)
        path_after = _lstat(path, label)
    finally:
        os.close(descriptor)
    if total > maximum:
        raise ExecutionError(f"{label} exceeds its byte bound")
    identity = _file_identity(before)
    if identity != _file_identity(after) or identity != _file_identity(path_after):
        raise ExecutionError(f"{label} changed or was replaced during read")
    return b"".join(chunks), identity


def _canonical_owned_directory(path: Path, label: str) -> Path:
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ExecutionError(f"{label} is unavailable") from exc
    if resolved != path:
        raise ExecutionError(f"{label} must be a canonical real directory")
    _require_owned_directory(path, label)
    return path


def _require_owned_directory(path: Path, label: str) -> None:
    facts = _lstat(path, label)
    if (
        not stat.S_ISDIR(facts.st_mode)
        or stat.S_ISLNK(facts.st_mode)
        or facts.st_uid != os.getuid()
    ):
        raise ExecutionError(f"{label} must be an owned real directory")


def _directory_identity(path: Path, label: str) -> tuple[int, int, int, int, int, int]:
    facts = _lstat(path, label)
    if not stat.S_ISDIR(facts.st_mode) or stat.S_ISLNK(facts.st_mode):
        raise ExecutionError(f"{label} is not a stable directory")
    return _file_identity(facts)


def _file_identity(facts: os.stat_result) -> tuple[int, int, int, int, int, int]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_mode,
        facts.st_size,
        facts.st_mtime_ns,
        facts.st_ctime_ns,
    )


def _lstat(path: Path, label: str) -> os.stat_result:
    try:
        return path.lstat()
    except OSError as exc:
        raise ExecutionError(f"{label} is unavailable") from exc
