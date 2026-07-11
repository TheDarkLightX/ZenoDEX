"""Exact compiler and verifier source closure for frozen ZRPF V3 evidence."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
from pathlib import Path, PurePosixPath
from typing import Any

SCHEMA = "zenodex/zrpf_v3_frozen_source_closure/v1"
MAX_SOURCE_BYTES = 16 * 1024 * 1024

SOURCE_ROWS: tuple[tuple[str, str], ...] = tuple(
    sorted(
        (
            ("workspace_build", "zk/state_proof_risc0/Cargo.toml"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/Cargo.toml"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/src/lib.rs"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/src/recursive.rs"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/src/surfaces.rs"),
            ("protocol_dependency", "zk/zrpf_protocol/Cargo.toml"),
            ("protocol_dependency", "zk/zrpf_protocol/protocol/Cargo.toml"),
            ("protocol_dependency", "zk/zrpf_protocol/protocol/src/lib.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/hash.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/ids.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/leaf.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/mod.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/proposal.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/sets.rs"),
            ("workspace_build", "zk/zrpf_risc0/.cargo/config.toml"),
            ("workspace_build", "zk/zrpf_risc0/Cargo.lock"),
            ("workspace_build", "zk/zrpf_risc0/Cargo.toml"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/Cargo.toml"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/src/input_v1.rs"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/src/lib.rs"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/src/structural_v1.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/Cargo.toml"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/bin/prove_semantic_epoch.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/bin/prove_structural_l1.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/bin/prove_structural_tree.rs"),
            ("verification_harness", "zk/zrpf_risc0/harness/src/bin/verify_semantic_epoch.rs"),
            ("verification_harness", "zk/zrpf_risc0/harness/src/bin/verify_structural_tree.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/main.rs"),
            ("guest_build", "zk/zrpf_risc0/methods/Cargo.toml"),
            ("guest_build", "zk/zrpf_risc0/methods/build.rs"),
            ("guest_build", "zk/zrpf_risc0/methods/src/lib.rs"),
            ("semantic_guest", "zk/zrpf_risc0/methods/semantic_epoch/Cargo.toml"),
            ("semantic_guest", "zk/zrpf_risc0/methods/semantic_epoch/src/main.rs"),
            ("adapter_guest", "zk/zrpf_risc0/methods/v1_leaf_adapter/Cargo.toml"),
            ("adapter_guest", "zk/zrpf_risc0/methods/v1_leaf_adapter/src/main.rs"),
            ("structural_l1_guest", "zk/zrpf_risc0/methods/structural_aggregate_l1/Cargo.toml"),
            ("structural_l1_guest", "zk/zrpf_risc0/methods/structural_aggregate_l1/src/main.rs"),
            ("structural_l2_guest", "zk/zrpf_risc0/methods/structural_aggregate_l2/Cargo.toml"),
            ("structural_l2_guest", "zk/zrpf_risc0/methods/structural_aggregate_l2/src/main.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/Cargo.toml"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/adapter_input_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/hashing_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/lib.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/risc0_binding_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/source_binding_v3.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/source_policy_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/v1_leaf_adapter.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/Cargo.toml"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/bind_v1.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/codec_v1.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/epoch_v1.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/input_v1.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/lib.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/recompose_v1.rs"),
            ("verification_harness", "zk/zrpf_risc0/verifier/Cargo.toml"),
            ("verification_harness", "zk/zrpf_risc0/verifier/src/lib.rs"),
            ("verification_harness", "zk/zrpf_risc0/verifier/src/semantic_epoch_v1.rs"),
        ),
        key=lambda row: row[1],
    )
)

SCAN_DIRECTORIES = (
    "zk/state_proof_risc0/shared/src",
    "zk/zrpf_protocol/protocol/src",
    "zk/zrpf_risc0/aggregate_shared/src",
    "zk/zrpf_risc0/harness/src",
    "zk/zrpf_risc0/methods",
    "zk/zrpf_risc0/semantic_shared/src",
    "zk/zrpf_risc0/shared/src",
    "zk/zrpf_risc0/verifier/src",
)


class SourceClosureError(ValueError):
    """Raised when a source tree cannot satisfy the frozen closure contract."""


def build_source_closure(repository_root: Path) -> dict[str, Any]:
    root = _resolved_repository_root(repository_root)
    _reject_target_directories(root)
    _validate_compiler_source_inventory(root)

    files: list[dict[str, Any]] = []
    closure_hasher = hashlib.sha256()
    for role, relative in SOURCE_ROWS:
        raw = _read_source(root, relative)
        digest = hashlib.sha256(raw).hexdigest()
        row = {
            "path": relative,
            "role": role,
            "sha256": digest,
            "size_bytes": len(raw),
        }
        files.append(row)
        closure_hasher.update(role.encode("utf-8"))
        closure_hasher.update(b"\0")
        closure_hasher.update(relative.encode("utf-8"))
        closure_hasher.update(b"\0")
        closure_hasher.update(digest.encode("ascii"))
        closure_hasher.update(b"\0")
        closure_hasher.update(str(len(raw)).encode("ascii"))
        closure_hasher.update(b"\n")

    commit = _git_output(root, "rev-parse", "HEAD")
    dirty = _git_output(root, "status", "--porcelain", "--untracked-files=all")
    if dirty:
        raise SourceClosureError("source worktree must be clean before snapshot")
    return {
        "definition": "sha256 of sorted role, path, sha256, and size records with NUL field separators and LF record separators",
        "file_count": len(files),
        "files": files,
        "git_commit": commit,
        "schema": SCHEMA,
        "sha256": closure_hasher.hexdigest(),
        "status": "frozen_source_closure",
        "worktree_clean": True,
    }


def check_source_closure(document: Any, repository_root: Path) -> list[str]:
    if not isinstance(document, dict):
        return ["source closure must be an object"]
    try:
        expected = build_source_closure(repository_root)
    except SourceClosureError as exc:
        return [str(exc)]
    return [] if document == expected else ["source closure differs from the current clean worktree"]


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def write_create_new(path: Path, raw: bytes) -> None:
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise SourceClosureError("snapshot output parent is unavailable") from exc
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(parent / path.name, flags, 0o644)
    except OSError as exc:
        raise SourceClosureError("create-new snapshot output failed") from exc
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise SourceClosureError("snapshot output write made no progress")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory_descriptor = os.open(parent, os.O_RDONLY)
    try:
        os.fsync(directory_descriptor)
    finally:
        os.close(directory_descriptor)


def _resolved_repository_root(path: Path) -> Path:
    try:
        root = path.resolve(strict=True)
    except OSError as exc:
        raise SourceClosureError("repository root is unavailable") from exc
    if path.is_symlink() or not root.is_dir() or not (root / ".git").exists():
        raise SourceClosureError("repository root must be a non-symlink git worktree")
    return root


def _read_source(root: Path, relative: str) -> bytes:
    pure = PurePosixPath(relative)
    if pure.is_absolute() or ".." in pure.parts or str(pure) != relative:
        raise SourceClosureError(f"unsafe source path: {relative}")
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    directory_flags = flags | os.O_DIRECTORY
    descriptors: list[int] = []
    try:
        descriptor = os.open(root, directory_flags)
        descriptors.append(descriptor)
        for component in pure.parts[:-1]:
            descriptor = os.open(component, directory_flags, dir_fd=descriptor)
            descriptors.append(descriptor)
        file_descriptor = os.open(
            pure.parts[-1],
            flags | os.O_NONBLOCK,
            dir_fd=descriptor,
        )
        descriptors.append(file_descriptor)
        before = os.fstat(file_descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > MAX_SOURCE_BYTES
        ):
            raise SourceClosureError(
                f"source file is not a bounded regular file: {relative}"
            )
        output = bytearray()
        while len(output) < before.st_size:
            chunk = os.read(
                file_descriptor,
                min(1024 * 1024, before.st_size - len(output)),
            )
            if not chunk:
                raise SourceClosureError(f"source file changed while read: {relative}")
            output.extend(chunk)
        if os.read(file_descriptor, 1):
            raise SourceClosureError(f"source file changed while read: {relative}")
        after = os.fstat(file_descriptor)
    except OSError as exc:
        raise SourceClosureError(f"source file unavailable: {relative}") from exc
    finally:
        for opened in reversed(descriptors):
            os.close(opened)
    if _source_identity(before) != _source_identity(after):
        raise SourceClosureError(f"source file changed while read: {relative}")
    return bytes(output)


def _source_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _validate_compiler_source_inventory(root: Path) -> None:
    expected_rs = {path for _, path in SOURCE_ROWS if path.endswith(".rs")}
    discovered: set[str] = set()
    for relative_root in SCAN_DIRECTORIES:
        directory = root / relative_root
        if not directory.is_dir() or directory.is_symlink():
            raise SourceClosureError(f"compiler source directory unavailable: {relative_root}")
        for path in directory.rglob("*.rs"):
            if path.is_symlink() or not path.is_file():
                raise SourceClosureError("compiler source inventory contains a non-regular path")
            discovered.add(path.relative_to(root).as_posix())
    if discovered != expected_rs:
        missing = sorted(expected_rs - discovered)
        extra = sorted(discovered - expected_rs)
        raise SourceClosureError(
            f"compiler Rust source inventory mismatch: missing={missing}, extra={extra}"
        )


def _reject_target_directories(root: Path) -> None:
    for relative in (
        "zk/state_proof_risc0/shared",
        "zk/zrpf_protocol",
        "zk/zrpf_risc0",
    ):
        for candidate in (root / relative).rglob("target"):
            if candidate.is_dir():
                raise SourceClosureError("compiler-visible source scope contains target directory")


def _git_output(root: Path, *args: str) -> str:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise SourceClosureError("git source identity command failed") from exc
    return result.stdout.strip()
