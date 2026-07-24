"""Private Git snapshot and stable file operations for the V6 rebuild."""

from __future__ import annotations

import hashlib
import os
import shutil
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import ExecutionError

SOURCE_SNAPSHOT_DIRECTORY = "source-snapshot"
SNAPSHOT_ROOT_DOMAIN = b"zenodex.zrpf.spot_v6.private_source_snapshot.v1\0"
MAX_SNAPSHOT_FILES = 8_192
MAX_SNAPSHOT_BYTES = 64 * 1024 * 1024
MAX_SOURCE_FILE_BYTES = 16 * 1024 * 1024
V2_CANDIDATE_PATHS = (
    "config/proof_profiles/zrpf_current_source_anchor_v2.json",
    "config/proof_profiles/zrpf_v2_leaf_adapter_source_policy_v2.json",
)


@dataclass(frozen=True)
class SnapshotEntry:
    relative_path: str
    git_mode: str
    object_id: str


@dataclass(frozen=True)
class MaterializedSnapshot:
    root: Path
    entries: tuple[SnapshotEntry, ...]


class GitSnapshotter:
    """Materialize the exact bounded compiler-relevant tree from Git blobs."""

    def materialize(
        self,
        repo_root: Path,
        source_commit: str,
        destination: Path,
    ) -> MaterializedSnapshot:
        entries = _snapshot_entries(repo_root, source_commit)
        create_private_directory(destination)
        try:
            _materialize_git_entries(repo_root, entries, destination)
        except BaseException:
            shutil.rmtree(destination, ignore_errors=True)
            raise
        return MaterializedSnapshot(destination, entries)


def validate_initial_snapshot(
    snapshot: MaterializedSnapshot,
    plan: dict[str, Any],
) -> None:
    broad = _inventory_facts(
        snapshot,
        planner.RELEVANT_WORKSPACE_ROOTS,
        b"zenodex.zrpf.spot_v6.tracked_workspace_source.v1\0",
    )
    expected_broad = plan["tracked_workspace_source_coverage"]
    for field in ("tracked_file_count", "tracked_bytes", "inventory_root_sha256"):
        if broad[field] != expected_broad[field]:
            raise ExecutionError(f"snapshot tracked workspace {field} mismatch")
    source = _inventory_facts(
        snapshot,
        planner.SOURCE_GUEST_WORKSPACE_ROOTS,
        b"zenodex.zrpf.current_spot.source_workspace.v2\0",
    )
    expected_source = plan["source_guest_source_coverage"]
    for field in ("tracked_file_count", "tracked_bytes", "inventory_root_sha256"):
        if source[field] != expected_source[field]:
            raise ExecutionError(f"snapshot source guest {field} mismatch")


def snapshot_root(snapshot: MaterializedSnapshot) -> str:
    digest, _total = _hash_entries(snapshot.root, snapshot.entries, SNAPSHOT_ROOT_DOMAIN)
    return digest


def protected_historical_hashes(snapshot_root: Path) -> dict[str, str]:
    return {
        relative: hashlib.sha256(
            read_bounded_regular(
                resolve_snapshot_path(snapshot_root, relative),
                f"historical artifact {relative}",
                MAX_SOURCE_FILE_BYTES,
                allow_empty=True,
            )
        ).hexdigest()
        for relative in planner.PROTECTED_HISTORICAL_ARTIFACTS
    }


def require_historical_unchanged(snapshot_root: Path, expected: dict[str, str]) -> None:
    if protected_historical_hashes(snapshot_root) != expected:
        raise ExecutionError("protected historical V1 artifact changed")


def require_snapshot_unchanged(
    snapshot: MaterializedSnapshot,
    expected_root: str,
    pass_id: str,
) -> None:
    if snapshot_root(snapshot) != expected_root:
        raise ExecutionError(f"source snapshot changed during {pass_id}")


def resolve_snapshot_path(snapshot_root: Path, relative: str) -> Path:
    pure = PurePosixPath(relative)
    if (
        pure.is_absolute()
        or not pure.parts
        or ".." in pure.parts
        or pure.as_posix() != relative
        or any(ord(character) < 32 or ord(character) == 127 for character in relative)
    ):
        raise ExecutionError("repin path is noncanonical")
    root = snapshot_root.resolve(strict=True)
    candidate = root.joinpath(*pure.parts)
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise ExecutionError("repin path is unavailable") from exc
    if resolved != candidate or root not in resolved.parents:
        raise ExecutionError("repin path escapes or traverses a symlink")
    return candidate


def read_bounded_regular(
    path: Path,
    label: str,
    maximum: int,
    *,
    allow_empty: bool = False,
) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ExecutionError(f"{label} is not a bounded regular file") from exc
    try:
        before = os.fstat(descriptor)
        minimum_ok = before.st_size >= 0 if allow_empty else before.st_size > 0
        if not stat.S_ISREG(before.st_mode) or not minimum_ok or before.st_size > maximum:
            raise ExecutionError(f"{label} is not a bounded regular file")
        chunks: list[bytes] = []
        size = 0
        while size <= maximum:
            chunk = os.read(descriptor, min(1 << 20, maximum + 1 - size))
            if not chunk:
                break
            chunks.append(chunk)
            size += len(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if size > maximum:
        raise ExecutionError(f"{label} exceeds its byte bound")
    identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    if identity != (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    ):
        raise ExecutionError(f"{label} changed during read")
    return b"".join(chunks)


def replace_regular(path: Path, raw: bytes) -> None:
    facts = path.lstat()
    if not stat.S_ISREG(facts.st_mode) or stat.S_ISLNK(facts.st_mode):
        raise ExecutionError("replacement target is not a regular file")
    temporary = path.with_name(f".{path.name}.repin-{os.getpid()}")
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory_descriptor = os.open(
            path.parent,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(directory_descriptor)
        finally:
            os.close(directory_descriptor)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise
    finally:
        os.close(descriptor)


def create_private_directory(path: Path) -> None:
    if path.exists() or path.is_symlink():
        raise ExecutionError("private directory must begin absent")
    path.mkdir(mode=0o700)
    facts = path.lstat()
    if (
        not stat.S_ISDIR(facts.st_mode)
        or stat.S_ISLNK(facts.st_mode)
        or facts.st_uid != os.getuid()
        or stat.S_IMODE(facts.st_mode) != 0o700
    ):
        raise ExecutionError("private directory creation rejected")


def _inventory_facts(
    snapshot: MaterializedSnapshot,
    roots: tuple[str, ...],
    domain: bytes,
) -> dict[str, Any]:
    selected = tuple(
        entry
        for entry in snapshot.entries
        if any(
            entry.relative_path == root or entry.relative_path.startswith(f"{root}/")
            for root in roots
        )
    )
    digest, total = _hash_entries(snapshot.root, selected, domain)
    return {
        "tracked_file_count": len(selected),
        "tracked_bytes": total,
        "inventory_root_sha256": digest,
    }


def _hash_entries(
    root: Path,
    entries: tuple[SnapshotEntry, ...],
    domain: bytes,
) -> tuple[str, int]:
    hasher = hashlib.sha256()
    hasher.update(domain)
    total = 0
    for entry in entries:
        raw = read_bounded_regular(
            resolve_snapshot_path(root, entry.relative_path),
            f"snapshot file {entry.relative_path}",
            MAX_SOURCE_FILE_BYTES,
            allow_empty=True,
        )
        total += len(raw)
        if total > MAX_SNAPSHOT_BYTES:
            raise ExecutionError("source snapshot exceeds its byte bound")
        encoded = entry.relative_path.encode("utf-8")
        mode = entry.git_mode.encode("ascii")
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
        hasher.update(len(mode).to_bytes(1, "big"))
        hasher.update(mode)
        hasher.update(len(raw).to_bytes(8, "big"))
        hasher.update(hashlib.sha256(raw).digest())
    return hasher.hexdigest(), total


def _snapshot_entries(repo_root: Path, source_commit: str) -> tuple[SnapshotEntry, ...]:
    planner.require_no_git_replace_refs(repo_root)
    pathspecs = tuple(
        dict.fromkeys(
            (
                *planner.RELEVANT_WORKSPACE_ROOTS,
                *planner.PROTECTED_HISTORICAL_ARTIFACTS,
                *V2_CANDIDATE_PATHS,
            )
        )
    )
    completed = planner._run_git(
        repo_root.resolve(strict=True),
        ["ls-tree", "-r", "-z", source_commit, "--", *pathspecs],
        maximum_stdout=8 * 1024 * 1024,
    )
    parsed = planner._parse_ls_tree(completed.stdout)
    entries = tuple(SnapshotEntry(path, mode, object_id) for path, mode, object_id in parsed)
    if not entries or len(entries) > MAX_SNAPSHOT_FILES:
        raise ExecutionError("source snapshot entry count is outside the bound")
    paths = {entry.relative_path for entry in entries}
    required = set(planner.PROTECTED_HISTORICAL_ARTIFACTS) | set(V2_CANDIDATE_PATHS)
    if not required.issubset(paths):
        raise ExecutionError("source snapshot misses governed candidate or historical files")
    return entries


def _materialize_git_entries(
    repo_root: Path,
    entries: tuple[SnapshotEntry, ...],
    destination: Path,
) -> None:
    request = b"".join(f"{entry.object_id}\n".encode("ascii") for entry in entries)
    completed = planner._run_git(
        repo_root.resolve(strict=True),
        ["cat-file", "--batch"],
        input_bytes=request,
        maximum_stdout=MAX_SNAPSHOT_BYTES + len(entries) * 128,
    )
    output = completed.stdout
    cursor = 0
    total = 0
    for entry in entries:
        line_end = output.find(b"\n", cursor)
        if line_end < 0:
            raise ExecutionError("source snapshot blob header is unavailable")
        header = output[cursor:line_end].split()
        cursor = line_end + 1
        if (
            len(header) != 3
            or header[0] != entry.object_id.encode("ascii")
            or header[1] != b"blob"
            or not header[2].isdigit()
        ):
            raise ExecutionError("source snapshot object is not the expected blob")
        size = int(header[2])
        end = cursor + size
        total += size
        if (
            size < 0
            or size > MAX_SOURCE_FILE_BYTES
            or total > MAX_SNAPSHOT_BYTES
            or end >= len(output)
            or output[end : end + 1] != b"\n"
        ):
            raise ExecutionError("source snapshot blob framing exceeds its bound")
        path = destination.joinpath(*PurePosixPath(entry.relative_path).parts)
        path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        mode = 0o700 if entry.git_mode == "100755" else 0o600
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
        try:
            with os.fdopen(descriptor, "wb", closefd=False) as stream:
                stream.write(output[cursor:end])
                stream.flush()
                os.fsync(stream.fileno())
        finally:
            os.close(descriptor)
        cursor = end + 1
    if cursor != len(output):
        raise ExecutionError("source snapshot blob batch has trailing bytes")
