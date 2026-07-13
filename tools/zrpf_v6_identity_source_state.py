"""Exact persistent source-state tracking for the ZRPF V6 rebuild."""

from __future__ import annotations

import hashlib
import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Callable, Mapping, Sequence

from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_identity_source_snapshot import (
    MAX_SNAPSHOT_BYTES,
    MAX_SNAPSHOT_FILES,
    MAX_SOURCE_FILE_BYTES,
    SNAPSHOT_ROOT_DOMAIN,
    MaterializedSnapshot,
)


@dataclass(frozen=True)
class _ExpectedSourceFile:
    raw: bytes
    mode: int


@dataclass
class ExpectedSourceState:
    """Exact source state accepted between governed persistent writes.

    The checks detect persistent mutation. They do not establish immutability
    against hostile code with the executor's UID, which can still mutate and
    restore bytes entirely between two checks.
    """

    snapshot: MaterializedSnapshot
    expected_files: dict[str, _ExpectedSourceFile]
    expected_directories: dict[str, tuple[int, int, int, int]]
    expected_root_sha256: str
    root_identity: tuple[int, int, int, int]

    @classmethod
    def capture(cls, snapshot: MaterializedSnapshot) -> ExpectedSourceState:
        expected_paths = tuple(entry.relative_path for entry in snapshot.entries)
        expected_directory_paths = _expected_snapshot_directories(expected_paths)
        root_identity = _source_root_identity(snapshot.root)
        initial_paths, expected_directories = _scan_live_source_inventory(snapshot.root)
        if (
            set(initial_paths) != set(expected_paths)
            or set(expected_directories) != expected_directory_paths
        ):
            raise ExecutionError("initial source snapshot live inventory mismatch")
        files = _read_exact_live_source_tree(
            snapshot.root,
            expected_paths,
            expected_directories,
            root_identity,
            "initial source state",
        )
        for entry in snapshot.entries:
            expected_mode = 0o700 if entry.git_mode == "100755" else 0o600
            if files[entry.relative_path].mode != expected_mode:
                raise ExecutionError("initial source file mode differs from Git materialization")
        state = cls(
            snapshot=snapshot,
            expected_files=files,
            expected_directories=expected_directories,
            expected_root_sha256=_expected_source_root(snapshot, files),
            root_identity=root_identity,
        )
        state.require_current("initial source state")
        return state

    def expected_bytes(self, relative_path: str) -> bytes:
        source = self.expected_files.get(relative_path)
        if source is None:
            raise ExecutionError("governed source transition path is absent")
        return source.raw

    def require_current(self, transition: str) -> str:
        actual = _read_exact_live_source_tree(
            self.snapshot.root,
            tuple(self.expected_files),
            self.expected_directories,
            self.root_identity,
            transition,
        )
        if actual != self.expected_files:
            raise ExecutionError(
                f"source snapshot changed: bytes or modes differ during {transition}"
            )
        actual_root = _expected_source_root(self.snapshot, actual)
        if actual_root != self.expected_root_sha256:
            raise ExecutionError(f"source snapshot changed: root differs during {transition}")
        return self.expected_root_sha256

    def apply_exact_transition(
        self,
        relative_path: str,
        expected_raw: bytes,
        action: Callable[[], None],
        transition: str,
    ) -> None:
        self.require_current(f"before {transition}")
        current = self.expected_files.get(relative_path)
        if current is None:
            raise ExecutionError("governed source transition path is absent")
        expected_files = dict(self.expected_files)
        expected_files[relative_path] = _ExpectedSourceFile(expected_raw, current.mode)
        expected_root = _expected_source_root(self.snapshot, expected_files)
        action()
        actual = _read_exact_live_source_tree(
            self.snapshot.root,
            tuple(expected_files),
            self.expected_directories,
            self.root_identity,
            f"after {transition}",
        )
        if actual != expected_files:
            raise ExecutionError(
                f"source transition {transition} changed undeclared paths or bytes"
            )
        actual_root = _expected_source_root(self.snapshot, actual)
        if actual_root != expected_root:
            raise ExecutionError(f"source transition {transition} root mismatch")
        self.expected_files = expected_files
        self.expected_root_sha256 = expected_root


def render_expected_repin(
    raw: bytes,
    symbol: str,
    value_kind: str,
    value: list[int],
) -> bytes:
    """Render the one exact post-write source expected from a governed repin."""

    shapes = {
        "image_id_words_le": ("u32", 8, 0xFFFFFFFF),
        "sha256_bytes": ("u8", 32, 0xFF),
        "source_closure_root_bytes": ("u8", 32, 0xFF),
    }
    shape = shapes.get(value_kind)
    if re.fullmatch(r"[A-Z][A-Z0-9_]*", symbol) is None or shape is None:
        raise ExecutionError("repin declaration is invalid")
    type_name, width, maximum = shape
    if (
        type(value) is not list
        or len(value) != width
        or any(type(item) is not int or not 0 <= item <= maximum for item in value)
    ):
        raise ExecutionError("repin value shape is invalid")
    try:
        source = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise ExecutionError("repin source is not UTF-8") from exc
    pattern = re.compile(
        rf"^pub const {re.escape(symbol)}: \[{type_name}; {width}\] = \[[^\]]*\];$",
        re.MULTILINE,
    )
    matches = list(pattern.finditer(source))
    if len(matches) != 1:
        raise ExecutionError(f"repin symbol {symbol} must occur exactly once")
    values = "\n".join(f"    {item}," for item in value)
    declaration = f"pub const {symbol}: [{type_name}; {width}] = [\n{values}\n];"
    updated = source[: matches[0].start()] + declaration + source[matches[0].end() :]
    return updated.encode("utf-8")


def _expected_snapshot_directories(paths: Sequence[str]) -> frozenset[str]:
    directories: set[str] = set()
    for relative in paths:
        parent = PurePosixPath(relative).parent
        while parent != PurePosixPath("."):
            directories.add(parent.as_posix())
            parent = parent.parent
    return frozenset(directories)


def _source_root_identity(path: Path) -> tuple[int, int, int, int]:
    try:
        facts = path.lstat()
    except OSError as exc:
        raise ExecutionError("source snapshot root is unavailable") from exc
    mode = stat.S_IMODE(facts.st_mode)
    if (
        not stat.S_ISDIR(facts.st_mode)
        or stat.S_ISLNK(facts.st_mode)
        or facts.st_uid != os.getuid()
        or mode != 0o700
    ):
        raise ExecutionError("source snapshot root identity is unsafe")
    return (facts.st_dev, facts.st_ino, facts.st_uid, mode)


def _read_exact_live_source_tree(
    root: Path,
    expected_paths: Sequence[str],
    expected_directories: Mapping[str, tuple[int, int, int, int]],
    root_identity: tuple[int, int, int, int],
    transition: str,
) -> dict[str, _ExpectedSourceFile]:
    if _source_root_identity(root) != root_identity:
        raise ExecutionError(f"source snapshot root changed during {transition}")
    first_files, first_directories = _scan_live_source_inventory(root)
    if set(first_files) != set(expected_paths) or first_directories != expected_directories:
        raise ExecutionError(f"source snapshot live inventory mismatch during {transition}")

    result: dict[str, _ExpectedSourceFile] = {}
    total = 0
    for relative in expected_paths:
        raw, mode = _read_live_source_file(
            root.joinpath(*PurePosixPath(relative).parts),
            first_files[relative],
            transition,
        )
        total += len(raw)
        if total > MAX_SNAPSHOT_BYTES:
            raise ExecutionError("source snapshot exceeds its byte bound")
        result[relative] = _ExpectedSourceFile(raw, mode)

    second_files, second_directories = _scan_live_source_inventory(root)
    if (
        first_files != second_files
        or first_directories != second_directories
        or _source_root_identity(root) != root_identity
    ):
        raise ExecutionError(f"source snapshot changed while checking {transition}")
    return result


def _scan_live_source_inventory(
    root: Path,
) -> tuple[dict[str, tuple[int, ...]], dict[str, tuple[int, int, int, int]]]:
    files: dict[str, tuple[int, ...]] = {}
    directories: dict[str, tuple[int, int, int, int]] = {}
    pending: list[tuple[Path, PurePosixPath]] = [(root, PurePosixPath("."))]
    while pending:
        current, relative_parent = pending.pop()
        try:
            entries = sorted(os.scandir(current), key=lambda entry: entry.name)
        except OSError as exc:
            raise ExecutionError("source snapshot inventory is unavailable") from exc
        for entry in entries:
            try:
                facts = entry.stat(follow_symlinks=False)
            except OSError as exc:
                raise ExecutionError("source snapshot entry is unstable") from exc
            relative = (
                PurePosixPath(entry.name)
                if relative_parent == PurePosixPath(".")
                else relative_parent / entry.name
            )
            canonical = relative.as_posix()
            if stat.S_ISDIR(facts.st_mode) and not stat.S_ISLNK(facts.st_mode):
                if facts.st_uid != os.getuid():
                    raise ExecutionError("source snapshot directory identity is unsafe")
                directories[canonical] = _stable_directory_identity(facts)
                pending.append((Path(entry.path), relative))
                continue
            if not stat.S_ISREG(facts.st_mode) or stat.S_ISLNK(facts.st_mode):
                raise ExecutionError("source snapshot contains a symlink or special file")
            if facts.st_uid != os.getuid() or facts.st_nlink != 1:
                raise ExecutionError("source snapshot file ownership or link count is unsafe")
            files[canonical] = _stable_file_facts(facts)
            if len(files) > MAX_SNAPSHOT_FILES:
                raise ExecutionError("source snapshot live inventory exceeds its bound")
    return files, directories


def _read_live_source_file(
    path: Path,
    enumerated_facts: tuple[int, ...],
    transition: str,
) -> tuple[bytes, int]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ExecutionError(f"source snapshot file is unavailable during {transition}") from exc
    try:
        before = os.fstat(descriptor)
        if (
            _stable_file_facts(before) != enumerated_facts
            or not stat.S_ISREG(before.st_mode)
            or before.st_uid != os.getuid()
            or before.st_nlink != 1
            or before.st_size < 0
            or before.st_size > MAX_SOURCE_FILE_BYTES
        ):
            raise ExecutionError(f"source snapshot file identity rejected during {transition}")
        chunks: list[bytes] = []
        size = 0
        while size <= MAX_SOURCE_FILE_BYTES:
            chunk = os.read(
                descriptor,
                min(1 << 20, MAX_SOURCE_FILE_BYTES + 1 - size),
            )
            if not chunk:
                break
            chunks.append(chunk)
            size += len(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if size > MAX_SOURCE_FILE_BYTES:
        raise ExecutionError("source snapshot file exceeds its byte bound")
    if _stable_file_facts(before) != _stable_file_facts(after):
        raise ExecutionError(f"source snapshot file changed during {transition}")
    return b"".join(chunks), stat.S_IMODE(before.st_mode)


def _stable_file_facts(facts: os.stat_result) -> tuple[int, ...]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_mode,
        facts.st_uid,
        facts.st_gid,
        facts.st_nlink,
        facts.st_size,
        facts.st_mtime_ns,
        facts.st_ctime_ns,
    )


def _stable_directory_identity(facts: os.stat_result) -> tuple[int, int, int, int]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_uid,
        stat.S_IMODE(facts.st_mode),
    )


def _expected_source_root(
    snapshot: MaterializedSnapshot,
    files: Mapping[str, _ExpectedSourceFile],
) -> str:
    if set(files) != {entry.relative_path for entry in snapshot.entries}:
        raise ExecutionError("expected source state file map is incomplete")
    hasher = hashlib.sha256()
    hasher.update(SNAPSHOT_ROOT_DOMAIN)
    for entry in snapshot.entries:
        source = files[entry.relative_path]
        encoded_path = entry.relative_path.encode("utf-8")
        encoded_git_mode = entry.git_mode.encode("ascii")
        hasher.update(len(encoded_path).to_bytes(4, "big"))
        hasher.update(encoded_path)
        hasher.update(len(encoded_git_mode).to_bytes(1, "big"))
        hasher.update(encoded_git_mode)
        hasher.update(len(source.raw).to_bytes(8, "big"))
        hasher.update(hashlib.sha256(source.raw).digest())
    return hasher.hexdigest()
