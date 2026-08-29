#!/usr/bin/env python3
"""Build the exact research-only O-003B retired Tau bridge inventory."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import time
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import BinaryIO, Final, Sequence, cast

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.retired_tau_bridge_inventory_v1 import (  # noqa: E402
    EVALUATOR_PATHS_V1,
    EXPECTED_SCOPED_FILE_COUNT_V1,
    EXPECTED_SCOPED_SOURCE_BYTES_V1,
    GIT_COMMAND_TIMEOUT_SECONDS_V1,
    INVENTORY_PATH_V1,
    MAX_ARCHIVE_BYTES_V1,
    MAX_ARTIFACT_BYTES_V1,
    MAX_GIT_COMMANDS_V1,
    MAX_SEMANTIC_WORK_UNITS_V1,
    MAX_SINGLE_SOURCE_BYTES_V1,
    MAX_SOURCE_FILES_V1,
    MAX_TOTAL_SOURCE_BYTES_V1,
    PARENT_COMMIT_V1,
    PARENT_TREE_V1,
    REQUIRED_CLOSURE_PATHS_V1,
    SCOPE_CLASSES_V1,
    DependencyCandidateV1,
    GitBindingV1,
    InventoryRejectV1,
    ScanResultV1,
    TreeEntryV1,
    build_inventory_payload_v1,
    canonical_json_bytes_v1,
    discover_source_signals_v1,
    reject_v1,
    scope_classes_v1,
    sha256_prefixed_v1,
)

_TREE_ROW_RE: Final = re.compile(
    rb"(?P<mode>[0-9]{6}) (?P<kind>[a-z]+) (?P<object>[0-9a-f]{40}) +(?P<size>[0-9-]+)\t(?P<path>.*)\Z"
)
_GIT_STDERR_MAX_BYTES_V1: Final = 64 * 1024
_READ_CHUNK_BYTES_V1: Final = 65_536
_READ_ONLY_GIT_SUBCOMMANDS_V1: Final = frozenset(
    {"archive", "cat-file", "diff", "ls-tree", "rev-list", "rev-parse"}
)
_EVALUATOR_PATH_SET_V1: Final = frozenset(EVALUATOR_PATHS_V1)
_MAX_ANCESTRY_COMMITS_V1: Final = 4096
_MAX_ANCESTRY_BYTES_V1: Final = 8 * 1024 * 1024
_MAX_EVALUATOR_TREE_BYTES_V1: Final = 8 * 1024 * 1024
_MAX_EVALUATOR_FILES_V1: Final = 8192
_MAX_EVALUATOR_WORKTREE_BYTES_V1: Final = 256 * 1024 * 1024


@dataclass(slots=True)
class GitCommandBudgetV1:
    limit: int = MAX_GIT_COMMANDS_V1
    used: int = 0

    def consume(self, subcommand: str) -> None:
        if self.used >= self.limit:
            reject_v1("GIT_COMMAND_BUDGET_EXCEEDED", subcommand)
        self.used += 1


def _git_binary_v1() -> str:
    binary = shutil.which("git", path=os.defpath)
    if binary is None or not os.path.isabs(binary):
        reject_v1("GIT_COMMAND_FAILED", "absolute Git executable unavailable")
    return binary


def _git_environment_v1() -> dict[str, str]:
    return {
        "GIT_ATTR_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_SYSTEM": os.devnull,
        "GIT_EDITOR": "/bin/false",
        "GIT_EXTERNAL_DIFF": "/bin/false",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_PAGER": "",
        "GIT_SEQUENCE_EDITOR": "/bin/false",
        "LC_ALL": "C",
        "PAGER": "",
        "PATH": os.defpath,
        "XDG_CONFIG_HOME": os.devnull,
    }


def _kill_and_wait_v1(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except OSError:
        pass
    try:
        process.wait(timeout=1.0)
    except (OSError, subprocess.TimeoutExpired):
        try:
            process.kill()
            process.wait(timeout=1.0)
        except (OSError, subprocess.TimeoutExpired):
            pass


def _run_git_v1(
    root: Path,
    arguments: Sequence[str],
    *,
    max_stdout_bytes: int,
    accepted_returncodes: frozenset[int] = frozenset({0}),
    stdin_bytes: bytes | None = None,
    budget: GitCommandBudgetV1 | None = None,
) -> subprocess.CompletedProcess[bytes]:
    if not arguments or arguments[0] not in _READ_ONLY_GIT_SUBCOMMANDS_V1:
        reject_v1("GIT_COMMAND_FAILED", "subcommand is outside the closed read-only set")
    if budget is not None:
        budget.consume(arguments[0])
    deadline = time.monotonic() + GIT_COMMAND_TIMEOUT_SECONDS_V1
    checked_root = os.path.abspath(os.fspath(root))
    argv = (
        _git_binary_v1(),
        "--no-pager",
        "-c",
        "core.attributesFile=/dev/null",
        "-c",
        "core.checkStat=default",
        "-c",
        "core.editor=/bin/false",
        "-c",
        "core.excludesFile=/dev/null",
        "-c",
        "core.fileMode=true",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "core.ignoreStat=false",
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.pager=",
        "-c",
        "core.trustctime=true",
        "-c",
        f"core.worktree={checked_root}",
        "-c",
        "diff.external=/bin/false",
        "-c",
        "diff.ignoreSubmodules=none",
        "-c",
        "sequence.editor=/bin/false",
        "-C",
        checked_root,
        *arguments,
    )
    environment = _git_environment_v1()
    environment["GIT_WORK_TREE"] = checked_root
    try:
        process = subprocess.Popen(
            argv,
            stdin=subprocess.PIPE if stdin_bytes is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            start_new_session=True,
        )
    except OSError as exc:
        reject_v1("GIT_COMMAND_FAILED", type(exc).__name__)
    if process.stdout is None or process.stderr is None:
        _kill_and_wait_v1(process)
        reject_v1("GIT_COMMAND_FAILED", "subprocess pipes unavailable")
    stdout = cast(BinaryIO, process.stdout)
    stderr = cast(BinaryIO, process.stderr)
    stdin = cast(BinaryIO, process.stdin) if process.stdin is not None else None
    stdin_payload = b"" if stdin_bytes is None else stdin_bytes
    output = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    stdin_offset = 0
    try:
        selector.register(stdout, selectors.EVENT_READ, "stdout")
        selector.register(stderr, selectors.EVENT_READ, "stderr")
        if stdin_bytes is not None:
            if stdin is None:
                _kill_and_wait_v1(process)
                reject_v1("GIT_COMMAND_FAILED", "subprocess stdin unavailable")
            if not stdin_bytes:
                stdin.close()
            else:
                os.set_blocking(stdin.fileno(), False)
                selector.register(stdin, selectors.EVENT_WRITE, "stdin")
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _kill_and_wait_v1(process)
                reject_v1("GIT_COMMAND_TIMEOUT", arguments[0])
            for key, _mask in selector.select(timeout=min(0.05, remaining)):
                if key.data == "stdin":
                    if stdin is None:
                        _kill_and_wait_v1(process)
                        reject_v1("GIT_COMMAND_FAILED", "subprocess stdin unavailable")
                    try:
                        written = os.write(key.fd, stdin_payload[stdin_offset:])
                    except BlockingIOError:
                        continue
                    except OSError:
                        _kill_and_wait_v1(process)
                        reject_v1("GIT_COMMAND_FAILED", "subprocess stdin write failed")
                    if written <= 0:
                        _kill_and_wait_v1(process)
                        reject_v1("GIT_COMMAND_FAILED", "subprocess stdin zero-byte write")
                    stdin_offset += written
                    if stdin_offset == len(stdin_payload):
                        selector.unregister(key.fileobj)
                        stdin.close()
                    continue
                chunk = os.read(key.fd, _READ_CHUNK_BYTES_V1)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                stream = str(key.data)
                output[stream].extend(chunk)
                limit = max_stdout_bytes if stream == "stdout" else _GIT_STDERR_MAX_BYTES_V1
                if len(output[stream]) > limit:
                    _kill_and_wait_v1(process)
                    reject_v1("GIT_OUTPUT_BUDGET_EXCEEDED", arguments[0])
        returncode = process.wait(timeout=max(0.01, deadline - time.monotonic()))
    except InventoryRejectV1:
        _kill_and_wait_v1(process)
        raise
    except (OSError, subprocess.TimeoutExpired):
        _kill_and_wait_v1(process)
        reject_v1("GIT_COMMAND_FAILED", arguments[0])
    except BaseException:
        _kill_and_wait_v1(process)
        raise
    finally:
        selector.close()
        if stdin is not None and not stdin.closed:
            stdin.close()
        stdout.close()
        stderr.close()
    if returncode not in accepted_returncodes:
        reject_v1("GIT_COMMAND_FAILED", f"{arguments[0]}:{returncode}")
    return subprocess.CompletedProcess(
        argv,
        returncode,
        stdout=bytes(output["stdout"]),
        stderr=bytes(output["stderr"]),
    )


def _raw_commit_parents_v1(raw: bytes, commit: str) -> tuple[str, ...]:
    header, separator, _message = raw.partition(b"\n\n")
    if not separator:
        reject_v1("RAW_COMMIT_HEADER_MALFORMED", commit)
    parents: list[str] = []
    for line in header.splitlines():
        if line.startswith(b"parent "):
            parent = line[7:]
            if not re.fullmatch(rb"[0-9a-f]{40}", parent):
                reject_v1("RAW_COMMIT_HEADER_MALFORMED", commit)
            parents.append(parent.decode("ascii"))
    return tuple(parents)


def _verify_raw_ancestry_v1(
    root: Path,
    evaluator_commit: str,
    budget: GitCommandBudgetV1 | None = None,
) -> None:
    listed = _run_git_v1(
        root,
        ("rev-list", "--parents", "--topo-order", evaluator_commit),
        max_stdout_bytes=_MAX_ANCESTRY_BYTES_V1,
        budget=budget,
    ).stdout.decode("ascii").splitlines()
    if not listed or len(listed) > _MAX_ANCESTRY_COMMITS_V1:
        reject_v1("RAW_ANCESTRY_BUDGET_EXCEEDED", str(len(listed)))
    records: list[tuple[str, tuple[str, ...]]] = []
    for row in listed:
        parts = row.split()
        if not parts or any(re.fullmatch(r"[0-9a-f]{40}", part) is None for part in parts):
            reject_v1("RAW_ANCESTRY_LIST_MALFORMED", row[:80])
        records.append((parts[0], tuple(parts[1:])))
    if records[0][0] != evaluator_commit or PARENT_COMMIT_V1 not in {commit for commit, _parents in records}:
        reject_v1("EVALUATOR_NOT_DESCENDANT_OF_SUBJECT", evaluator_commit)
    raw = _run_git_v1(
        root,
        ("cat-file", "--batch"),
        max_stdout_bytes=_MAX_ANCESTRY_BYTES_V1,
        stdin_bytes=("\n".join(commit for commit, _parents in records) + "\n").encode("ascii"),
        budget=budget,
    ).stdout
    offset = 0
    for commit, expected_parents in records:
        newline = raw.find(b"\n", offset)
        if newline < 0:
            reject_v1("RAW_COMMIT_HEADER_MALFORMED", commit)
        prefix = raw[offset:newline].split()
        if len(prefix) != 3 or prefix[0] != commit.encode("ascii") or prefix[1] != b"commit":
            reject_v1("RAW_COMMIT_HEADER_MALFORMED", commit)
        try:
            size = int(prefix[2])
        except ValueError:
            reject_v1("RAW_COMMIT_HEADER_MALFORMED", commit)
        start, end = newline + 1, newline + 1 + size
        if size < 1 or end >= len(raw) or raw[end : end + 1] != b"\n":
            reject_v1("RAW_COMMIT_HEADER_MALFORMED", commit)
        if _raw_commit_parents_v1(raw[start:end], commit) != expected_parents:
            reject_v1("RAW_ANCESTRY_HEADER_MISMATCH", commit)
        offset = end + 1
    if offset != len(raw):
        reject_v1("RAW_COMMIT_HEADER_MALFORMED", "trailing-data")


def _parse_git_name_status_v1(raw: bytes) -> tuple[tuple[str, str], ...]:
    fields = raw.split(b"\0")
    if fields[-1] != b"" or len(fields[:-1]) % 2 != 0:
        reject_v1("EVALUATOR_DIFF_MALFORMED", sha256_prefixed_v1(raw))
    rows: list[tuple[str, str]] = []
    for index in range(0, len(fields) - 1, 2):
        try:
            status = fields[index].decode("ascii")
        except UnicodeDecodeError:
            reject_v1("EVALUATOR_DIFF_MALFORMED", sha256_prefixed_v1(raw))
        if status not in {"A", "D", "M", "T", "U", "X", "B"}:
            reject_v1("EVALUATOR_DIFF_MALFORMED", status)
        rows.append((status, _canonical_path_v1(fields[index + 1])))
    return tuple(rows)


def _complete_tree_entries_v1(
    root: Path,
    evaluator_commit: str,
    budget: GitCommandBudgetV1 | None,
) -> tuple[TreeEntryV1, ...]:
    raw = _run_git_v1(
        root,
        ("ls-tree", "-r", "-z", "-l", "--full-tree", evaluator_commit),
        max_stdout_bytes=_MAX_EVALUATOR_TREE_BYTES_V1,
        budget=budget,
    ).stdout
    entries: list[TreeEntryV1] = []
    total_bytes = 0
    for row in filter(None, raw.split(b"\0")):
        match = _TREE_ROW_RE.fullmatch(row)
        if match is None:
            reject_v1("EVALUATOR_TREE_ENTRY_MALFORMED", sha256_prefixed_v1(row))
        path = _canonical_path_v1(match.group("path"))
        mode = match.group("mode").decode("ascii")
        if mode not in {"100644", "100755"} or match.group("kind") != b"blob":
            reject_v1("EVALUATOR_FILE_NOT_REGULAR_BLOB", path)
        try:
            size = int(match.group("size"))
        except ValueError:
            reject_v1("EVALUATOR_TREE_ENTRY_MALFORMED", path)
        total_bytes += size
        if (
            len(entries) >= _MAX_EVALUATOR_FILES_V1
            or size < 0
            or total_bytes > _MAX_EVALUATOR_WORKTREE_BYTES_V1
        ):
            reject_v1("EVALUATOR_WORKTREE_BUDGET_EXCEEDED", path)
        entries.append(TreeEntryV1(path, mode, match.group("object").decode("ascii"), size, ()))
    if not entries or len({entry.path for entry in entries}) != len(entries):
        reject_v1("EVALUATOR_TREE_ENTRY_MALFORMED", "empty-or-duplicate")
    return tuple(entries)


def _raw_regular_file_v1(path: Path, expected_size: int, label: str) -> tuple[bytes, os.stat_result]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        before = path.lstat()
        if (
            stat.S_ISLNK(before.st_mode)
            or not stat.S_ISREG(before.st_mode)
            or before.st_size != expected_size
        ):
            reject_v1("EVALUATOR_RAW_FILE_MISMATCH", label)
        descriptor = os.open(path, flags)
        opened = os.fstat(descriptor)
        if (opened.st_dev, opened.st_ino) != (before.st_dev, before.st_ino):
            reject_v1("EVALUATOR_RAW_FILE_CHANGED", label)
        chunks: list[bytes] = []
        remaining = expected_size + 1
        while remaining:
            chunk = os.read(descriptor, min(_READ_CHUNK_BYTES_V1, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        after = os.fstat(descriptor)
    except InventoryRejectV1:
        raise
    except OSError as exc:
        raise InventoryRejectV1("EVALUATOR_RAW_FILE_READ_FAILED", label) from exc
    finally:
        if "descriptor" in locals():
            os.close(descriptor)
    raw = b"".join(chunks)
    stable_fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
    if len(raw) != expected_size or any(getattr(before, name) != getattr(after, name) for name in stable_fields):
        reject_v1("EVALUATOR_RAW_FILE_CHANGED", label)
    return raw, after


def _git_blob_id_v1(raw: bytes) -> str:
    prefix = b"blob " + str(len(raw)).encode("ascii") + b"\0"
    return hashlib.sha1(prefix + raw, usedforsecurity=False).hexdigest()


def _verify_raw_worktree_v1(
    root: Path,
    entries: Sequence[TreeEntryV1],
    permitted_untracked: frozenset[str],
) -> None:
    expected = {entry.path: entry for entry in entries}
    allowed_files = set(expected) | set(permitted_untracked)
    allowed_directories = {"."}
    for path in allowed_files:
        parts = PurePosixPath(path).parts
        allowed_directories.update(PurePosixPath(*parts[:index]).as_posix() for index in range(1, len(parts)))
    observed: set[str] = set()
    try:
        walker = os.walk(root, topdown=True, followlinks=False)
        for directory, directory_names, file_names in walker:
            relative_directory = Path(directory).relative_to(root).as_posix()
            relative_directory = "." if relative_directory == "." else relative_directory
            kept_directories: list[str] = []
            for name in sorted(directory_names):
                if relative_directory == "." and name == ".git":
                    continue
                relative = name if relative_directory == "." else f"{relative_directory}/{name}"
                status = (Path(directory) / name).lstat()
                if relative not in allowed_directories or stat.S_ISLNK(status.st_mode) or not stat.S_ISDIR(status.st_mode):
                    reject_v1("EVALUATOR_UNEXPECTED_WORKTREE_ENTRY", relative)
                kept_directories.append(name)
            directory_names[:] = kept_directories
            for name in sorted(file_names):
                if relative_directory == "." and name == ".git":
                    continue
                relative = name if relative_directory == "." else f"{relative_directory}/{name}"
                if relative not in allowed_files:
                    reject_v1("EVALUATOR_UNEXPECTED_WORKTREE_ENTRY", relative)
                observed.add(relative)
    except InventoryRejectV1:
        raise
    except (OSError, ValueError) as exc:
        raise InventoryRejectV1("EVALUATOR_WORKTREE_WALK_FAILED", type(exc).__name__) from exc
    if observed != allowed_files:
        reject_v1("EVALUATOR_WORKTREE_COVERAGE_MISMATCH", str(len(allowed_files - observed)))
    for path, entry in expected.items():
        raw, status = _raw_regular_file_v1(root / path, entry.size, path)
        expected_executable = entry.mode == "100755"
        if bool(status.st_mode & stat.S_IXUSR) != expected_executable or _git_blob_id_v1(raw) != entry.object_id:
            reject_v1("EVALUATOR_TRACKED_BLOB_MISMATCH", path)
    for path in permitted_untracked:
        status = (root / path).lstat()
        if stat.S_ISLNK(status.st_mode) or not stat.S_ISREG(status.st_mode) or status.st_size > MAX_SINGLE_SOURCE_BYTES_V1:
            reject_v1("EVALUATOR_DRAFT_FILE_NOT_REGULAR", path)


def _validate_evaluator_scope_v1(
    root: Path,
    evaluator_commit: str,
    budget: GitCommandBudgetV1 | None = None,
) -> None:
    changed = _run_git_v1(
        root,
        (
            "diff",
            "--no-ext-diff",
            "--no-textconv",
            "--ignore-submodules=none",
            "--name-status",
            "--no-renames",
            "-z",
            f"{PARENT_COMMIT_V1}..{evaluator_commit}",
        ),
        max_stdout_bytes=64 * 1024,
        budget=budget,
    ).stdout
    rows = _parse_git_name_status_v1(changed)
    exact_committed_rows = {("A", path) for path in _EVALUATOR_PATH_SET_V1}
    if rows and set(rows) != exact_committed_rows:
        reject_v1("EVALUATOR_COMMITTED_SCOPE_MISMATCH", str(rows))
    if not rows and evaluator_commit != PARENT_COMMIT_V1:
        reject_v1("EVALUATOR_DRAFT_NOT_AT_PARENT", evaluator_commit)
    entries = _complete_tree_entries_v1(root, evaluator_commit, budget)
    permitted_untracked = _EVALUATOR_PATH_SET_V1 if not rows else frozenset()
    _verify_raw_worktree_v1(root, entries, permitted_untracked)


def read_git_binding_v1(
    root: Path,
    budget: GitCommandBudgetV1 | None = None,
) -> GitBindingV1:
    resolved = _run_git_v1(
        root,
        ["rev-parse", f"{PARENT_COMMIT_V1}^{{commit}}", f"{PARENT_COMMIT_V1}^{{tree}}", "HEAD^{commit}"],
        max_stdout_bytes=256,
        budget=budget,
    ).stdout.decode("ascii").splitlines()
    if len(resolved) != 3 or resolved[:2] != [PARENT_COMMIT_V1, PARENT_TREE_V1]:
        reject_v1("SUBJECT_GIT_BINDING_MISMATCH", ":".join(resolved[:2]))
    _validate_evaluator_scope_v1(root, resolved[2], budget)
    _verify_raw_ancestry_v1(root, resolved[2], budget)
    return GitBindingV1(commit=resolved[0], tree=resolved[1])


def _canonical_path_v1(raw: bytes) -> str:
    try:
        path = raw.decode()
    except UnicodeDecodeError as exc:
        reject_v1("NON_UTF8_REPOSITORY_PATH", str(exc.start))
    pure = PurePosixPath(path)
    if not path or "\\" in path or pure.is_absolute() or pure.as_posix() != path or any(
        part in {"", ".", ".."} for part in pure.parts
    ):
        reject_v1("INVALID_REPOSITORY_PATH", path)
    return path


def _read_tree_entries_v1(
    root: Path,
    binding: GitBindingV1,
    budget: GitCommandBudgetV1 | None = None,
) -> tuple[TreeEntryV1, ...]:
    raw = _run_git_v1(
        root,
        ["ls-tree", "-r", "-z", "-l", "--full-tree", binding.commit],
        max_stdout_bytes=2 * 1024 * 1024,
        budget=budget,
    ).stdout
    selected: list[TreeEntryV1] = []
    total_bytes = 0
    for row in filter(None, raw.split(b"\0")):
        match = _TREE_ROW_RE.fullmatch(row)
        if match is None:
            reject_v1("INVALID_GIT_TREE_ENTRY", sha256_prefixed_v1(row))
        path = _canonical_path_v1(match.group("path"))
        mode = match.group("mode").decode()
        classes = scope_classes_v1(path, mode)
        if not classes:
            continue
        kind, size_text = match.group("kind"), match.group("size")
        if mode not in {"100644", "100755"} or kind != b"blob" or size_text == b"-":
            reject_v1("SCOPED_ENTRY_NOT_REGULAR_BLOB", path)
        size = int(size_text)
        total_bytes += size
        if size > MAX_SINGLE_SOURCE_BYTES_V1:
            reject_v1("SOURCE_FILE_BUDGET_EXCEEDED", path)
        if len(selected) >= MAX_SOURCE_FILES_V1 or total_bytes > MAX_TOTAL_SOURCE_BYTES_V1:
            reject_v1("SOURCE_SCOPE_BUDGET_EXCEEDED", path)
        selected.append(
            TreeEntryV1(path, mode, match.group("object").decode(), size, classes)
        )
    selected.sort(key=lambda entry: entry.path)
    if EXPECTED_SCOPED_FILE_COUNT_V1 >= 0 and (len(selected), total_bytes) != (
        EXPECTED_SCOPED_FILE_COUNT_V1,
        EXPECTED_SCOPED_SOURCE_BYTES_V1,
    ):
        reject_v1("SUBJECT_SCOPE_IDENTITY_MISMATCH", f"{len(selected)}:{total_bytes}")
    return tuple(selected)


def _scan_blob_v1(
    entry: TreeEntryV1,
    raw: bytes,
) -> tuple[dict[str, object], DependencyCandidateV1 | None, int]:
    if len(raw) != entry.size:
        reject_v1("GIT_ARCHIVE_SIZE_MISMATCH", entry.path)
    source_sha256 = sha256_prefixed_v1(raw)
    signals, work_units = discover_source_signals_v1(entry.path, raw)
    candidate = (
        DependencyCandidateV1(entry.path, source_sha256, signals) if signals else None
    )
    return entry.scope_row(source_sha256), candidate, work_units


def _scan_archive_v1(archive: bytes, entries: Sequence[TreeEntryV1]) -> ScanResultV1:
    expected = {entry.path: entry for entry in entries}
    seen: set[str] = set()
    scope_rows: list[dict[str, object]] = []
    dependencies: list[DependencyCandidateV1] = []
    counts = {name: 0 for name in SCOPE_CLASSES_V1}
    closure_sources: dict[str, bytes] = {}
    work_units = 0
    try:
        tar = tarfile.open(fileobj=io.BytesIO(archive), mode="r:")
    except tarfile.TarError as exc:
        reject_v1("INVALID_GIT_ARCHIVE", type(exc).__name__)
    with tar:
        for member in tar:
            if member.isdir():
                continue
            path = _canonical_path_v1(member.name.encode())
            entry = expected.get(path)
            if entry is None or path in seen or not member.isfile():
                reject_v1("GIT_ARCHIVE_ENTRY_MISMATCH", path)
            extracted = tar.extractfile(member)
            if extracted is None:
                reject_v1("GIT_ARCHIVE_ENTRY_UNREADABLE", path)
            extracted = cast(BinaryIO, extracted)
            raw = extracted.read(MAX_SINGLE_SOURCE_BYTES_V1 + 1)
            scope_row, candidate, file_work = _scan_blob_v1(entry, raw)
            work_units += file_work
            if work_units > MAX_SEMANTIC_WORK_UNITS_V1:
                reject_v1("SEMANTIC_SCAN_BUDGET_EXCEEDED", path)
            scope_rows.append(scope_row)
            dependencies.extend(() if candidate is None else (candidate,))
            for name in entry.scope_classes:
                counts[name] += 1
            if path in REQUIRED_CLOSURE_PATHS_V1:
                closure_sources[path] = raw
            seen.add(path)
    if seen != set(expected):
        reject_v1("GIT_ARCHIVE_COVERAGE_MISMATCH", str(len(set(expected) - seen)))
    if set(closure_sources) != REQUIRED_CLOSURE_PATHS_V1:
        reject_v1("ROUTE_CLOSURE_SOURCE_MISSING", str(len(closure_sources)))
    scope_rows.sort(key=lambda row: str(row["path"]))
    return ScanResultV1(
        source_scope_root=sha256_prefixed_v1(canonical_json_bytes_v1(scope_rows)),
        dependencies=tuple(sorted(dependencies, key=lambda candidate: candidate.source_path)),
        class_counts=tuple(sorted(counts.items())),
        file_count=len(entries),
        total_source_bytes=sum(entry.size for entry in entries),
        semantic_work_units=work_units,
        closure_sources=closure_sources,
    )


def _scan_subject_v1(
    root: Path,
    binding: GitBindingV1,
    budget: GitCommandBudgetV1,
) -> ScanResultV1:
    entries = _read_tree_entries_v1(root, binding, budget)
    archive = _run_git_v1(
        root,
        ["archive", "--format=tar", binding.commit, "--", *(entry.path for entry in entries)],
        max_stdout_bytes=MAX_ARCHIVE_BYTES_V1,
        budget=budget,
    ).stdout
    return _scan_archive_v1(archive, entries)


def build_inventory_object_v1(root: Path) -> dict[str, object]:
    budget = GitCommandBudgetV1()
    binding = read_git_binding_v1(root, budget)
    return build_inventory_payload_v1(binding, _scan_subject_v1(root, binding, budget))


def build_inventory_bytes_v1(root: Path) -> bytes:
    raw = canonical_json_bytes_v1(build_inventory_object_v1(root))
    if len(raw) > MAX_ARTIFACT_BYTES_V1:
        reject_v1("ARTIFACT_TOO_LARGE", str(len(raw)))
    return raw


def _write_exact_output_v1(path: Path, raw: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        if path.exists() and (
            stat.S_ISLNK(path.lstat().st_mode) or not stat.S_ISREG(path.lstat().st_mode)
        ):
            raise InventoryRejectV1("OUTPUT_NOT_REGULAR_FILE", str(path))
        descriptor = os.open(path, flags, 0o644)
    except OSError as exc:
        raise InventoryRejectV1("OUTPUT_WRITE_FAILED", type(exc).__name__) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise InventoryRejectV1("OUTPUT_NOT_REGULAR_FILE", str(path))
        offset = 0
        while offset < len(raw):
            written = os.write(descriptor, raw[offset:])
            if written <= 0:
                raise InventoryRejectV1("OUTPUT_WRITE_FAILED", "zero-byte-write")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    root = parser.parse_args(argv).root
    try:
        raw = build_inventory_bytes_v1(root)
        _write_exact_output_v1(root / INVENTORY_PATH_V1, raw)
    except InventoryRejectV1 as exc:
        print(json.dumps({"code": exc.code, "detail": exc.detail, "ok": False}, sort_keys=True))
        return 1
    except (OSError, ValueError) as exc:
        print(json.dumps({"code": "BUILDER_INPUT_ERROR", "detail": type(exc).__name__, "ok": False}, sort_keys=True))
        return 1
    print(json.dumps({"artifact": INVENTORY_PATH_V1.as_posix(), "bytes": len(raw), "ok": True}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
