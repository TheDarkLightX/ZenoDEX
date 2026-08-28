#!/usr/bin/env python3
"""Build the O-008A artifact from bounded committed Git objects.

The implementation subject is C, a direct child of the fixed base P. The
artifact is written only after C and is intended to be committed alone as E.
This shell deliberately records Git/object-store and executable trust as
nonclaims; it makes no network request and invokes no Rust or RISC0 build.
"""

from __future__ import annotations

import argparse
import os
import secrets
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn, cast

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.risc0_build_host_qualification_v1 import (  # noqa: E402
    ARTIFACT_PATH_V1,
    DEPENDENCY_INVENTORY_PATH_V1,
    EXPECTED_PARENT_SHA256_V1,
    IMPLEMENTATION_PATHS_V1,
    LEGACY_LOCK_PATH_V1,
    LEGACY_WORKSPACE_V1,
    MAX_ARTIFACT_BYTES_V1,
    PLAN_PATH_V1,
    REQUIRED_LOCKED_PACKAGES_V1,
    REQUIRED_TMPDIR_V1,
    STATIC_SOURCE_PATHS_V1,
    QualificationRejectV1,
    QualificationSourceSnapshotV1,
    ResourceObservationV1,
    SourceEntryV1,
    build_qualification_artifact_v1,
    build_stale_placeholder_artifact_v1,
    canonical_json_bytes_v1,
    decode_json_object_v1,
    is_git_oid_v1,
    required_version_from_inventory_source_v1,
    sha256_prefixed_v1,
    validate_exact_o008a_plan_row_v1,
)
from tools.risc0_dependency_policy_v1 import audit_risc0_dependency_policy_v1  # noqa: E402

MAX_GIT_METADATA_BYTES_V1: Final = 2 * 1024 * 1024
MAX_GIT_STDERR_BYTES_V1: Final = 64 * 1024
MAX_SOURCE_FILE_BYTES_V1: Final = 2 * 1024 * 1024
MAX_SOURCE_TOTAL_BYTES_V1: Final = 16 * 1024 * 1024
GIT_TIMEOUT_SECONDS_V1: Final = 15.0
MAX_GIT_COMMIT_BYTES_V1: Final = 1024 * 1024

_REGULAR_GIT_MODES_V1: Final = frozenset({"100644", "100755"})
_READ_ONLY_GIT_SUBCOMMANDS_V1: Final = frozenset(
    {"cat-file", "diff-tree", "ls-tree", "rev-parse"}
)
_ARTIFACT_PARENT_COMPONENTS_V1: Final = ("docs", "research")
_ARTIFACT_BASENAME_V1: Final = Path(ARTIFACT_PATH_V1).name


class QualificationInputErrorV1(ValueError):
    """A fail-closed shell or committed-object observation rejection."""

    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code} at {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


@dataclass(frozen=True)
class GitTreeEntryV1:
    path: str
    git_mode: str
    object_type: str
    blob_oid: str
    size_bytes: int


@dataclass(frozen=True)
class BuildArtifactOutcomeV1:
    artifact: dict[str, object]
    replay_ready: bool


def _input_reject(code: str, path: str, detail: str) -> NoReturn:
    raise QualificationInputErrorV1(code, path, detail)


def _safe_repo_path_v1(path: str) -> bool:
    if not path or path.startswith("/") or "\x00" in path:
        return False
    if any(0xD800 <= ord(character) <= 0xDFFF for character in path):
        return False
    return all(component not in {"", ".", ".."} for component in path.split("/"))


def _is_cargo_input_path_v1(path: str) -> bool:
    if not path.startswith("zk/"):
        return False
    name = Path(path).name
    return name in {"Cargo.toml", "Cargo.lock"}


def _is_selected_source_path_v1(path: str) -> bool:
    return path in STATIC_SOURCE_PATHS_V1 or _is_cargo_input_path_v1(path)


def _validated_root_v1(root: Path) -> Path:
    root_path = Path(os.path.abspath(os.fspath(root)))
    try:
        metadata = root_path.lstat()
    except OSError as exc:
        _input_reject("REPOSITORY_ROOT", str(root_path), type(exc).__name__)
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        _input_reject("REPOSITORY_ROOT", str(root_path), "regular non-symlink directory required")
    return root_path


def _sanitized_git_environment_v1() -> dict[str, str]:
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
        "GIT_TERMINAL_PROMPT": "0",
        "LANG": "C",
        "LC_ALL": "C",
        "PAGER": "",
        "PATH": os.defpath,
        "XDG_CONFIG_HOME": os.devnull,
    }


def _terminate_process_v1(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except OSError:
        if process.poll() is None:
            try:
                process.kill()
            except OSError:
                pass
    try:
        process.wait(timeout=1)
    except (OSError, subprocess.TimeoutExpired):
        pass


def _collect_bounded_process_output_v1(
    process: subprocess.Popen[bytes],
    *,
    max_stdout_bytes: int,
    max_stderr_bytes: int,
) -> tuple[int, bytes, bytes]:
    stdout_stream = process.stdout
    stderr_stream = process.stderr
    if stdout_stream is None or stderr_stream is None:
        _terminate_process_v1(process)
        _input_reject("GIT_PIPE", "git", "stdout and stderr pipes are required")
    selector = selectors.DefaultSelector()
    buffers: dict[str, bytearray] = {"stdout": bytearray(), "stderr": bytearray()}
    limits = {"stdout": max_stdout_bytes, "stderr": max_stderr_bytes}
    deadline = time.monotonic() + GIT_TIMEOUT_SECONDS_V1
    try:
        for name, stream in (("stdout", stdout_stream), ("stderr", stderr_stream)):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, data=name)
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _input_reject("GIT_TIMEOUT", "git", "bounded command exceeded its time budget")
            events = selector.select(remaining)
            for key, _event in events:
                name = str(key.data)
                try:
                    chunk = os.read(key.fd, 64 * 1024)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(key.fd)
                    continue
                if len(buffers[name]) + len(chunk) > limits[name]:
                    _input_reject("GIT_OUTPUT_LIMIT", "git", f"{name} exceeds its bounded output limit")
                buffers[name].extend(chunk)
        try:
            returncode = process.wait(timeout=1)
        except subprocess.TimeoutExpired:
            _input_reject("GIT_TIMEOUT", "git", "command did not exit after output closed")
    except BaseException:
        _terminate_process_v1(process)
        raise
    finally:
        selector.close()
        stdout_stream.close()
        stderr_stream.close()
    return returncode, bytes(buffers["stdout"]), bytes(buffers["stderr"])


def _run_bounded_process_v1(
    command: tuple[str, ...],
    *,
    max_stdout_bytes: int,
    max_stderr_bytes: int = MAX_GIT_STDERR_BYTES_V1,
    allowed_returncodes: frozenset[int] = frozenset({0}),
) -> tuple[int, bytes, bytes]:
    """Run a local command while capping both pipes before buffering unbounded data."""

    try:
        process = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=_sanitized_git_environment_v1(),
            close_fds=True,
            bufsize=0,
            start_new_session=True,
        )
    except OSError as exc:
        _input_reject("GIT_UNAVAILABLE", "git", type(exc).__name__)
    returncode, stdout, stderr = _collect_bounded_process_output_v1(
        process,
        max_stdout_bytes=max_stdout_bytes,
        max_stderr_bytes=max_stderr_bytes,
    )
    if returncode not in allowed_returncodes:
        detail = stderr.decode("utf-8", "replace").strip()[:512] or f"exit {returncode}"
        _input_reject("GIT_COMMAND_FAILED", "git", detail)
    return returncode, stdout, stderr


@dataclass(frozen=True)
class GitObjectStoreV1:
    """Bounded local Git object access. Object-store trust remains a nonclaim."""

    root: Path
    git_executable: Path

    @classmethod
    def open_v1(cls, root: Path) -> "GitObjectStoreV1":
        checked_root = _validated_root_v1(root)
        git_path = shutil.which("git", path=os.defpath)
        if git_path is None or not os.path.isabs(git_path):
            _input_reject("GIT_UNAVAILABLE", "git", "git executable was not found")
        try:
            resolved_git = Path(git_path).resolve(strict=True)
        except OSError as exc:
            _input_reject("GIT_UNAVAILABLE", "git", type(exc).__name__)
        try:
            metadata = resolved_git.stat()
        except OSError as exc:
            _input_reject("GIT_UNAVAILABLE", "git", type(exc).__name__)
        if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved_git, os.X_OK):
            _input_reject("GIT_UNAVAILABLE", "git", "resolved Git path must be an executable regular file")
        return cls(root=checked_root, git_executable=resolved_git)

    def run_v1(
        self,
        *arguments: str,
        max_stdout_bytes: int = MAX_GIT_METADATA_BYTES_V1,
        allowed_returncodes: frozenset[int] = frozenset({0}),
    ) -> tuple[int, bytes, bytes]:
        if not arguments or arguments[0] not in _READ_ONLY_GIT_SUBCOMMANDS_V1:
            _input_reject("GIT_SUBCOMMAND", "git", "only the closed read-only Git command set is permitted")
        return _run_bounded_process_v1(
            (
                str(self.git_executable),
                "--no-pager",
                "-c",
                "core.attributesFile=/dev/null",
                "-c",
                "core.editor=/bin/false",
                "-c",
                "core.excludesFile=/dev/null",
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "core.pager=",
                "-c",
                "diff.external=/bin/false",
                "-c",
                "sequence.editor=/bin/false",
                "-C",
                str(self.root),
                *arguments,
            ),
            max_stdout_bytes=max_stdout_bytes,
            allowed_returncodes=allowed_returncodes,
        )

    def commit_oid_v1(self, revision: str) -> str:
        _returncode, raw, _stderr = self.run_v1("rev-parse", "--verify", f"{revision}^{{commit}}")
        value = _git_single_ascii_v1(raw, "GIT_COMMIT_OID")
        if not is_git_oid_v1(value):
            _input_reject("GIT_COMMIT_OID", revision, "Git returned an invalid commit OID")
        return value

    def tree_oid_v1(self, commit: str) -> str:
        _returncode, raw, _stderr = self.run_v1("rev-parse", "--verify", f"{commit}^{{tree}}")
        value = _git_single_ascii_v1(raw, "GIT_TREE_OID")
        if not is_git_oid_v1(value):
            _input_reject("GIT_TREE_OID", commit, "Git returned an invalid tree OID")
        return value

    def commit_parents_v1(self, commit: str) -> tuple[str, ...]:
        """Read parents from the immutable commit object, bypassing graft traversal."""

        _returncode, raw, _stderr = self.run_v1(
            "cat-file",
            "commit",
            commit,
            max_stdout_bytes=MAX_GIT_COMMIT_BYTES_V1,
        )
        header, separator, _message = raw.partition(b"\n\n")
        if not separator or b"\x00" in header:
            _input_reject("GIT_PARENTS", commit, "commit object lacks a canonical header")
        parents: list[str] = []
        tree_seen = False
        continuation_allowed = False
        for line in header.split(b"\n"):
            if line.startswith(b" "):
                if not continuation_allowed:
                    _input_reject("GIT_PARENTS", commit, "orphan commit-header continuation")
                continue
            continuation_allowed = True
            name, separator, value = line.partition(b" ")
            if not separator or not name or not value:
                _input_reject("GIT_PARENTS", commit, "malformed commit-header row")
            if name == b"tree":
                if tree_seen:
                    _input_reject("GIT_PARENTS", commit, "duplicate tree header")
                tree_seen = True
            elif name == b"parent":
                try:
                    parent = value.decode("ascii")
                except UnicodeDecodeError as exc:
                    _input_reject("GIT_PARENTS", commit, type(exc).__name__)
                if not is_git_oid_v1(parent):
                    _input_reject("GIT_PARENTS", commit, "invalid raw parent OID")
                parents.append(parent)
        if not tree_seen:
            _input_reject("GIT_PARENTS", commit, "commit object lacks one tree header")
        return tuple(parents)

    def diff_name_status_v1(self, before: str, after: str) -> tuple[tuple[str, str], ...]:
        _returncode, raw, _stderr = self.run_v1(
            "diff-tree",
            "--no-ext-diff",
            "--no-textconv",
            "--no-commit-id",
            "-r",
            "--name-status",
            "-z",
            "--no-renames",
            before,
            after,
        )
        fields = [item for item in raw.split(b"\0") if item]
        if len(fields) % 2 != 0:
            _input_reject("GIT_DIFF_FORMAT", after, "NUL records must contain status-path pairs")
        rows: list[tuple[str, str]] = []
        for index in range(0, len(fields), 2):
            try:
                status_text = fields[index].decode("ascii")
                path = fields[index + 1].decode("utf-8")
            except UnicodeDecodeError as exc:
                _input_reject("GIT_DIFF_FORMAT", after, type(exc).__name__)
            if status_text not in {"A", "M", "D", "T"} or not _safe_repo_path_v1(path):
                _input_reject("GIT_DIFF_FORMAT", after, "unexpected change record")
            rows.append((status_text, path))
        return tuple(rows)

    def tree_entries_v1(self, commit: str, pathspecs: tuple[str, ...]) -> tuple[GitTreeEntryV1, ...]:
        _returncode, raw, _stderr = self.run_v1(
            "ls-tree",
            "-r",
            "-l",
            "-z",
            commit,
            "--",
            *pathspecs,
        )
        entries: list[GitTreeEntryV1] = []
        for item in raw.split(b"\0"):
            if not item:
                continue
            try:
                header, path_raw = item.split(b"\t", 1)
                mode_raw, kind_raw, oid_raw, size_raw = header.split()
                git_mode = mode_raw.decode("ascii")
                object_type = kind_raw.decode("ascii")
                blob_oid = oid_raw.decode("ascii")
                size_text = size_raw.decode("ascii")
                path = path_raw.decode("utf-8")
                size_bytes = int(size_text)
            except (UnicodeDecodeError, ValueError) as exc:
                _input_reject("GIT_TREE_FORMAT", commit, type(exc).__name__)
            if (
                object_type != "blob"
                or not is_git_oid_v1(blob_oid)
                or size_bytes < 0
                or not _safe_repo_path_v1(path)
            ):
                _input_reject("GIT_TREE_FORMAT", commit, "unexpected tree entry")
            entries.append(
                GitTreeEntryV1(
                    path=path,
                    git_mode=git_mode,
                    object_type=object_type,
                    blob_oid=blob_oid,
                    size_bytes=size_bytes,
                )
            )
        if tuple(entry.path for entry in entries) != tuple(sorted(entry.path for entry in entries)):
            _input_reject("GIT_TREE_ORDER", commit, "tree entries are not in canonical path order")
        if len({entry.path for entry in entries}) != len(entries):
            _input_reject("GIT_TREE_DUPLICATE", commit, "tree contains duplicate selected paths")
        return tuple(entries)

    def blob_bytes_v1(self, entry: GitTreeEntryV1) -> bytes:
        if entry.size_bytes > MAX_SOURCE_FILE_BYTES_V1:
            _input_reject("SOURCE_SIZE_LIMIT", entry.path, "Git blob exceeds the per-file bound")
        _returncode, raw, _stderr = self.run_v1(
            "cat-file",
            "blob",
            entry.blob_oid,
            max_stdout_bytes=entry.size_bytes,
        )
        if len(raw) != entry.size_bytes:
            _input_reject("GIT_BLOB_SIZE", entry.path, "Git blob byte count differs from its tree record")
        return raw


def _git_single_ascii_v1(raw: bytes, code: str) -> str:
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        _input_reject(code, "git", type(exc).__name__)
    if not text.endswith("\n") or text.count("\n") != 1:
        _input_reject(code, "git", "expected exactly one ASCII line")
    value = text[:-1]
    if not value or "\x00" in value:
        _input_reject(code, "git", "empty or NUL-containing scalar")
    return value


def _source_pathspecs_v1() -> tuple[str, ...]:
    # ls-tree does not support glob pathspec magic. Its bounded zk traversal is
    # filtered immediately to the closed Cargo manifest and lock selection.
    return (*STATIC_SOURCE_PATHS_V1, "zk")


def collect_source_entries_v1(
    store: GitObjectStoreV1,
    commit: str,
) -> tuple[tuple[SourceEntryV1, ...], dict[str, bytes]]:
    """Read the complete source subject from C Git blobs, never worktree paths."""

    entries = store.tree_entries_v1(commit, _source_pathspecs_v1())
    selected = [entry for entry in entries if _is_selected_source_path_v1(entry.path)]
    selected_paths = {entry.path for entry in selected}
    missing = [path for path in STATIC_SOURCE_PATHS_V1 if path not in selected_paths]
    if missing:
        _input_reject("SOURCE_MISSING", missing[0], "required static source is absent from C")
    for required_path in (LEGACY_LOCK_PATH_V1, f"{LEGACY_WORKSPACE_V1}/Cargo.toml"):
        if required_path not in selected_paths:
            _input_reject("SOURCE_MISSING", required_path, "required legacy Cargo input is absent from C")
    if not any(_is_cargo_input_path_v1(entry.path) for entry in selected):
        _input_reject("SOURCE_CARGO_MISSING", "zk", "no Cargo manifest or lock is present")

    total_bytes = 0
    source_entries: list[SourceEntryV1] = []
    source_bytes: dict[str, bytes] = {}
    for entry in selected:
        if entry.git_mode not in _REGULAR_GIT_MODES_V1:
            _input_reject("SOURCE_GIT_MODE", entry.path, "regular non-symlink Git mode required")
        total_bytes += entry.size_bytes
        if total_bytes > MAX_SOURCE_TOTAL_BYTES_V1:
            _input_reject("SOURCE_TOTAL_LIMIT", "source_inventory", "combined blob size exceeds the bound")
        raw = store.blob_bytes_v1(entry)
        source_bytes[entry.path] = raw
        source_entries.append(
            SourceEntryV1(
                path=entry.path,
                git_mode=entry.git_mode,
                size_bytes=entry.size_bytes,
                blob_oid=entry.blob_oid,
                sha256=sha256_prefixed_v1(raw),
            )
        )
    return tuple(source_entries), source_bytes


def _write_materialized_cargo_blob_v1(root: Path, path: str, raw: bytes) -> None:
    if not _is_cargo_input_path_v1(path) or not _safe_repo_path_v1(path):
        _input_reject("POLICY_MATERIALIZE_PATH", path, "only safe Cargo inputs may be materialized")
    destination = root / path
    destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    no_follow = getattr(os, "O_NOFOLLOW", 0)
    if no_follow == 0:
        _input_reject("POLICY_MATERIALIZE_NOFOLLOW", path, "platform lacks O_NOFOLLOW")
    descriptor = os.open(destination, flags | no_follow, 0o600)
    try:
        offset = 0
        while offset < len(raw):
            wrote = os.write(descriptor, raw[offset:])
            if wrote <= 0:
                _input_reject("POLICY_MATERIALIZE_WRITE", path, "short write")
            offset += wrote
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _dependency_policy_report_v1(source_bytes: dict[str, bytes]) -> dict[str, object]:
    """Run the existing audit semantics on a private copy of committed Cargo blobs."""

    with tempfile.TemporaryDirectory(prefix="zenodex-o008a-policy-") as temp_dir:
        materialized_root = Path(temp_dir)
        for path in sorted(source_bytes):
            if _is_cargo_input_path_v1(path):
                _write_materialized_cargo_blob_v1(materialized_root, path, source_bytes[path])
        try:
            report = audit_risc0_dependency_policy_v1(materialized_root)
        except (OSError, UnicodeError, tomllib.TOMLDecodeError, ValueError) as exc:
            _input_reject("DEPENDENCY_POLICY_AUDIT", "zk", type(exc).__name__)
    if type(report) is not dict:
        _input_reject("DEPENDENCY_POLICY_AUDIT", "zk", "audit must return an exact object")
    canonical_json_bytes_v1(report)
    return dict(report)


def _legacy_manifest_requirements_v1(report: dict[str, object]) -> tuple[dict[str, object], ...]:
    dependencies = report.get("dependencies")
    if type(dependencies) is not list:
        _input_reject("DEPENDENCY_POLICY_SHAPE", "dependencies", "audit dependency rows must be a list")
    rows: list[dict[str, object]] = []
    dependency_rows = cast(list[object], dependencies)
    for index, row in enumerate(dependency_rows):
        if type(row) is not dict:
            _input_reject("DEPENDENCY_POLICY_SHAPE", f"dependencies[{index}]", "row must be an object")
        dependency_row = cast(dict[str, object], row)
        workspace = dependency_row.get("workspace")
        package = dependency_row.get("package")
        manifest = dependency_row.get("manifest")
        requirement = dependency_row.get("requirement")
        if workspace != LEGACY_WORKSPACE_V1 or package not in REQUIRED_LOCKED_PACKAGES_V1:
            continue
        if type(manifest) is not str or type(package) is not str:
            _input_reject("DEPENDENCY_POLICY_SHAPE", f"dependencies[{index}]", "manifest and package are required")
        rows.append(
            {
                "manifest": manifest,
                "package": package,
                "requirement": requirement,
            }
        )
    return tuple(sorted(rows, key=lambda row: (str(row["manifest"]), str(row["package"]))))


def _legacy_lock_versions_v1(raw: bytes) -> tuple[dict[str, object], ...]:
    try:
        document = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        _input_reject("LOCK_PARSE", LEGACY_LOCK_PATH_V1, type(exc).__name__)
    packages = document.get("package")
    if type(packages) is not list:
        _input_reject("LOCK_PACKAGE_LIST", LEGACY_LOCK_PATH_V1, "Cargo.lock package list is required")
    rows: list[dict[str, object]] = []
    package_rows = cast(list[object], packages)
    for package_name in REQUIRED_LOCKED_PACKAGES_V1:
        versions: set[str] = set()
        for package in package_rows:
            if type(package) is dict and package.get("name") == package_name:
                version = package.get("version")
                if type(version) is str:
                    versions.add(version)
        rows.append({"package": package_name, "versions": sorted(versions)})
    return tuple(rows)


def verify_implementation_subject_v1(
    store: GitObjectStoreV1,
    implementation_commit: str,
    *,
    expected_parent: str = EXPECTED_PARENT_SHA256_V1,
) -> str:
    """Require C to be P's direct child and to add only the implementation subject."""

    commit = store.commit_oid_v1(implementation_commit)
    parents = store.commit_parents_v1(commit)
    if parents != (expected_parent,):
        _input_reject("IMPLEMENTATION_PARENT", commit, "C must have P as its sole direct parent")
    changes = store.diff_name_status_v1(expected_parent, commit)
    expected_changes = tuple(("A", path) for path in sorted(IMPLEMENTATION_PATHS_V1))
    if changes != expected_changes:
        _input_reject("IMPLEMENTATION_COMMIT_SHAPE", commit, "C must add exactly the four implementation paths")
    return store.tree_oid_v1(commit)


def collect_qualification_snapshot_v1(
    root: Path,
    *,
    implementation_commit: str | None = None,
    expected_parent: str = EXPECTED_PARENT_SHA256_V1,
) -> QualificationSourceSnapshotV1:
    """Collect C's source and policy inputs solely from immutable Git blobs."""

    store = GitObjectStoreV1.open_v1(root)
    commit = store.commit_oid_v1("HEAD") if implementation_commit is None else store.commit_oid_v1(implementation_commit)
    implementation_tree = verify_implementation_subject_v1(store, commit, expected_parent=expected_parent)
    source_entries, source_bytes = collect_source_entries_v1(store, commit)
    plan = decode_json_object_v1(source_bytes[PLAN_PATH_V1], PLAN_PATH_V1, max_bytes=MAX_SOURCE_FILE_BYTES_V1)
    exact_plan_row = validate_exact_o008a_plan_row_v1(plan)
    required_version_source = required_version_from_inventory_source_v1(source_bytes[DEPENDENCY_INVENTORY_PATH_V1])
    policy_report = _dependency_policy_report_v1(source_bytes)
    manifest_requirements = _legacy_manifest_requirements_v1(policy_report)
    lock_versions = _legacy_lock_versions_v1(source_bytes[LEGACY_LOCK_PATH_V1])
    return QualificationSourceSnapshotV1(
        base_commit=expected_parent,
        implementation_commit=commit,
        implementation_tree=implementation_tree,
        source_entries=source_entries,
        exact_plan_row=exact_plan_row,
        required_version_source=required_version_source,
        dependency_policy_report=policy_report,
        legacy_manifest_requirements=manifest_requirements,
        legacy_lock_versions=lock_versions,
    )


def capture_resource_observation_v1() -> ResourceObservationV1:
    """Capture staging facts only after source and toolchain gates pass."""

    tmpdir = os.environ.get("TMPDIR", "")
    tmpdir_matches_required = tmpdir == REQUIRED_TMPDIR_V1
    free_tmp_bytes: int | None = None
    if tmpdir_matches_required:
        try:
            values = os.statvfs(REQUIRED_TMPDIR_V1)
            free_tmp_bytes = values.f_bavail * values.f_frsize
        except OSError:
            free_tmp_bytes = None
    available_memory_bytes: int | None = None
    try:
        pages = os.sysconf("SC_AVPHYS_PAGES")
        page_size = os.sysconf("SC_PAGE_SIZE")
        if type(pages) is int and type(page_size) is int and pages >= 0 and page_size > 0:
            available_memory_bytes = pages * page_size
    except (OSError, ValueError):
        available_memory_bytes = None
    return ResourceObservationV1(
        tmpdir_matches_required=tmpdir_matches_required,
        free_tmp_bytes=free_tmp_bytes,
        available_memory_bytes=available_memory_bytes,
    )


def resource_observation_from_artifact_v1(artifact: dict[str, object]) -> ResourceObservationV1 | None:
    """Recover a recorded post-toolchain staging observation for replay comparison."""

    resource = artifact.get("resource_preflight")
    if type(resource) is not dict:
        _input_reject("ARTIFACT_RESOURCE", "resource_preflight", "resource projection must be an object")
    resource_object = cast(dict[str, object], resource)
    state = resource_object.get("capture_state")
    if state in {"DEFERRED_UNTIL_TOOLCHAIN_GATES_PASS", "INSUFFICIENT_AFTER_TOOLCHAIN_GATES_PASS"}:
        return None
    if state != "OBSERVED_AFTER_TOOLCHAIN_GATES_PASS":
        _input_reject("ARTIFACT_RESOURCE", "resource_preflight.capture_state", "unknown capture state")
    tmpdir_matches = resource_object.get("tmpdir_matches_required")
    free_tmp_bytes = resource_object.get("observed_tmp_free_bytes")
    available_memory = resource_object.get("observed_available_memory_bytes")
    if type(tmpdir_matches) is not bool:
        _input_reject("ARTIFACT_RESOURCE", "resource_preflight.tmpdir_matches_required", "exact bool required")
    for path, value in (
        ("resource_preflight.observed_tmp_free_bytes", free_tmp_bytes),
        ("resource_preflight.observed_available_memory_bytes", available_memory),
    ):
        if type(value) is not int or value < 0:
            _input_reject("ARTIFACT_RESOURCE", path, "nonnegative exact integer required")
    return ResourceObservationV1(
        tmpdir_matches_required=tmpdir_matches,
        free_tmp_bytes=cast(int, free_tmp_bytes),
        available_memory_bytes=cast(int, available_memory),
    )


def build_artifact_for_head_v1(
    root: Path = REPO_ROOT,
    *,
    expected_parent: str = EXPECTED_PARENT_SHA256_V1,
) -> BuildArtifactOutcomeV1:
    """Build a replay-ready artifact for C or a visible stale placeholder at P."""

    try:
        store = GitObjectStoreV1.open_v1(root)
        head = store.commit_oid_v1("HEAD")
        snapshot = collect_qualification_snapshot_v1(root, implementation_commit=head, expected_parent=expected_parent)
        preliminary = build_qualification_artifact_v1(snapshot, resource=None)
        resource_projection = preliminary.get("resource_preflight")
        if type(resource_projection) is not dict:
            _input_reject("RESOURCE_PROJECTION", "resource_preflight", "artifact projection must be an object")
        resource_projection_object = cast(dict[str, object], resource_projection)
        resource = (
            None
            if resource_projection_object.get("capture_state") == "DEFERRED_UNTIL_TOOLCHAIN_GATES_PASS"
            else capture_resource_observation_v1()
        )
        return BuildArtifactOutcomeV1(
            artifact=build_qualification_artifact_v1(snapshot, resource=resource),
            replay_ready=True,
        )
    except (QualificationInputErrorV1, QualificationRejectV1) as exc:
        observed_head: str | None = None
        try:
            observed_head = GitObjectStoreV1.open_v1(root).commit_oid_v1("HEAD")
        except QualificationInputErrorV1:
            observed_head = None
        return BuildArtifactOutcomeV1(
            artifact=build_stale_placeholder_artifact_v1(
                base_commit=expected_parent,
                observed_head=observed_head,
                rejection_code=exc.code,
            ),
            replay_ready=False,
        )


def _open_directory_no_follow_v1(path: Path, label: str) -> int:
    no_follow = getattr(os, "O_NOFOLLOW", 0)
    if no_follow == 0:
        _input_reject("ARTIFACT_NOFOLLOW", label, "platform lacks O_NOFOLLOW")
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | no_follow)
    except OSError as exc:
        _input_reject("ARTIFACT_PARENT", label, type(exc).__name__)
    metadata = os.fstat(descriptor)
    if not stat.S_ISDIR(metadata.st_mode):
        os.close(descriptor)
        _input_reject("ARTIFACT_PARENT", label, "regular directory required")
    return descriptor


def _open_child_directory_no_follow_v1(parent_fd: int, component: str) -> int:
    no_follow = getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(
            component,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | no_follow,
            dir_fd=parent_fd,
        )
    except OSError as exc:
        _input_reject("ARTIFACT_PARENT", component, type(exc).__name__)
    metadata = os.fstat(descriptor)
    if not stat.S_ISDIR(metadata.st_mode):
        os.close(descriptor)
        _input_reject("ARTIFACT_PARENT", component, "regular directory required")
    return descriptor


def _verify_artifact_target_v1(parent_fd: int) -> None:
    try:
        metadata = os.stat(_ARTIFACT_BASENAME_V1, dir_fd=parent_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    except OSError as exc:
        _input_reject("ARTIFACT_TARGET", ARTIFACT_PATH_V1, type(exc).__name__)
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
        _input_reject("ARTIFACT_TARGET", ARTIFACT_PATH_V1, "existing target must be a singly linked regular file")


def _write_all_v1(descriptor: int, raw: bytes) -> None:
    offset = 0
    while offset < len(raw):
        wrote = os.write(descriptor, raw[offset:])
        if wrote <= 0:
            _input_reject("ARTIFACT_WRITE", ARTIFACT_PATH_V1, "short write")
        offset += wrote


def write_artifact_atomically_v1(root: Path, raw: bytes) -> Path:
    """Use a same-directory secure temporary file, fsync, and atomic replace."""

    if type(raw) is not bytes or len(raw) > MAX_ARTIFACT_BYTES_V1:
        _input_reject("ARTIFACT_SIZE_LIMIT", ARTIFACT_PATH_V1, "canonical output exceeds the byte bound")
    root_path = _validated_root_v1(root)
    root_fd = _open_directory_no_follow_v1(root_path, str(root_path))
    parent_fd = root_fd
    temporary_name: str | None = None
    temporary_fd: int | None = None
    try:
        for component in _ARTIFACT_PARENT_COMPONENTS_V1:
            child_fd = _open_child_directory_no_follow_v1(parent_fd, component)
            if parent_fd != root_fd:
                os.close(parent_fd)
            parent_fd = child_fd
        _verify_artifact_target_v1(parent_fd)
        for _attempt in range(64):
            candidate = f".{_ARTIFACT_BASENAME_V1}.{secrets.token_hex(16)}.tmp"
            try:
                temporary_fd = os.open(
                    candidate,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
                    0o600,
                    dir_fd=parent_fd,
                )
                temporary_name = candidate
                break
            except FileExistsError:
                continue
            except OSError as exc:
                _input_reject("ARTIFACT_TEMP", ARTIFACT_PATH_V1, type(exc).__name__)
        if temporary_fd is None or temporary_name is None:
            _input_reject("ARTIFACT_TEMP", ARTIFACT_PATH_V1, "unable to allocate a unique secure temporary file")
        temporary_descriptor = temporary_fd
        temporary_filename = temporary_name
        _write_all_v1(temporary_descriptor, raw)
        metadata = os.fstat(temporary_descriptor)
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1 or metadata.st_size != len(raw):
            _input_reject("ARTIFACT_TEMP", ARTIFACT_PATH_V1, "temporary output shape changed")
        os.fsync(temporary_descriptor)
        os.close(temporary_descriptor)
        temporary_fd = None
        os.replace(
            temporary_filename,
            _ARTIFACT_BASENAME_V1,
            src_dir_fd=parent_fd,
            dst_dir_fd=parent_fd,
        )
        temporary_name = None
        os.fsync(parent_fd)
    finally:
        if temporary_fd is not None:
            os.close(temporary_fd)
        if temporary_name is not None:
            try:
                os.unlink(temporary_name, dir_fd=parent_fd)
            except OSError:
                pass
        if parent_fd != root_fd:
            os.close(parent_fd)
        os.close(root_fd)
    return root_path / ARTIFACT_PATH_V1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    outcome = build_artifact_for_head_v1(args.root)
    raw = canonical_json_bytes_v1(outcome.artifact)
    write_artifact_atomically_v1(args.root, raw)
    result = outcome.artifact.get("result")
    status = result.get("status") if type(result) is dict else "REJECTED_BUILDER_OUTPUT"
    report = {
        "artifact_path": ARTIFACT_PATH_V1,
        "artifact_state": outcome.artifact.get("artifact_state"),
        "artifact_written": True,
        "network": "NETWORK_NOT_REQUESTED",
        "replay_ready": outcome.replay_ready,
        "status": status,
    }
    print(canonical_json_bytes_v1(report).decode("utf-8"))
    return 0 if outcome.replay_ready else 1


if __name__ == "__main__":
    raise SystemExit(main())
