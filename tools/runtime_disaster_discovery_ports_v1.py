#!/usr/bin/env python3
"""Effect ports for the WholeEconomyDisasterCoverageV1 shells.

This module owns every effect the runner and the verifier perform: fixed-argv
Git probes with a sanitized environment, openat-style no-follow bounded reads
with byte ceilings enforced before allocation, registered-argv execution, and
the one-read cache that binds each path to the captured tree object.  Tests
replace ``ShellPortsV1`` with deterministic fakes.
"""

from __future__ import annotations

import datetime as dt
import errno
import hashlib
import os
import platform
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from tools.runtime_disaster_discovery_evidence_v1 import ExecutionObservationV1
from tools.runtime_disaster_discovery_primitives_v1 import (
    DiscoveryReject,
    RejectCodeV1,
    sha256_hex,
    validate_repo_path,
)
from tools.runtime_disaster_discovery_registry_v1 import RegisteredRunnerV1
from tools.runtime_disaster_discovery_sources_v1 import HeadEntryV1, OwnedSourceV1
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    MAX_GIT_OUTPUT_BYTES_V1,
    MAX_RUNNER_OUTPUT_BYTES_V1,
    MAX_SOURCE_BYTES_V1,
    PathKindV1,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
_GIT_OID_LEN = 40
_READ_CHUNK = 1 << 16
_PROCESS_TERMINATION_GRACE_S = 0.25
_RUNNER_STREAM_DOMAIN_V1 = b"zenodex/wedc1/runner-stream/v1\x00"
_INCOMPLETE_STREAM_DOMAIN_V1 = b"zenodex/wedc1/incomplete-runner-stream/v1\x00"


@dataclass(frozen=True, slots=True)
class _ProcessCaptureV1:
    returncode: int | None
    stdout_sha256: str
    stderr_sha256: str
    stdout: bytes
    stderr: bytes
    timed_out: bool
    output_limit_exceeded: bool


@dataclass(frozen=True, slots=True)
class GitHeadStateV1:
    """Commit and tree captured together; the tree is resolved from the captured commit."""

    commit: str
    tree: str
    worktree_clean: bool | None


@dataclass(frozen=True, slots=True)
class HeadLookupV1:
    available: bool
    entry: HeadEntryV1 | None


@dataclass(frozen=True, slots=True)
class FileReadV1:
    """One bounded read of one repository path; ``data`` is None unless REGULAR."""

    kind: PathKindV1
    symlink_in_ancestry: bool
    data: bytes | None


@dataclass(frozen=True, slots=True)
class RunnerExecutionRequestV1:
    """One runner plus the exact owned source tree it must execute."""

    runner: RegisteredRunnerV1
    source_tree: tuple[tuple[str, bytes], ...]

    def __post_init__(self) -> None:
        if type(self.runner) is not RegisteredRunnerV1:
            raise TypeError("runner execution request requires an exact runner")
        if type(self.source_tree) is not tuple:
            raise TypeError("runner execution source tree must be a tuple")
        paths: list[str] = []
        for row in self.source_tree:
            if type(row) is not tuple or len(row) != 2:
                raise TypeError("runner execution source row must be an exact pair")
            path, data = row
            paths.append(validate_repo_path(path, "runner execution source path"))
            if type(data) is not bytes:
                raise TypeError("runner execution source bytes must have the exact type")
        if paths != sorted(paths) or len(paths) != len(set(paths)):
            raise ValueError("runner execution source paths must be unique and ordered")
        if self.runner.argv[1] not in paths:
            raise ValueError("runner execution source tree omits the runner")


@dataclass(frozen=True)
class ShellPortsV1:
    """Injected effect ports.  Tests replace them with deterministic fakes."""

    read_file: Callable[[str], FileReadV1]
    tree_entry: Callable[[str, str], HeadLookupV1]
    head_state: Callable[[], GitHeadStateV1 | None]
    execute: Callable[[RunnerExecutionRequestV1], ExecutionObservationV1]
    race_boundary: Callable[[str], None]
    now_utc_iso: Callable[[], str]
    python_version: str


def _git_env() -> dict[str, str]:
    return {
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "HOME": os.devnull,
        "LC_ALL": "C",
        "PATH": os.defpath,
    }


def _terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    """Bound termination to the process group created for this execution."""

    try:
        os.killpg(process.pid, signal.SIGTERM)
    except OSError:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except OSError:
        pass
    try:
        process.wait(timeout=_PROCESS_TERMINATION_GRACE_S)
    except subprocess.TimeoutExpired:
        pass


def _failed_process_capture_v1() -> _ProcessCaptureV1:
    empty_hash = sha256_hex(b"")
    return _ProcessCaptureV1(None, empty_hash, empty_hash, b"", b"", False, False)


def _drain_bounded_streams(
    process: subprocess.Popen[bytes],
    *,
    timeout_s: float,
    max_output_bytes: int,
    retain_output: bool,
) -> _ProcessCaptureV1:
    """Drain both pipes under one deadline and combined byte ceiling."""

    if process.stdout is None or process.stderr is None:
        return _failed_process_capture_v1()
    streams = {
        process.stdout.fileno(): ("stdout", process.stdout),
        process.stderr.fileno(): ("stderr", process.stderr),
    }
    selected = selectors.DefaultSelector()
    hashes = {"stdout": hashlib.sha256(), "stderr": hashlib.sha256()}
    retained: dict[str, list[bytes]] = {"stdout": [], "stderr": []}
    total = 0
    deadline = time.monotonic() + timeout_s
    timed_out = False
    output_limit_exceeded = False
    try:
        for descriptor in streams:
            os.set_blocking(descriptor, False)
            selected.register(descriptor, selectors.EVENT_READ)
        while selected.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                break
            events = selected.select(timeout=min(remaining, 0.05))
            if not events and process.poll() is not None:
                events = [(key, selectors.EVENT_READ) for key in tuple(selected.get_map().values())]
            for key, _mask in events:
                descriptor = key.fd
                name, stream = streams[descriptor]
                try:
                    chunk = os.read(descriptor, _READ_CHUNK)
                except BlockingIOError:
                    continue
                if not chunk:
                    selected.unregister(descriptor)
                    stream.close()
                    continue
                hashes[name].update(chunk)
                total += len(chunk)
                if retain_output:
                    retained[name].append(chunk)
                if total > max_output_bytes:
                    output_limit_exceeded = True
                    break
            if output_limit_exceeded:
                break
        if not timed_out and not output_limit_exceeded:
            try:
                process.wait(timeout=max(0.0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                timed_out = True
        if timed_out or output_limit_exceeded:
            _terminate_process_group(process)
    finally:
        for key in tuple(selected.get_map().values()):
            _name, stream = streams[key.fd]
            selected.unregister(key.fd)
            stream.close()
        selected.close()
    return _ProcessCaptureV1(
        returncode=None if timed_out or output_limit_exceeded else process.returncode,
        stdout_sha256=hashes["stdout"].hexdigest(),
        stderr_sha256=hashes["stderr"].hexdigest(),
        stdout=b"".join(retained["stdout"]),
        stderr=b"".join(retained["stderr"]),
        timed_out=timed_out,
        output_limit_exceeded=output_limit_exceeded,
    )


def _run_bounded_process(
    argv: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout_s: float,
    max_output_bytes: int,
    retain_output: bool,
) -> _ProcessCaptureV1:
    """Run one process in a new session while hashing a bounded output stream."""

    try:
        process = subprocess.Popen(
            argv,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            close_fds=True,
            start_new_session=True,
        )
    except OSError:
        return _failed_process_capture_v1()
    try:
        try:
            return _drain_bounded_streams(
                process,
                timeout_s=timeout_s,
                max_output_bytes=max_output_bytes,
                retain_output=retain_output,
            )
        except OSError:
            return _failed_process_capture_v1()
    finally:
        for stream in (process.stdout, process.stderr):
            if stream is not None and not stream.closed:
                stream.close()
        if process.poll() is None:
            _terminate_process_group(process)


def _git(root: Path, *args: str) -> str | None:
    git = shutil.which("git", path=os.defpath)
    if git is None:
        return None
    completed = _run_bounded_process(
        [git, "-c", "core.hooksPath=/dev/null", "-C", str(root), *args],
        cwd=root,
        env=_git_env(),
        timeout_s=30,
        max_output_bytes=MAX_GIT_OUTPUT_BYTES_V1,
        retain_output=True,
    )
    if completed.returncode != 0 or completed.timed_out or completed.output_limit_exceeded:
        return None
    return completed.stdout.decode("utf-8", errors="replace")


def _is_oid(text: str) -> bool:
    return len(text) == _GIT_OID_LEN and all(char in "0123456789abcdef" for char in text)


def probe_head_state(root: Path) -> GitHeadStateV1 | None:
    """Capture the commit first, then resolve the tree from that exact commit object."""

    commit = _git(root, "rev-parse", "--verify", "HEAD^{commit}")
    if commit is None or not _is_oid(commit.strip()):
        return None
    commit_text = commit.strip()
    tree = _git(root, "rev-parse", "--verify", f"{commit_text}^{{tree}}")
    if tree is None or not _is_oid(tree.strip()):
        return None
    status = _git(root, "status", "--porcelain", "--untracked-files=all")
    return GitHeadStateV1(
        commit_text, tree.strip(), None if status is None else status.strip() == ""
    )


def probe_tree_entry(root: Path, tree_oid: str, path: str) -> HeadLookupV1:
    """Look a path up in the captured tree object, never in the moving HEAD name."""

    if not _is_oid(tree_oid):
        return HeadLookupV1(False, None)
    output = _git(root, "ls-tree", "-z", tree_oid, "--", path)
    if output is None:
        return HeadLookupV1(False, None)
    rows = [row for row in output.split("\x00") if row]
    if not rows:
        return HeadLookupV1(True, None)
    meta, _tab, entry_path = rows[0].partition("\t")
    parts = meta.split(" ")
    if len(parts) != 3 or entry_path != path:
        return HeadLookupV1(False, None)
    return HeadLookupV1(
        True, HeadEntryV1(path=path, git_mode=parts[0], object_type=parts[1], object_id=parts[2])
    )


def _path_kind(mode: int) -> PathKindV1:
    if stat.S_ISREG(mode):
        return PathKindV1.REGULAR
    if stat.S_ISLNK(mode):
        return PathKindV1.SYMLINK
    if stat.S_ISDIR(mode):
        return PathKindV1.DIRECTORY
    if stat.S_ISFIFO(mode):
        return PathKindV1.FIFO
    if stat.S_ISCHR(mode) or stat.S_ISBLK(mode):
        return PathKindV1.DEVICE
    if stat.S_ISSOCK(mode):
        return PathKindV1.SOCKET
    return PathKindV1.OTHER


def read_descriptor_bounded(descriptor: int, max_bytes: int) -> FileReadV1:
    """fstat first; refuse non-regular files and anything above the ceiling before reading."""

    info = os.fstat(descriptor)
    kind = _path_kind(info.st_mode)
    if kind is not PathKindV1.REGULAR:
        return FileReadV1(kind, False, None)
    if info.st_size > max_bytes:
        return FileReadV1(PathKindV1.OVERSIZE, False, None)
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = os.read(descriptor, min(_READ_CHUNK, max_bytes + 1 - total))
        if not chunk:
            break
        total += len(chunk)
        if total > max_bytes:
            return FileReadV1(PathKindV1.OVERSIZE, False, None)
        chunks.append(chunk)
    return FileReadV1(PathKindV1.REGULAR, False, b"".join(chunks))


def _open_component_dirs(root: Path, components: list[str]) -> int | FileReadV1:
    """Descend directory components with O_NOFOLLOW relative to the previous descriptor."""

    try:
        dir_fd = os.open(str(root), os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    except OSError:
        return FileReadV1(PathKindV1.MISSING, False, None)
    for component in components:
        try:
            mode = os.lstat(component, dir_fd=dir_fd).st_mode
        except OSError:
            os.close(dir_fd)
            return FileReadV1(PathKindV1.MISSING, False, None)
        if stat.S_ISLNK(mode):
            os.close(dir_fd)
            return FileReadV1(PathKindV1.SYMLINK, True, None)
        if not stat.S_ISDIR(mode):
            os.close(dir_fd)
            return FileReadV1(PathKindV1.OTHER, False, None)
        try:
            next_fd = os.open(
                component,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                dir_fd=dir_fd,
            )
        except OSError as exc:
            os.close(dir_fd)
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                return FileReadV1(PathKindV1.SYMLINK, True, None)
            return FileReadV1(PathKindV1.MISSING, False, None)
        os.close(dir_fd)
        dir_fd = next_fd
    return dir_fd


def read_file_bounded(root: Path, path: str, max_bytes: int = MAX_SOURCE_BYTES_V1) -> FileReadV1:
    """Open each component relative to the previous directory descriptor with O_NOFOLLOW.

    No path component is ever re-resolved after it was checked, so a
    parent-symlink swap between check and use cannot redirect the read.  FIFOs
    and devices are opened non-blocking and never read.
    """

    validate_repo_path(path, "source path")
    components = path.split("/")
    opened = _open_component_dirs(root, components[:-1])
    if isinstance(opened, FileReadV1):
        return opened
    dir_fd = opened
    try:
        try:
            file_fd = os.open(
                components[-1],
                os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC,
                dir_fd=dir_fd,
            )
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                return FileReadV1(PathKindV1.SYMLINK, False, None)
            if exc.errno == errno.ENXIO:
                return FileReadV1(PathKindV1.SOCKET, False, None)
            return FileReadV1(PathKindV1.MISSING, False, None)
        try:
            return read_descriptor_bounded(file_fd, max_bytes)
        except OSError:
            return FileReadV1(PathKindV1.OTHER, False, None)
        finally:
            os.close(file_fd)
    finally:
        os.close(dir_fd)


def build_runner_execution_request_v1(
    runner: RegisteredRunnerV1,
    sources: dict[str, bytes],
) -> RunnerExecutionRequestV1:
    """Own an ordered exact source snapshot for one registered runner."""

    if type(sources) is not dict:
        raise TypeError("runner execution sources must be an exact dictionary")
    rows: list[tuple[str, bytes]] = []
    for path in sorted(sources):
        data = sources[path]
        if type(path) is not str or type(data) is not bytes:
            raise TypeError("runner execution sources require exact path and bytes types")
        rows.append((path, bytes(data)))
    return RunnerExecutionRequestV1(runner=runner, source_tree=tuple(rows))


def _materialize_runner_source_tree_v1(
    root: Path,
    source_tree: tuple[tuple[str, bytes], ...],
) -> None:
    """Write a private no-follow copy of the already-owned source snapshot."""

    directories: set[Path] = {root}
    for path, data in source_tree:
        destination = root / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        current = destination.parent
        while current != root.parent:
            directories.add(current)
            if current == root:
                break
            current = current.parent
        descriptor = os.open(
            destination,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC,
            0o400,
        )
        try:
            view = memoryview(data)
            while view:
                written = os.write(descriptor, view)
                view = view[written:]
        finally:
            os.close(descriptor)
    for directory in sorted(directories, key=lambda item: len(item.parts), reverse=True):
        directory.chmod(0o500)


def _canonical_runner_stream_hash_v1(data: bytes, workspace_root: Path) -> str:
    """Hash an injective typed framing of literals and workspace occurrences."""

    ephemeral_prefix = os.fsencode(workspace_root)
    parts = data.split(ephemeral_prefix)
    digest = hashlib.sha256()
    digest.update(_RUNNER_STREAM_DOMAIN_V1)
    digest.update(len(parts).to_bytes(8, "big"))
    for index, literal in enumerate(parts):
        digest.update(b"\x00")
        digest.update(len(literal).to_bytes(8, "big"))
        digest.update(literal)
        if index + 1 < len(parts):
            digest.update(b"\x01")
    return digest.hexdigest()


def _incomplete_runner_stream_hash_v1(
    stream_name: bytes,
    *,
    timed_out: bool,
    output_limit_exceeded: bool,
) -> str:
    """Commit only the typed incomplete outcome, never scheduler-dependent bytes."""

    return sha256_hex(
        _INCOMPLETE_STREAM_DOMAIN_V1
        + stream_name
        + bytes((int(timed_out), int(output_limit_exceeded)))
    )


def _runner_stream_hashes_v1(
    completed: _ProcessCaptureV1,
    workspace_root: Path,
) -> tuple[str, str]:
    if completed.timed_out or completed.output_limit_exceeded:
        fields = {
            "timed_out": completed.timed_out,
            "output_limit_exceeded": completed.output_limit_exceeded,
        }
        return (
            _incomplete_runner_stream_hash_v1(b"stdout\x00", **fields),
            _incomplete_runner_stream_hash_v1(b"stderr\x00", **fields),
        )
    return (
        _canonical_runner_stream_hash_v1(completed.stdout, workspace_root),
        _canonical_runner_stream_hash_v1(completed.stderr, workspace_root),
    )


def execute_registered_runner(request: RunnerExecutionRequestV1) -> ExecutionObservationV1:
    """Execute one runner from its private captured source tree."""

    if type(request) is not RunnerExecutionRequestV1:
        raise TypeError("runner execution request must have the exact type")
    runner = request.runner
    with tempfile.TemporaryDirectory(prefix="wedc1-runner-", dir="/tmp") as workspace:
        workspace_root = Path(workspace)
        source_root = workspace_root / "source"
        private_home = workspace_root / "home"
        source_root.mkdir()
        private_home.mkdir()
        _materialize_runner_source_tree_v1(source_root, request.source_tree)
        env = {
            "HOME": str(private_home),
            "LANG": "C",
            "LC_ALL": "C",
            "PATH": os.defpath,
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONHASHSEED": "0",
            "PYTHONNOUSERSITE": "1",
            "PYTHONPATH": str(source_root),
            "PYTHONSAFEPATH": "1",
            "PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1",
            "TMPDIR": str(private_home),
            "TZ": "UTC",
            "XDG_CACHE_HOME": str(private_home),
            "XDG_CONFIG_HOME": str(private_home),
        }
        completed = _run_bounded_process(
            [sys.executable, "-s", "-P", *runner.argv[1:]],
            cwd=source_root,
            env=env,
            timeout_s=runner.timeout_s,
            max_output_bytes=MAX_RUNNER_OUTPUT_BYTES_V1,
            retain_output=True,
        )
        stdout_sha256, stderr_sha256 = _runner_stream_hashes_v1(completed, workspace_root)
    return ExecutionObservationV1(
        runner_id=runner.runner_id,
        argv_sha256=runner.argv_sha256,
        returncode=completed.returncode,
        stdout_sha256=stdout_sha256,
        stderr_sha256=stderr_sha256,
        timed_out=completed.timed_out,
        output_limit_exceeded=completed.output_limit_exceeded,
    )


def default_ports(root: Path = REPO_ROOT) -> ShellPortsV1:
    return ShellPortsV1(
        read_file=lambda path: read_file_bounded(root, path),
        tree_entry=lambda tree, path: probe_tree_entry(root, tree, path),
        head_state=lambda: probe_head_state(root),
        execute=execute_registered_runner,
        race_boundary=lambda _name: None,
        now_utc_iso=lambda: dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        python_version=platform.python_version(),
    )


class OneReadCacheV1:
    """Each path is read at most once per run and bound to the captured tree object."""

    def __init__(self, ports: ShellPortsV1, tree_oid: str) -> None:
        self._ports = ports
        self._tree_oid = tree_oid
        self._owned: dict[str, OwnedSourceV1] = {}

    def get(self, path: str) -> OwnedSourceV1:
        if path not in self._owned:
            lookup = self._ports.tree_entry(self._tree_oid, path)
            read = self._ports.read_file(path)
            self._owned[path] = OwnedSourceV1(
                path, read.kind, read.symlink_in_ancestry, read.data, lookup.entry, lookup.available
            )
        return self._owned[path]


def capture_head(ports: ShellPortsV1) -> GitHeadStateV1:
    head = ports.head_state()
    if head is None:
        raise DiscoveryReject(RejectCodeV1.GIT_PROBE_UNAVAILABLE, "HEAD")
    return head


def require_same_head(ports: ShellPortsV1, captured: GitHeadStateV1, boundary: str) -> None:
    """Reject when the commit or tree moved across a read, execution, or render boundary."""

    current = ports.head_state()
    if current is None or current.commit != captured.commit or current.tree != captured.tree:
        raise DiscoveryReject(RejectCodeV1.HEAD_MOVED, boundary)
