"""Bounded subprocess capture for retained ZRPF V3 evidence tooling."""

from __future__ import annotations

import ctypes
import fcntl
import os
import resource
import selectors
import signal
import subprocess
import time
from dataclasses import dataclass
from enum import Enum
from functools import partial
from pathlib import Path
from typing import IO

_LIBC = ctypes.CDLL(None, use_errno=True)
STDIN_SEALS = (
    fcntl.F_SEAL_SEAL
    | fcntl.F_SEAL_SHRINK
    | fcntl.F_SEAL_GROW
    | fcntl.F_SEAL_WRITE
)
STDIN_TRANSPORT = "linux_memfd_full_seals_v1"


class ProcessProfile(str, Enum):
    BUILD = "build"
    REPLAY = "replay"
    TOOL = "tool"


@dataclass(frozen=True)
class ProcessRequest:
    command: tuple[str, ...]
    cwd: Path
    env: dict[str, str]
    timeout_seconds: int
    output_limit_bytes: int
    profile: ProcessProfile
    pass_fds: tuple[int, ...] = ()
    stdin_bytes: bytes | None = None
    input_limit_bytes: int = 64 * 1024 * 1024


def run_bounded(request: ProcessRequest) -> subprocess.CompletedProcess[bytes]:
    if (
        request.timeout_seconds <= 0
        or request.output_limit_bytes <= 0
        or request.input_limit_bytes <= 0
    ):
        raise ValueError("subprocess bounds must be positive")
    if request.stdin_bytes is not None and not isinstance(request.stdin_bytes, bytes):
        raise TypeError("stdin_bytes must be bytes or None")
    if request.stdin_bytes is not None and len(request.stdin_bytes) > request.input_limit_bytes:
        raise ValueError("subprocess stdin exceeded cap")
    stdin_descriptor: int | None = None
    try:
        if request.stdin_bytes is not None:
            stdin_descriptor = _sealed_stdin(request.stdin_bytes)
            stdin: int | IO[bytes] = stdin_descriptor
        else:
            stdin = subprocess.DEVNULL
        process = subprocess.Popen(
            request.command,
            cwd=request.cwd,
            env=request.env,
            stdin=stdin,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            pass_fds=request.pass_fds,
            preexec_fn=partial(
                _apply_process_profile,
                request.profile,
                request.timeout_seconds,
                request.output_limit_bytes,
            ),
            start_new_session=True,
        )
    finally:
        if stdin_descriptor is not None:
            os.close(stdin_descriptor)
    if process.stdout is None or process.stderr is None:
        _kill_process_group(process)
        raise RuntimeError("subprocess pipes were not created")
    deadline = time.monotonic() + request.timeout_seconds
    try:
        stdout, stderr = _capture_bounded(process, request, deadline)
        try:
            return_code = process.wait(timeout=max(0.1, deadline - time.monotonic()))
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError("subprocess timed out") from exc
    except BaseException:
        _kill_process_group(process)
        raise
    return subprocess.CompletedProcess(request.command, return_code, stdout, stderr)


def _sealed_stdin(raw: bytes) -> int:
    if not hasattr(os, "memfd_create"):
        raise RuntimeError("sealed stdin transport is unavailable")
    descriptor = os.memfd_create(
        "zrpf-replay-stdin",
        os.MFD_ALLOW_SEALING | getattr(os, "MFD_CLOEXEC", 0),
    )
    try:
        view = memoryview(raw)
        offset = 0
        while offset < len(view):
            written = os.write(descriptor, view[offset:])
            if written <= 0:
                raise RuntimeError("sealed stdin write failed")
            offset += written
        fcntl.fcntl(descriptor, fcntl.F_ADD_SEALS, STDIN_SEALS)
        if fcntl.fcntl(descriptor, fcntl.F_GET_SEALS) != STDIN_SEALS:
            raise RuntimeError("sealed stdin seal mismatch")
        os.lseek(descriptor, 0, os.SEEK_SET)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _apply_process_profile(
    profile: ProcessProfile,
    timeout_seconds: int,
    output_limit_bytes: int,
) -> None:
    os.umask(0o077)
    _set_limit(resource.RLIMIT_CORE, 0)
    _set_limit(resource.RLIMIT_CPU, timeout_seconds + 5)
    if profile is ProcessProfile.BUILD:
        _set_limit(resource.RLIMIT_FSIZE, 8 * 1024 * 1024 * 1024)
        _set_limit(resource.RLIMIT_NOFILE, 4_096)
        _set_limit(resource.RLIMIT_NPROC, 32_768)
    elif profile is ProcessProfile.REPLAY:
        _set_limit(resource.RLIMIT_AS, 8 * 1024 * 1024 * 1024)
        _set_limit(resource.RLIMIT_FSIZE, output_limit_bytes)
        _set_limit(resource.RLIMIT_NOFILE, 64)
        _set_limit(resource.RLIMIT_NPROC, 1)
        _set_limit(resource.RLIMIT_STACK, 64 * 1024 * 1024)
    elif profile is ProcessProfile.TOOL:
        _set_limit(resource.RLIMIT_AS, 4 * 1024 * 1024 * 1024)
        _set_limit(resource.RLIMIT_FSIZE, 1024 * 1024 * 1024)
        _set_limit(resource.RLIMIT_NOFILE, 256)
        _set_limit(resource.RLIMIT_NPROC, 32_768)
    else:  # pragma: no cover - Enum exhaustiveness guard
        raise RuntimeError("unknown process security profile")
    _set_no_new_privileges()


def _set_limit(kind: int, requested: int) -> None:
    _, inherited_hard = resource.getrlimit(kind)
    bounded = requested if inherited_hard == resource.RLIM_INFINITY else min(
        requested, inherited_hard
    )
    resource.setrlimit(kind, (bounded, bounded))


def _set_no_new_privileges() -> None:
    if _LIBC.prctl(38, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "prctl(PR_SET_NO_NEW_PRIVS) failed")


def _capture_bounded(
    process: subprocess.Popen[bytes],
    request: ProcessRequest,
    deadline: float,
) -> tuple[bytes, bytes]:
    stdout_stream = process.stdout
    stderr_stream = process.stderr
    if stdout_stream is None or stderr_stream is None:
        raise RuntimeError("subprocess pipes were not created")
    stdout = bytearray()
    stderr = bytearray()
    streams = {
        stdout_stream.fileno(): (stdout_stream, stdout),
        stderr_stream.fileno(): (stderr_stream, stderr),
    }
    selector = selectors.DefaultSelector()
    for stream, _ in streams.values():
        selector.register(stream, selectors.EVENT_READ)
    try:
        _drain_selector(selector, streams, request.output_limit_bytes, deadline)
    finally:
        selector.close()
    return bytes(stdout), bytes(stderr)


def _drain_selector(
    selector: selectors.BaseSelector,
    streams: dict[int, tuple[IO[bytes], bytearray]],
    output_limit: int,
    deadline: float,
) -> None:
    while selector.get_map():
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise RuntimeError("subprocess timed out")
        events = selector.select(remaining)
        if not events:
            raise RuntimeError("subprocess timed out")
        for key, _ in events:
            _read_ready_stream(selector, streams, key.fd, output_limit)


def _read_ready_stream(
    selector: selectors.BaseSelector,
    streams: dict[int, tuple[IO[bytes], bytearray]],
    file_descriptor: int,
    output_limit: int,
) -> None:
    stream, output = streams[file_descriptor]
    read_size = min(65_536, output_limit + 1 - len(output))
    chunk = os.read(file_descriptor, read_size)
    if chunk:
        output.extend(chunk)
        if len(output) > output_limit:
            raise RuntimeError("subprocess output exceeded cap")
        return
    selector.unregister(file_descriptor)
    stream.close()


def _kill_process_group(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    for stream in (process.stdout, process.stderr):
        if stream is not None:
            stream.close()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()
