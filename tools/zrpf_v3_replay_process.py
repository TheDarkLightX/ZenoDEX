"""Bounded subprocess capture for retained ZRPF V3 evidence tooling."""

from __future__ import annotations

import os
import selectors
import signal
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import IO


@dataclass(frozen=True)
class ProcessRequest:
    command: tuple[str, ...]
    cwd: Path
    env: dict[str, str]
    timeout_seconds: int
    output_limit_bytes: int


def run_bounded(request: ProcessRequest) -> subprocess.CompletedProcess[bytes]:
    if request.timeout_seconds <= 0 or request.output_limit_bytes <= 0:
        raise ValueError("subprocess bounds must be positive")
    process = subprocess.Popen(
        request.command,
        cwd=request.cwd,
        env=request.env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
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
