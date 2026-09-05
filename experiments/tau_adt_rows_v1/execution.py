"""Linux-only bounded process IO for explicit Tau research probes.

The immutable ELF copy reuses the receipt adapter's measured-copy checker.
Python, the OS, the dynamic loader and system libraries remain trusted.
"""

from __future__ import annotations

import fcntl
import os
import selectors
import subprocess
from contextlib import contextmanager
from pathlib import Path
from time import monotonic_ns
from typing import Iterator

from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    _copy_measured_elf_v1,
    _kill_and_reap_v1,
)

OUTPUT_LIMITS = {"stdout": 65536, "stderr": 4096}


@contextmanager
def frozen_executable(binary: Path, expected_sha256: str) -> Iterator[int]:
    source = os.open(binary, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    snapshot = None
    try:
        snapshot = os.memfd_create("zenodex-tau-research", os.MFD_ALLOW_SEALING | os.MFD_CLOEXEC)
        try:
            _copy_measured_elf_v1(source, snapshot, expected_sha256)
        except GlobalReceiptVerifierErrorV1 as exc:
            raise ValueError("Tau executable differs from the measured research subject") from exc
        os.fchmod(snapshot, 0o500)
        fcntl.fcntl(snapshot, fcntl.F_ADD_SEALS,
                    fcntl.F_SEAL_SEAL | fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK)
        yield snapshot
    finally:
        os.close(source)
        if snapshot is not None:
            os.close(snapshot)


def run_bounded(
    argv: tuple[str, ...], request: bytes, *, pass_fds: tuple[int, ...] = (), timeout_ms: int = 12000,
) -> subprocess.CompletedProcess[str]:
    if len(request) > 65536 or not 1 <= timeout_ms <= 12000:
        raise ValueError("research process input or deadline exceeds bounds")
    deadline = monotonic_ns() + timeout_ms * 1_000_000
    process = subprocess.Popen(
        argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env={"LC_ALL": "C"}, pass_fds=pass_fds, start_new_session=True, bufsize=0, cwd="/",
    )
    output = {"stdout": bytearray(), "stderr": bytearray()}
    pending = memoryview(request)
    try:
        with selectors.DefaultSelector() as selector:
            for name, stream in (("stdin", process.stdin), ("stdout", process.stdout), ("stderr", process.stderr)):
                if stream is None:
                    raise ValueError("research process pipe unavailable")
                os.set_blocking(stream.fileno(), False)
                selector.register(stream, selectors.EVENT_WRITE if name == "stdin" else selectors.EVENT_READ, name)
            while selector.get_map() or process.poll() is None:
                remaining = deadline - monotonic_ns()
                if remaining <= 0:
                    raise ValueError("research process deadline exceeded")
                for key, _ in selector.select(min(remaining / 1_000_000_000, 0.05)):
                    if key.data == "stdin":
                        try:
                            count = os.write(key.fd, pending[:4096])
                        except BrokenPipeError:
                            count = len(pending)
                        pending = pending[count:]
                        if not pending:
                            selector.unregister(key.fileobj)
                            if process.stdin is not None:
                                process.stdin.close()
                    else:
                        buffer = output[key.data]
                        chunk = os.read(key.fd, min(4096, OUTPUT_LIMITS[key.data] + 1 - len(buffer)))
                        buffer.extend(chunk)
                        if len(buffer) > OUTPUT_LIMITS[key.data]:
                            raise ValueError(f"research process {key.data} limit exceeded")
                        if not chunk:
                            selector.unregister(key.fileobj)
        status = process.wait()
    finally:
        _kill_and_reap_v1(process)
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream is not None:
                stream.close()
    if any(b"\r" in value for value in output.values()):
        raise ValueError("noncanonical carriage return in research transcript")
    return subprocess.CompletedProcess(argv, status, output["stdout"].decode("ascii"), output["stderr"].decode("ascii"))
