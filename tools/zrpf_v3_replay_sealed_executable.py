"""Descriptor-bound executable images for ZRPF retained-receipt replay."""

from __future__ import annotations

import fcntl
import hashlib
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from types import TracebackType
from typing import Literal

MAX_EXECUTABLE_BYTES = 64 * 1024 * 1024
REQUIRED_SEALS = (
    fcntl.F_SEAL_SEAL
    | fcntl.F_SEAL_SHRINK
    | fcntl.F_SEAL_GROW
    | fcntl.F_SEAL_WRITE
)


@dataclass(frozen=True)
class ExecutableIdentity:
    sha256: str
    size_bytes: int
    transport: str


class SealedExecutable:
    """Own an immutable Linux memfd containing exact executable bytes."""

    def __init__(self, source: Path) -> None:
        self._source = source
        self._descriptor: int | None = None
        self._identity: ExecutableIdentity | None = None

    def __enter__(self) -> SealedExecutable:
        if not hasattr(os, "memfd_create") or not Path("/proc/self/fd").is_dir():
            raise RuntimeError("sealed executable transport is unavailable")
        raw = _stable_regular_file_bytes(self._source)
        descriptor = os.memfd_create(
            "zrpf-replay-verifier",
            os.MFD_ALLOW_SEALING | getattr(os, "MFD_CLOEXEC", 0),
        )
        try:
            _write_all(descriptor, raw)
            os.fchmod(descriptor, 0o500)
            fcntl.fcntl(descriptor, fcntl.F_ADD_SEALS, REQUIRED_SEALS)
            if fcntl.fcntl(descriptor, fcntl.F_GET_SEALS) != REQUIRED_SEALS:
                raise RuntimeError("executable memfd seal mismatch")
        except BaseException:
            os.close(descriptor)
            raise
        self._descriptor = descriptor
        self._identity = ExecutableIdentity(
            sha256=hashlib.sha256(raw).hexdigest(),
            size_bytes=len(raw),
            transport="linux_memfd_full_seals_v1",
        )
        return self

    def __exit__(
        self,
        _exception_type: type[BaseException] | None,
        _exception: BaseException | None,
        _traceback: TracebackType | None,
    ) -> Literal[False]:
        if self._descriptor is not None:
            os.close(self._descriptor)
            self._descriptor = None
        return False

    @property
    def command_path(self) -> str:
        descriptor = self._require_descriptor()
        return f"/proc/self/fd/{descriptor}"

    @property
    def pass_fds(self) -> tuple[int, ...]:
        return (self._require_descriptor(),)

    @property
    def identity(self) -> ExecutableIdentity:
        if self._identity is None:
            raise RuntimeError("sealed executable has not been opened")
        return self._identity

    def _require_descriptor(self) -> int:
        if self._descriptor is None:
            raise RuntimeError("sealed executable is not open")
        return self._descriptor


def _stable_regular_file_bytes(path: Path) -> bytes:
    # A hostile FIFO must reach fstat and reject without blocking before any
    # subprocess timeout or sandbox boundary exists.
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise RuntimeError("built verifier is unavailable or symlinked") from exc
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > MAX_EXECUTABLE_BYTES
        ):
            raise RuntimeError("built verifier is not a bounded regular file")
        raw = _read_exact(descriptor, before.st_size)
        after = os.fstat(descriptor)
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
            raise RuntimeError("built verifier changed while being sealed")
        return raw
    finally:
        os.close(descriptor)


def _read_exact(descriptor: int, size: int) -> bytes:
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        chunk = os.read(descriptor, min(remaining, 1024 * 1024))
        if not chunk:
            raise RuntimeError("built verifier was truncated while being sealed")
        chunks.append(chunk)
        remaining -= len(chunk)
    if os.read(descriptor, 1):
        raise RuntimeError("built verifier grew while being sealed")
    return b"".join(chunks)


def _write_all(descriptor: int, raw: bytes) -> None:
    view = memoryview(raw)
    offset = 0
    while offset < len(view):
        written = os.write(descriptor, view[offset:])
        if written <= 0:
            raise RuntimeError("sealed executable write failed")
        offset += written
