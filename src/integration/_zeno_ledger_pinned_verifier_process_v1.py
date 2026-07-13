"""Private one-shot process shell for a pinned ZenoLedger verifier."""

from __future__ import annotations

import fcntl
import hashlib
import os
import resource
import signal
import stat
import struct
import subprocess
import tempfile
import time
from enum import Enum
from pathlib import Path
from typing import BinaryIO, NoReturn

MAX_VERIFIER_EXECUTABLE_BYTES = 256 * 1024 * 1024
MAX_VERIFIER_STDOUT_BYTES = 2 * 1024 * 1024
MAX_VERIFIER_STDERR_BYTES = 64 * 1024
DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES = 4 * 1024 * 1024 * 1024
DEFAULT_VERIFIER_STACK_BYTES = 16 * 1024 * 1024


class VerifierExecutableFormatV1(str, Enum):
    """Dependency-closure policy for the pinned verifier executable."""

    STATIC_ELF_X86_64 = "static_elf_x86_64"
    TEST_SCRIPT = "test_script"


class PinnedVerifierProcessFailure(str, Enum):
    EXECUTABLE_INVALID = "executable_invalid"
    EXECUTABLE_HASH_MISMATCH = "executable_hash_mismatch"
    PROCESS_FAILED = "process_failed"
    TIMEOUT = "timeout"
    OUTPUT_INVALID = "output_invalid"


class PinnedVerifierProcessError(ValueError):
    def __init__(self, reason: PinnedVerifierProcessFailure, detail: str) -> None:
        self.reason = reason
        super().__init__(f"{reason.value}: {detail}")


def execute_pinned_verifier_once(
    *,
    executable: Path,
    expected_sha256: str,
    executable_format: VerifierExecutableFormatV1,
    request_bytes: bytes,
    timeout_seconds: int,
    max_address_space_bytes: int,
    max_stack_bytes: int,
) -> bytes:
    """Snapshot, execute once, bound outputs, and tear down the verifier."""

    executable_fd: int | None = None
    process: subprocess.Popen[bytes] | None = None
    try:
        executable_fd, actual_sha256 = _sealed_executable_snapshot(
            executable,
            executable_format=executable_format,
        )
        if actual_sha256 != expected_sha256:
            raise PinnedVerifierProcessError(
                PinnedVerifierProcessFailure.EXECUTABLE_HASH_MISMATCH,
                "pinned verifier executable hash mismatch",
            )
        with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
            process = _start_verifier(executable_fd, stdout_file, stderr_file)
            _apply_resource_limits(
                process.pid,
                timeout_seconds=timeout_seconds,
                max_address_space_bytes=max_address_space_bytes,
                max_stack_bytes=max_stack_bytes,
            )
            process.communicate(input=request_bytes, timeout=timeout_seconds)
            stdout = _read_bounded_output(
                stdout_file,
                max_bytes=MAX_VERIFIER_STDOUT_BYTES,
                label="stdout",
            )
            _read_bounded_output(
                stderr_file,
                max_bytes=MAX_VERIFIER_STDERR_BYTES,
                label="stderr",
            )
            if process.returncode != 0:
                raise PinnedVerifierProcessError(
                    PinnedVerifierProcessFailure.PROCESS_FAILED,
                    f"pinned verifier exited with status {process.returncode}",
                )
            return stdout
    except subprocess.TimeoutExpired as exc:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.TIMEOUT,
            "pinned verifier timed out",
        ) from exc
    except PinnedVerifierProcessError:
        raise
    except (OSError, ValueError) as exc:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.PROCESS_FAILED,
            "pinned verifier process failed",
        ) from exc
    finally:
        try:
            if process is not None:
                _terminate_process_group(process)
        finally:
            if executable_fd is not None:
                os.close(executable_fd)


def _start_verifier(
    executable_fd: int,
    stdout_file: BinaryIO,
    stderr_file: BinaryIO,
) -> subprocess.Popen[bytes]:
    return subprocess.Popen(
        [f"/proc/self/fd/{executable_fd}"],
        stdin=subprocess.PIPE,
        stdout=stdout_file,
        stderr=stderr_file,
        start_new_session=True,
        pass_fds=(executable_fd,),
        cwd="/",
        env={"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C", "TZ": "UTC"},
    )


def _apply_resource_limits(
    process_id: int,
    *,
    timeout_seconds: int,
    max_address_space_bytes: int,
    max_stack_bytes: int,
) -> None:
    try:
        resource.prlimit(
            process_id,
            resource.RLIMIT_AS,
            (max_address_space_bytes, max_address_space_bytes),
        )
        resource.prlimit(
            process_id,
            resource.RLIMIT_STACK,
            (max_stack_bytes, max_stack_bytes),
        )
        cpu_seconds = timeout_seconds + 1
        resource.prlimit(process_id, resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))
        resource.prlimit(process_id, resource.RLIMIT_CORE, (0, 0))
        resource.prlimit(
            process_id,
            resource.RLIMIT_FSIZE,
            (MAX_VERIFIER_STDOUT_BYTES, MAX_VERIFIER_STDOUT_BYTES),
        )
        resource.prlimit(process_id, resource.RLIMIT_NOFILE, (32, 32))
        resource.prlimit(process_id, resource.RLIMIT_NPROC, (1, 1))
    except (OSError, ValueError) as exc:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.PROCESS_FAILED,
            "failed to apply verifier resource limits",
        ) from exc


def _sealed_executable_snapshot(
    path: Path,
    *,
    executable_format: VerifierExecutableFormatV1,
) -> tuple[int, str]:
    if not hasattr(os, "memfd_create"):
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
            "sealed verifier execution requires memfd_create",
        )
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    source_fd = os.open(path, flags)
    memfd = -1
    try:
        before = _validate_source_executable(source_fd)
        memfd = os.memfd_create(
            "zenodex-ledger-risc0-verifier",
            flags=os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
        )
        copied, digest = _copy_executable(source_fd, memfd)
        after = os.fstat(source_fd)
        if copied != before.st_size or _file_identity(before) != _file_identity(after):
            raise PinnedVerifierProcessError(
                PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
                "verifier executable changed while being snapshotted",
            )
        _seal_executable_memfd(
            memfd,
            file_size=copied,
            executable_format=executable_format,
        )
        return memfd, digest
    except BaseException:
        if memfd >= 0:
            os.close(memfd)
        raise
    finally:
        os.close(source_fd)


def _validate_source_executable(source_fd: int) -> os.stat_result:
    source_stat = os.fstat(source_fd)
    if not stat.S_ISREG(source_stat.st_mode) or source_stat.st_mode & 0o022:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
            "verifier must be a non-group/world-writable regular file",
        )
    if source_stat.st_size <= 0 or source_stat.st_size > MAX_VERIFIER_EXECUTABLE_BYTES:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
            "verifier executable size is invalid",
        )
    return source_stat


def _copy_executable(source_fd: int, memfd: int) -> tuple[int, str]:
    digest = hashlib.sha256()
    copied = 0
    while True:
        chunk = os.read(source_fd, 1024 * 1024)
        if not chunk:
            break
        copied += len(chunk)
        if copied > MAX_VERIFIER_EXECUTABLE_BYTES:
            raise PinnedVerifierProcessError(
                PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
                "verifier executable exceeds byte limit",
            )
        digest.update(chunk)
        view = memoryview(chunk)
        while view:
            written = os.write(memfd, view)
            if written <= 0:
                raise OSError("failed to copy verifier executable")
            view = view[written:]
    return copied, digest.hexdigest()


def _file_identity(source_stat: os.stat_result) -> tuple[int, int, int, int, int, int]:
    return (
        source_stat.st_dev,
        source_stat.st_ino,
        source_stat.st_mode,
        source_stat.st_size,
        source_stat.st_mtime_ns,
        source_stat.st_ctime_ns,
    )


def _seal_executable_memfd(
    memfd: int,
    *,
    file_size: int,
    executable_format: VerifierExecutableFormatV1,
) -> None:
    os.fchmod(memfd, 0o500)
    os.lseek(memfd, 0, os.SEEK_SET)
    if executable_format is VerifierExecutableFormatV1.STATIC_ELF_X86_64:
        _require_static_x86_64_elf(memfd, file_size)
    elif executable_format is not VerifierExecutableFormatV1.TEST_SCRIPT:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
            "verifier executable format is unsupported",
        )
    seals = fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_SEAL
    fcntl.fcntl(memfd, fcntl.F_ADD_SEALS, seals)


def _require_static_x86_64_elf(descriptor: int, file_size: int) -> None:
    header = os.pread(descriptor, 64, 0)
    if len(header) != 64 or header[:4] != b"\x7fELF":
        _executable_invalid("verifier must be a static ELF")
    if header[4] != 2 or header[5] != 1 or header[6] != 1:
        _executable_invalid("verifier ELF class, byte order, or version is unsupported")
    elf_type, machine = struct.unpack_from("<HH", header, 16)
    if elf_type not in (2, 3) or machine != 62:
        _executable_invalid("verifier must be an x86_64 executable ELF")
    offset = struct.unpack_from("<Q", header, 32)[0]
    size, count = struct.unpack_from("<HH", header, 54)
    table_size = size * count
    if size < 56 or count == 0 or offset + table_size > file_size:
        _executable_invalid("verifier ELF program headers are invalid")
    program_headers = os.pread(descriptor, table_size, offset)
    if len(program_headers) != table_size:
        _executable_invalid("verifier ELF program headers are truncated")
    for index in range(count):
        program_type = struct.unpack_from("<I", program_headers, index * size)[0]
        if program_type == 3:
            _executable_invalid("verifier ELF has a dynamic interpreter")


def _executable_invalid(detail: str) -> NoReturn:
    raise PinnedVerifierProcessError(
        PinnedVerifierProcessFailure.EXECUTABLE_INVALID,
        detail,
    )


def _read_bounded_output(
    stream: BinaryIO,
    *,
    max_bytes: int,
    label: str,
) -> bytes:
    size = os.fstat(stream.fileno()).st_size
    if size > max_bytes:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.OUTPUT_INVALID,
            f"verifier {label} exceeds byte limit",
        )
    stream.seek(0)
    output = stream.read(max_bytes + 1)
    if len(output) != size:
        raise PinnedVerifierProcessError(
            PinnedVerifierProcessFailure.OUTPUT_INVALID,
            f"verifier {label} changed while being read",
        )
    return output


def _terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    process_group_id = process.pid
    try:
        os.killpg(process_group_id, signal.SIGKILL)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired as exc:
            raise PinnedVerifierProcessError(
                PinnedVerifierProcessFailure.PROCESS_FAILED,
                "pinned verifier leader did not terminate",
            ) from exc
    deadline = time.monotonic() + 5
    while _process_group_exists(process_group_id):
        if time.monotonic() >= deadline:
            raise PinnedVerifierProcessError(
                PinnedVerifierProcessFailure.PROCESS_FAILED,
                "pinned verifier process group did not terminate",
            )
        time.sleep(0.01)


def _process_group_exists(process_group_id: int) -> bool:
    try:
        os.killpg(process_group_id, 0)
    except ProcessLookupError:
        return False
    return True
