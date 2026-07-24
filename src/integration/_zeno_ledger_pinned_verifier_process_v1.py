"""Private one-shot process shell for a pinned ZenoLedger verifier.

This is an intermediate Linux pre-exec contract.  The embedded Python launcher
runtime is not release-bound, and the process shell is not a complete native
sandbox.  Production authority remains false in the consuming boundary.
"""

from __future__ import annotations

import fcntl
import hashlib
import os
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
MAX_VERIFIER_OPEN_FILES = 32
# RLIMIT_NPROC limits later process creation under Linux per-real-UID accounting.
# It is not process isolation; process-group teardown independently owns any
# descendants that a governed test profile is explicitly allowed to create.
MAX_VERIFIER_PROCESSES = 1

# This source runs under the current trusted Python runtime with isolated mode
# enabled. It installs the complete child contract before replacing itself with
# the already sealed governed verifier. Any setup failure exits without calling
# execve, so the governed program never observes a partially applied profile.
_PRE_EXEC_LAUNCHER_SOURCE = r"""
import ctypes
import errno
import os
import resource
import sys

PR_SET_NO_NEW_PRIVS = 38
PR_GET_NO_NEW_PRIVS = 39
PR_SET_SECCOMP = 22
SECCOMP_MODE_FILTER = 2
SECCOMP_RET_KILL_PROCESS = 0x80000000
SECCOMP_RET_ERRNO = 0x00050000
SECCOMP_RET_ALLOW = 0x7fff0000
BPF_LD_W_ABS = 0x20
BPF_JMP_JEQ_K = 0x15
BPF_RET_K = 0x06


class SockFilter(ctypes.Structure):
    _fields_ = [
        ("code", ctypes.c_ushort),
        ("jt", ctypes.c_ubyte),
        ("jf", ctypes.c_ubyte),
        ("k", ctypes.c_uint32),
    ]


class SockFprog(ctypes.Structure):
    _fields_ = [("len", ctypes.c_ushort), ("filter", ctypes.POINTER(SockFilter))]


def set_limit(kind, requested):
    _soft, inherited_hard = resource.getrlimit(kind)
    if inherited_hard != resource.RLIM_INFINITY and requested > inherited_hard:
        raise RuntimeError("requested verifier limit exceeds inherited hard limit")
    resource.setrlimit(kind, (requested, requested))
    if resource.getrlimit(kind) != (requested, requested):
        raise RuntimeError("verifier resource limit did not install exactly")


def close_unexpected_fds(executable_fd):
    for name in os.listdir("/proc/self/fd"):
        descriptor = int(name)
        if descriptor in (0, 1, 2, executable_fd):
            continue
        try:
            os.close(descriptor)
        except OSError as exc:
            if exc.errno != errno.EBADF:
                raise


def install_no_new_privileges(libc):
    if libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "PR_SET_NO_NEW_PRIVS failed")
    if libc.prctl(PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) != 1:
        raise RuntimeError("PR_SET_NO_NEW_PRIVS did not persist")


def install_socket_deny_filter(libc, audit_arch, socket_syscall):
    filters = (SockFilter * 7)(
        SockFilter(BPF_LD_W_ABS, 0, 0, 4),
        SockFilter(BPF_JMP_JEQ_K, 1, 0, audit_arch),
        SockFilter(BPF_RET_K, 0, 0, SECCOMP_RET_KILL_PROCESS),
        SockFilter(BPF_LD_W_ABS, 0, 0, 0),
        SockFilter(BPF_JMP_JEQ_K, 0, 1, socket_syscall),
        SockFilter(BPF_RET_K, 0, 0, SECCOMP_RET_ERRNO | errno.EPERM),
        SockFilter(BPF_RET_K, 0, 0, SECCOMP_RET_ALLOW),
    )
    program = SockFprog(len(filters), filters)
    if libc.prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, ctypes.addressof(program), 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "SECCOMP_MODE_FILTER failed")


def main():
    if len(sys.argv) != 10:
        raise RuntimeError("invalid pre-exec launcher argument count")
    executable_fd = int(sys.argv[1])
    timeout_seconds = int(sys.argv[2])
    address_space_bytes = int(sys.argv[3])
    stack_bytes = int(sys.argv[4])
    open_files = int(sys.argv[5])
    audit_arch = int(sys.argv[6])
    socket_syscall = int(sys.argv[7])
    process_count = int(sys.argv[8])
    max_file_size_bytes = int(sys.argv[9])
    os.umask(0o077)
    close_unexpected_fds(executable_fd)
    set_limit(resource.RLIMIT_AS, address_space_bytes)
    set_limit(resource.RLIMIT_STACK, stack_bytes)
    set_limit(resource.RLIMIT_CPU, timeout_seconds + 1)
    set_limit(resource.RLIMIT_CORE, 0)
    set_limit(resource.RLIMIT_FSIZE, max_file_size_bytes)
    set_limit(resource.RLIMIT_NOFILE, open_files)
    set_limit(resource.RLIMIT_NPROC, process_count)
    libc = ctypes.CDLL(None, use_errno=True)
    libc.prctl.argtypes = [
        ctypes.c_int,
        ctypes.c_ulong,
        ctypes.c_ulong,
        ctypes.c_ulong,
        ctypes.c_ulong,
    ]
    libc.prctl.restype = ctypes.c_int
    install_no_new_privileges(libc)
    install_socket_deny_filter(libc, audit_arch, socket_syscall)
    path = "/proc/self/fd/" + str(executable_fd)
    os.execve(
        path,
        [path],
        {
            "PATH": "/usr/bin:/bin",
            "LANG": "C",
            "LC_ALL": "C",
            "RISC0_DEV_MODE": "0",
            "TZ": "UTC",
        },
    )


try:
    main()
except BaseException:
    try:
        os.write(2, b"pre-exec verifier launcher rejected\n")
    finally:
        os._exit(126)
"""


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
        self.detail = detail
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
    max_stdout_bytes: int = MAX_VERIFIER_STDOUT_BYTES,
    max_stderr_bytes: int = MAX_VERIFIER_STDERR_BYTES,
) -> bytes:
    """Snapshot, execute once, bound outputs, and tear down the verifier."""

    _validate_output_limit(max_stdout_bytes, label="stdout")
    _validate_output_limit(max_stderr_bytes, label="stderr")

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
            process = _start_verifier(
                executable_fd,
                stdout_file,
                stderr_file,
                timeout_seconds=timeout_seconds,
                max_address_space_bytes=max_address_space_bytes,
                max_stack_bytes=max_stack_bytes,
                max_file_size_bytes=max(max_stdout_bytes, max_stderr_bytes),
            )
            process.communicate(input=request_bytes, timeout=timeout_seconds)
            return_code = process.returncode
            _terminate_process_group(process)
            process = None
            stdout = _read_bounded_output(
                stdout_file,
                max_bytes=max_stdout_bytes,
                label="stdout",
            )
            stderr = _read_bounded_output(
                stderr_file,
                max_bytes=max_stderr_bytes,
                label="stderr",
            )
            if return_code != 0:
                raise PinnedVerifierProcessError(
                    PinnedVerifierProcessFailure.PROCESS_FAILED,
                    f"pinned verifier exited with status {return_code}",
                )
            if stderr:
                raise PinnedVerifierProcessError(
                    PinnedVerifierProcessFailure.OUTPUT_INVALID,
                    "successful pinned verifier emitted stderr",
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
    *,
    timeout_seconds: int,
    max_address_space_bytes: int,
    max_stack_bytes: int,
    max_file_size_bytes: int,
) -> subprocess.Popen[bytes]:
    audit_arch, socket_syscall = _seccomp_socket_profile()
    return subprocess.Popen(
        [
            "/proc/self/exe",
            "-I",
            "-S",
            "-c",
            _PRE_EXEC_LAUNCHER_SOURCE,
            str(executable_fd),
            str(timeout_seconds),
            str(max_address_space_bytes),
            str(max_stack_bytes),
            str(MAX_VERIFIER_OPEN_FILES),
            str(audit_arch),
            str(socket_syscall),
            str(MAX_VERIFIER_PROCESSES),
            str(max_file_size_bytes),
        ],
        stdin=subprocess.PIPE,
        stdout=stdout_file,
        stderr=stderr_file,
        start_new_session=True,
        close_fds=True,
        pass_fds=(executable_fd,),
        cwd="/",
        env={
            "PATH": "/usr/bin:/bin",
            "LANG": "C",
            "LC_ALL": "C",
            "RISC0_DEV_MODE": "0",
            "TZ": "UTC",
        },
    )


def _validate_output_limit(value: int, *, label: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"max verifier {label} bytes must be a positive int")


def _seccomp_socket_profile() -> tuple[int, int]:
    machine = os.uname().machine.lower()
    if machine in {"x86_64", "amd64"}:
        return 0xC000003E, 41
    if machine in {"aarch64", "arm64"}:
        return 0xC00000B7, 198
    raise PinnedVerifierProcessError(
        PinnedVerifierProcessFailure.PROCESS_FAILED,
        "host architecture has no governed verifier seccomp profile",
    )


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
