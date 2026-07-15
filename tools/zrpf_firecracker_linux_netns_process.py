"""Sealed, pre-limited process boundary for the Linux netns helper."""

from __future__ import annotations

import os
import signal
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import BinaryIO

from tools.zrpf_firecracker_linux_netns_protocol import (
    NETNS_HELPER_REQUEST_BYTES_V1,
    NETNS_HELPER_RESPONSE_BYTES_V1,
    LinuxNetnsAdapterRejectedV1,
    LinuxNetnsAdapterRejectV1,
)
from tools.zrpf_v3_replay_sealed_executable import SealedExecutable

_MAX_STDERR_BYTES_V1 = 4096
_MAX_ADDRESS_SPACE_BYTES_V1 = 256 * 1024 * 1024
_MAX_STACK_BYTES_V1 = 8 * 1024 * 1024
_TIMEOUT_SECONDS_V1 = 5
_ELF_PROGRAM_HEADER_BYTES_V1 = 56
_ELF_DYNAMIC_ENTRY_BYTES_V1 = 16
_ELF_MAX_PROGRAM_HEADERS_V1 = 128
_ELF_MAX_DYNAMIC_BYTES_V1 = 1024 * 1024

_PRE_EXEC_LAUNCHER_SOURCE_V1 = r"""
import ctypes
import errno
import os
import resource
import sys

PR_SET_NO_NEW_PRIVS = 38
PR_GET_NO_NEW_PRIVS = 39


def set_exact_limit(kind, requested):
    _soft, hard = resource.getrlimit(kind)
    if hard != resource.RLIM_INFINITY and requested > hard:
        raise RuntimeError("requested hard limit is unavailable")
    resource.setrlimit(kind, (requested, requested))
    if resource.getrlimit(kind) != (requested, requested):
        raise RuntimeError("resource limit did not install exactly")


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


def main():
    if len(sys.argv) != 5:
        raise RuntimeError("invalid launcher arguments")
    executable_fd = int(sys.argv[1])
    address_space_bytes = int(sys.argv[2])
    stack_bytes = int(sys.argv[3])
    timeout_seconds = int(sys.argv[4])
    os.umask(0o077)
    os.chdir("/")
    close_unexpected_fds(executable_fd)
    set_exact_limit(resource.RLIMIT_AS, address_space_bytes)
    set_exact_limit(resource.RLIMIT_STACK, stack_bytes)
    set_exact_limit(resource.RLIMIT_CPU, timeout_seconds + 1)
    set_exact_limit(resource.RLIMIT_CORE, 0)
    set_exact_limit(resource.RLIMIT_FSIZE, 4096)
    set_exact_limit(resource.RLIMIT_NOFILE, 8)
    set_exact_limit(resource.RLIMIT_NPROC, 1)
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "PR_SET_NO_NEW_PRIVS failed")
    if libc.prctl(PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) != 1:
        raise RuntimeError("no_new_privs did not persist")
    path = "/proc/self/fd/" + str(executable_fd)
    os.execve(
        path,
        [path],
        {"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin", "TZ": "UTC"},
    )


try:
    main()
except BaseException:
    try:
        os.write(2, b"zrpf_netns_launcher_rejected\n")
    finally:
        os._exit(126)
"""


def execute_pinned_helper_once(
    *,
    executable: Path,
    expected_sha256: str,
    request: bytes,
) -> bytes:
    if type(request) is not bytes or len(request) != NETNS_HELPER_REQUEST_BYTES_V1:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.REQUEST_INVALID)
    try:
        with SealedExecutable(executable) as sealed:
            if sealed.identity.sha256 != expected_sha256:
                raise LinuxNetnsAdapterRejectedV1(
                    LinuxNetnsAdapterRejectV1.EXECUTABLE_HASH_MISMATCH
                )
            _require_static_host_elf(sealed.pass_fds[0])
            return _run_sealed_helper(sealed, request)
    except LinuxNetnsAdapterRejectedV1:
        raise
    except (OSError, RuntimeError, ValueError) as exc:
        raise LinuxNetnsAdapterRejectedV1(
            LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID
        ) from exc


def _run_sealed_helper(sealed: SealedExecutable, request: bytes) -> bytes:
    process: subprocess.Popen[bytes] | None = None
    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        try:
            process = _start_helper(sealed, stdout_file, stderr_file)
            process.communicate(input=request, timeout=_TIMEOUT_SECONDS_V1)
            return_code = process.returncode
            _terminate_process_group(process)
            process = None
            stdout = _read_bounded(stdout_file, NETNS_HELPER_RESPONSE_BYTES_V1)
            stderr = _read_bounded(stderr_file, _MAX_STDERR_BYTES_V1)
            if return_code != 0 or stderr:
                raise LinuxNetnsAdapterRejectedV1(
                    LinuxNetnsAdapterRejectV1.PROCESS_FAILED
                )
            return stdout
        except subprocess.TimeoutExpired as exc:
            raise LinuxNetnsAdapterRejectedV1(
                LinuxNetnsAdapterRejectV1.PROCESS_TIMEOUT
            ) from exc
        finally:
            if process is not None:
                _terminate_process_group(process)


def _start_helper(
    sealed: SealedExecutable,
    stdout_file: BinaryIO,
    stderr_file: BinaryIO,
) -> subprocess.Popen[bytes]:
    executable_fd = sealed.pass_fds[0]
    return subprocess.Popen(
        [
            "/proc/self/exe",
            "-I",
            "-S",
            "-c",
            _PRE_EXEC_LAUNCHER_SOURCE_V1,
            str(executable_fd),
            str(_MAX_ADDRESS_SPACE_BYTES_V1),
            str(_MAX_STACK_BYTES_V1),
            str(_TIMEOUT_SECONDS_V1),
        ],
        stdin=subprocess.PIPE,
        stdout=stdout_file,
        stderr=stderr_file,
        start_new_session=True,
        close_fds=True,
        pass_fds=(executable_fd,),
        cwd="/",
        env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin", "TZ": "UTC"},
    )


def _terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    # The leader may have exited while a descendant remains in the dedicated
    # process group. Always target the group before accepting any output.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=1)
    except (subprocess.TimeoutExpired, ProcessLookupError):
        pass


def _read_bounded(stream: BinaryIO, maximum: int) -> bytes:
    stream.seek(0)
    raw = stream.read(maximum + 1)
    if len(raw) > maximum:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
    return raw


def _require_static_host_elf(descriptor: int) -> None:
    header = os.pread(descriptor, 64, 0)
    if len(header) != 64 or header[:6] != b"\x7fELF\x02\x01":
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID)
    machine = struct.unpack_from("<H", header, 18)[0]
    host_machine = os.uname().machine.lower()
    if host_machine in {"x86_64", "amd64"}:
        expected_machine = 62
    elif host_machine in {"aarch64", "arm64"}:
        expected_machine = 183
    else:
        raise LinuxNetnsAdapterRejectedV1(
            LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID
        )
    if machine != expected_machine:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID)
    program_offset = struct.unpack_from("<Q", header, 32)[0]
    entry_size = struct.unpack_from("<H", header, 54)[0]
    entry_count = struct.unpack_from("<H", header, 56)[0]
    if (
        entry_size < _ELF_PROGRAM_HEADER_BYTES_V1
        or entry_count == 0
        or entry_count > _ELF_MAX_PROGRAM_HEADERS_V1
    ):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID)
    for index in range(entry_count):
        entry = os.pread(descriptor, entry_size, program_offset + index * entry_size)
        if len(entry) != entry_size:
            raise LinuxNetnsAdapterRejectedV1(
                LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID
            )
        program_type = struct.unpack_from("<I", entry, 0)[0]
        if program_type == 3:
            raise LinuxNetnsAdapterRejectedV1(
                LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID
            )
        if program_type == 2:
            _require_dynamic_segment_without_needed(descriptor, entry)


def _require_dynamic_segment_without_needed(descriptor: int, entry: bytes) -> None:
    offset = struct.unpack_from("<Q", entry, 8)[0]
    size = struct.unpack_from("<Q", entry, 32)[0]
    if (
        size > _ELF_MAX_DYNAMIC_BYTES_V1
        or size % _ELF_DYNAMIC_ENTRY_BYTES_V1 != 0
    ):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID)
    dynamic = os.pread(descriptor, size, offset)
    if len(dynamic) != size:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID)
    for item_offset in range(0, len(dynamic), _ELF_DYNAMIC_ENTRY_BYTES_V1):
        tag = struct.unpack_from("<q", dynamic, item_offset)[0]
        if tag == 1:
            raise LinuxNetnsAdapterRejectedV1(
                LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID
            )
