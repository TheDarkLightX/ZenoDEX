"""Bounded Linux subprocess adapter for a selected RISC0 receipt endpoint.

The configured SHA-256 identifies reviewed ELF bytes. Every call copies those
bytes into a sealed memfd and executes that immutable snapshot. Release selection,
journal semantics, current-head admission, and publication remain separate gates.
The publisher, Linux kernel, installed /usr/bin/bwrap and four selected GNU/Linux
x86-64 runtime libraries remain trusted. The endpoint sees a read-only private
root and its own PID/network/IPC/user namespaces. Ledger/home directories,
host sockets, devices and procfs are not mounted.
The PID namespace contains descendants even when they change sessions. Startup
failure rejects; there is no direct-execution fallback. This does not establish
that an arbitrarily configured binary is honest, or bound aggregate host memory,
CPU or process consumption across concurrent requests.
The publisher must retain exclusive ownership of reaping its verifier child.

Protocol V1: ``ZDXRV1RQ | image[32] | journal_len:u32le | receipt_len:u32le |
journal | encoded_receipt``. The measured endpoint and its receipt-schema
declaration pin the codec; there is no payload auto-detection. The historical
epoch endpoint uses postcard; asset module/coordinator endpoints use their
native JSON encoding. Success is exactly ``ZDXRV1OK | sha256(request) |
image[32]`` with exit status zero and empty stderr. All other outcomes reject.
Receipt and journal bytes retain their existing encodings.
"""

from __future__ import annotations

import fcntl
import hashlib
import os
import selectors
import signal
import stat
import struct
import subprocess
import time
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from typing import Iterator

from ._verifier_process import unreaped_exit_status as _unreaped_exit_status_v1

MAX_RECEIPT_BYTES_V1 = 16 * 1024 * 1024
MAX_JOURNAL_BYTES_V1 = 1024 * 1024
MAX_EXECUTABLE_BYTES_V1 = 128 * 1024 * 1024
MAX_OUTPUT_BYTES_V1 = 4096
_REQUEST_MAGIC_V1 = b"ZDXRV1RQ"
_RESPONSE_MAGIC_V1 = b"ZDXRV1OK"


class GlobalReceiptVerifierRejectV1(str, Enum):
    INPUT_BOUNDS = "INPUT_BOUNDS"
    IMAGE_BINDING = "IMAGE_BINDING"
    EXECUTABLE_UNAVAILABLE = "EXECUTABLE_UNAVAILABLE"
    EXECUTABLE_BINDING = "EXECUTABLE_BINDING"
    PROCESS_UNAVAILABLE = "PROCESS_UNAVAILABLE"
    PROCESS_TIMEOUT = "PROCESS_TIMEOUT"
    OUTPUT_LIMIT = "OUTPUT_LIMIT"
    VERIFICATION_REJECTED = "VERIFICATION_REJECTED"
    RESPONSE_BINDING = "RESPONSE_BINDING"


class GlobalReceiptVerifierErrorV1(RuntimeError):
    """Stable public rejection with no backend output or filesystem disclosure."""

    def __init__(self, reason: GlobalReceiptVerifierRejectV1) -> None:
        self.reason = reason
        super().__init__(f"economic receipt verifier rejected: {reason.value}")


def _exact_hex_v1(value: object, size: int) -> bool:
    return (
        type(value) is str
        and len(value) == size
        and all(character in "0123456789abcdef" for character in value)
    )


@dataclass(frozen=True, slots=True)
class GlobalReceiptVerifierV1:
    """Implement SuccinctReceiptVerifierV1 for one explicitly selected guest image.

    Construction grants no release, state, migration, or writer authority. A real
    receipt and reviewed build evidence must qualify the selected executable.
    """

    executable_path: str
    executable_sha256: str
    expected_image_id: str
    timeout_ms: int

    def __post_init__(self) -> None:
        if (
            type(self.executable_path) is not str
            or not os.path.isabs(self.executable_path)
            or "\x00" in self.executable_path
        ):
            raise ValueError("receipt verifier executable path must be absolute")
        if not _exact_hex_v1(self.executable_sha256, 64):
            raise ValueError("receipt verifier executable SHA-256 must be lowercase hex")
        image = self.expected_image_id
        if type(image) is not str or not image.startswith("0x"):
            raise ValueError("receipt verifier image must be a nonzero canonical root")
        if not _exact_hex_v1(image[2:], 64) or image == "0x" + "00" * 32:
            raise ValueError("receipt verifier image must be a nonzero canonical root")
        if type(self.timeout_ms) is not int or not 1 <= self.timeout_ms <= 60_000:
            raise ValueError("receipt verifier timeout must be between 1 and 60000 ms")

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        if type(expected_image_id) is not str or expected_image_id != self.expected_image_id:
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.IMAGE_BINDING)
        request = _encode_request_v1(receipt_bytes, expected_image_id, expected_journal_bytes)
        with _sealed_executable_v1(self) as executable_fd:
            stdout, stderr, returncode = _invoke_v1(executable_fd, request, self.timeout_ms)
        if returncode != 0:
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED)
        expected = (
            _RESPONSE_MAGIC_V1
            + hashlib.sha256(request).digest()
            + bytes.fromhex(expected_image_id[2:])
        )
        if stdout != expected or stderr:
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.RESPONSE_BINDING)


def _encode_request_v1(receipt: bytes, image_id: str, journal: bytes) -> bytes:
    for value, limit in ((receipt, MAX_RECEIPT_BYTES_V1), (journal, MAX_JOURNAL_BYTES_V1)):
        if type(value) is not bytes or not 1 <= len(value) <= limit:
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.INPUT_BOUNDS)
    return (
        _REQUEST_MAGIC_V1
        + bytes.fromhex(image_id[2:])
        + struct.pack("<II", len(journal), len(receipt))
        + journal
        + receipt
    )


def _copy_measured_elf_v1(source_fd: int, target_fd: int, expected_sha256: str) -> None:
    metadata = os.fstat(source_fd)
    if not stat.S_ISREG(metadata.st_mode) or not 1 <= metadata.st_size <= MAX_EXECUTABLE_BYTES_V1:
        raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
    digest = hashlib.sha256()
    total = 0
    while chunk := os.read(source_fd, 65536):
        if total == 0 and not chunk.startswith(b"\x7fELF"):
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
        total += len(chunk)
        if total > MAX_EXECUTABLE_BYTES_V1:
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
        digest.update(chunk)
        pending = memoryview(chunk)
        while pending:
            count = os.write(target_fd, pending)
            if count <= 0:
                raise OSError("executable snapshot write failed")
            pending = pending[count:]
    if total != metadata.st_size or digest.hexdigest() != expected_sha256:
        raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
    os.lseek(target_fd, 0, os.SEEK_SET)


@contextmanager
def _sealed_executable_v1(verifier: GlobalReceiptVerifierV1) -> Iterator[int]:
    source_fd = snapshot_fd = None
    try:
        source_fd = os.open(verifier.executable_path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        snapshot_fd = os.memfd_create("zenodex-receipt-verifier-v1", os.MFD_ALLOW_SEALING)
        _copy_measured_elf_v1(source_fd, snapshot_fd, verifier.executable_sha256)
        os.fchmod(snapshot_fd, 0o500)
        fcntl.fcntl(
            snapshot_fd,
            fcntl.F_ADD_SEALS,
            fcntl.F_SEAL_SEAL | fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK,
        )
    except OSError:
        if snapshot_fd is not None:
            os.close(snapshot_fd)
        raise GlobalReceiptVerifierErrorV1(
            GlobalReceiptVerifierRejectV1.EXECUTABLE_UNAVAILABLE
        ) from None
    except GlobalReceiptVerifierErrorV1:
        if snapshot_fd is not None:
            os.close(snapshot_fd)
        raise
    finally:
        if source_fd is not None:
            os.close(source_fd)
    try:
        yield snapshot_fd
    finally:
        os.close(snapshot_fd)


def _kill_and_reap_v1(process: subprocess.Popen[bytes]) -> None:
    # Never signal a PID after wait/poll reaped it: the kernel may reuse it.
    if process.returncode is None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait()


def _sandbox_command_v1(executable_fd: int) -> tuple[str, ...]:
    # Fixed runtime closure, not caller-controlled directories or PATH lookup.
    # The selected distro image must qualify bwrap and these library bytes.
    libraries = ("libc.so.6", "libgcc_s.so.1", "libm.so.6", "ld-linux-x86-64.so.2")
    bindings = tuple(
        argument
        for library in libraries
        for argument in ("--ro-bind", f"/lib/x86_64-linux-gnu/{library}", f"/runtime/{library}")
    )
    return (
        "/usr/bin/bwrap",
        "--unshare-user", "--unshare-pid", "--unshare-net", "--unshare-ipc", "--unshare-uts",
        "--disable-userns", "--cap-drop", "ALL", "--new-session", "--die-with-parent",
        *bindings,
        # bwrap owns this descriptor, copies the sealed bytes and closes it.
        "--perms", "0500", "--ro-bind-data", str(executable_fd), "/verifier",
        "--remount-ro", "/",
        "--chdir", "/", "--", "/runtime/ld-linux-x86-64.so.2",
        "--inhibit-cache", "--library-path", "/runtime", "/verifier",
    )


def _invoke_v1(executable_fd: int, request: bytes, timeout_ms: int) -> tuple[bytes, bytes, int]:
    try:
        process = subprocess.Popen(
            _sandbox_command_v1(executable_fd),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env={"RISC0_DEV_MODE": "0", "LC_ALL": "C"},
            pass_fds=(executable_fd,),
            start_new_session=True,
            bufsize=0,
            cwd="/",
        )
    except OSError:
        raise GlobalReceiptVerifierErrorV1(
            GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE
        ) from None
    try:
        return _exchange_v1(process, request, timeout_ms)
    except OSError:
        raise GlobalReceiptVerifierErrorV1(
            GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE
        ) from None
    finally:
        _kill_and_reap_v1(process)
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream is not None:
                stream.close()


def _write_request_chunk_v1(
    selector: selectors.BaseSelector,
    descriptor: int,
    pending: memoryview,
) -> memoryview:
    try:
        count = os.write(descriptor, pending[:65536])
    except BrokenPipeError:
        count = len(pending)
    pending = pending[count:]
    if not pending:
        key = selector.get_key(descriptor)
        selector.unregister(descriptor)
        key.fileobj.close()  # type: ignore[union-attr]
    return pending


def _read_output_chunk_v1(
    selector: selectors.BaseSelector,
    descriptor: int,
    output: bytearray,
) -> None:
    chunk = os.read(descriptor, MAX_OUTPUT_BYTES_V1 + 1 - len(output))
    output.extend(chunk)
    if len(output) > MAX_OUTPUT_BYTES_V1:
        raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.OUTPUT_LIMIT)
    if not chunk:
        selector.unregister(descriptor)


def _exchange_v1(
    process: subprocess.Popen[bytes],
    request: bytes,
    timeout_ms: int,
) -> tuple[bytes, bytes, int]:
    deadline_ns = time.monotonic_ns() + timeout_ms * 1_000_000
    output = {"stdout": bytearray(), "stderr": bytearray()}
    pending = memoryview(request)
    with selectors.DefaultSelector() as selector:
        for name, stream in (
            ("stdin", process.stdin),
            ("stdout", process.stdout),
            ("stderr", process.stderr),
        ):
            if stream is None:
                raise GlobalReceiptVerifierErrorV1(
                    GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE
                )
            os.set_blocking(stream.fileno(), False)
            mask = selectors.EVENT_WRITE if name == "stdin" else selectors.EVENT_READ
            selector.register(stream, mask, name)
        while True:
            exit_status = None
            if not selector.get_map():
                exit_status = _unreaped_exit_status_v1(process.pid)
            remaining_ns = deadline_ns - time.monotonic_ns()
            if remaining_ns <= 0:
                raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.PROCESS_TIMEOUT)
            if exit_status is not None:
                return bytes(output["stdout"]), bytes(output["stderr"]), exit_status
            for key, _ in selector.select(min(remaining_ns / 1_000_000_000, 0.05)):
                if key.data == "stdin":
                    pending = _write_request_chunk_v1(selector, key.fd, pending)
                else:
                    _read_output_chunk_v1(selector, key.fd, output[key.data])
