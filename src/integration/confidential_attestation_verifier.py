from __future__ import annotations

import json
import os
import select
import signal
import subprocess
import time
from contextlib import suppress
from dataclasses import dataclass
from typing import IO, Any, Mapping, Optional, Sequence

from ..state.canonical import bounded_json_utf8_size, canonical_json_bytes
from .confidential_attestation import (
    VerifiedConfidentialAttestation,
    make_confidential_extension_receipt_from_verified_attestation,
)


@dataclass(frozen=True)
class ConfidentialAttestationVerifierConfig:
    enabled: bool = False
    verifier_cmd: Optional[Sequence[str]] = None
    allow_path_lookup: bool = False
    timeout_s: float = 10.0
    max_request_bytes: int = 256_000
    max_stdout_bytes: int = 32_000
    max_stderr_bytes: int = 8_000


class ConfidentialAttestationVerifier:
    def verify(self, payload: object) -> tuple[VerifiedConfidentialAttestation | None, Optional[str]]:
        raise NotImplementedError


class DisabledConfidentialAttestationVerifier(ConfidentialAttestationVerifier):
    def verify(self, payload: object) -> tuple[VerifiedConfidentialAttestation | None, Optional[str]]:
        return None, "confidential attestation verification disabled"


class MisconfiguredConfidentialAttestationVerifier(ConfidentialAttestationVerifier):
    def __init__(self, reason: str) -> None:
        self._reason = str(reason)

    def verify(self, payload: object) -> tuple[VerifiedConfidentialAttestation | None, Optional[str]]:
        return None, self._reason


class UnsupportedPlatformConfidentialAttestationVerifier(ConfidentialAttestationVerifier):
    def __init__(self, reason: str) -> None:
        self._reason = str(reason)

    def verify(self, payload: object) -> tuple[VerifiedConfidentialAttestation | None, Optional[str]]:
        return None, self._reason


class SubprocessConfidentialAttestationVerifier(ConfidentialAttestationVerifier):
    def __init__(
        self,
        *,
        cmd: Sequence[str],
        timeout_s: float,
        max_bytes: int,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> None:
        if not cmd:
            raise ValueError("cmd must be non-empty")
        if isinstance(timeout_s, bool) or not isinstance(timeout_s, (int, float)) or timeout_s <= 0:
            raise ValueError("timeout_s must be positive")
        if isinstance(max_bytes, bool) or not isinstance(max_bytes, int) or max_bytes <= 0:
            raise ValueError("max_bytes must be positive")
        if isinstance(max_stdout_bytes, bool) or not isinstance(max_stdout_bytes, int) or max_stdout_bytes <= 0:
            raise ValueError("max_stdout_bytes must be positive")
        if isinstance(max_stderr_bytes, bool) or not isinstance(max_stderr_bytes, int) or max_stderr_bytes <= 0:
            raise ValueError("max_stderr_bytes must be positive")
        self._cmd = list(cmd)
        self._timeout_s = float(timeout_s)
        self._max_bytes = int(max_bytes)
        self._max_stdout = int(max_stdout_bytes)
        self._max_stderr = int(max_stderr_bytes)

    def verify(self, payload: object) -> tuple[VerifiedConfidentialAttestation | None, Optional[str]]:
        if not isinstance(payload, Mapping):
            return None, "payload must be an object"
        request_bytes, err = _payload_bytes(payload, max_bytes=self._max_bytes)
        if err is not None:
            return None, err
        if request_bytes is None:
            return None, "invalid attestation request"

        proc: subprocess.Popen[bytes]
        try:
            proc = subprocess.Popen(
                self._cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
                close_fds=True,
                bufsize=0,
            )
        except (OSError, ValueError) as exc:
            return None, f"confidential attestation verifier error: {exc}"

        if proc.stdin is None or proc.stdout is None or proc.stderr is None:
            # Cleanup is best-effort only; the fail-closed decision is the returned error.
            with suppress(Exception):
                proc.kill()
            return None, "confidential attestation verifier misconfigured (subprocess pipes unavailable)"

        try:
            streams = _pipe_streams(proc)
            if streams is None:
                return None, "confidential attestation verifier misconfigured (subprocess pipes unavailable)"
            stream_err = _configure_nonblocking_streams(streams)
            if stream_err is not None:
                _kill_proc_group(proc)
                _wait_after_kill(proc)
                return None, stream_err
            deadline = time.monotonic() + self._timeout_s
            stdout_buf, stderr_buf, io_err = _exchange_bytes(
                streams=streams,
                stdin_bytes=request_bytes,
                deadline=deadline,
                max_stdout_bytes=self._max_stdout,
                max_stderr_bytes=self._max_stderr,
            )
            if io_err is not None:
                return None, io_err
            rc, wait_err = _wait_for_exit(proc, deadline=deadline)
            if wait_err is not None:
                return None, wait_err
            if rc != 0:
                err_text = stderr_buf.decode("utf-8", errors="replace").strip()
                return None, f"confidential attestation verifier failed (exit {rc}): {err_text or 'no stderr'}"
            return _parse_verified_attestation(stdout_buf)
        finally:
            # Cleanup is best-effort only; verification has already accepted or rejected.
            with suppress(Exception):
                if proc.returncode is None:
                    _kill_proc_group(proc)
                proc.wait(timeout=0.2)


def _payload_bytes(payload: Mapping[str, Any], *, max_bytes: int) -> tuple[bytes | None, Optional[str]]:
    try:
        bounded_json_utf8_size(payload, max_bytes=max_bytes)
        return canonical_json_bytes(payload), None
    except ValueError:
        return None, "attestation request too large"
    except (TypeError, UnicodeEncodeError) as exc:
        return None, f"invalid attestation request encoding: {exc}"


def _pipe_streams(proc: subprocess.Popen[bytes]) -> tuple[IO[bytes], IO[bytes], IO[bytes]] | None:
    stdin = proc.stdin
    stdout = proc.stdout
    stderr = proc.stderr
    if stdin is None or stdout is None or stderr is None:
        return None
    return stdin, stdout, stderr


def _configure_nonblocking_streams(streams: tuple[IO[bytes], IO[bytes], IO[bytes]]) -> Optional[str]:
    for stream in streams:
        try:
            os.set_blocking(stream.fileno(), False)
        except (OSError, ValueError) as exc:
            return f"confidential attestation verifier requires non-blocking pipes: {exc}"
    return None


def _kill_proc_group(proc: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(proc.pid, signal.SIGKILL)
        return
    except ProcessLookupError:
        return
    except (OSError, RuntimeError):
        pass
    with suppress(Exception):
        proc.kill()


def _wait_after_kill(proc: subprocess.Popen[bytes], *, timeout_s: float = 0.2) -> None:
    with suppress(Exception):
        proc.wait(timeout=timeout_s)


def _exchange_bytes(
    *,
    streams: tuple[IO[bytes], IO[bytes], IO[bytes]],
    stdin_bytes: bytes,
    deadline: float,
    max_stdout_bytes: int,
    max_stderr_bytes: int,
) -> tuple[bytes, bytes, Optional[str]]:
    stdin, stdout, stderr = streams
    stdout_buf = bytearray()
    stderr_buf = bytearray()
    stdin_view = memoryview(stdin_bytes)
    stdin_off = 0
    stdin_open = len(stdin_view) > 0
    stdout_open = True
    stderr_open = True
    if not stdin_open:
        try:
            stdin.close()
        except (OSError, ValueError, RuntimeError):
            return b"", b"", "confidential attestation verifier stdin close error"
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return b"", b"", "confidential attestation verification timed out"
        ready_r, ready_w, select_err = _select_ready_streams(
            streams=streams,
            stdin_open=stdin_open and stdin_off < len(stdin_view),
            stdout_open=stdout_open,
            stderr_open=stderr_open,
            timeout_s=min(0.1, remaining),
        )
        if select_err is not None:
            return b"", b"", select_err
        if not ready_r and not ready_w:
            continue
        stdin_off, stdin_open, write_err = _write_ready_stdin(
            stdin=stdin,
            ready_w=ready_w,
            stdin_view=stdin_view,
            stdin_off=stdin_off,
            stdin_open=stdin_open,
        )
        if write_err is not None:
            return b"", b"", write_err
        stdout_open, stderr_open, read_err = _read_ready_streams(
            stdout=stdout,
            stderr=stderr,
            ready_r=ready_r,
            stdout_open=stdout_open,
            stderr_open=stderr_open,
            stdout_buf=stdout_buf,
            stderr_buf=stderr_buf,
            max_stdout_bytes=max_stdout_bytes,
            max_stderr_bytes=max_stderr_bytes,
        )
        if read_err is not None:
            return b"", b"", read_err
        if not stdout_open and not stderr_open and not stdin_open:
            return bytes(stdout_buf), bytes(stderr_buf), None


def _select_ready_streams(
    *,
    streams: tuple[IO[bytes], IO[bytes], IO[bytes]],
    stdin_open: bool,
    stdout_open: bool,
    stderr_open: bool,
    timeout_s: float,
) -> tuple[list[IO[bytes]], list[IO[bytes]], Optional[str]]:
    stdin, stdout, stderr = streams
    rlist: list[IO[bytes]] = []
    if stdout_open:
        rlist.append(stdout)
    if stderr_open:
        rlist.append(stderr)
    wlist: list[IO[bytes]] = []
    if stdin_open:
        wlist.append(stdin)
    try:
        ready_r, ready_w, _ = select.select(rlist, wlist, [], timeout_s)
    except (OSError, ValueError):
        return [], [], "confidential attestation verifier select error"
    return list(ready_r), list(ready_w), None


def _write_ready_stdin(
    *,
    stdin: IO[bytes],
    ready_w: list[IO[bytes]],
    stdin_view: memoryview,
    stdin_off: int,
    stdin_open: bool,
) -> tuple[int, bool, Optional[str]]:
    if stdin not in ready_w:
        return stdin_off, stdin_open, None
    try:
        n_written = stdin.write(stdin_view[stdin_off : stdin_off + 4096])
    except BrokenPipeError:
        return stdin_off, stdin_open, "confidential attestation verifier stdin broken pipe"
    except BlockingIOError:
        return stdin_off, stdin_open, None
    except (OSError, ValueError, RuntimeError):
        return stdin_off, stdin_open, "confidential attestation verifier stdin error"
    if isinstance(n_written, int) and not isinstance(n_written, bool):
        n = n_written
    else:
        return stdin_off, stdin_open, "confidential attestation verifier stdin invalid write result"
    if n <= 0:
        return stdin_off, stdin_open, "confidential attestation verifier stdin made no progress"
    next_off = stdin_off + int(n)
    if next_off < len(stdin_view):
        return next_off, True, None
    try:
        stdin.close()
    except (OSError, ValueError, RuntimeError):
        return next_off, False, "confidential attestation verifier stdin close error"
    return next_off, False, None


def _read_ready_streams(
    *,
    stdout: IO[bytes],
    stderr: IO[bytes],
    ready_r: list[IO[bytes]],
    stdout_open: bool,
    stderr_open: bool,
    stdout_buf: bytearray,
    stderr_buf: bytearray,
    max_stdout_bytes: int,
    max_stderr_bytes: int,
) -> tuple[bool, bool, Optional[str]]:
    for stream in ready_r:
        try:
            chunk_obj = stream.read(4096)
        except BlockingIOError:
            continue
        except (OSError, ValueError, RuntimeError):
            return stdout_open, stderr_open, "confidential attestation verifier stdout/stderr read error"
        if not chunk_obj:
            if stream is stdout:
                stdout_open = False
            if stream is stderr:
                stderr_open = False
            continue
        chunk = bytes(chunk_obj)
        if stream is stdout:
            stdout_buf += chunk
            if len(stdout_buf) > max_stdout_bytes:
                return stdout_open, stderr_open, "verifier stdout too large"
            continue
        stderr_buf += chunk
        if len(stderr_buf) > max_stderr_bytes:
            return stdout_open, stderr_open, "verifier stderr too large"
    return stdout_open, stderr_open, None


def _wait_for_exit(proc: subprocess.Popen[bytes], *, deadline: float) -> tuple[int, Optional[str]]:
    rc = proc.poll()
    if rc is not None:
        return rc, None
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        _kill_proc_group(proc)
        _wait_after_kill(proc)
        return -1, "confidential attestation verification timed out"
    try:
        return proc.wait(timeout=remaining), None
    except subprocess.TimeoutExpired:
        _kill_proc_group(proc)
        _wait_after_kill(proc)
        return -1, "confidential attestation verification timed out"
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
        _kill_proc_group(proc)
        _wait_after_kill(proc)
        return -1, "confidential attestation verifier did not exit"


def _parse_verified_attestation(stdout_bytes: bytes) -> tuple[VerifiedConfidentialAttestation | None, Optional[str]]:
    try:
        result = json.loads(stdout_bytes)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        return None, f"invalid verifier output: {exc}"
    if not isinstance(result, dict):
        return None, "invalid verifier output (not an object)"
    ok = result.get("ok")
    if ok is False:
        error_value = result.get("error")
        if isinstance(error_value, str) and error_value:
            return None, error_value
        return None, "attestation rejected"
    if ok is not True:
        return None, "invalid verifier output (missing ok)"
    verified_obj = result.get("result")
    if not isinstance(verified_obj, Mapping):
        return None, "invalid verifier output (missing result)"
    measurement = verified_obj.get("measurement")
    policy_digest = verified_obj.get("policy_digest")
    attestation_epoch = verified_obj.get("attestation_epoch")
    if not isinstance(measurement, str):
        return None, "invalid verifier output: measurement must be a string"
    if not isinstance(policy_digest, str):
        return None, "invalid verifier output: policy_digest must be a string"
    if not isinstance(attestation_epoch, int) or isinstance(attestation_epoch, bool):
        return None, "invalid verifier output: attestation_epoch must be an int"
    try:
        verified = VerifiedConfidentialAttestation(
            measurement=measurement,
            policy_digest=policy_digest,
            attestation_epoch=attestation_epoch,
        )
    except (TypeError, ValueError) as exc:
        return None, f"invalid verifier output: {exc}"
    return verified, None


def verify_and_make_confidential_extension_receipt(
    *,
    verifier: ConfidentialAttestationVerifier,
    attestation_payload: object,
    extension_id: str,
    provider_id: str,
    request_id: str,
    policy_version: str,
    do_execute: int,
    policy_ok: int,
    nonce_unused: int,
    output_bound_ok: int,
    current_epoch: int,
    max_attestation_age: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> tuple[dict[str, Any] | None, Optional[str]]:
    if not isinstance(verifier, ConfidentialAttestationVerifier):
        raise TypeError("verifier must be a ConfidentialAttestationVerifier")
    verified_attestation, err = verifier.verify(attestation_payload)
    if err is not None:
        return None, err
    if verified_attestation is None:
        return None, "attestation rejected"
    receipt = make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=verified_attestation,
        extension_id=extension_id,
        provider_id=provider_id,
        request_id=request_id,
        policy_version=policy_version,
        do_execute=do_execute,
        policy_ok=policy_ok,
        nonce_unused=nonce_unused,
        output_bound_ok=output_bound_ok,
        current_epoch=current_epoch,
        max_attestation_age=max_attestation_age,
        fee_charged=fee_charged,
        receipt_fee=receipt_fee,
        credit_before=credit_before,
        credit_after=credit_after,
        provider_balance_before=provider_balance_before,
        provider_balance_after=provider_balance_after,
    )
    return receipt, None


def make_confidential_attestation_verifier(
    config: ConfidentialAttestationVerifierConfig,
) -> ConfidentialAttestationVerifier:
    if not config.enabled:
        return DisabledConfidentialAttestationVerifier()
    if not config.verifier_cmd:
        return MisconfiguredConfidentialAttestationVerifier(
            "confidential attestation verifier misconfigured (missing verifier_cmd)"
        )
    if os.name != "posix":
        return UnsupportedPlatformConfidentialAttestationVerifier(
            f"confidential attestation verifier unsupported on platform: os.name={os.name!r}"
        )
    cmd0 = config.verifier_cmd[0]
    if not isinstance(cmd0, str) or not cmd0:
        return MisconfiguredConfidentialAttestationVerifier(
            "confidential attestation verifier misconfigured (verifier_cmd[0] must be a non-empty string)"
        )
    if not config.allow_path_lookup:
        if not os.path.isabs(cmd0):
            return MisconfiguredConfidentialAttestationVerifier(
                "confidential attestation verifier misconfigured (verifier_cmd must be an absolute path when allow_path_lookup=False)"
            )
        if not (os.path.isfile(cmd0) and os.access(cmd0, os.X_OK)):
            return MisconfiguredConfidentialAttestationVerifier(
                f"confidential attestation verifier misconfigured (verifier_cmd not executable): {cmd0}"
            )
    return SubprocessConfidentialAttestationVerifier(
        cmd=config.verifier_cmd,
        timeout_s=config.timeout_s,
        max_bytes=config.max_request_bytes,
        max_stdout_bytes=config.max_stdout_bytes,
        max_stderr_bytes=config.max_stderr_bytes,
    )
