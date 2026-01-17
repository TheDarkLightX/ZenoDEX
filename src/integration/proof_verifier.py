"""
Proof verification plumbing (imperative shell).

This module provides a minimal interface to make settlement proof-carrying
without hard-coding a specific ZK system into the repo.

Design goals:
- Deterministic, fail-closed verification.
- Pluggable verifier backend (e.g., an existing MPRD ZK verifier).
- No secret/key handling here (verification only).

IMPORTANT:
- This module invokes an external process and uses wall-clock timeouts.
- Do not make consensus-critical accept/reject decisions based on it unless
  every validator runs the same verifier deterministically.
"""

from __future__ import annotations

import json
import os
import select
import signal
import subprocess
import time
from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence, Tuple

from ..state.canonical import bounded_json_utf8_size, canonical_json_bytes


@dataclass(frozen=True)
class ProofVerifierConfig:
    enabled: bool = False
    # External verifier command; receives JSON on stdin; returns JSON on stdout.
    verifier_cmd: Optional[Sequence[str]] = None
    # If False, verifier_cmd[0] must be an absolute path (fail-closed).
    allow_path_lookup: bool = False
    timeout_s: float = 10.0
    max_proof_bytes: int = 256_000  # hard cap for DoS resistance
    max_stdout_bytes: int = 32_000
    max_stderr_bytes: int = 8_000


class ProofVerifier:
    """Interface for verifying a proof payload."""

    def verify(self, payload: Mapping[str, Any]) -> Tuple[bool, Optional[str]]:
        raise NotImplementedError


class DisabledProofVerifier(ProofVerifier):
    def verify(self, payload: Mapping[str, Any]) -> Tuple[bool, Optional[str]]:
        return False, "proof verification disabled"


class MisconfiguredProofVerifier(ProofVerifier):
    def __init__(self, reason: str) -> None:
        self._reason = str(reason)

    def verify(self, payload: Mapping[str, Any]) -> Tuple[bool, Optional[str]]:
        return False, self._reason


class UnsupportedPlatformProofVerifier(ProofVerifier):
    def __init__(self, reason: str) -> None:
        self._reason = str(reason)

    def verify(self, payload: Mapping[str, Any]) -> Tuple[bool, Optional[str]]:
        return False, self._reason


class SubprocessProofVerifier(ProofVerifier):
    """
    Verify a proof by calling an external verifier process.

    Protocol:
    - stdin: canonical JSON bytes of `payload`
    - stdout: JSON object with keys:
        - ok: bool
        - error: optional str
    Any parse/timeout/subprocess error => fail-closed.
    """

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
        if timeout_s <= 0:
            raise ValueError("timeout_s must be positive")
        if max_bytes <= 0:
            raise ValueError("max_bytes must be positive")
        if max_stdout_bytes <= 0:
            raise ValueError("max_stdout_bytes must be positive")
        if max_stderr_bytes <= 0:
            raise ValueError("max_stderr_bytes must be positive")
        self._cmd = list(cmd)
        self._timeout_s = float(timeout_s)
        self._max_bytes = int(max_bytes)
        self._max_stdout = int(max_stdout_bytes)
        self._max_stderr = int(max_stderr_bytes)

    def verify(self, payload: Mapping[str, Any]) -> Tuple[bool, Optional[str]]:
        if not isinstance(payload, Mapping):
            return False, "payload must be an object"

        def _kill_proc_group() -> None:
            # start_new_session=True makes the child its own process group leader.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                return
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    return

        def _wait_after_kill(timeout_s: float = 0.2) -> None:
            try:
                proc.wait(timeout=timeout_s)
            except Exception:
                return

        try:
            bounded_json_utf8_size(payload, max_bytes=self._max_bytes)
            proof_bytes = canonical_json_bytes(payload)
        except ValueError:
            return False, "proof payload too large"
        except Exception as exc:
            return False, f"invalid proof payload encoding: {exc}"

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
        except Exception as exc:
            return False, f"proof verifier error: {exc}"

        assert proc.stdin is not None and proc.stdout is not None and proc.stderr is not None
        try:
            for stream in (proc.stdin, proc.stdout, proc.stderr):
                try:
                    os.set_blocking(stream.fileno(), False)
                except Exception as exc:
                    # Fail-closed: this verifier relies on non-blocking pipes to
                    # enforce the write-side timeout when the child never reads.
                    _kill_proc_group()
                    _wait_after_kill()
                    return False, f"proof verifier requires non-blocking pipes: {exc}"

            stdout_buf = bytearray()
            stderr_buf = bytearray()

            stdin_view = memoryview(proof_bytes)
            stdin_off = 0
            stdin_open = True
            stdout_open = True
            stderr_open = True
            if len(stdin_view) == 0:
                stdin_open = False
                try:
                    proc.stdin.close()
                except Exception:
                    _kill_proc_group()
                    _wait_after_kill()
                    return False, "proof verifier stdin close error"

            deadline = time.monotonic() + self._timeout_s
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    _kill_proc_group()
                    _wait_after_kill()
                    return False, "proof verification timed out"

                rlist = []
                if stdout_open:
                    rlist.append(proc.stdout)
                if stderr_open:
                    rlist.append(proc.stderr)
                wlist = []
                if stdin_open and stdin_off < len(stdin_view):
                    wlist.append(proc.stdin)

                if not rlist and not wlist:
                    break

                try:
                    ready_r, ready_w, _ = select.select(rlist, wlist, [], min(0.1, remaining))
                except Exception:
                    _kill_proc_group()
                    _wait_after_kill()
                    return False, "proof verifier select error"
                if not ready_r and not ready_w:
                    continue

                for stream in ready_w:
                    try:
                        n = stream.write(stdin_view[stdin_off : stdin_off + 4096])
                    except BrokenPipeError:
                        _kill_proc_group()
                        _wait_after_kill()
                        return False, "proof verifier stdin broken pipe"
                    except BlockingIOError:
                        continue
                    except Exception:
                        _kill_proc_group()
                        _wait_after_kill()
                        return False, "proof verifier stdin error"

                    if n is None:
                        n = 0
                    stdin_off += int(n)
                    if stdin_off >= len(stdin_view):
                        stdin_open = False
                        try:
                            proc.stdin.close()
                        except Exception:
                            _kill_proc_group()
                            _wait_after_kill()
                            return False, "proof verifier stdin close error"

                for stream in ready_r:
                    try:
                        chunk = stream.read(4096)
                    except BlockingIOError:
                        continue
                    except Exception:
                        _kill_proc_group()
                        _wait_after_kill()
                        return False, "proof verifier stdout/stderr read error"
                    if not chunk:
                        if stream is proc.stdout:
                            stdout_open = False
                        elif stream is proc.stderr:
                            stderr_open = False
                        continue

                    if isinstance(chunk, str):
                        chunk_b = chunk.encode("utf-8", errors="replace")
                    else:
                        chunk_b = bytes(chunk)

                    if stream is proc.stdout:
                        stdout_buf += chunk_b
                        if len(stdout_buf) > self._max_stdout:
                            _kill_proc_group()
                            _wait_after_kill()
                            return False, "verifier stdout too large"
                    else:
                        stderr_buf += chunk_b
                        if len(stderr_buf) > self._max_stderr:
                            _kill_proc_group()
                            _wait_after_kill()
                            return False, "verifier stderr too large"

                if not stdout_open and not stderr_open and (not stdin_open):
                    break

            rc = proc.poll()
            if stdin_off < len(stdin_view):
                _kill_proc_group()
                _wait_after_kill()
                return False, "proof verifier stdin incomplete write"
            if rc is None:
                try:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        _kill_proc_group()
                        _wait_after_kill()
                        return False, "proof verification timed out"
                    rc = proc.wait(timeout=remaining)
                except subprocess.TimeoutExpired:
                    _kill_proc_group()
                    _wait_after_kill()
                    return False, "proof verification timed out"
                except Exception:
                    _kill_proc_group()
                    _wait_after_kill()
                    return False, "proof verifier did not exit"

            if rc != 0:
                err = stderr_buf.decode("utf-8", errors="replace").strip()
                return False, f"proof verifier failed (exit {rc}): {err or 'no stderr'}"

            try:
                result = json.loads(bytes(stdout_buf))
            except Exception as exc:
                return False, f"invalid verifier output: {exc}"

            if not isinstance(result, dict):
                return False, "invalid verifier output (not an object)"

            ok = result.get("ok")
            if ok is True:
                return True, None
            if ok is False:
                err = result.get("error")
                if isinstance(err, str) and err:
                    return False, err
                return False, "proof rejected"

            return False, "invalid verifier output (missing ok)"
        finally:
            # Ensure the child is not left as a zombie, even if we returned early.
            try:
                if proc.returncode is None:
                    _kill_proc_group()
                proc.wait(timeout=0.2)
            except Exception:
                pass


def make_proof_verifier(config: ProofVerifierConfig) -> ProofVerifier:
    if not config.enabled:
        return DisabledProofVerifier()
    if not config.verifier_cmd:
        return MisconfiguredProofVerifier("proof verifier misconfigured (missing verifier_cmd)")
    if os.name != "posix":
        return UnsupportedPlatformProofVerifier(f"proof verifier unsupported on platform: os.name={os.name!r}")
    cmd0 = config.verifier_cmd[0]
    if not isinstance(cmd0, str) or not cmd0:
        return MisconfiguredProofVerifier("proof verifier misconfigured (verifier_cmd[0] must be a non-empty string)")
    if not config.allow_path_lookup:
        if not os.path.isabs(cmd0):
            return MisconfiguredProofVerifier(
                "proof verifier misconfigured (verifier_cmd must be an absolute path when allow_path_lookup=False)"
            )
        if not (os.path.isfile(cmd0) and os.access(cmd0, os.X_OK)):
            return MisconfiguredProofVerifier(f"proof verifier misconfigured (verifier_cmd not executable): {cmd0}")
    return SubprocessProofVerifier(
        cmd=config.verifier_cmd,
        timeout_s=config.timeout_s,
        max_bytes=config.max_proof_bytes,
        max_stdout_bytes=config.max_stdout_bytes,
        max_stderr_bytes=config.max_stderr_bytes,
    )
