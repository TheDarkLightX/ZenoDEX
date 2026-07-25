# [TESTER] v1

from __future__ import annotations

import json
import sys
from collections.abc import Sequence

import pytest

import src.integration.proof_verifier as proof_verifier
from src.integration.proof_verifier import (
    DisabledProofVerifier,
    MisconfiguredProofVerifier,
    ProofVerifier,
    ProofVerifierConfig,
    SubprocessProofVerifier,
    UnsupportedPlatformProofVerifier,
    make_proof_verifier,
)


class _FakeStream:
    def __init__(
        self,
        name: str,
        *,
        reads: Sequence[object] = (),
        writes: Sequence[object] = (),
        close_exc: Exception | None = None,
    ) -> None:
        self.name = name
        self._reads = list(reads)
        self._writes = list(writes)
        self._close_exc = close_exc

    def fileno(self) -> int:
        return {"stdin": 10, "stdout": 11, "stderr": 12}[self.name]

    def write(self, _data: object) -> object:
        if not self._writes:
            raise AssertionError(f"unexpected write to {self.name}")
        item = self._writes.pop(0)
        if isinstance(item, BaseException):
            raise item
        return item

    def read(self, _size: int) -> object:
        if self._reads:
            item = self._reads.pop(0)
            if isinstance(item, BaseException):
                raise item
            return item
        return b""

    def close(self) -> None:
        if self._close_exc is not None:
            raise self._close_exc


class _FakeProc:
    def __init__(
        self,
        *,
        stdin: _FakeStream | None = None,
        stdout: _FakeStream | None = None,
        stderr: _FakeStream | None = None,
        poll_results: Sequence[object] = (),
        wait_results: Sequence[object] = (),
    ) -> None:
        self.pid = 4321
        self.stdin = stdin or _FakeStream("stdin")
        self.stdout = stdout or _FakeStream("stdout")
        self.stderr = stderr or _FakeStream("stderr")
        self.returncode: int | None = None
        self._poll_results = list(poll_results)
        self._wait_results = list(wait_results)

    def poll(self) -> object:
        if self._poll_results:
            item = self._poll_results.pop(0)
            if item is not None:
                self.returncode = int(item)
            return item
        return self.returncode

    def wait(self, timeout: float | None = None) -> int:
        del timeout
        if self._wait_results:
            item = self._wait_results.pop(0)
            if isinstance(item, BaseException):
                raise item
            self.returncode = int(item)
            return self.returncode
        if self.returncode is None:
            self.returncode = 0
        return self.returncode

    def kill(self) -> None:
        self.returncode = -9


def _patch_fake_process(
    monkeypatch: pytest.MonkeyPatch,
    proc: _FakeProc,
    *,
    proof_bytes: bytes,
    schedule: Sequence[tuple[set[str], set[str]]],
) -> None:
    monkeypatch.setattr(proof_verifier, "canonical_json_bytes", lambda payload: proof_bytes)
    monkeypatch.setattr(proof_verifier, "bounded_json_utf8_size", lambda payload, max_bytes: len(proof_bytes))
    monkeypatch.setattr(proof_verifier.subprocess, "Popen", lambda *args, **kwargs: proc)
    monkeypatch.setattr(proof_verifier.os, "set_blocking", lambda fd, blocking: None)
    monkeypatch.setattr(proof_verifier.os, "killpg", lambda pid, sig: (_ for _ in ()).throw(ProcessLookupError()))

    ready = list(schedule)

    def _fake_select(rlist: list[object], wlist: list[object], _xlist: list[object], _timeout: float) -> tuple[list[object], list[object], list[object]]:
        if not ready:
            raise AssertionError("unexpected select call")
        ready_r_names, ready_w_names = ready.pop(0)
        return (
            [stream for stream in rlist if getattr(stream, "name", None) in ready_r_names],
            [stream for stream in wlist if getattr(stream, "name", None) in ready_w_names],
            [],
        )

    monkeypatch.setattr(proof_verifier.select, "select", _fake_select)


def test_basic_verifier_variants_return_expected_reasons() -> None:
    assert DisabledProofVerifier().verify({}) == (False, "proof verification disabled")
    assert MisconfiguredProofVerifier("bad config").verify({}) == (False, "bad config")
    assert UnsupportedPlatformProofVerifier("no posix").verify({}) == (False, "no posix")


def test_proof_verifier_base_class_requires_override() -> None:
    with pytest.raises(NotImplementedError):
        ProofVerifier().verify({})


@pytest.mark.parametrize(
    ("kwargs", "reason"),
    [
        ({"cmd": [], "timeout_s": 1.0, "max_bytes": 1, "max_stdout_bytes": 1, "max_stderr_bytes": 1}, "cmd must be non-empty"),
        ({"cmd": [sys.executable], "timeout_s": 0.0, "max_bytes": 1, "max_stdout_bytes": 1, "max_stderr_bytes": 1}, "timeout_s must be positive"),
        ({"cmd": [sys.executable], "timeout_s": 1.0, "max_bytes": 0, "max_stdout_bytes": 1, "max_stderr_bytes": 1}, "max_bytes must be positive"),
        ({"cmd": [sys.executable], "timeout_s": 1.0, "max_bytes": 1, "max_stdout_bytes": 0, "max_stderr_bytes": 1}, "max_stdout_bytes must be positive"),
        ({"cmd": [sys.executable], "timeout_s": 1.0, "max_bytes": 1, "max_stdout_bytes": 1, "max_stderr_bytes": 0}, "max_stderr_bytes must be positive"),
    ],
)
def test_subprocess_verifier_init_rejects_invalid_limits(kwargs: dict[str, object], reason: str) -> None:
    with pytest.raises(ValueError, match=reason):
        SubprocessProofVerifier(**kwargs)  # type: ignore[arg-type]


def test_subprocess_verifier_rejects_non_mapping_and_oversized_payload() -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=32,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert verifier.verify(["not", "a", "mapping"]) == (False, "payload must be an object")  # type: ignore[arg-type]
    ok, err = verifier.verify({"x": "A" * 100})
    assert ok is False
    assert err == "proof payload too large"


def test_subprocess_verifier_rejects_invalid_payload_encoding(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=32,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    monkeypatch.setattr(proof_verifier, "canonical_json_bytes", lambda payload: (_ for _ in ()).throw(TypeError("bad canonical form")))
    ok, err = verifier.verify({"x": 1})
    assert ok is False
    assert err == "invalid proof payload encoding: bad canonical form"


def test_subprocess_verifier_rejects_spawn_error(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    def _boom(*_args: object, **_kwargs: object) -> object:
        raise OSError("spawn failed")

    monkeypatch.setattr(proof_verifier.subprocess, "Popen", _boom)
    ok, err = verifier.verify({"ok": True})
    assert ok is False
    assert err == "proof verifier error: spawn failed"


def test_subprocess_verifier_rejects_missing_subprocess_pipes(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    proc = _FakeProc()
    proc.stdin = None
    monkeypatch.setattr(proof_verifier, "canonical_json_bytes", lambda payload: b"{}")
    monkeypatch.setattr(proof_verifier, "bounded_json_utf8_size", lambda payload, max_bytes: 2)
    monkeypatch.setattr(proof_verifier.subprocess, "Popen", lambda *args, **kwargs: proc)

    ok, err = verifier.verify({"ok": True})
    assert ok is False
    assert err == "proof verifier misconfigured (subprocess pipes unavailable)"


def test_subprocess_verifier_rejects_non_blocking_pipe_requirement(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    def _bad_set_blocking(*_args: object, **_kwargs: object) -> None:
        raise OSError("no non-blocking")

    monkeypatch.setattr(proof_verifier.os, "set_blocking", _bad_set_blocking)
    ok, err = verifier.verify({"ok": True})
    assert ok is False
    assert err is not None
    assert "requires non-blocking pipes" in err


def test_subprocess_verifier_rejects_select_error(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    def _bad_select(*_args: object, **_kwargs: object) -> object:
        raise OSError("select failed")

    monkeypatch.setattr(proof_verifier.select, "select", _bad_select)
    ok, err = verifier.verify({"ok": True})
    assert ok is False
    assert err == "proof verifier select error"


def test_subprocess_verifier_rejects_nonzero_exit_and_bad_output_shapes() -> None:
    nonzero = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.stderr.write('boom'); sys.exit(7)"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    ok, err = nonzero.verify({"ok": True})
    assert ok is False
    assert err == "proof verifier failed (exit 7): boom"

    invalid_json = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('not json')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    ok, err = invalid_json.verify({"ok": True})
    assert ok is False
    assert err is not None
    assert "invalid verifier output" in err

    list_output = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('[1, 2, 3]')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert list_output.verify({"ok": True}) == (False, "invalid verifier output (not an object)")

    missing_ok = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"result\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert missing_ok.verify({"ok": True}) == (False, "invalid verifier output (missing ok)")


def test_subprocess_verifier_drains_early_exit_before_classifying_output() -> None:
    large_payload = {"proof": "x" * 200_000}

    invalid_output = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('not json')"],
        timeout_s=1.0,
        max_bytes=400_000,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    ok, err = invalid_output.verify(large_payload)
    assert ok is False
    assert err is not None
    assert "invalid verifier output" in err

    unread_valid_output = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=400_000,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert unread_valid_output.verify(large_payload) == (
        False,
        "proof verifier stdin broken pipe",
    )


def test_subprocess_verifier_rejects_large_stdout_and_stderr() -> None:
    large_stdout = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.stdout.write('x' * 128)"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=16,
        max_stderr_bytes=256,
    )
    assert large_stdout.verify({"ok": True}) == (False, "verifier stdout too large")

    large_stderr = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.stderr.write('x' * 128)"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=16,
    )
    assert large_stderr.verify({"ok": True}) == (False, "verifier stderr too large")


def test_subprocess_verifier_propagates_reject_reason_or_default() -> None:
    explicit_reason = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": false, \"error\": \"bad proof\"}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert explicit_reason.verify({"ok": True}) == (False, "bad proof")

    implicit_reason = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": false}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert implicit_reason.verify({"ok": True}) == (False, "proof rejected")


def test_subprocess_verifier_handles_empty_payload_and_string_stdout(monkeypatch: pytest.MonkeyPatch) -> None:
    proc = _FakeProc(
        stdout=_FakeStream("stdout", reads=['{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        proc,
        proof_bytes=b"",
        schedule=[
            ({"stdout", "stderr"}, set()),
            ({"stdout"}, set()),
        ],
    )

    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert verifier.verify({"ok": True}) == (True, None)


def test_subprocess_verifier_handles_none_write_before_success(monkeypatch: pytest.MonkeyPatch) -> None:
    proof_bytes = json.dumps({"ok": True}, separators=(",", ":")).encode("utf-8")
    proc = _FakeProc(
        stdin=_FakeStream("stdin", writes=[None, len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[b'{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        proc,
        proof_bytes=proof_bytes,
        schedule=[
            (set(), {"stdin"}),
            ({"stdout", "stderr"}, {"stdin"}),
            ({"stdout"}, set()),
        ],
    )

    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert verifier.verify({"ok": True}) == (True, None)


def test_subprocess_verifier_rejects_empty_payload_close_error(monkeypatch: pytest.MonkeyPatch) -> None:
    proc = _FakeProc(
        stdin=_FakeStream("stdin", close_exc=RuntimeError("close failed")),
        stdout=_FakeStream("stdout"),
        stderr=_FakeStream("stderr"),
    )
    _patch_fake_process(
        monkeypatch,
        proc,
        proof_bytes=b"",
        schedule=[],
    )

    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin close error")


def test_subprocess_verifier_rejects_stdin_write_error_variants(monkeypatch: pytest.MonkeyPatch) -> None:
    proof_bytes = b'{"ok":true}'
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    broken_pipe = _FakeProc(
        stdin=_FakeStream("stdin", writes=[BrokenPipeError()]),
        stdout=_FakeStream("stdout", reads=[b'{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[0],
    )
    kill_calls: list[tuple[int, int]] = []
    _patch_fake_process(
        monkeypatch,
        broken_pipe,
        proof_bytes=proof_bytes,
        schedule=[(set(), {"stdin"}), ({"stdout", "stderr"}, set()), ({"stdout"}, set())],
    )
    monkeypatch.setattr(proof_verifier.os, "killpg", lambda pid, sig: kill_calls.append((pid, sig)))
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin broken pipe")
    assert not kill_calls

    blocking = _FakeProc(
        stdin=_FakeStream("stdin", writes=[BlockingIOError(), len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[b'{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        blocking,
        proof_bytes=proof_bytes,
        schedule=[(set(), {"stdin"}), ({"stdout", "stderr"}, {"stdin"}), ({"stdout"}, set())],
    )
    assert verifier.verify({"ok": True}) == (True, None)

    generic_error = _FakeProc(stdin=_FakeStream("stdin", writes=[RuntimeError("boom")], close_exc=None))
    _patch_fake_process(monkeypatch, generic_error, proof_bytes=proof_bytes, schedule=[(set(), {"stdin"})])
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin error")

    invalid_write = _FakeProc(stdin=_FakeStream("stdin", writes=["bad-result"]))
    _patch_fake_process(monkeypatch, invalid_write, proof_bytes=proof_bytes, schedule=[(set(), {"stdin"})])
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin invalid write result")


def test_subprocess_verifier_rejects_stdin_close_and_read_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    proof_bytes = b'{"ok":true}'
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    close_error = _FakeProc(stdin=_FakeStream("stdin", writes=[len(proof_bytes)], close_exc=RuntimeError("close failed")))
    _patch_fake_process(monkeypatch, close_error, proof_bytes=proof_bytes, schedule=[(set(), {"stdin"})])
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin close error")

    read_blocking = _FakeProc(
        stdin=_FakeStream("stdin", writes=[len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[BlockingIOError(), b'{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        read_blocking,
        proof_bytes=proof_bytes,
        schedule=[(set(), {"stdin"}), ({"stdout", "stderr"}, set()), ({"stdout"}, set()), ({"stdout"}, set())],
    )
    assert verifier.verify({"ok": True}) == (True, None)

    read_error = _FakeProc(
        stdin=_FakeStream("stdin", writes=[len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[RuntimeError("read failed")]),
        stderr=_FakeStream("stderr"),
    )
    _patch_fake_process(monkeypatch, read_error, proof_bytes=proof_bytes, schedule=[(set(), {"stdin"}), ({"stdout"}, set())])
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdout/stderr read error")

    invalid_chunk = _FakeProc(
        stdin=_FakeStream("stdin", writes=[len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[object()]),
        stderr=_FakeStream("stderr"),
    )
    _patch_fake_process(monkeypatch, invalid_chunk, proof_bytes=proof_bytes, schedule=[(set(), {"stdin"}), ({"stdout"}, set())])
    assert verifier.verify({"ok": True}) == (False, "proof verifier returned invalid stream chunk")


def test_subprocess_verifier_covers_stderr_eof_path(monkeypatch: pytest.MonkeyPatch) -> None:
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    stderr_only = _FakeProc(
        stdout=_FakeStream("stdout", reads=[b""]),
        stderr=_FakeStream("stderr", reads=[b"noise", b""]),
        poll_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        stderr_only,
        proof_bytes=b"",
        schedule=[({"stdout", "stderr"}, set()), ({"stderr"}, set())],
    )
    ok, err = verifier.verify({"ok": True})
    assert ok is False
    assert err is not None
    assert "invalid verifier output" in err


def test_subprocess_verifier_rejects_wait_timeout_and_exit_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    proof_bytes = b'{"ok":true}'

    timeout_proc = _FakeProc(
        stdin=_FakeStream("stdin", writes=[len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[None],
        wait_results=[proof_verifier.subprocess.TimeoutExpired(cmd=["fake"], timeout=0.1), 0],
    )
    _patch_fake_process(
        monkeypatch,
        timeout_proc,
        proof_bytes=proof_bytes,
        schedule=[
            (set(), {"stdin"}),
            ({"stdout", "stderr"}, set()),
        ],
    )

    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert verifier.verify({"ok": True}) == (False, "proof verification timed out")

    exit_proc = _FakeProc(
        stdin=_FakeStream("stdin", writes=[len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[None],
        wait_results=[RuntimeError("did not exit"), 0],
    )
    _patch_fake_process(
        monkeypatch,
        exit_proc,
        proof_bytes=proof_bytes,
        schedule=[
            (set(), {"stdin"}),
            ({"stdout", "stderr"}, set()),
        ],
    )

    assert verifier.verify({"ok": True}) == (False, "proof verifier did not exit")


def test_subprocess_verifier_rejects_wait_deadline_expiry_and_cleanup_wait_error(monkeypatch: pytest.MonkeyPatch) -> None:
    proof_bytes = b'{"ok":true}'
    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )

    deadline_proc = _FakeProc(
        stdin=_FakeStream("stdin", writes=[len(proof_bytes)]),
        stdout=_FakeStream("stdout", reads=[b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[None],
        wait_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        deadline_proc,
        proof_bytes=proof_bytes,
        schedule=[(set(), {"stdin"}), ({"stdout", "stderr"}, set())],
    )
    monotonic_values = iter([0.0, 0.5, 1.5])
    monkeypatch.setattr(proof_verifier.time, "monotonic", lambda: next(monotonic_values))
    assert verifier.verify({"ok": True}) == (False, "proof verification timed out")

    cleanup_proc = _FakeProc(
        stdin=_FakeStream("stdin", writes=[BrokenPipeError()]),
        stdout=_FakeStream("stdout", reads=[b'{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[0],
        wait_results=[RuntimeError("wait failed")],
    )
    _patch_fake_process(
        monkeypatch,
        cleanup_proc,
        proof_bytes=proof_bytes,
        schedule=[(set(), {"stdin"}), ({"stdout", "stderr"}, set()), ({"stdout"}, set())],
    )
    monkeypatch.setattr(proof_verifier.time, "monotonic", lambda: 0.0)
    monkeypatch.setattr(proof_verifier.os, "killpg", lambda pid, sig: (_ for _ in ()).throw(RuntimeError("kill failed")))
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin broken pipe")


def test_subprocess_verifier_covers_kill_fallback_wait_deadline_and_finally_cleanup(monkeypatch: pytest.MonkeyPatch) -> None:
    proof_bytes = b'{"ok":true}'

    class _KillRaisesProc(_FakeProc):
        def kill(self) -> None:
            raise RuntimeError("kill failed")

    broken_proc = _KillRaisesProc(stdin=_FakeStream("stdin", writes=[RuntimeError("boom")]))
    _patch_fake_process(monkeypatch, broken_proc, proof_bytes=proof_bytes, schedule=[(set(), {"stdin"})])
    monkeypatch.setattr(proof_verifier.os, "killpg", lambda pid, sig: (_ for _ in ()).throw(RuntimeError("killpg failed")))

    verifier = SubprocessProofVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=1024,
        max_stdout_bytes=256,
        max_stderr_bytes=256,
    )
    assert verifier.verify({"ok": True}) == (False, "proof verifier stdin error")

    wait_deadline_proc = _FakeProc(
        stdout=_FakeStream("stdout", reads=[b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
        poll_results=[None],
        wait_results=[0],
    )
    _patch_fake_process(
        monkeypatch,
        wait_deadline_proc,
        proof_bytes=b"",
        schedule=[({"stdout", "stderr"}, set())],
    )
    monotonic_values = iter([0.0, 0.1, 1.5])
    monkeypatch.setattr(proof_verifier.time, "monotonic", lambda: next(monotonic_values))
    assert verifier.verify({"ok": True}) == (False, "proof verification timed out")

    class _PollZeroCleanupWaitProc(_FakeProc):
        def poll(self) -> object:
            return 0

        def wait(self, timeout: float | None = None) -> int:
            del timeout
            raise RuntimeError("cleanup wait failed")

    cleanup_proc = _PollZeroCleanupWaitProc(
        stdout=_FakeStream("stdout", reads=[b'{"ok": true}', b""]),
        stderr=_FakeStream("stderr", reads=[b""]),
    )
    _patch_fake_process(
        monkeypatch,
        cleanup_proc,
        proof_bytes=b"",
        schedule=[({"stdout", "stderr"}, set()), ({"stdout"}, set())],
    )
    monkeypatch.setattr(proof_verifier.time, "monotonic", lambda: 0.0)
    assert verifier.verify({"ok": True}) == (True, None)


def test_make_proof_verifier_covers_platform_and_cmd_validation(monkeypatch: pytest.MonkeyPatch, tmp_path) -> None:
    disabled = make_proof_verifier(ProofVerifierConfig(enabled=False))
    assert isinstance(disabled, DisabledProofVerifier)

    monkeypatch.setattr(proof_verifier.os, "name", "nt")
    unsupported = make_proof_verifier(ProofVerifierConfig(enabled=True, verifier_cmd=["C:\\verifier.exe"]))
    assert isinstance(unsupported, UnsupportedPlatformProofVerifier)

    monkeypatch.setattr(proof_verifier.os, "name", "posix")
    blank_cmd = make_proof_verifier(ProofVerifierConfig(enabled=True, verifier_cmd=[""]))
    assert isinstance(blank_cmd, MisconfiguredProofVerifier)

    missing_path = make_proof_verifier(
        ProofVerifierConfig(enabled=True, verifier_cmd=[str(tmp_path / "missing-verifier")], allow_path_lookup=False)
    )
    assert isinstance(missing_path, MisconfiguredProofVerifier)

    allow_lookup = make_proof_verifier(
        ProofVerifierConfig(enabled=True, verifier_cmd=["python3", "-m", "fake_verifier"], allow_path_lookup=True)
    )
    assert isinstance(allow_lookup, SubprocessProofVerifier)
