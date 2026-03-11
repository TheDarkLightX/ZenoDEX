# [TESTER] v1

from __future__ import annotations

import sys

import pytest

import src.integration.proof_verifier as proof_verifier
from src.integration.proof_verifier import (
    DisabledProofVerifier,
    MisconfiguredProofVerifier,
    ProofVerifierConfig,
    SubprocessProofVerifier,
    UnsupportedPlatformProofVerifier,
    make_proof_verifier,
)


def test_basic_verifier_variants_return_expected_reasons() -> None:
    assert DisabledProofVerifier().verify({}) == (False, "proof verification disabled")
    assert MisconfiguredProofVerifier("bad config").verify({}) == (False, "bad config")
    assert UnsupportedPlatformProofVerifier("no posix").verify({}) == (False, "no posix")


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


def test_make_proof_verifier_covers_platform_and_cmd_validation(monkeypatch: pytest.MonkeyPatch, tmp_path) -> None:
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

