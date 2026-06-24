from __future__ import annotations

import sys

import pytest

from src.integration import confidential_attestation_verifier
from src.integration.confidential_attestation_verifier import (
    ConfidentialAttestationVerifierConfig,
    MisconfiguredConfidentialAttestationVerifier,
    SubprocessConfidentialAttestationVerifier,
    verify_and_make_confidential_extension_receipt,
    make_confidential_attestation_verifier,
)


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
MEASUREMENT = f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"


def test_make_confidential_attestation_verifier_requires_absolute_cmd_when_path_lookup_disabled() -> None:
    verifier = make_confidential_attestation_verifier(
        ConfidentialAttestationVerifierConfig(
            enabled=True,
            verifier_cmd=["python3", "-c", "print('{\"ok\":true}')"],
            allow_path_lookup=False,
        )
    )
    assert isinstance(verifier, MisconfiguredConfidentialAttestationVerifier)


def test_subprocess_confidential_attestation_verifier_returns_typed_attestation() -> None:
    cmd = [
        sys.executable,
        "-c",
        (
            "import json, sys; "
            "sys.stdin.buffer.read(); "
            f"print(json.dumps({{'ok': True, 'result': {{'measurement': '{MEASUREMENT}', 'policy_digest': '{POLICY_DIGEST}', 'attestation_epoch': 2}}}}))"
        ),
    ]
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=cmd,
        timeout_s=2.0,
        max_bytes=10_000,
        max_stdout_bytes=10_000,
        max_stderr_bytes=1_000,
    )
    verified, err = verifier.verify(
        {
            "provider": "nitro",
            "policy_digest": POLICY_DIGEST,
            "issued_at_s": 120,
            "epoch_length_s": 60,
            "summary": {"pcrs": {"0": NITRO_PCR0, "8": NITRO_PCR8}},
        }
    )
    assert err is None
    assert verified is not None
    assert verified.measurement == MEASUREMENT
    assert verified.policy_digest == POLICY_DIGEST
    assert verified.attestation_epoch == 2


def test_verify_and_make_confidential_extension_receipt_wires_verified_output_into_python_flow() -> None:
    cmd = [
        sys.executable,
        "-c",
        (
            "import json, sys; "
            "sys.stdin.buffer.read(); "
            f"print(json.dumps({{'ok': True, 'result': {{'measurement': '{MEASUREMENT}', 'policy_digest': '{POLICY_DIGEST}', 'attestation_epoch': 8}}}}))"
        ),
    ]
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=cmd,
        timeout_s=2.0,
        max_bytes=10_000,
        max_stdout_bytes=10_000,
        max_stderr_bytes=1_000,
    )
    receipt, err = verify_and_make_confidential_extension_receipt(
        verifier=verifier,
        attestation_payload={
            "provider": "nitro",
            "policy_digest": POLICY_DIGEST,
            "issued_at_s": 480,
            "epoch_length_s": 60,
            "summary": {"pcrs": {"0": NITRO_PCR0, "8": NITRO_PCR8}},
        },
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-verifier",
        policy_version="tee-policy-v1",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    assert err is None
    assert receipt is not None
    assert receipt["body"]["measurement"] == MEASUREMENT
    assert receipt["body"]["policy_digest"] == POLICY_DIGEST
    assert receipt["body"]["attestation"]["attestation_epoch"] == 8


def test_subprocess_confidential_attestation_verifier_rejects_invalid_result_shape() -> None:
    cmd = [
        sys.executable,
        "-c",
        (
            "import json, sys; "
            "sys.stdin.buffer.read(); "
            "print(json.dumps({'ok': True, 'result': {'measurement': 'nitro:pcr0:bad:pcr8:"
            + ("b" * 96)
            + "', 'policy_digest': '0x"
            + ("d" * 64)
            + "', 'attestation_epoch': 2}}))"
        ),
    ]
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=cmd,
        timeout_s=2.0,
        max_bytes=10_000,
        max_stdout_bytes=10_000,
        max_stderr_bytes=1_000,
    )
    verified, err = verifier.verify({"provider": "nitro"})
    assert verified is None
    assert err is not None
    assert "invalid verifier output" in err


def test_subprocess_confidential_attestation_verifier_rejects_non_canonical_payload() -> None:
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
        timeout_s=1.0,
        max_bytes=10_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )
    verified, err = verifier.verify({"bad_float": 1.25})
    assert verified is None
    assert err is not None
    assert "invalid attestation request encoding" in err


def test_confidential_attestation_verifier_caps_boundary_error_details(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    long_detail = "x" * 300

    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
        timeout_s=1.0,
        max_bytes=10_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )

    with monkeypatch.context() as m:
        def _faulting_popen(*_args: object, **_kwargs: object) -> object:
            raise OSError(long_detail)

        m.setattr(confidential_attestation_verifier.subprocess, "Popen", _faulting_popen)
        verified, err = verifier.verify({"provider": "nitro"})
        assert verified is None
        assert err == "confidential attestation verifier error: " + ("x" * 200)

    with monkeypatch.context() as m:
        m.setattr(
            confidential_attestation_verifier,
            "bounded_json_utf8_size",
            lambda value, *, max_bytes: (_ for _ in ()).throw(TypeError(long_detail)),
        )
        payload_bytes, err = confidential_attestation_verifier._payload_bytes(
            {"provider": "nitro"},
            max_bytes=10_000,
        )
        assert payload_bytes is None
        assert err == "invalid attestation request encoding: " + ("x" * 200)

    class _FakeStream:
        def fileno(self) -> int:
            return 1

    with monkeypatch.context() as m:
        m.setattr(
            confidential_attestation_verifier.os,
            "set_blocking",
            lambda fd, blocking: (_ for _ in ()).throw(OSError(long_detail)),
        )
        err = confidential_attestation_verifier._configure_nonblocking_streams(
            (_FakeStream(), _FakeStream(), _FakeStream()),
        )
        assert err == "confidential attestation verifier requires non-blocking pipes: " + ("x" * 200)

    cmd = [
        sys.executable,
        "-c",
        "import sys; sys.stderr.write('x' * 300); sys.exit(7)",
    ]
    stderr_verifier = SubprocessConfidentialAttestationVerifier(
        cmd=cmd,
        timeout_s=2.0,
        max_bytes=10_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )
    verified, err = stderr_verifier.verify({"provider": "nitro"})
    assert verified is None
    assert err == "confidential attestation verifier failed (exit 7): " + ("x" * 200)

    verified, err = confidential_attestation_verifier._parse_verified_attestation(
        ('{"ok": false, "error": "' + long_detail + '"}').encode(),
    )
    assert verified is None
    assert err == "x" * 200


def test_subprocess_confidential_attestation_verifier_surfaces_internal_payload_encoder_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=10_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )

    def _faulting_encoder(_payload: object) -> bytes:
        raise RuntimeError("attestation encoder internal fault")

    monkeypatch.setattr(confidential_attestation_verifier, "canonical_json_bytes", _faulting_encoder)

    with pytest.raises(RuntimeError, match="attestation encoder internal fault"):
        verifier.verify({"provider": "nitro"})


def test_subprocess_confidential_attestation_verifier_surfaces_unexpected_spawn_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=[sys.executable, "-c", "print('{\"ok\": true}')"],
        timeout_s=1.0,
        max_bytes=10_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )

    def _faulting_popen(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("attestation spawn internal fault")

    monkeypatch.setattr(confidential_attestation_verifier.subprocess, "Popen", _faulting_popen)

    with pytest.raises(RuntimeError, match="attestation spawn internal fault"):
        verifier.verify({"provider": "nitro"})


def test_subprocess_confidential_attestation_verifier_limits_stdout() -> None:
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=[sys.executable, "-c", "print('A' * 50000)"],
        timeout_s=2.0,
        max_bytes=10_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )
    verified, err = verifier.verify({"provider": "nitro"})
    assert verified is None
    assert err == "verifier stdout too large"


def test_subprocess_confidential_attestation_verifier_times_out_if_verifier_never_reads_stdin() -> None:
    verifier = SubprocessConfidentialAttestationVerifier(
        cmd=[sys.executable, "-c", "import time; time.sleep(10)"],
        timeout_s=0.2,
        max_bytes=500_000,
        max_stdout_bytes=1_000,
        max_stderr_bytes=1_000,
    )
    verified, err = verifier.verify({"x": "A" * 200_000})
    assert verified is None
    assert err == "confidential attestation verification timed out"
