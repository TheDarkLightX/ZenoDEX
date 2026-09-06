"""Measured BLS transport controls; real crypto requires the explicit built ELF."""

from __future__ import annotations

import fcntl
import hashlib
import os
from pathlib import Path

import pytest

from src.core import bls_command_verifier_protocol_v1 as protocol
from src.core.economic_command_signature_verifier_deployment_v1 import (
    command_signature_verifier_backend_protocol_root_v1,
)
from src.integration import sealed_bls_command_verifier_v1 as bridge
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
)

ARTIFACT = b"\x7fELFmeasurement-fixture-is-not-a-verifier"


def _backend() -> bridge.SealedBlsCommandVerifierV1:
    return bridge.SealedBlsCommandVerifierV1(
        ARTIFACT, hashlib.sha256(ARTIFACT).hexdigest(), 5000,
    )


def _request_fields() -> dict:
    return dict(signature_algorithm=protocol.BLS_COMMAND_ALGORITHM_V1,
                signer_public_key="0x" + "01" * 48,
                signature_bytes=b"\x02" * 96, message_bytes=b"abc")


def test_request_fixed_vector_and_successor_identity_are_exact() -> None:
    request = protocol.encode_bls_command_request_v1(**_request_fields())
    assert request == b"ZDXBLSV1" + b"\x01" * 48 + b"\x02" * 96 + b"\x03\0\0\0abc"
    assert protocol.bls_command_verifier_protocol_root_v1() != command_signature_verifier_backend_protocol_root_v1()


@pytest.mark.parametrize("size", (1, 1024 * 1024))
def test_message_boundary_frames_roundtrip_exact_response(size: int) -> None:
    request = protocol.encode_bls_command_request_v1(**(_request_fields() | {"message_bytes": b"x" * size}))
    assert request[152:156] == size.to_bytes(4, "little")
    assert len(request) == 156 + size
    assert protocol.decode_bls_command_response_v1(
        request, b"ZDXBOKV1" + hashlib.sha256(request).digest(),
    ) is True


@pytest.mark.parametrize("raw_request", (b"", b"ZDXBLSV1", b"x" * 157))
def test_invalid_request_cannot_be_qualified_by_a_matching_response_digest(raw_request: bytes) -> None:
    with pytest.raises(ValueError, match="framing mismatch"):
        protocol.decode_bls_command_response_v1(
            raw_request, b"ZDXBOKV1" + hashlib.sha256(raw_request).digest(),
        )


@pytest.mark.parametrize("changes", (
    {"signature_algorithm": "BLS_OTHER"}, {"signer_public_key": "0x" + "AA" * 48},
    {"signer_public_key": "0x" + "00" * 47}, {"message_bytes": b""},
    {"message_bytes": b"x" * (1024 * 1024 + 1)}, {"message_bytes": bytearray(b"a")},
    {"signature_bytes": b"x" * 95}, {"signature_bytes": bytearray(b"x" * 96)},
))
def test_invalid_signature_request_rejects_before_process(
    monkeypatch: pytest.MonkeyPatch, changes: dict,
) -> None:
    def forbidden(*_args):
        pytest.fail("invalid request launched verifier")
    monkeypatch.setattr(bridge, "_invoke_v1", forbidden)
    assert _backend().verify_command_signature(**(_request_fields() | changes)) is False


@pytest.mark.parametrize("accept", (False, True))
def test_exact_response_is_bound_to_request_and_executed_snapshot_is_sealed(
    monkeypatch: pytest.MonkeyPatch, accept: bool,
) -> None:
    seen = []
    def exchange(descriptor, request, timeout_ms):
        seen.append(descriptor)
        assert timeout_ms == 5000
        assert os.read(descriptor, len(ARTIFACT) + 1) == ARTIFACT
        seals = fcntl.fcntl(descriptor, fcntl.F_GET_SEALS)
        required = fcntl.F_SEAL_SEAL | fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK
        assert seals & required == required
        with pytest.raises(OSError):
            os.write(descriptor, b"x")
        magic = b"ZDXBOKV1" if accept else b"ZDXBNOV1"
        return magic + hashlib.sha256(request).digest(), b"", 0
    monkeypatch.setattr(bridge, "_invoke_v1", exchange)
    assert _backend().verify_command_signature(**_request_fields()) is accept
    with pytest.raises(OSError):
        os.fstat(seen[0])


@pytest.mark.parametrize("case", ("digest", "magic", "extra", "short", "stderr", "exit"))
def test_invalid_process_response_never_becomes_a_signature_verdict(
    monkeypatch: pytest.MonkeyPatch, case: str,
) -> None:
    def exchange(_descriptor, request, _timeout_ms):
        response = b"ZDXBOKV1" + hashlib.sha256(request).digest()
        if case == "digest":
            response = response[:8] + b"\0" * 32
        elif case == "magic":
            response = b"ZDXRV1OK" + response[8:]
        elif case == "extra":
            response += b"\n"
        elif case == "short":
            response = response[:-1]
        return response, b"error" if case == "stderr" else b"", 1 if case == "exit" else 0
    monkeypatch.setattr(bridge, "_invoke_v1", exchange)
    with pytest.raises(bridge.SealedBlsCommandVerifierErrorV1) as caught:
        _backend().verify_command_signature(**_request_fields())
    expected = "PROCESS_REJECTED" if case in ("stderr", "exit") else "RESPONSE_BINDING"
    assert caught.value.reason.value == expected


@pytest.mark.parametrize("reason", (
    GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE,
    GlobalReceiptVerifierRejectV1.PROCESS_TIMEOUT,
    GlobalReceiptVerifierRejectV1.OUTPUT_LIMIT,
))
def test_shared_transport_failures_remain_typed_and_release_descriptor(
    monkeypatch: pytest.MonkeyPatch, reason: GlobalReceiptVerifierRejectV1,
) -> None:
    descriptors = []
    def fail(descriptor, *_args):
        descriptors.append(descriptor)
        raise GlobalReceiptVerifierErrorV1(reason)
    monkeypatch.setattr(bridge, "_invoke_v1", fail)
    with pytest.raises(bridge.SealedBlsCommandVerifierErrorV1) as caught:
        _backend().verify_command_signature(**_request_fields())
    assert caught.value.reason.value == reason.value
    with pytest.raises(OSError):
        os.fstat(descriptors[0])


def test_acquired_bytes_survive_path_replacement_and_bad_identity_never_loads(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    path = tmp_path / "verifier"
    path.write_bytes(ARTIFACT)
    digest = hashlib.sha256(ARTIFACT).hexdigest()
    backend = bridge.load_sealed_bls_command_verifier_v1(path, expected_sha256=digest, timeout_ms=5000)
    path.write_bytes(b"\x7fELFreplacement")
    def exchange(descriptor, request, _timeout_ms):
        assert os.read(descriptor, len(ARTIFACT) + 1) == ARTIFACT
        return b"ZDXBOKV1" + hashlib.sha256(request).digest(), b"", 0
    monkeypatch.setattr(bridge, "_invoke_v1", exchange)
    assert backend.verify_command_signature(**_request_fields()) is True
    with pytest.raises(bridge.SealedBlsCommandVerifierErrorV1) as caught:
        bridge.load_sealed_bls_command_verifier_v1(path, expected_sha256=digest, timeout_ms=5000)
    assert caught.value.reason.value == "EXECUTABLE_BINDING"
    link = tmp_path / "link"
    link.symlink_to(path)
    with pytest.raises(bridge.SealedBlsCommandVerifierErrorV1) as caught:
        bridge.load_sealed_bls_command_verifier_v1(link, expected_sha256=digest, timeout_ms=5000)
    assert caught.value.reason.value == "EXECUTABLE_UNAVAILABLE"


def test_real_measured_endpoint_matches_independent_g2basic_signatures() -> None:
    configured = os.environ.get("ZENODEX_BLS_VERIFIER_TEST_BINARY")
    if not configured:
        pytest.skip("explicit offline-built BLS verifier required for real execution evidence")
    assert configured is not None
    from py_ecc.bls import G2Basic, G2ProofOfPossession
    path = Path(configured)
    backend = bridge.load_sealed_bls_command_verifier_v1(
        path, expected_sha256=hashlib.sha256(path.read_bytes()).hexdigest(), timeout_ms=5000,
    )
    for scalar, message in ((1, b"a"), (42, bytes(range(256))), (31337, b"x" * 1024)):
        # Public test scalars; these are never wallet keys or funded identities.
        key = G2Basic.SkToPk(scalar)
        signature = G2Basic.Sign(scalar, message)
        rows = (
            (key, message, signature), (key, message + b"changed", signature),
            (G2Basic.SkToPk(scalar + 1), message, signature),
            (key, message, G2ProofOfPossession.Sign(scalar, message)),
            (b"\xc0" + b"\0" * 47, message, signature),
            (key, message, b"\xc0" + b"\0" * 95),
        )
        for public_key, signed_message, sig in rows:
            expected = G2Basic.Verify(public_key, signed_message, sig)
            actual = backend.verify_command_signature(
                signature_algorithm=protocol.BLS_COMMAND_ALGORITHM_V1,
                signer_public_key="0x" + public_key.hex(),
                message_bytes=signed_message, signature_bytes=sig,
            )
            assert actual is expected
