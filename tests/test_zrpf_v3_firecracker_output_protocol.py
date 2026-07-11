from __future__ import annotations

import hashlib

import pytest

from tools import zrpf_v3_firecracker_output_protocol as protocol


def test_request_vector_is_canonical_and_round_trips() -> None:
    request = _request()
    encoded = request.encode()

    assert len(encoded) == protocol.REQUEST_BYTES_V1
    assert protocol.decode_request(encoded) == request
    assert hashlib.sha256(encoded).hexdigest() == (
        "2caa4a31adf44fef35e63a06574a5626eadd02aa2c25a869adce4ef04479d196"
    )


@pytest.mark.parametrize(
    ("offset", "value", "code"),
    [
        (0, 0, "request_magic"),
        (8, 2, "request_version"),
        (12, 1, "request_flags"),
        (48, 0, "request_profile"),
        (188, 1, "request_reserved"),
    ],
)
def test_request_mutations_reject_at_stable_boundaries(offset: int, value: int, code: str) -> None:
    changed = bytearray(_request().encode())
    changed[offset] = value

    with pytest.raises(protocol.FirecrackerProtocolReject) as captured:
        protocol.decode_request(bytes(changed))

    assert captured.value.code == code


def test_committed_output_vector_round_trips_and_binds_request() -> None:
    payload = b'{"ok":true}\n'
    output = protocol.build_committed_output(
        _request(), observed_input_drive_sha256=bytes([3]) * 32, payload=payload
    )

    assert protocol.validate_committed_output(output, _request()) == payload
    assert hashlib.sha256(output).hexdigest() == (
        "d8eebca6acbf13687118569667aff7a61e6c4c55d3a3d4e8799e762690b0e494"
    )


def test_committed_output_rejects_stale_binding_trailing_data_and_marker() -> None:
    payload = b'{"ok":true}'
    output = bytearray(
        protocol.build_committed_output(
            _request(), observed_input_drive_sha256=bytes([3]) * 32, payload=payload
        )
    )

    output[32] ^= 1
    _assert_output_reject(output, "output_binding")
    output[32] ^= 1
    output[protocol.OUTPUT_HEADER_BYTES_V1 + len(payload) + 1] = 1
    _assert_output_reject(output, "output_trailing_bytes")
    output[protocol.OUTPUT_HEADER_BYTES_V1 + len(payload) + 1] = 0
    output[-1] ^= 1
    _assert_output_reject(output, "output_commit")


def test_committed_output_rejects_declared_payload_above_cap() -> None:
    output = bytearray(
        protocol.build_committed_output(
            _request(),
            observed_input_drive_sha256=bytes([3]) * 32,
            payload=b'{"ok":true}',
        )
    )
    output[16:20] = (protocol.OUTPUT_PAYLOAD_CAP_BYTES_V1 + 1).to_bytes(
        4,
        "little",
    )

    _assert_output_reject(output, "output_payload")


def test_request_constructor_rejects_zero_or_wrong_width_bindings() -> None:
    with pytest.raises(TypeError):
        protocol.FirecrackerRequestV1()

    with pytest.raises(protocol.FirecrackerProtocolReject) as captured:
        protocol.FirecrackerRequestV1.validated(
            run_nonce_256=bytes(32),
            runtime_manifest_sha256=bytes([2]) * 32,
            input_drive_sha256=bytes([3]) * 32,
            replay_intent_sha256=bytes([4]) * 32,
        )
    assert captured.value.code == "request_nonce"

    with pytest.raises(protocol.FirecrackerProtocolReject) as mutable:
        protocol.FirecrackerRequestV1.validated(
            run_nonce_256=bytearray([1]) * 32,  # type: ignore[arg-type]
            runtime_manifest_sha256=bytes([2]) * 32,
            input_drive_sha256=bytes([3]) * 32,
            replay_intent_sha256=bytes([4]) * 32,
        )
    assert mutable.value.code == "request_nonce"

    with pytest.raises(protocol.FirecrackerProtocolReject) as zero_intent:
        protocol.FirecrackerRequestV1.validated(
            run_nonce_256=bytes([1]) * 32,
            runtime_manifest_sha256=bytes([2]) * 32,
            input_drive_sha256=bytes([3]) * 32,
            replay_intent_sha256=bytes(32),
        )
    assert zero_intent.value.code == "request_intent"

    with pytest.raises(protocol.FirecrackerProtocolReject) as captured:
        protocol.FirecrackerRequestV1.validated(
            run_nonce_256=bytes([1]) * 31,
            runtime_manifest_sha256=bytes([2]) * 32,
            input_drive_sha256=bytes([3]) * 32,
            replay_intent_sha256=bytes([4]) * 32,
        )
    assert captured.value.code == "request_nonce"


def _request() -> protocol.FirecrackerRequestV1:
    return protocol.FirecrackerRequestV1.validated(
        run_nonce_256=bytes([1]) * 32,
        runtime_manifest_sha256=bytes([2]) * 32,
        input_drive_sha256=bytes([3]) * 32,
        replay_intent_sha256=bytes([4]) * 32,
    )


def _assert_output_reject(raw: bytearray, code: str) -> None:
    with pytest.raises(protocol.FirecrackerProtocolReject) as captured:
        protocol.validate_committed_output(bytes(raw), _request())
    assert captured.value.code == code
