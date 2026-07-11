"""Strict host-side mirror of the ZRPF Firecracker request/output ABI."""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass

REQUEST_BYTES_V1 = 192
OUTPUT_BYTES_V1 = 16_777_216
OUTPUT_HEADER_BYTES_V1 = 256
OUTPUT_COMMIT_BYTES_V1 = 32
OUTPUT_PAYLOAD_CAP_BYTES_V1 = 65_536
REQUEST_MAGIC_V1 = b"ZRPFREQ1"
OUTPUT_MAGIC_V1 = b"ZRPFOU01"
OUTPUT_COMMIT_DOMAIN_V1 = b"zenodex/zrpf_firecracker_output_commit/v1\x00"
VERSION_V1 = 1
ACCEPTED_STATUS_V1 = 1
CANDIDATE_PROFILE_CANONICAL_SHA256_V1 = bytes.fromhex(
    "3be22c7d06bc3c4a7f0d83065fe2cadbb7b284830a70797165e32e229a1bdd0f"
)


class FirecrackerProtocolReject(ValueError):
    """Stable fail-closed rejection for the fixed binary protocol."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True, init=False)
class FirecrackerRequestV1:
    run_nonce_256: bytes
    runtime_manifest_sha256: bytes
    input_drive_sha256: bytes
    replay_intent_sha256: bytes

    def __new__(cls) -> FirecrackerRequestV1:
        raise TypeError("FirecrackerRequestV1 requires validated construction")

    @classmethod
    def validated(
        cls,
        *,
        run_nonce_256: bytes,
        runtime_manifest_sha256: bytes,
        input_drive_sha256: bytes,
        replay_intent_sha256: bytes,
    ) -> FirecrackerRequestV1:
        _require_digest(run_nonce_256, "request_nonce")
        _require_digest(runtime_manifest_sha256, "request_manifest")
        _require_digest(input_drive_sha256, "request_input")
        _require_digest(replay_intent_sha256, "request_intent")
        value = object.__new__(cls)
        object.__setattr__(value, "run_nonce_256", run_nonce_256)
        object.__setattr__(value, "runtime_manifest_sha256", runtime_manifest_sha256)
        object.__setattr__(value, "input_drive_sha256", input_drive_sha256)
        object.__setattr__(value, "replay_intent_sha256", replay_intent_sha256)
        return value

    def encode(self) -> bytes:
        output = bytearray(REQUEST_BYTES_V1)
        output[0:8] = REQUEST_MAGIC_V1
        struct.pack_into("<HHI", output, 8, VERSION_V1, REQUEST_BYTES_V1, 0)
        output[16:48] = self.run_nonce_256
        output[48:80] = CANDIDATE_PROFILE_CANONICAL_SHA256_V1
        output[80:112] = self.runtime_manifest_sha256
        output[112:144] = self.input_drive_sha256
        struct.pack_into("<QI", output, 144, OUTPUT_BYTES_V1, OUTPUT_PAYLOAD_CAP_BYTES_V1)
        output[156:188] = self.replay_intent_sha256
        return bytes(output)

    @property
    def sha256(self) -> bytes:
        return hashlib.sha256(self.encode()).digest()


def decode_request(raw: bytes) -> FirecrackerRequestV1:
    if len(raw) != REQUEST_BYTES_V1:
        raise FirecrackerProtocolReject("request_length")
    if raw[0:8] != REQUEST_MAGIC_V1:
        raise FirecrackerProtocolReject("request_magic")
    version, header_bytes, flags = struct.unpack_from("<HHI", raw, 8)
    if version != VERSION_V1 or header_bytes != REQUEST_BYTES_V1:
        raise FirecrackerProtocolReject("request_version")
    if flags != 0:
        raise FirecrackerProtocolReject("request_flags")
    output_bytes, payload_cap = struct.unpack_from("<QI", raw, 144)
    if output_bytes != OUTPUT_BYTES_V1 or payload_cap != OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise FirecrackerProtocolReject("request_output_bounds")
    if raw[48:80] != CANDIDATE_PROFILE_CANONICAL_SHA256_V1:
        raise FirecrackerProtocolReject("request_profile")
    if any(raw[188:]):
        raise FirecrackerProtocolReject("request_reserved")
    return FirecrackerRequestV1.validated(
        run_nonce_256=raw[16:48],
        runtime_manifest_sha256=raw[80:112],
        input_drive_sha256=raw[112:144],
        replay_intent_sha256=raw[156:188],
    )


def build_committed_output(
    request: FirecrackerRequestV1,
    *,
    observed_input_drive_sha256: bytes,
    payload: bytes,
) -> bytes:
    if observed_input_drive_sha256 != request.input_drive_sha256:
        raise FirecrackerProtocolReject("output_binding")
    header = _build_output_header(request, payload)
    marker = _output_commit_marker(header, payload)
    output = bytearray(OUTPUT_BYTES_V1)
    output[:OUTPUT_HEADER_BYTES_V1] = header
    output[OUTPUT_HEADER_BYTES_V1 : OUTPUT_HEADER_BYTES_V1 + len(payload)] = payload
    output[-OUTPUT_COMMIT_BYTES_V1:] = marker
    return bytes(output)


def validate_committed_output(raw: bytes, request: FirecrackerRequestV1) -> bytes:
    if len(raw) != OUTPUT_BYTES_V1:
        raise FirecrackerProtocolReject("output_length")
    payload_length = _validate_output_header(raw, request)
    payload_end = OUTPUT_HEADER_BYTES_V1 + payload_length
    commit_offset = OUTPUT_BYTES_V1 - OUTPUT_COMMIT_BYTES_V1
    if payload_end > commit_offset:
        raise FirecrackerProtocolReject("output_payload")
    payload = raw[OUTPUT_HEADER_BYTES_V1:payload_end]
    if hashlib.sha256(payload).digest() != raw[192:224]:
        raise FirecrackerProtocolReject("output_payload")
    if any(raw[payload_end:commit_offset]):
        raise FirecrackerProtocolReject("output_trailing_bytes")
    marker = _output_commit_marker(raw[:OUTPUT_HEADER_BYTES_V1], payload)
    if raw[commit_offset:] != marker:
        raise FirecrackerProtocolReject("output_commit")
    return payload


def _build_output_header(request: FirecrackerRequestV1, payload: bytes) -> bytes:
    if not payload or len(payload) > OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise FirecrackerProtocolReject("output_payload")
    header = bytearray(OUTPUT_HEADER_BYTES_V1)
    header[0:8] = OUTPUT_MAGIC_V1
    struct.pack_into(
        "<HHIIIQ",
        header,
        8,
        VERSION_V1,
        OUTPUT_HEADER_BYTES_V1,
        ACCEPTED_STATUS_V1,
        len(payload),
        0,
        OUTPUT_BYTES_V1,
    )
    header[32:64] = request.run_nonce_256
    header[64:96] = request.sha256
    header[96:128] = request.input_drive_sha256
    header[128:160] = CANDIDATE_PROFILE_CANONICAL_SHA256_V1
    header[160:192] = request.runtime_manifest_sha256
    header[192:224] = hashlib.sha256(payload).digest()
    return bytes(header)


def _validate_output_header(raw: bytes, request: FirecrackerRequestV1) -> int:
    version, header_bytes, status, payload_length, reserved, output_bytes = struct.unpack_from(
        "<HHIIIQ", raw, 8
    )
    if (
        raw[0:8] != OUTPUT_MAGIC_V1
        or version != VERSION_V1
        or header_bytes != OUTPUT_HEADER_BYTES_V1
        or status != ACCEPTED_STATUS_V1
        or reserved != 0
        or output_bytes != OUTPUT_BYTES_V1
        or any(raw[224:OUTPUT_HEADER_BYTES_V1])
    ):
        raise FirecrackerProtocolReject("output_header")
    if (
        raw[32:64] != request.run_nonce_256
        or raw[64:96] != request.sha256
        or raw[96:128] != request.input_drive_sha256
        or raw[128:160] != CANDIDATE_PROFILE_CANONICAL_SHA256_V1
        or raw[160:192] != request.runtime_manifest_sha256
    ):
        raise FirecrackerProtocolReject("output_binding")
    if not 0 < payload_length <= OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise FirecrackerProtocolReject("output_payload")
    return payload_length


def _output_commit_marker(header: bytes, payload: bytes) -> bytes:
    return hashlib.sha256(OUTPUT_COMMIT_DOMAIN_V1 + header + payload).digest()


def _require_digest(value: bytes, code: str) -> None:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise FirecrackerProtocolReject(code)
