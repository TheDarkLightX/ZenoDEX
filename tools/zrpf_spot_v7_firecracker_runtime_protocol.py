"""Exact data-only Spot V7 Firecracker request and committed-output codec.

The retained structural V3 replay profile is a different protocol. This V1
profile has its own magic values, canonical profile descriptor, profile digest,
and commit domain. Successful decoding establishes byte-level consistency and
fresh-request binding only. It grants no Firecracker execution, release,
settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from typing import Final

from tools.zrpf_spot_v7_verifier_payload_codec import (
    SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1 as _SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1,
)
from tools.zrpf_spot_v7_verifier_payload_codec import (
    SpotV7FirecrackerProtocolRejectV1,
    StructurallyDecodedSpotV7VerifierPayloadV1,
)
from tools.zrpf_spot_v7_verifier_payload_codec import (
    decode_structural_v7_verifier_payload_v1 as _decode_structural_v7_payload,
)

SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1: Final = 224
SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1: Final = 16_777_216
SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1: Final = 288
SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1: Final = 32
SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1: Final = _SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1

SPOT_V7_FIRECRACKER_REQUEST_MAGIC_V1: Final = b"ZSV7REQ1"
SPOT_V7_FIRECRACKER_OUTPUT_MAGIC_V1: Final = b"ZSV7OUT1"
SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_DOMAIN_V1: Final = (
    b"zenodex/zrpf_spot_v7_firecracker_output_commit/v1\x00"
)
SPOT_V7_FIRECRACKER_PROTOCOL_VERSION_V1: Final = 1
SPOT_V7_FIRECRACKER_DATA_ONLY_COMMITTED_STATUS_V1: Final = 1

SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1: Final = (
    b"\n".join(
        (
            b"zenodex.zrpf.spot_v7.firecracker.runtime_profile.v1",
            b"request_magic=ZSV7REQ1",
            b"request_bytes=224",
            b"request_version=1",
            b"request_endian=little",
            b"request_layout=magic:u8x8,version:u16,bytes:u16,flags:u32,nonce:u8x32,profile:u8x32,runtime_manifest:u8x32,machine_config:u8x32,input_drive:u8x32,output_bytes:u64,payload_cap:u32,settlement_intent:u8x32,reserved:u8x4",
            b"output_magic=ZSV7OUT1",
            b"output_bytes=16777216",
            b"output_header_bytes=288",
            b"output_commit_bytes=32",
            b"output_payload_cap_bytes=65536",
            b"output_header_endian=little",
            b"output_header_layout=magic:u8x8,version:u16,header_bytes:u16,status:u32,payload_bytes:u32,flags:u32,output_bytes:u64,nonce:u8x32,request_sha256:u8x32,profile:u8x32,runtime_manifest:u8x32,machine_config:u8x32,input_drive:u8x32,settlement_intent:u8x32,payload_sha256:u8x32",
            b"output_status=1:data_only_committed",
            b"output_zero_region=header_plus_payload_to_commit_offset",
            b"payload_magic=ZSPTV7O1",
            b"payload_version=1",
            b"payload_codec=SpotSettlementV7VerifierOutputV1_structural_envelope_big_endian",
            b"payload_journal_magic=ZSPTV7J1",
            b"payload_journal_version=1",
            b"commit_domain=zenodex/zrpf_spot_v7_firecracker_output_commit/v1\\0",
            b"commit_formula=sha256(domain||profile_sha256||request_sha256||header||payload)",
            b"authority=data_only",
        )
    )
    + b"\n"
)
SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1: Final = hashlib.sha256(
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1
).digest()

SPOT_V7_FIRECRACKER_RUNTIME_SETTLEMENT_AUTHORITY_V1: Final = False
SPOT_V7_FIRECRACKER_RUNTIME_RELEASE_AUTHORITY_V1: Final = False
SPOT_V7_FIRECRACKER_RUNTIME_PRODUCTION_READY_V1: Final = False


@dataclass(frozen=True, slots=True, init=False)
class SpotV7FirecrackerRequestV1:
    """Canonical request bindings for one fresh Spot V7 microVM execution."""

    run_nonce_256: bytes
    runtime_manifest_sha256: bytes
    machine_config_sha256: bytes
    input_drive_sha256: bytes
    settlement_intent_sha256: bytes

    def __new__(cls) -> SpotV7FirecrackerRequestV1:
        raise TypeError("SpotV7FirecrackerRequestV1 requires validated construction")

    @classmethod
    def validated(
        cls,
        *,
        run_nonce_256: bytes,
        runtime_manifest_sha256: bytes,
        machine_config_sha256: bytes,
        input_drive_sha256: bytes,
        settlement_intent_sha256: bytes,
    ) -> SpotV7FirecrackerRequestV1:
        _require_digest(run_nonce_256, "request_nonce")
        _require_digest(runtime_manifest_sha256, "request_manifest")
        _require_digest(machine_config_sha256, "request_machine_config")
        _require_digest(input_drive_sha256, "request_input")
        _require_digest(settlement_intent_sha256, "request_intent")
        value = object.__new__(cls)
        object.__setattr__(value, "run_nonce_256", run_nonce_256)
        object.__setattr__(value, "runtime_manifest_sha256", runtime_manifest_sha256)
        object.__setattr__(value, "machine_config_sha256", machine_config_sha256)
        object.__setattr__(value, "input_drive_sha256", input_drive_sha256)
        object.__setattr__(value, "settlement_intent_sha256", settlement_intent_sha256)
        return value

    def encode(self) -> bytes:
        output = bytearray(SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1)
        output[0:8] = SPOT_V7_FIRECRACKER_REQUEST_MAGIC_V1
        struct.pack_into(
            "<HHI",
            output,
            8,
            SPOT_V7_FIRECRACKER_PROTOCOL_VERSION_V1,
            SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1,
            0,
        )
        output[16:48] = self.run_nonce_256
        output[48:80] = SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        output[80:112] = self.runtime_manifest_sha256
        output[112:144] = self.machine_config_sha256
        output[144:176] = self.input_drive_sha256
        struct.pack_into(
            "<QI",
            output,
            176,
            SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1,
            SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1,
        )
        output[188:220] = self.settlement_intent_sha256
        return bytes(output)

    @property
    def sha256(self) -> bytes:
        return hashlib.sha256(self.encode()).digest()


def decode_exact_request_v1(raw: bytes) -> SpotV7FirecrackerRequestV1:
    """Decode one exact 224-byte request and reject every noncanonical bit."""

    _require_exact_bytes(raw, SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1, "request_length")
    _validate_request_header(raw)
    if raw[48:80] != SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1:
        raise SpotV7FirecrackerProtocolRejectV1("request_profile")
    if any(raw[220:]):
        raise SpotV7FirecrackerProtocolRejectV1("request_reserved")
    return SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=raw[16:48],
        runtime_manifest_sha256=raw[80:112],
        machine_config_sha256=raw[112:144],
        input_drive_sha256=raw[144:176],
        settlement_intent_sha256=raw[188:220],
    )


def build_data_only_committed_output_v1(
    request: SpotV7FirecrackerRequestV1,
    *,
    observed_input_drive_sha256: bytes,
    payload: bytes,
) -> bytes:
    """Build a canonical test/vector image without creating runtime authority."""

    _require_exact_request_type(request)
    _require_digest(observed_input_drive_sha256, "output_binding")
    if observed_input_drive_sha256 != request.input_drive_sha256:
        raise SpotV7FirecrackerProtocolRejectV1("output_binding")
    decoded_payload = decode_structural_v7_verifier_payload_v1(payload)
    header = _build_output_header(request, decoded_payload.raw_bytes)
    marker = _output_commit_marker(request, header, decoded_payload.raw_bytes)
    output = bytearray(SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1)
    output[:SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1] = header
    payload_end = SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1 + len(payload)
    output[SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1:payload_end] = payload
    output[-SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1:] = marker
    return bytes(output)


def validate_exact_committed_output_v1(
    raw: bytes,
    request: SpotV7FirecrackerRequestV1,
) -> StructurallyDecodedSpotV7VerifierPayloadV1:
    """Validate the fixed output image, fresh request binding, and V7 payload."""

    _require_exact_request_type(request)
    _require_exact_bytes(raw, SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1, "output_length")
    payload_length = _validate_output_header(raw, request)
    payload_end = SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1 + payload_length
    commit_offset = SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 - SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1
    if payload_end > commit_offset:
        raise SpotV7FirecrackerProtocolRejectV1("output_payload")
    payload = raw[SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1:payload_end]
    if hashlib.sha256(payload).digest() != raw[256:288]:
        raise SpotV7FirecrackerProtocolRejectV1("output_payload")
    if any(raw[payload_end:commit_offset]):
        raise SpotV7FirecrackerProtocolRejectV1("output_trailing_bytes")
    expected_marker = _output_commit_marker(
        request,
        raw[:SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1],
        payload,
    )
    if raw[commit_offset:] != expected_marker:
        raise SpotV7FirecrackerProtocolRejectV1("output_commit")
    return decode_structural_v7_verifier_payload_v1(payload)


def decode_structural_v7_verifier_payload_v1(
    raw: bytes,
) -> StructurallyDecodedSpotV7VerifierPayloadV1:
    """Check the bounded V7 structural envelope without proof authority."""

    return _decode_structural_v7_payload(raw)


def _validate_request_header(raw: bytes) -> None:
    if raw[:8] != SPOT_V7_FIRECRACKER_REQUEST_MAGIC_V1:
        raise SpotV7FirecrackerProtocolRejectV1("request_magic")
    version, request_bytes, flags = struct.unpack_from("<HHI", raw, 8)
    if (
        version != SPOT_V7_FIRECRACKER_PROTOCOL_VERSION_V1
        or request_bytes != SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1
    ):
        raise SpotV7FirecrackerProtocolRejectV1("request_version")
    if flags != 0:
        raise SpotV7FirecrackerProtocolRejectV1("request_flags")
    output_bytes, payload_cap = struct.unpack_from("<QI", raw, 176)
    if (
        output_bytes != SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1
        or payload_cap != SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1
    ):
        raise SpotV7FirecrackerProtocolRejectV1("request_output_bounds")


def _build_output_header(request: SpotV7FirecrackerRequestV1, payload: bytes) -> bytes:
    header = bytearray(SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1)
    header[:8] = SPOT_V7_FIRECRACKER_OUTPUT_MAGIC_V1
    struct.pack_into(
        "<HHIIIQ",
        header,
        8,
        SPOT_V7_FIRECRACKER_PROTOCOL_VERSION_V1,
        SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1,
        SPOT_V7_FIRECRACKER_DATA_ONLY_COMMITTED_STATUS_V1,
        len(payload),
        0,
        SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1,
    )
    header[32:64] = request.run_nonce_256
    header[64:96] = request.sha256
    header[96:128] = SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    header[128:160] = request.runtime_manifest_sha256
    header[160:192] = request.machine_config_sha256
    header[192:224] = request.input_drive_sha256
    header[224:256] = request.settlement_intent_sha256
    header[256:288] = hashlib.sha256(payload).digest()
    return bytes(header)


def _validate_output_header(raw: bytes, request: SpotV7FirecrackerRequestV1) -> int:
    version, header_bytes, status, payload_length, flags, output_bytes = struct.unpack_from(
        "<HHIIIQ", raw, 8
    )
    if (
        raw[:8] != SPOT_V7_FIRECRACKER_OUTPUT_MAGIC_V1
        or version != SPOT_V7_FIRECRACKER_PROTOCOL_VERSION_V1
        or header_bytes != SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1
        or status != SPOT_V7_FIRECRACKER_DATA_ONLY_COMMITTED_STATUS_V1
        or flags != 0
        or output_bytes != SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1
    ):
        raise SpotV7FirecrackerProtocolRejectV1("output_header")
    bindings = (
        (raw[32:64], request.run_nonce_256),
        (raw[64:96], request.sha256),
        (raw[96:128], SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1),
        (raw[128:160], request.runtime_manifest_sha256),
        (raw[160:192], request.machine_config_sha256),
        (raw[192:224], request.input_drive_sha256),
        (raw[224:256], request.settlement_intent_sha256),
    )
    if any(actual != expected for actual, expected in bindings):
        raise SpotV7FirecrackerProtocolRejectV1("output_binding")
    if not 0 < payload_length <= SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise SpotV7FirecrackerProtocolRejectV1("output_payload")
    return payload_length


def _output_commit_marker(
    request: SpotV7FirecrackerRequestV1,
    header: bytes,
    payload: bytes,
) -> bytes:
    return hashlib.sha256(
        SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_DOMAIN_V1
        + SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        + request.sha256
        + header
        + payload
    ).digest()


def _require_exact_request_type(value: SpotV7FirecrackerRequestV1) -> None:
    if type(value) is not SpotV7FirecrackerRequestV1:
        raise TypeError("request must be exact SpotV7FirecrackerRequestV1")


def _require_exact_bytes(value: bytes, length: int, code: str) -> None:
    if type(value) is not bytes or len(value) != length:
        raise SpotV7FirecrackerProtocolRejectV1(code)


def _require_digest(value: bytes, code: str) -> None:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise SpotV7FirecrackerProtocolRejectV1(code)
