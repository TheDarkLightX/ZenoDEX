"""Exact proof-neutral codec for the Spot V7 Firecracker authority input.

The manifest binds proposed artifacts and compiled image identities. Decoding
does not verify either receipt and grants no execution, release, settlement,
or production authority.
"""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from typing import Final

from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
)

SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1: Final = 256
SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1: Final = 16 * 1024 * 1024
SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1: Final = 16 * 1024 * 1024
SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1: Final = 16 * 1024 * 1024

_MAGIC_V1: Final = b"ZSV7AIM1"
_VERSION_V1: Final = 1

SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1: Final = (
    b"\n".join(
        (
            b"zenodex.zrpf.spot_v7.firecracker.authority_input_profile.v1",
            b"manifest_magic=ZSV7AIM1",
            b"manifest_bytes=256",
            b"manifest_version=1",
            b"manifest_endian=big",
            b"image_id_word_endian=little",
            b"manifest_layout=magic:u8x8,version:u16,bytes:u16,flags:u32,profile:u8x32,runtime_profile:u8x32,v7_image_id:u32lex8,v6_image_id:u32lex8,v7_receipt_bytes:u32,v7_receipt_sha256:u8x32,v7_guest_input_bytes:u32,v7_guest_input_sha256:u8x32,v6_receipt_bytes:u32,v6_receipt_sha256:u8x32,reserved:u8x4",
            b"artifact_names=spot-v7-authority-input.bin,spot-v7.receipt.json,spot-v7.guest-input.bin,spot-v6.receipt.json",
            b"v7_receipt_max_bytes=16777216",
            b"v7_guest_input_max_bytes=16777216",
            b"v6_receipt_max_bytes=16777216",
            b"runtime_profile_sha256=c8cf02b22988315b667c8b37675b6c8d8cd56f5638b8aa176357a044a89fcdd6",
            b"request_settlement_intent_binding=authority_input_manifest_sha256",
            b"verification=governed_spot_v7_verifier_once",
            b"output=derived_spot_v7_verifier_output_v1",
            b"authority=disabled_until_final_images_release_runner_store",
        )
    )
    + b"\n"
)
SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1: Final = hashlib.sha256(
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1
).digest()


class SpotV7FirecrackerAuthorityInputRejectV1(ValueError):
    """Stable rejection for the proof-neutral authority-input manifest."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class DecodedSpotV7FirecrackerAuthorityInputManifestV1:
    v7_image_id: tuple[int, ...]
    v6_image_id: tuple[int, ...]
    v7_receipt_length: int
    v7_receipt_sha256: bytes
    guest_input_length: int
    guest_input_sha256: bytes
    v6_receipt_length: int
    v6_receipt_sha256: bytes

    def encode(self) -> bytes:
        return _encode_fields(self)

    @property
    def sha256(self) -> bytes:
        return hashlib.sha256(self.encode()).digest()


def build_authority_input_manifest_v1(
    *,
    v7_image_id: tuple[int, ...],
    v6_image_id: tuple[int, ...],
    v7_receipt_bytes: bytes,
    guest_input_bytes: bytes,
    v6_receipt_bytes: bytes,
) -> bytes:
    """Construct the exact manifest from all three bounded artifact bytes."""

    value = DecodedSpotV7FirecrackerAuthorityInputManifestV1(
        v7_image_id=_require_image_id(v7_image_id, "authority_v7_image_id_unmaterialized"),
        v6_image_id=_require_image_id(v6_image_id, "authority_v6_image_id_unmaterialized"),
        v7_receipt_length=_require_artifact_length(
            v7_receipt_bytes,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1,
            "authority_v7_receipt_length",
        ),
        v7_receipt_sha256=hashlib.sha256(v7_receipt_bytes).digest(),
        guest_input_length=_require_artifact_length(
            guest_input_bytes,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1,
            "authority_guest_input_length",
        ),
        guest_input_sha256=hashlib.sha256(guest_input_bytes).digest(),
        v6_receipt_length=_require_artifact_length(
            v6_receipt_bytes,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1,
            "authority_v6_receipt_length",
        ),
        v6_receipt_sha256=hashlib.sha256(v6_receipt_bytes).digest(),
    )
    return value.encode()


def decode_exact_authority_input_manifest_v1(
    raw: bytes,
) -> DecodedSpotV7FirecrackerAuthorityInputManifestV1:
    """Decode one exact canonical binary manifest."""

    if type(raw) is not bytes or len(raw) != SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_length")
    if raw[0:8] != _MAGIC_V1:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_magic")
    version, length, flags = struct.unpack_from(">HHI", raw, 8)
    if version != _VERSION_V1 or length != SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_version")
    if flags != 0:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_flags")
    if raw[16:48] != SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_profile")
    if raw[48:80] != SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_runtime_profile")
    if any(raw[252:256]):
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_reserved")
    value = DecodedSpotV7FirecrackerAuthorityInputManifestV1(
        v7_image_id=_decode_image_id(raw[80:112], "authority_v7_image_id_unmaterialized"),
        v6_image_id=_decode_image_id(raw[112:144], "authority_v6_image_id_unmaterialized"),
        v7_receipt_length=_require_declared_length(
            struct.unpack_from(">I", raw, 144)[0],
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1,
            "authority_v7_receipt_length",
        ),
        v7_receipt_sha256=_require_digest(raw[148:180], "authority_v7_receipt_binding"),
        guest_input_length=_require_declared_length(
            struct.unpack_from(">I", raw, 180)[0],
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1,
            "authority_guest_input_length",
        ),
        guest_input_sha256=_require_digest(raw[184:216], "authority_guest_input_binding"),
        v6_receipt_length=_require_declared_length(
            struct.unpack_from(">I", raw, 216)[0],
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1,
            "authority_v6_receipt_length",
        ),
        v6_receipt_sha256=_require_digest(raw[220:252], "authority_v6_receipt_binding"),
    )
    if value.encode() != raw:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_noncanonical")
    return value


def _encode_fields(value: DecodedSpotV7FirecrackerAuthorityInputManifestV1) -> bytes:
    output = bytearray(SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1)
    output[0:8] = _MAGIC_V1
    struct.pack_into(">HHI", output, 8, _VERSION_V1, len(output), 0)
    output[16:48] = SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1
    output[48:80] = SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    output[80:112] = struct.pack("<8I", *value.v7_image_id)
    output[112:144] = struct.pack("<8I", *value.v6_image_id)
    struct.pack_into(">I", output, 144, value.v7_receipt_length)
    output[148:180] = value.v7_receipt_sha256
    struct.pack_into(">I", output, 180, value.guest_input_length)
    output[184:216] = value.guest_input_sha256
    struct.pack_into(">I", output, 216, value.v6_receipt_length)
    output[220:252] = value.v6_receipt_sha256
    return bytes(output)


def _decode_image_id(raw: bytes, code: str) -> tuple[int, ...]:
    if len(raw) != 32:
        raise SpotV7FirecrackerAuthorityInputRejectV1("authority_manifest_length")
    return _require_image_id(struct.unpack("<8I", raw), code)


def _require_image_id(value: tuple[int, ...], code: str) -> tuple[int, ...]:
    if (
        type(value) is not tuple
        or len(value) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFF_FFFF for word in value)
        or not any(value)
    ):
        raise SpotV7FirecrackerAuthorityInputRejectV1(code)
    return value


def _require_artifact_length(raw: bytes, maximum: int, code: str) -> int:
    if type(raw) is not bytes or not 0 < len(raw) <= maximum:
        raise SpotV7FirecrackerAuthorityInputRejectV1(code)
    return len(raw)


def _require_declared_length(value: int, maximum: int, code: str) -> int:
    if type(value) is not int or not 0 < value <= maximum:
        raise SpotV7FirecrackerAuthorityInputRejectV1(code)
    return value


def _require_digest(raw: bytes, code: str) -> bytes:
    if type(raw) is not bytes or len(raw) != 32 or not any(raw):
        raise SpotV7FirecrackerAuthorityInputRejectV1(code)
    return raw
