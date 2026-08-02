"""Focused G02 canonical proof-context codec tests."""

from __future__ import annotations

from experiments.fcis_m6_g02_proof_context_check import (
    build_context,
    build_rust_input,
)
from src.core.fcis_m6_g02_proof_context_codec import (
    G02ProofContextCodeV1,
    G02ProofContextRejectV1,
    G02ProofContextSuccessV1,
    decode_g02_proof_context_v1,
    encode_g02_proof_context_v1,
)


def test_codec_round_trip_is_byte_and_root_stable() -> None:
    context = build_context()
    encoded = encode_g02_proof_context_v1(context)
    result = decode_g02_proof_context_v1(encoded)

    assert type(result) is G02ProofContextSuccessV1
    assert result.context == context
    assert result.canonical_bytes == encoded
    assert result.codec_root.startswith("0x")


def test_codec_rejects_unknown_version_and_field() -> None:
    encoded = encode_g02_proof_context_v1(build_context())
    version = bytearray(encoded)
    version[11] = 2
    unknown = encoded.replace(b"chain_id", b"foreign!", 1)

    version_result = decode_g02_proof_context_v1(bytes(version))
    unknown_result = decode_g02_proof_context_v1(unknown)
    assert type(version_result) is G02ProofContextRejectV1
    assert type(unknown_result) is G02ProofContextRejectV1
    assert version_result.code is G02ProofContextCodeV1.WRONG_VERSION
    assert unknown_result.code is G02ProofContextCodeV1.UNKNOWN_FIELD


def test_codec_rejects_wrong_type_and_trailing_frame() -> None:
    encoded = encode_g02_proof_context_v1(build_context())
    trailing = decode_g02_proof_context_v1(encoded + b"\x00")

    assert type(decode_g02_proof_context_v1(object())) is G02ProofContextRejectV1
    assert type(trailing) is G02ProofContextRejectV1
    assert trailing.code is G02ProofContextCodeV1.INVALID_FRAME


def test_rust_input_is_one_fixed_order_record() -> None:
    fields = build_rust_input().rstrip("\n").split("\t")

    assert len(fields) == 15
    assert fields[11:14] == ["7", "5", "10"]
