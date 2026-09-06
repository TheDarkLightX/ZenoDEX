"""Finite group/encoding evidence for the explicitly supplied real sealed ELF.

Oracle grade 3: py_ecc constructs and checks four on-curve, non-infinity points
outside the prime-order subgroup before native rejection is observed. Additional
cases cover compression/infinity flags, both G2 field coordinates, and three
noncanonical x+p aliases of valid encodings. Every case passes the byte-frame
encoder; operational failures cannot satisfy the required False verdict.

Set ZENODEX_BLS_VERIFIER_TEST_BINARY to the checksum-verified native artifact.
The pinned hash is an evidence subject, not a runtime trust or release policy.
There are no mocks, blst-generated expectations, or shared-source mutants.
These finite checks do not prove universal group/encoding equivalence, isolated
subgroup-guard mutation kills, cryptographic security, build reproducibility,
or publication authority. No state, settlement, or mounting path is exercised.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest
from eth_typing import BLSPubkey, BLSSignature
from py_ecc.bls import G2Basic
from py_ecc.bls.g2_primitives import (
    G1_to_pubkey,
    G2_to_signature,
    pubkey_to_G1,
    signature_to_G2,
)
from py_ecc.bls.hash_to_curve import map_to_curve_G1, map_to_curve_G2
from py_ecc.optimized_bls12_381 import (
    FQ,
    FQ2,
    b,
    b2,
    curve_order,
    eq,
    field_modulus,
    is_inf,
    is_on_curve,
    multiply,
)

from src.core import bls_command_verifier_protocol_v1 as protocol
from src.integration import sealed_bls_command_verifier_v1 as bridge

_VERIFIED_BINARY_SHA256 = "597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee"
_MESSAGE = b"zenodex-sealed-bls-group-validation-v1/0"
_COORDINATE_MASK = (1 << 381) - 1
_MALFORMED_G1_CASES = (
    "compression_flag_clear",
    "infinity_flag_on_finite_point",
    "infinity_with_sign_flag",
    "infinity_with_payload",
    "first_coordinate_at_modulus",
    "first_coordinate_above_modulus",
)
_MALFORMED_G2_CASES = _MALFORMED_G1_CASES + (
    "second_coordinate_at_modulus",
    "second_coordinate_above_modulus",
    "second_coordinate_with_compression_bit",
)


@pytest.fixture(scope="module")
def real_backend() -> bridge.SealedBlsCommandVerifierV1:
    configured = os.environ.get("ZENODEX_BLS_VERIFIER_TEST_BINARY")
    if not configured:
        pytest.skip("explicit checksum-verified BLS executable required")
    assert configured is not None
    return bridge.load_sealed_bls_command_verifier_v1(
        Path(configured), expected_sha256=_VERIFIED_BINARY_SHA256, timeout_ms=5000,
    )


def _native_verdict(
    backend: bridge.SealedBlsCommandVerifierV1,
    public_key: BLSPubkey,
    signature: BLSSignature,
) -> bool:
    request = protocol.encode_bls_command_request_v1(
        signature_algorithm=protocol.BLS_COMMAND_ALGORITHM_V1,
        signer_public_key="0x" + public_key.hex(),
        message_bytes=_MESSAGE, signature_bytes=signature,
    )
    assert request == (
        b"ZDXBLSV1" + public_key + signature
        + len(_MESSAGE).to_bytes(4, "little") + _MESSAGE
    )
    return backend.verify_command_signature(
        signature_algorithm=protocol.BLS_COMMAND_ALGORITHM_V1,
        signer_public_key="0x" + public_key.hex(),
        message_bytes=_MESSAGE, signature_bytes=signature,
    )


@pytest.fixture(scope="module")
def valid_pair(
    real_backend: bridge.SealedBlsCommandVerifierV1,
) -> tuple[BLSPubkey, BLSSignature]:
    # Public test scalar, selected so all three x+p aliases fit their wire words.
    public_key = G2Basic.SkToPk(2)
    signature = G2Basic.Sign(2, _MESSAGE)
    key_point = pubkey_to_G1(public_key)
    signature_point = signature_to_G2(signature)
    assert is_on_curve(key_point, b) and not is_inf(key_point)
    assert is_on_curve(signature_point, b2) and not is_inf(signature_point)
    assert is_inf(multiply(key_point, curve_order))
    assert is_inf(multiply(signature_point, curve_order))
    assert G2Basic.Verify(public_key, _MESSAGE, signature) is True
    assert _native_verdict(real_backend, public_key, signature) is True
    return public_key, signature


@pytest.mark.parametrize("seed", (1, 2))
def test_on_curve_canonical_g1_outside_subgroup_rejects_with_valid_signature(
    real_backend: bridge.SealedBlsCommandVerifierV1,
    valid_pair: tuple[BLSPubkey, BLSSignature],
    seed: int,
) -> None:
    # This map precedes cofactor clearing; membership is checked arithmetically.
    point = map_to_curve_G1(FQ(seed))
    assert is_on_curve(point, b)
    assert not is_inf(point)
    assert not is_inf(multiply(point, curve_order))
    public_key = G1_to_pubkey(point)
    decoded = pubkey_to_G1(public_key)
    assert eq(decoded, point)
    assert G1_to_pubkey(decoded) == public_key
    assert G2Basic.KeyValidate(public_key) is False
    _, signature = valid_pair
    assert G2Basic.Verify(public_key, _MESSAGE, signature) is False
    assert _native_verdict(real_backend, public_key, signature) is False


@pytest.mark.parametrize("seed", (1, 3))
def test_on_curve_canonical_g2_outside_subgroup_rejects_with_valid_key(
    real_backend: bridge.SealedBlsCommandVerifierV1,
    valid_pair: tuple[BLSPubkey, BLSSignature],
    seed: int,
) -> None:
    point = map_to_curve_G2(FQ2((seed, seed + 1)))
    assert is_on_curve(point, b2)
    assert not is_inf(point)
    assert not is_inf(multiply(point, curve_order))
    signature = G2_to_signature(point)
    decoded = signature_to_G2(signature)
    assert eq(decoded, point)
    assert G2_to_signature(decoded) == signature
    public_key, _ = valid_pair
    assert G2Basic.Verify(public_key, _MESSAGE, signature) is False
    assert _native_verdict(real_backend, public_key, signature) is False


def _malformed_compressed_cases(canonical: bytes) -> dict[str, bytes]:
    tail = canonical[48:]
    cases = {
        "compression_flag_clear": bytes((canonical[0] & 0x7F,)) + canonical[1:],
        "infinity_flag_on_finite_point": bytes((canonical[0] | 0x40,)) + canonical[1:],
        "infinity_with_sign_flag": b"\xe0" + bytes(len(canonical) - 1),
        "infinity_with_payload": b"\xc0" + bytes(len(canonical) - 2) + b"\x01",
        "first_coordinate_at_modulus": ((1 << 383) | field_modulus).to_bytes(48, "big") + tail,
        "first_coordinate_above_modulus": ((1 << 383) | (field_modulus + 1)).to_bytes(48, "big") + tail,
    }
    if len(canonical) == 96:
        cases.update({
            "second_coordinate_at_modulus": canonical[:48] + field_modulus.to_bytes(48, "big"),
            "second_coordinate_above_modulus": canonical[:48] + (field_modulus + 1).to_bytes(48, "big"),
            "second_coordinate_with_compression_bit": (
                canonical[:48] + bytes((canonical[48] | 0x80,)) + canonical[49:]
            ),
        })
    return cases


@pytest.mark.parametrize("case", _MALFORMED_G1_CASES)
def test_malformed_g1_compression_reaches_native_rejection(
    real_backend: bridge.SealedBlsCommandVerifierV1,
    valid_pair: tuple[BLSPubkey, BLSSignature],
    case: str,
) -> None:
    public_key, signature = valid_pair
    malformed = BLSPubkey(_malformed_compressed_cases(public_key)[case])
    assert len(malformed) == 48 and malformed != public_key
    with pytest.raises(ValueError):
        pubkey_to_G1(malformed)
    assert G2Basic.Verify(malformed, _MESSAGE, signature) is False
    assert _native_verdict(real_backend, malformed, signature) is False


@pytest.mark.parametrize("case", _MALFORMED_G2_CASES)
def test_malformed_g2_compression_reaches_native_rejection(
    real_backend: bridge.SealedBlsCommandVerifierV1,
    valid_pair: tuple[BLSPubkey, BLSSignature],
    case: str,
) -> None:
    public_key, signature = valid_pair
    malformed = BLSSignature(_malformed_compressed_cases(signature)[case])
    assert len(malformed) == 96 and malformed != signature
    with pytest.raises(ValueError):
        signature_to_G2(malformed)
    assert G2Basic.Verify(public_key, _MESSAGE, malformed) is False
    assert _native_verdict(real_backend, public_key, malformed) is False


def _alias_coordinate_by_field_modulus(canonical: bytes, word_index: int) -> bytes:
    offset = 48 * word_index
    word = int.from_bytes(canonical[offset:offset + 48], "big")
    coordinate = word & _COORDINATE_MASK if word_index == 0 else word
    flags = word ^ coordinate
    assert 0 <= coordinate < field_modulus
    aliased_coordinate = coordinate + field_modulus
    assert aliased_coordinate < (1 << (381 if word_index == 0 else 384))
    assert aliased_coordinate % field_modulus == coordinate
    aliased_word = (flags | aliased_coordinate).to_bytes(48, "big")
    return canonical[:offset] + aliased_word + canonical[offset + 48:]


def test_noncanonical_g1_field_alias_of_valid_key_rejects(
    real_backend: bridge.SealedBlsCommandVerifierV1,
    valid_pair: tuple[BLSPubkey, BLSSignature],
) -> None:
    public_key, signature = valid_pair
    aliased = BLSPubkey(_alias_coordinate_by_field_modulus(public_key, 0))
    assert aliased != public_key
    with pytest.raises(ValueError, match="less than field modulus"):
        pubkey_to_G1(aliased)
    assert G2Basic.Verify(aliased, _MESSAGE, signature) is False
    assert _native_verdict(real_backend, aliased, signature) is False


@pytest.mark.parametrize("word_index", (0, 1), ids=("imaginary", "real"))
def test_noncanonical_g2_field_alias_of_valid_signature_rejects(
    real_backend: bridge.SealedBlsCommandVerifierV1,
    valid_pair: tuple[BLSPubkey, BLSSignature],
    word_index: int,
) -> None:
    public_key, signature = valid_pair
    aliased = BLSSignature(_alias_coordinate_by_field_modulus(signature, word_index))
    assert aliased != signature
    with pytest.raises(ValueError, match="less than field modulus"):
        signature_to_G2(aliased)
    assert G2Basic.Verify(public_key, _MESSAGE, aliased) is False
    assert _native_verdict(real_backend, public_key, aliased) is False
