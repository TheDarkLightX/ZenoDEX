from __future__ import annotations

import hashlib

import pytest

from src.integration._zrpf_settlement_admission_journal_codec import (
    MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
    MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
    SETTLEMENT_ADMISSION_FIXED_BYTES_V1,
    DecodedSettlementAdmissionJournalV1,
    SettlementAdmissionJournalDecodeErrorV1,
    SettlementSemanticRootKindV1,
    decode_exact_settlement_admission_journal_v1,
    derive_settlement_certificate_id_v1,
)

_MAGIC = b"ZRPFSAV1"
_CERTIFICATE = b"canonical-certificate-postcard-v1"
_EFFECT_PLAN = b"canonical-effect-plan-postcard-v2"


def _root(index: int) -> bytes:
    return bytes([index]) * 32


def _valid_frame() -> bytes:
    total = SETTLEMENT_ADMISSION_FIXED_BYTES_V1 + len(_CERTIFICATE) + len(_EFFECT_PLAN)
    frame = bytearray()
    frame.extend(_MAGIC)
    frame.extend((1).to_bytes(2, "big"))
    frame.extend(total.to_bytes(4, "big"))
    frame.extend(len(_CERTIFICATE).to_bytes(4, "big"))
    frame.extend(len(_EFFECT_PLAN).to_bytes(4, "big"))
    frame.extend(_CERTIFICATE)
    frame.extend(_EFFECT_PLAN)
    frame.extend(hashlib.sha256(_CERTIFICATE).digest())
    frame.extend(hashlib.sha256(_EFFECT_PLAN).digest())
    frame.extend((1).to_bytes(2, "big"))
    frame.extend((2).to_bytes(2, "big"))
    frame.extend(_root(1))
    frame.extend(_root(2))
    frame.extend((99).to_bytes(8, "big"))
    frame.extend(_root(3))
    frame.extend(_root(4))
    frame.extend(_root(5))
    frame.extend(_root(6))
    frame.append(SettlementSemanticRootKindV1.VALUE_SUBTREE)
    frame.extend(_root(7))
    for index in range(8, 16):
        frame.extend(_root(index))
    frame.extend((17).to_bytes(4, "big"))
    frame.extend((19).to_bytes(4, "big"))
    for index in range(16, 26):
        frame.extend(_root(index))
    frame.extend(derive_settlement_certificate_id_v1(_CERTIFICATE))
    frame.extend(_root(26))
    assert len(frame) == total
    return bytes(frame)


def _replace_u32(frame: bytes, offset: int, value: int) -> bytes:
    mutated = bytearray(frame)
    mutated[offset : offset + 4] = value.to_bytes(4, "big")
    return bytes(mutated)


def test_exact_frame_extracts_every_fixed_field_and_exact_inner_bytes() -> None:
    raw = _valid_frame()
    decoded = decode_exact_settlement_admission_journal_v1(raw)

    assert type(decoded) is DecodedSettlementAdmissionJournalV1
    assert decoded.journal_version == 1
    assert decoded.certificate_bytes == _CERTIFICATE
    assert decoded.effect_plan_bytes == _EFFECT_PLAN
    assert decoded.certificate_sha256 == hashlib.sha256(_CERTIFICATE).digest()
    assert decoded.effect_plan_sha256 == hashlib.sha256(_EFFECT_PLAN).digest()
    assert decoded.certificate_version == 1
    assert decoded.effect_plan_version == 2
    assert decoded.application_id == _root(1)
    assert decoded.chain_or_domain_id == _root(2)
    assert decoded.epoch_id == 99
    assert decoded.semantic_profile_id == _root(3)
    assert decoded.semantic_journal_hash == _root(4)
    assert decoded.semantic_claim_binding == _root(5)
    assert decoded.proof_tree_root == _root(6)
    assert decoded.semantic_root_kind is SettlementSemanticRootKindV1.VALUE_SUBTREE
    assert decoded.semantic_root == _root(7)
    assert decoded.dependency_manifest_root == _root(8)
    assert decoded.public_policy_hash == _root(9)
    assert decoded.economic_action_batch_commitment == _root(10)
    assert decoded.settlement_effect_plan_commitment == _root(11)
    assert decoded.economic_action_ids_root == _root(12)
    assert decoded.action_authorization_bindings_root == _root(13)
    assert decoded.authorization_grant_spends_root == _root(14)
    assert decoded.consumed_object_ids_root == _root(15)
    assert decoded.action_count == 17
    assert decoded.consumed_object_count == 19
    assert decoded.pre_state_root == _root(16)
    assert decoded.post_state_root == _root(17)
    assert decoded.cell_writes_root == _root(18)
    assert decoded.asset_effects_root == _root(19)
    assert decoded.messages_root == _root(20)
    assert decoded.carries_root == _root(21)
    assert decoded.rewards_root == _root(22)
    assert decoded.data_availability_certificate_root == _root(23)
    assert decoded.schedule_certificate_root == _root(24)
    assert decoded.carry_continuity_certificate_root == _root(25)
    assert decoded.settlement_certificate_id == derive_settlement_certificate_id_v1(
        _CERTIFICATE
    )
    assert decoded.certificate_commitment == _root(26)
    assert decoded.journal_sha256 == hashlib.sha256(raw).digest()


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (lambda value: b"BROKEN!!" + value[8:], "magic"),
        (
            lambda value: value[:8] + (2).to_bytes(2, "big") + value[10:],
            "version",
        ),
        (lambda value: value[:-1], "truncated"),
        (lambda value: value + b"x", "trailing"),
        (lambda value: _replace_u32(value, 10, len(value) - 1), "trailing"),
        (lambda value: _replace_u32(value, 10, len(value) + 1), "truncated"),
        (lambda value: _replace_u32(value, 14, 0), "certificate byte length"),
        (lambda value: _replace_u32(value, 18, 0), "effect-plan byte length"),
        (
            lambda value: _replace_u32(value, 18, MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 + 1),
            "effect-plan byte length",
        ),
        (lambda value: _replace_u32(value, 14, len(_CERTIFICATE) + 1), "length mismatch"),
    ],
)
def test_malformed_header_or_lengths_reject(
    mutation: object,
    message: str,
) -> None:
    mutate = mutation
    assert callable(mutate)
    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match=message):
        decode_exact_settlement_admission_journal_v1(mutate(_valid_frame()))


def test_inner_hash_mutations_reject_at_their_exact_boundary() -> None:
    raw = _valid_frame()
    certificate_offset = 22
    effect_plan_offset = certificate_offset + len(_CERTIFICATE)
    certificate_hash_offset = effect_plan_offset + len(_EFFECT_PLAN)
    plan_hash_offset = certificate_hash_offset + 32

    certificate_mutation = bytearray(raw)
    certificate_mutation[certificate_offset] ^= 1
    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="certificate SHA-256"):
        decode_exact_settlement_admission_journal_v1(bytes(certificate_mutation))

    plan_hash_mutation = bytearray(raw)
    plan_hash_mutation[plan_hash_offset] ^= 1
    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="effect-plan SHA-256"):
        decode_exact_settlement_admission_journal_v1(bytes(plan_hash_mutation))


def test_invalid_semantic_root_discriminator_rejects() -> None:
    raw = bytearray(_valid_frame())
    fixed_projection_start = 22 + len(_CERTIFICATE) + len(_EFFECT_PLAN)
    semantic_root_tag_offset = fixed_projection_start + 64 + 4 + 104 + 96
    raw[semantic_root_tag_offset] = 2

    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="discriminator"):
        decode_exact_settlement_admission_journal_v1(bytes(raw))


def test_mutated_certificate_identifier_rejects() -> None:
    raw = bytearray(_valid_frame())
    certificate_id_offset = len(raw) - 64
    raw[certificate_id_offset] ^= 1

    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="certificate ID"):
        decode_exact_settlement_admission_journal_v1(bytes(raw))


def test_type_empty_and_global_bound_reject_before_field_parsing() -> None:
    with pytest.raises(TypeError, match="exactly bytes"):
        decode_exact_settlement_admission_journal_v1(bytearray(_valid_frame()))
    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="empty"):
        decode_exact_settlement_admission_journal_v1(b"")
    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="too large"):
        decode_exact_settlement_admission_journal_v1(
            b"x" * (MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 + 1)
        )


def test_certificate_identifier_uses_exact_rust_domain_framing() -> None:
    domain = b"zenodex.zrpf.settlement_certificate_id.v1"
    expected = hashlib.sha256(
        len(domain).to_bytes(2, "big")
        + domain
        + len(_CERTIFICATE).to_bytes(4, "big")
        + _CERTIFICATE
    ).digest()
    assert derive_settlement_certificate_id_v1(_CERTIFICATE) == expected

    with pytest.raises(TypeError, match="exactly bytes"):
        derive_settlement_certificate_id_v1(bytearray(_CERTIFICATE))
    with pytest.raises(SettlementAdmissionJournalDecodeErrorV1, match="outside"):
        derive_settlement_certificate_id_v1(b"")
