"""Strict proof-neutral decoder for ``SettlementAdmissionJournalV1``.

This module mirrors the outer ``ZRPFSAV1`` fixed-width framing produced by the
Rust protocol crate.  It validates byte bounds, framing, embedded SHA-256
digests, the semantic-root discriminator, and the certificate identifier
derived from the exact certificate bytes.

The decoded value remains proof-neutral.  This module does not decode the
Postcard certificate or effect plan, authenticate a proof receipt, establish
that the duplicated projection agrees with the inner objects, or authorize a
ledger mutation.  Those checks belong to the governed Rust verifier and the
atomic admission boundary.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import IntEnum

SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1 = b"ZRPFSAV1"
SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1 = 1
SETTLEMENT_ADMISSION_FIXED_BYTES_V1 = 971
MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 = 1_024
MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 = 8 * 1024 * 1024
MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 = (
    SETTLEMENT_ADMISSION_FIXED_BYTES_V1
    + MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1
    + MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2
)

_SETTLEMENT_CERTIFICATE_ID_DOMAIN_V1 = b"zenodex.zrpf.settlement_certificate_id.v1"


class SettlementAdmissionJournalDecodeErrorV1(ValueError):
    """Stable fail-closed error for malformed V1 admission frames."""


class SettlementSemanticRootKindV1(IntEnum):
    """Closed discriminator used by the fixed semantic-root projection."""

    SEMANTIC_EPOCH = 0
    VALUE_SUBTREE = 1


@dataclass(frozen=True, slots=True)
class DecodedSettlementAdmissionJournalV1:
    """Exact byte strings and duplicated fixed fields from one V1 frame."""

    journal_version: int
    certificate_bytes: bytes
    effect_plan_bytes: bytes
    certificate_sha256: bytes
    effect_plan_sha256: bytes
    certificate_version: int
    effect_plan_version: int
    application_id: bytes
    chain_or_domain_id: bytes
    epoch_id: int
    semantic_profile_id: bytes
    semantic_journal_hash: bytes
    semantic_claim_binding: bytes
    proof_tree_root: bytes
    semantic_root_kind: SettlementSemanticRootKindV1
    semantic_root: bytes
    dependency_manifest_root: bytes
    public_policy_hash: bytes
    economic_action_batch_commitment: bytes
    settlement_effect_plan_commitment: bytes
    economic_action_ids_root: bytes
    action_authorization_bindings_root: bytes
    authorization_grant_spends_root: bytes
    consumed_object_ids_root: bytes
    action_count: int
    consumed_object_count: int
    pre_state_root: bytes
    post_state_root: bytes
    cell_writes_root: bytes
    asset_effects_root: bytes
    messages_root: bytes
    carries_root: bytes
    rewards_root: bytes
    data_availability_certificate_root: bytes
    schedule_certificate_root: bytes
    carry_continuity_certificate_root: bytes
    settlement_certificate_id: bytes
    certificate_commitment: bytes
    journal_sha256: bytes


def decode_exact_settlement_admission_journal_v1(
    raw: bytes,
) -> DecodedSettlementAdmissionJournalV1:
    """Decode one exact bounded V1 frame without granting proof authority."""

    _require_input_size(raw)
    reader = _Reader(raw)
    if reader.read_exact(8) != SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1:
        raise SettlementAdmissionJournalDecodeErrorV1("invalid settlement admission magic")
    journal_version = reader.read_u16()
    if journal_version != SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1:
        raise SettlementAdmissionJournalDecodeErrorV1(
            "invalid settlement admission journal version"
        )
    declared_total = reader.read_u32()
    if len(raw) > declared_total:
        raise SettlementAdmissionJournalDecodeErrorV1("trailing settlement admission bytes")
    if len(raw) < declared_total:
        raise SettlementAdmissionJournalDecodeErrorV1("truncated settlement admission frame")

    certificate_len = reader.read_u32()
    effect_plan_len = reader.read_u32()
    _require_inner_lengths(certificate_len, effect_plan_len)
    expected_total = SETTLEMENT_ADMISSION_FIXED_BYTES_V1 + certificate_len + effect_plan_len
    if declared_total != expected_total:
        raise SettlementAdmissionJournalDecodeErrorV1(
            "settlement admission frame length mismatch"
        )

    certificate_bytes = reader.read_exact(certificate_len)
    effect_plan_bytes = reader.read_exact(effect_plan_len)
    certificate_sha256 = reader.read_exact(32)
    if hashlib.sha256(certificate_bytes).digest() != certificate_sha256:
        raise SettlementAdmissionJournalDecodeErrorV1("certificate SHA-256 mismatch")
    effect_plan_sha256 = reader.read_exact(32)
    if hashlib.sha256(effect_plan_bytes).digest() != effect_plan_sha256:
        raise SettlementAdmissionJournalDecodeErrorV1("effect-plan SHA-256 mismatch")

    certificate_version = reader.read_u16()
    effect_plan_version = reader.read_u16()
    application_id = reader.read_exact(32)
    chain_or_domain_id = reader.read_exact(32)
    epoch_id = reader.read_u64()
    semantic_profile_id = reader.read_exact(32)
    semantic_journal_hash = reader.read_exact(32)
    semantic_claim_binding = reader.read_exact(32)
    proof_tree_root = reader.read_exact(32)
    semantic_root_kind = _decode_semantic_root_kind(reader.read_u8())
    semantic_root = reader.read_exact(32)
    dependency_manifest_root = reader.read_exact(32)
    public_policy_hash = reader.read_exact(32)
    economic_action_batch_commitment = reader.read_exact(32)
    settlement_effect_plan_commitment = reader.read_exact(32)
    economic_action_ids_root = reader.read_exact(32)
    action_authorization_bindings_root = reader.read_exact(32)
    authorization_grant_spends_root = reader.read_exact(32)
    consumed_object_ids_root = reader.read_exact(32)
    action_count = reader.read_u32()
    consumed_object_count = reader.read_u32()
    final_roots = tuple(reader.read_exact(32) for _ in range(12))
    reader.require_finished()

    settlement_certificate_id = final_roots[10]
    if settlement_certificate_id != derive_settlement_certificate_id_v1(certificate_bytes):
        raise SettlementAdmissionJournalDecodeErrorV1(
            "derived settlement certificate ID mismatch"
        )

    return DecodedSettlementAdmissionJournalV1(
        journal_version=journal_version,
        certificate_bytes=certificate_bytes,
        effect_plan_bytes=effect_plan_bytes,
        certificate_sha256=certificate_sha256,
        effect_plan_sha256=effect_plan_sha256,
        certificate_version=certificate_version,
        effect_plan_version=effect_plan_version,
        application_id=application_id,
        chain_or_domain_id=chain_or_domain_id,
        epoch_id=epoch_id,
        semantic_profile_id=semantic_profile_id,
        semantic_journal_hash=semantic_journal_hash,
        semantic_claim_binding=semantic_claim_binding,
        proof_tree_root=proof_tree_root,
        semantic_root_kind=semantic_root_kind,
        semantic_root=semantic_root,
        dependency_manifest_root=dependency_manifest_root,
        public_policy_hash=public_policy_hash,
        economic_action_batch_commitment=economic_action_batch_commitment,
        settlement_effect_plan_commitment=settlement_effect_plan_commitment,
        economic_action_ids_root=economic_action_ids_root,
        action_authorization_bindings_root=action_authorization_bindings_root,
        authorization_grant_spends_root=authorization_grant_spends_root,
        consumed_object_ids_root=consumed_object_ids_root,
        action_count=action_count,
        consumed_object_count=consumed_object_count,
        pre_state_root=final_roots[0],
        post_state_root=final_roots[1],
        cell_writes_root=final_roots[2],
        asset_effects_root=final_roots[3],
        messages_root=final_roots[4],
        carries_root=final_roots[5],
        rewards_root=final_roots[6],
        data_availability_certificate_root=final_roots[7],
        schedule_certificate_root=final_roots[8],
        carry_continuity_certificate_root=final_roots[9],
        settlement_certificate_id=settlement_certificate_id,
        certificate_commitment=final_roots[11],
        journal_sha256=hashlib.sha256(raw).digest(),
    )


def derive_settlement_certificate_id_v1(certificate_bytes: bytes) -> bytes:
    """Mirror the Rust domain-separated certificate identifier derivation."""

    if type(certificate_bytes) is not bytes:
        raise TypeError("certificate_bytes must be exactly bytes")
    certificate_len = len(certificate_bytes)
    if not 1 <= certificate_len <= MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1:
        raise SettlementAdmissionJournalDecodeErrorV1(
            "certificate byte length is outside the V1 bounds"
        )
    domain_len = len(_SETTLEMENT_CERTIFICATE_ID_DOMAIN_V1)
    preimage = (
        domain_len.to_bytes(2, "big")
        + _SETTLEMENT_CERTIFICATE_ID_DOMAIN_V1
        + certificate_len.to_bytes(4, "big")
        + certificate_bytes
    )
    return hashlib.sha256(preimage).digest()


def _require_input_size(raw: bytes) -> None:
    if type(raw) is not bytes:
        raise TypeError("settlement admission journal must be exactly bytes")
    if not raw:
        raise SettlementAdmissionJournalDecodeErrorV1("empty settlement admission frame")
    if len(raw) > MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1:
        raise SettlementAdmissionJournalDecodeErrorV1("settlement admission frame is too large")


def _require_inner_lengths(certificate_len: int, effect_plan_len: int) -> None:
    if not 1 <= certificate_len <= MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1:
        raise SettlementAdmissionJournalDecodeErrorV1("invalid certificate byte length")
    if not 1 <= effect_plan_len <= MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2:
        raise SettlementAdmissionJournalDecodeErrorV1("invalid effect-plan byte length")


def _decode_semantic_root_kind(value: int) -> SettlementSemanticRootKindV1:
    try:
        return SettlementSemanticRootKindV1(value)
    except ValueError as exc:
        raise SettlementAdmissionJournalDecodeErrorV1(
            "invalid settlement semantic-root discriminator"
        ) from exc


class _Reader:
    __slots__ = ("_offset", "_raw")

    def __init__(self, raw: bytes) -> None:
        self._raw = raw
        self._offset = 0

    def read_exact(self, length: int) -> bytes:
        end = self._offset + length
        value = self._raw[self._offset : end]
        if len(value) != length:
            raise SettlementAdmissionJournalDecodeErrorV1(
                "truncated settlement admission field"
            )
        self._offset = end
        return value

    def read_u8(self) -> int:
        return int.from_bytes(self.read_exact(1), "big")

    def read_u16(self) -> int:
        return int.from_bytes(self.read_exact(2), "big")

    def read_u32(self) -> int:
        return int.from_bytes(self.read_exact(4), "big")

    def read_u64(self) -> int:
        return int.from_bytes(self.read_exact(8), "big")

    def require_finished(self) -> None:
        if self._offset != len(self._raw):
            raise SettlementAdmissionJournalDecodeErrorV1(
                "trailing settlement admission fields"
            )
