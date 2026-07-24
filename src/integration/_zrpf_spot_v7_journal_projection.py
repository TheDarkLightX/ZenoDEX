"""Exact nested Spot V7 journal projection for state replay."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from src.integration._zrpf_spot_v7_firecracker_output import (
    _V7_EFFECT_BINDING_JOURNAL_BYTES_V1,
    _V7_JOURNAL_FIXED_FIELD_COUNT_V1,
    _V7_JOURNAL_HEADER_BYTES_V1,
    _V7_SEMANTIC_JOURNAL_BYTES_V1,
    SpotV7CommittedOutputRejectV1,
    _decode_effect_binding_journal_v1,
    _decode_spot_v7_journal_v1,
    _read_nonzero_bytes32_fields,
)
from src.integration.zeno_ledger_spot_state_domain_bridge_v1 import (
    RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1,
    RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5,
)

_GOVERNED_COMPATIBILITY_PROFILE_ID_V1 = bytes.fromhex(
    RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1[2:]
)
_GOVERNED_STATE_ROOT_SCHEME_ID_V5 = bytes.fromhex(RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5[2:])


@dataclass(frozen=True, slots=True)
class _DecodedSpotV7SemanticJournalProjectionV1:
    """Exact fields retained by the nested semantic and binding journals."""

    compatibility_profile_id: bytes
    state_root_scheme_id: bytes
    source_pre_app_hash: bytes
    source_post_app_hash: bytes
    source_pre_nonce_root: bytes
    source_post_nonce_root: bytes
    pre_state_root: bytes
    post_state_root: bytes
    sender_pubkey: bytes
    ingress_nonce: int
    source_child_claim_binding: bytes
    source_child_journal_sha256: bytes
    data_availability_certificate_root: bytes
    data_root: bytes
    settlement_effect_plan_commitment: bytes
    settlement_effect_plan_bytes_sha256: bytes
    cell_transitions_root: bytes
    economic_action_id: bytes
    action_ids_root: bytes


@dataclass(frozen=True, slots=True)
class _DecodedExactSpotV7StateSemanticJournalV1:
    compatibility_profile_id: bytes
    state_root_scheme_id: bytes
    source_pre_app_hash: bytes
    source_post_app_hash: bytes
    source_pre_nonce_root: bytes
    source_post_nonce_root: bytes
    pre_state_root: bytes
    post_state_root: bytes
    sender_pubkey: bytes
    ingress_nonce: int


def _decode_spot_v7_semantic_journal_projection_v1(
    journal: bytes,
) -> _DecodedSpotV7SemanticJournalProjectionV1:
    """Decode the exact nested projection after full V7 journal checks."""

    plan, journal_fixed, binding_fixed, _host_input_length = _decode_spot_v7_journal_v1(journal)
    semantic_offset = _V7_JOURNAL_HEADER_BYTES_V1 + 32 * _V7_JOURNAL_FIXED_FIELD_COUNT_V1
    semantic = journal[semantic_offset : semantic_offset + _V7_SEMANTIC_JOURNAL_BYTES_V1]
    state = _decode_exact_state_semantic_journal_v1(semantic)
    binding_offset = semantic_offset + _V7_SEMANTIC_JOURNAL_BYTES_V1
    binding = journal[binding_offset : binding_offset + _V7_EFFECT_BINDING_JOURNAL_BYTES_V1]
    if _decode_effect_binding_journal_v1(binding) != binding_fixed:
        raise SpotV7CommittedOutputRejectV1("v7_semantic_binding")
    governed_profile = (
        (state.compatibility_profile_id, _GOVERNED_COMPATIBILITY_PROFILE_ID_V1),
        (state.state_root_scheme_id, _GOVERNED_STATE_ROOT_SCHEME_ID_V5),
    )
    if any(actual != expected for actual, expected in governed_profile):
        raise SpotV7CommittedOutputRejectV1("v7_semantic_profile")
    associations = (
        (state.compatibility_profile_id, binding_fixed[0]),
        (state.state_root_scheme_id, binding_fixed[1]),
        (state.pre_state_root, binding_fixed[6]),
        (state.post_state_root, binding_fixed[7]),
    )
    if any(actual != expected for actual, expected in associations):
        raise SpotV7CommittedOutputRejectV1("v7_semantic_binding")
    return _DecodedSpotV7SemanticJournalProjectionV1(
        compatibility_profile_id=state.compatibility_profile_id,
        state_root_scheme_id=state.state_root_scheme_id,
        source_pre_app_hash=state.source_pre_app_hash,
        source_post_app_hash=state.source_post_app_hash,
        source_pre_nonce_root=state.source_pre_nonce_root,
        source_post_nonce_root=state.source_post_nonce_root,
        pre_state_root=state.pre_state_root,
        post_state_root=state.post_state_root,
        sender_pubkey=state.sender_pubkey,
        ingress_nonce=state.ingress_nonce,
        source_child_claim_binding=journal_fixed[2],
        source_child_journal_sha256=journal_fixed[3],
        data_availability_certificate_root=journal_fixed[4],
        data_root=journal_fixed[5],
        settlement_effect_plan_commitment=binding_fixed[4],
        settlement_effect_plan_bytes_sha256=hashlib.sha256(plan).digest(),
        cell_transitions_root=binding_fixed[5],
        economic_action_id=binding_fixed[8],
        action_ids_root=journal_fixed[12],
    )


def _decode_exact_state_semantic_journal_v1(
    semantic: bytes,
) -> _DecodedExactSpotV7StateSemanticJournalV1:
    if type(semantic) is not bytes or len(semantic) != _V7_SEMANTIC_JOURNAL_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("v7_semantic_journal_length")
    if int.from_bytes(semantic[:2], "big") != 1:
        raise SpotV7CommittedOutputRejectV1("v7_semantic_journal_version")
    commitments = _read_nonzero_bytes32_fields(
        semantic,
        offset=2,
        count=8,
        code="v7_semantic_journal_field",
    )
    sender_offset = 2 + 8 * 32
    sender = semantic[sender_offset : sender_offset + 48]
    ingress_nonce = int.from_bytes(semantic[sender_offset + 48 :], "big")
    if len(sender) != 48 or ingress_nonce == 0:
        raise SpotV7CommittedOutputRejectV1("v7_semantic_journal_field")
    return _DecodedExactSpotV7StateSemanticJournalV1(
        compatibility_profile_id=commitments[0],
        state_root_scheme_id=commitments[1],
        source_pre_app_hash=commitments[2],
        source_post_app_hash=commitments[3],
        source_pre_nonce_root=commitments[4],
        source_post_nonce_root=commitments[5],
        pre_state_root=commitments[6],
        post_state_root=commitments[7],
        sender_pubkey=sender,
        ingress_nonce=ingress_nonce,
    )
