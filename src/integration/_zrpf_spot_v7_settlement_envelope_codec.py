"""Canonical bounded codec and candidate projection for Spot V7 replay."""

from __future__ import annotations

import hashlib
import json
from typing import Any, NoReturn

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _candidate_action_authorization_bindings_root,
    _candidate_action_ids_root,
    _candidate_authorization_grant_spends_root,
    _candidate_consumed_object_ids_root,
    _derive_capability_commitment,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_output import (
    SpotV7CommittedOutputRejectV1,
)
from src.integration._zrpf_spot_v7_journal_projection import (
    _decode_spot_v7_semantic_journal_projection_v1,
    _DecodedSpotV7SemanticJournalProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    ENVELOPE_PROPOSAL_HASH_DOMAIN_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1,
    SpotV7SettlementEnvelopeReplayErrorV1,
)
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AssetEffectV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
)
from src.state.canonical import bounded_json_utf8_size

MAX_ENVELOPE_BYTES_V1 = 256 * 1_024
MAX_ENVELOPE_DEPTH_V1 = 12
MAX_ENVELOPE_ITEMS_V1 = 512
MAX_HEADER_OR_CONFIG_BYTES_V1 = 256 * 1_024
MAX_LEDGER_BODY_BYTES_V1 = 1 * 1_024 * 1_024
MAX_PRE_STATE_SNAPSHOT_BYTES_V1 = 24 * 1_024 * 1_024
MAX_PRE_STATE_SNAPSHOT_ITEMS_V1 = 500_000


def build_spot_v7_settlement_envelope_v1(settlement: object) -> dict[str, Any]:
    """Build the one exact body envelope for a sealed V7 candidate."""

    settlement_value = _require_settlement_capability(settlement)
    candidate = settlement_value._candidate_for_atomic_store()
    semantic = _semantic_projection(candidate)
    proposal = _candidate_proposal(candidate, semantic)
    proposal_hash = hash_v0(ENVELOPE_PROPOSAL_HASH_DOMAIN_V1, proposal)
    envelope = {
        "schema": SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1,
        "profile": SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
        "proposal": proposal,
        "expected_receipt": _receipt(
            candidate,
            proposal_hash=proposal_hash,
            accepted=True,
            reject_code=None,
        ),
    }
    encode_spot_v7_settlement_envelope_v1(envelope)
    return envelope


def encode_spot_v7_settlement_envelope_v1(envelope: object) -> bytes:
    """Encode bounded plain envelope data using canonical JSON bytes."""

    value = _snapshot_envelope(envelope)
    _require_outer_envelope_shape(value)
    encoded = canonical_json_bytes_v0(value)
    if not encoded or len(encoded) > MAX_ENVELOPE_BYTES_V1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_size")
    return encoded


def decode_exact_spot_v7_settlement_envelope_v1(raw: bytes) -> dict[str, Any]:
    """Decode only one exact canonical bounded envelope byte string."""

    if type(raw) is not bytes or not raw or len(raw) > MAX_ENVELOPE_BYTES_V1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_size")
    try:
        decoded = json.loads(
            raw,
            object_pairs_hook=_reject_duplicate_pairs,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
        )
    except (TypeError, ValueError, json.JSONDecodeError, RecursionError) as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("canonical_envelope") from exc
    if type(decoded) is not dict:
        raise SpotV7SettlementEnvelopeReplayErrorV1("canonical_envelope")
    try:
        encoded = encode_spot_v7_settlement_envelope_v1(decoded)
    except (TypeError, ValueError) as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("canonical_envelope") from exc
    if encoded != raw:
        raise SpotV7SettlementEnvelopeReplayErrorV1("canonical_envelope")
    return decoded


def _candidate_proposal(
    candidate: _SpotV7SettlementCandidateInputV1,
    semantic: _DecodedSpotV7SemanticJournalProjectionV1,
) -> dict[str, Any]:
    return {
        "application_id": candidate.application_id,
        "chain_or_domain_id": candidate.chain_or_domain_id,
        "epoch_id": candidate.epoch_id,
        "candidate_settlement_commitment": _derive_capability_commitment(candidate),
        "verified_program_id": candidate.verified_program_id,
        "verified_profile_id": candidate.verified_profile_id,
        "verified_program_manifest_root": candidate.verified_program_manifest_root,
        "source_child_claim_binding": _hex(semantic.source_child_claim_binding),
        "source_child_journal_sha256": _hex(semantic.source_child_journal_sha256),
        "data_availability_certificate_root": _hex(semantic.data_availability_certificate_root),
        "data_root": _hex(semantic.data_root),
        "proof_receipt_sha256": _sha256(candidate.exact_v7_receipt_bytes),
        "proof_journal_sha256": _sha256(candidate.exact_v7_journal_bytes),
        "firecracker_execution_record_sha256": _sha256(
            candidate.exact_firecracker_execution_record_bytes
        ),
        "firecracker_output_sha256": _sha256(candidate.exact_firecracker_output_bytes),
        "settlement_effect_plan_commitment": _hex(semantic.settlement_effect_plan_commitment),
        "settlement_effect_plan_bytes_sha256": _hex(semantic.settlement_effect_plan_bytes_sha256),
        "pre_state_root": _hex(semantic.pre_state_root),
        "post_state_root": _hex(semantic.post_state_root),
        "sender_pubkey": _hex(semantic.sender_pubkey),
        "ingress_nonce": semantic.ingress_nonce,
        "economic_action_id": _hex(semantic.economic_action_id),
        "action_ids_root": _hex(semantic.action_ids_root),
        "action_authorization_bindings_root": (
            _candidate_action_authorization_bindings_root(candidate)
        ),
        "authorization_grant_spends_root": (_candidate_authorization_grant_spends_root(candidate)),
        "authorization_nullifier": candidate.authorization_nullifier,
        "authorization_grant_spend_nullifier": (candidate.authorization_grant_spend_nullifier),
        "consumed_object_ids": list(candidate.consumed_object_ids),
        "consumed_object_ids_root": _candidate_consumed_object_ids_root(candidate),
        "cell_transitions_root": _hex(semantic.cell_transitions_root),
        "cell_transitions": [_transition_document(row) for row in candidate.cell_transitions],
        "asset_effects": [_asset_effect_document(row) for row in candidate.asset_effects],
    }


def _semantic_projection(
    candidate: _SpotV7SettlementCandidateInputV1,
) -> _DecodedSpotV7SemanticJournalProjectionV1:
    try:
        semantic = _decode_spot_v7_semantic_journal_projection_v1(candidate.exact_v7_journal_bytes)
    except SpotV7CommittedOutputRejectV1 as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("candidate_journal") from exc
    associations = (
        (_hex(semantic.pre_state_root), candidate.pre_state_root),
        (_hex(semantic.post_state_root), candidate.post_state_root),
        (_hex(semantic.source_child_claim_binding), candidate.source_child_claim_binding),
        (_hex(semantic.source_child_journal_sha256), candidate.source_child_journal_sha256),
        (
            _hex(semantic.data_availability_certificate_root),
            candidate.data_availability_certificate_root,
        ),
        (_hex(semantic.data_root), candidate.data_root),
        (
            _hex(semantic.settlement_effect_plan_commitment),
            candidate.settlement_effect_plan_commitment,
        ),
        (
            _hex(semantic.settlement_effect_plan_bytes_sha256),
            _sha256(candidate.exact_plan_b_bytes),
        ),
        (_hex(semantic.cell_transitions_root), candidate.cell_transitions_root),
        (_hex(semantic.economic_action_id), candidate.economic_action_id),
        (_hex(semantic.action_ids_root), _candidate_action_ids_root(candidate)),
    )
    if any(actual != expected for actual, expected in associations):
        raise SpotV7SettlementEnvelopeReplayErrorV1("candidate_journal")
    return semantic


def _receipt(
    candidate: _SpotV7SettlementCandidateInputV1,
    *,
    proposal_hash: str,
    accepted: bool,
    reject_code: str | None,
) -> dict[str, Any]:
    if type(accepted) is not bool:
        raise TypeError("receipt accepted must be bool")
    if accepted != (reject_code is None):
        raise ValueError("receipt acceptance and reject code disagree")
    return {
        "schema": SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1,
        "profile": SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
        "envelope_proposal_hash": proposal_hash,
        "candidate_settlement_commitment": _derive_capability_commitment(candidate),
        "proof_journal_sha256": _sha256(candidate.exact_v7_journal_bytes),
        "settlement_effect_plan_commitment": candidate.settlement_effect_plan_commitment,
        "economic_action_id": candidate.economic_action_id,
        "accepted": accepted,
        "reject_code": reject_code,
        "state_changed": accepted and candidate.pre_state_root != candidate.post_state_root,
        "pre_state_root": candidate.pre_state_root,
        "post_state_root": candidate.post_state_root if accepted else candidate.pre_state_root,
    }


def _transition_document(row: SpotV7CellTransitionV1) -> dict[str, Any]:
    if type(row) is not SpotV7CellTransitionV1:
        raise TypeError("candidate transition must be exact SpotV7CellTransitionV1")
    return {
        "role": "debit" if row.role is SpotV7CellRoleV1.DEBIT else "credit",
        "pre": _opening_document(row.pre),
        "post": _opening_document(row.post),
        "amount_atoms": row.amount_atoms,
        "commitment": row.commitment,
    }


def _opening_document(row: SpotV7CellOpeningV1) -> dict[str, Any]:
    if type(row) is not SpotV7CellOpeningV1:
        raise TypeError("candidate opening must be exact SpotV7CellOpeningV1")
    return {
        "kind": (
            "account_balance" if row.kind is SpotV7CellKindV1.ACCOUNT_BALANCE else "pool_reserve"
        ),
        "subject_id": row.subject_id,
        "asset_id": row.asset_id,
        "atoms": row.atoms,
        "cell_key": row.cell_key,
        "value_hash": row.value_hash,
    }


def _asset_effect_document(row: SpotV7AssetEffectV1) -> dict[str, Any]:
    if type(row) is not SpotV7AssetEffectV1:
        raise TypeError("candidate effect must be exact SpotV7AssetEffectV1")
    return {
        "economic_action_id": row.economic_action_id,
        "asset_id": row.asset_id,
        "amount_atoms": row.amount_atoms,
        "debit_atoms": row.debit_atoms,
        "credit_atoms": row.credit_atoms,
        "effect_id": row.effect_id,
    }


def _snapshot_exact_dict(
    value: object,
    *,
    name: str,
    max_bytes: int,
    max_items: int,
    reject_code: str,
) -> dict[str, Any]:
    try:
        if type(value) is not dict:
            raise TypeError(f"{name} must be an exact dict")
        bounded_json_utf8_size(
            value,
            max_bytes=max_bytes,
            max_depth=MAX_ENVELOPE_DEPTH_V1,
            max_items=max_items,
        )
        _require_plain_json(value, name=name, depth=0)
        canonical = canonical_json_bytes_v0(value)
        decoded = json.loads(canonical)
        if type(decoded) is not dict or canonical_json_bytes_v0(decoded) != canonical:
            raise ValueError(f"{name} is not an exact canonical JSON object")
    except SpotV7SettlementEnvelopeReplayErrorV1:
        raise
    except (TypeError, ValueError, OverflowError, RecursionError) as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1(reject_code) from exc
    return decoded


def _snapshot_envelope(value: object) -> dict[str, Any]:
    return _snapshot_exact_dict(
        value,
        name="settlement envelope",
        max_bytes=MAX_ENVELOPE_BYTES_V1,
        max_items=MAX_ENVELOPE_ITEMS_V1,
        reject_code="envelope_size",
    )


def _require_outer_envelope_shape(value: dict[str, Any]) -> None:
    if set(value) != {"schema", "profile", "proposal", "expected_receipt"}:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_keys")
    if value["schema"] != SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_schema")
    if value["profile"] != SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_profile")
    if type(value["proposal"]) is not dict or type(value["expected_receipt"]) is not dict:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_shape")


def _require_plain_json(value: object, *, name: str, depth: int) -> None:
    if depth > MAX_ENVELOPE_DEPTH_V1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_depth")
    if value is None or type(value) in {bool, int, str}:
        return
    if type(value) is list:
        for item in value:
            _require_plain_json(item, name=name, depth=depth + 1)
        return
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise TypeError(f"{name} keys must be exact strings")
        for item in value.values():
            _require_plain_json(item, name=name, depth=depth + 1)
        return
    raise TypeError(f"{name} contains unsupported value type {type(value).__name__}")


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate decoded JSON key")
        output[key] = value
    return output


def _reject_json_float(_value: str) -> NoReturn:
    raise ValueError("JSON floats are forbidden")


def _reject_json_constant(_value: str) -> NoReturn:
    raise ValueError("non-finite JSON constants are forbidden")


def _sha256(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _hex(value: bytes) -> str:
    return "0x" + value.hex()
