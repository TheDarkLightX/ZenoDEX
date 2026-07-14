"""Bounded plain-data contract for the Spot V7 ZenoLedger finality adapter.

This module owns deterministic input snapshotting and policy identity
derivation.  It does not authenticate signatures or mint authority-bearing
capabilities.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Final, cast

from src.integration._zrpf_spot_v7_settlement_envelope_codec import (
    MAX_ENVELOPE_BYTES_V1,
    MAX_ENVELOPE_DEPTH_V1,
    MAX_ENVELOPE_ITEMS_V1,
    MAX_HEADER_OR_CONFIG_BYTES_V1,
    MAX_LEDGER_BODY_BYTES_V1,
    MAX_PRE_STATE_SNAPSHOT_BYTES_V1,
    MAX_PRE_STATE_SNAPSHOT_ITEMS_V1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    ENVELOPE_PROPOSAL_HASH_DOMAIN_V1,
    ENVELOPE_RECEIPT_HASH_DOMAIN_V1,
    SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1,
    SPOT_V7_SETTLEMENT_REPLAY_MATERIAL_ROOT_DOMAIN_V2,
    SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_PROFILE_V2,
    SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V2,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_contract import (
    MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1,
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1,
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1,
    SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1,
    SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1,
)
from src.integration.zeno_ledger_live_quorum_v0 import (
    LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0,
)
from src.integration.zeno_ledger_replay import (
    REPLAY_ENGINE_CONFIG_PROFILE,
    REPLAY_ENGINE_CONFIG_SCHEMA,
)
from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
)
from src.integration.zeno_ledger_signer_registry import SIGNER_REGISTRY_SCHEMA_V0
from src.integration.zeno_ledger_spot_state_domain_bridge_v1 import (
    RESTRICTED_SPOT_STATE_DOMAIN_BRIDGE_SCHEMA_V1,
    RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1,
    RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5,
)
from src.integration.zeno_ledger_v0 import (
    APP_HASH_ROOT_FIELDS_V0,
    BODY_SCHEMA_V0,
    CHECKPOINT_SCHEMA_V0,
    HEADER_SCHEMA_V0,
    TX_RECEIPT_SCHEMA_V0,
    canonical_json_bytes_v0,
    hash_v0,
)
from src.integration.zeno_ledger_validator_schedule_v0 import (
    MAX_SCHEDULED_VALIDATORS_V1,
    SCHEDULE_MODE_V0,
    SCHEDULED_HEADER_ADMISSION_SCHEMA_V0,
    SCHEDULED_VALIDATOR_ENTRY_HASH_DOMAIN_V1,
    SCHEDULED_VALIDATOR_SET_HASH_DOMAIN_V1,
    SCHEDULED_VALIDATOR_SET_SCHEMA_V1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    _hash_bytes,
    _require_uint,
    _root_bytes_allow_zero,
)
from src.state.canonical import bounded_json_utf8_size

SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2: Final = (
    "zenodex/zrpf/spot_v7/zeno_ledger_checkpoint_finality_evidence/v2"
)
SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3: Final = (
    "zenodex/zrpf/spot_v7/zeno_ledger_checkpoint_finality_evidence/v3"
)
SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1: Final = (
    "zenodex/zrpf/spot_v7/zeno_ledger_proposer_authorship_admission/v1"
)

_FINALITY_NETWORK_DOMAIN_V1: Final = "zrpf_spot_v7_zeno_ledger_finality_network_v1"
_FINALITY_PROTOCOL_DOMAIN_V2: Final = "zrpf_spot_v7_zeno_ledger_finality_protocol_v2"
_FINALITY_PROTOCOL_DOMAIN_V3: Final = "zrpf_spot_v7_zeno_ledger_finality_protocol_v3"
_EXTERNAL_FINALITY_POLICY_DOMAIN_V2: Final = "zrpf_spot_v7_zeno_ledger_external_finality_policy_v2"
_PROPOSER_AUTHORSHIP_PAYLOAD_DOMAIN_V1: Final = (
    "zrpf_spot_v7_zeno_ledger_proposer_authorship_payload_v1"
)
_MAX_FINALITY_INPUT_BYTES_V1: Final = 1 * 1_024 * 1_024
_MAX_FINALITY_INPUT_DEPTH_V1: Final = 64
_MAX_FINALITY_INPUT_ITEMS_V1: Final = 32_768
_MAX_FINALITY_STRING_BYTES_V1: Final = 1 * 1_024 * 1_024
_MAX_FINALITY_QUORUM_SIGNERS_V1: Final = 256
_ZERO_ROOT: Final = "0x" + "00" * 32


class SpotV7ZenoLedgerFinalityBindingErrorV1(ValueError):
    """Stable fail-closed binding error before private capability minting."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_ZENO_LEDGER_FINALITY_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class ZenoLedgerCheckpointFinalityCursorV1:
    """Proposed prior application checkpoint; durable store CAS remains final."""

    sequence: int
    checkpoint_hash: str

    def __post_init__(self) -> None:
        _require_uint(self.sequence, name="checkpoint cursor sequence", maximum=MAX_U64)
        _root_bytes_allow_zero(self.checkpoint_hash, name="checkpoint cursor hash")


@dataclass(frozen=True, slots=True)
class _FinalityInputSnapshotV1:
    header: dict[str, Any]
    checkpoint: dict[str, Any]
    validator_set: dict[str, Any]
    proposer_id: str
    proposer_key_id: str
    proposer_envelope: dict[str, Any]
    registry: dict[str, Any]
    envelopes: tuple[dict[str, Any], ...]


def derive_zeno_ledger_finality_network_id_v1(chain_id: str) -> str:
    """Derive the policy identity for one exact ZenoLedger chain."""

    return hash_v0(
        _FINALITY_NETWORK_DOMAIN_V1,
        {"chain_id": _require_nonempty_string(chain_id, name="chain_id")},
    )


def derive_zeno_ledger_finality_protocol_id_v2() -> str:
    """Derive the fixed protocol identity for this adapter version."""

    return hash_v0(
        _FINALITY_PROTOCOL_DOMAIN_V2,
        {
            "checkpoint_schema": CHECKPOINT_SCHEMA_V0,
            "header_schema": HEADER_SCHEMA_V0,
            "live_quorum_schema": LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0,
            "signature_algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
            "signer_registry_schema": SIGNER_REGISTRY_SCHEMA_V0,
            "scheduled_validator_set_schema": SCHEDULED_VALIDATOR_SET_SCHEMA_V1,
            "scheduled_validator_set_hash_domain": (
                SCHEDULED_VALIDATOR_SET_HASH_DOMAIN_V1
            ),
            "scheduled_validator_entry_hash_domain": (
                SCHEDULED_VALIDATOR_ENTRY_HASH_DOMAIN_V1
            ),
            "maximum_scheduled_validators": MAX_SCHEDULED_VALIDATORS_V1,
            "scheduled_header_admission_schema": SCHEDULED_HEADER_ADMISSION_SCHEMA_V0,
            "validator_schedule_mode": SCHEDULE_MODE_V0,
            "proposer_authorship_schema": (
                SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1
            ),
            "proposer_signature_payload_kind": "checkpoint",
            "proposer_signature_payload_domain": _PROPOSER_AUTHORSHIP_PAYLOAD_DOMAIN_V1,
            "proposer_signature_required": True,
            "replay_observation_schema": (
                SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1
            ),
            "replay_observation_profile": (
                SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1
            ),
            "replay_engine_config_schema": REPLAY_ENGINE_CONFIG_SCHEMA,
            "replay_engine_config_profile": REPLAY_ENGINE_CONFIG_PROFILE,
            "replay_config_document_root_domain": (
                SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1
            ),
            "replayed_body_schema": BODY_SCHEMA_V0,
            "replayed_transaction_receipt_schema": TX_RECEIPT_SCHEMA_V0,
            "replayed_receipts_root_domain": (
                SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1
            ),
            "replayed_rejections_root_domain": (
                SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1
            ),
            "committed_proof_receipts_root_domain": (
                SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1
            ),
            "body_proof_receipt_projection_schema": (
                SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1
            ),
            "body_proof_receipt_projection_count": (
                SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1
            ),
            "maximum_replayed_receipts": (
                MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1
            ),
            "body_settlement_envelopes_required_empty": True,
            "app_hash_domain": "app_hash_v0",
            "app_hash_root_fields": list(APP_HASH_ROOT_FIELDS_V0),
        },
    )


def derive_zeno_ledger_finality_protocol_id_v3() -> str:
    """Bind finality to exact singleton Spot V7 settlement-envelope replay."""

    return hash_v0(
        _FINALITY_PROTOCOL_DOMAIN_V3,
        {
            "finality_evidence_schema": SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3,
            "proof_neutral_checkpoint_certificate_version": 2,
            "checkpoint_schema": CHECKPOINT_SCHEMA_V0,
            "header_schema": HEADER_SCHEMA_V0,
            "live_quorum_schema": LIVE_CHECKPOINT_QUORUM_ADMISSION_SCHEMA_V0,
            "signature_algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
            "signer_registry_schema": SIGNER_REGISTRY_SCHEMA_V0,
            "scheduled_validator_set_schema": SCHEDULED_VALIDATOR_SET_SCHEMA_V1,
            "scheduled_validator_set_hash_domain": (
                SCHEDULED_VALIDATOR_SET_HASH_DOMAIN_V1
            ),
            "scheduled_validator_entry_hash_domain": (
                SCHEDULED_VALIDATOR_ENTRY_HASH_DOMAIN_V1
            ),
            "maximum_scheduled_validators": MAX_SCHEDULED_VALIDATORS_V1,
            "scheduled_header_admission_schema": SCHEDULED_HEADER_ADMISSION_SCHEMA_V0,
            "validator_schedule_mode": SCHEDULE_MODE_V0,
            "proposer_authorship_schema": (
                SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1
            ),
            "proposer_signature_payload_kind": "checkpoint",
            "proposer_signature_payload_domain": _PROPOSER_AUTHORSHIP_PAYLOAD_DOMAIN_V1,
            "proposer_signature_required": True,
            "settlement_replay_observation_schema": (
                SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V2
            ),
            "settlement_replay_observation_profile": (
                SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_PROFILE_V2
            ),
            "settlement_replay_material_root_domain": (
                SPOT_V7_SETTLEMENT_REPLAY_MATERIAL_ROOT_DOMAIN_V2
            ),
            "settlement_envelope_schema": SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1,
            "settlement_envelope_profile": SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
            "settlement_envelope_receipt_schema": (
                SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1
            ),
            "settlement_envelope_proposal_hash_domain": (
                ENVELOPE_PROPOSAL_HASH_DOMAIN_V1
            ),
            "settlement_envelope_receipt_hash_domain": ENVELOPE_RECEIPT_HASH_DOMAIN_V1,
            "settlement_envelope_effect_ids_root_domain": (
                SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1
            ),
            "replay_engine_config_schema": REPLAY_ENGINE_CONFIG_SCHEMA,
            "replay_engine_config_profile": REPLAY_ENGINE_CONFIG_PROFILE,
            "replayed_body_schema": BODY_SCHEMA_V0,
            "body_proof_receipt_projection_schema": (
                SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1
            ),
            "body_proof_receipt_projection_count": (
                SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1
            ),
            "body_transactions_required_empty": True,
            "body_settlement_envelope_count": 1,
            "body_rejection_receipts_required_empty": True,
            "parent_rule": "zero_root_without_parent_else_exact_parent_header_hash",
            "maximum_envelope_bytes": MAX_ENVELOPE_BYTES_V1,
            "maximum_envelope_depth": MAX_ENVELOPE_DEPTH_V1,
            "maximum_envelope_items": MAX_ENVELOPE_ITEMS_V1,
            "maximum_header_or_config_bytes": MAX_HEADER_OR_CONFIG_BYTES_V1,
            "maximum_ledger_body_bytes": MAX_LEDGER_BODY_BYTES_V1,
            "maximum_pre_state_snapshot_bytes": MAX_PRE_STATE_SNAPSHOT_BYTES_V1,
            "maximum_pre_state_snapshot_items": MAX_PRE_STATE_SNAPSHOT_ITEMS_V1,
            "state_domain_bridge_schema": RESTRICTED_SPOT_STATE_DOMAIN_BRIDGE_SCHEMA_V1,
            "state_domain_compatibility_profile": (
                RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1
            ),
            "state_root_scheme": RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5,
            "app_hash_domain": "app_hash_v0",
            "app_hash_root_fields": list(APP_HASH_ROOT_FIELDS_V0),
        },
    )


def derive_zeno_ledger_external_finality_policy_hash_v2(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
) -> str:
    """Bind chain config, scheduled authorship, and strict quorum policy."""

    return hash_v0(
        _EXTERNAL_FINALITY_POLICY_DOMAIN_V2,
        {
            "chain_id": _require_nonempty_string(chain_id, name="chain_id"),
            "config_digest": _require_hash(config_digest, name="config_digest"),
            "sequencer_set_hash": _require_hash(
                sequencer_set_hash,
                name="sequencer_set_hash",
            ),
            "checkpoint_signatures_are_external": True,
            "embedded_signature_set_required_empty": True,
            "quorum_rule": "strictly_more_than_two_thirds_active_weight",
            "signature_algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
            "scheduled_proposer_signature_required": True,
            "scheduled_proposer_signature_payload_kind": "checkpoint",
            "scheduled_proposer_signature_payload_domain": (_PROPOSER_AUTHORSHIP_PAYLOAD_DOMAIN_V1),
        },
    )


def derive_zeno_ledger_proposer_authorship_payload_hash_v1(
    *,
    chain_id: str,
    height: int,
    header_hash: str,
    validator_set_hash: str,
    duty_hash: str,
) -> str:
    """Purpose-separate scheduled authorship from checkpoint quorum votes."""

    return hash_v0(
        _PROPOSER_AUTHORSHIP_PAYLOAD_DOMAIN_V1,
        {
            "chain_id": _require_nonempty_string(chain_id, name="chain_id"),
            "height": _require_uint(height, name="height", maximum=MAX_U64),
            "header_hash": _require_hash(header_hash, name="header_hash"),
            "validator_set_hash": _require_hash(
                validator_set_hash,
                name="validator_set_hash",
            ),
            "duty_hash": _require_hash(duty_hash, name="duty_hash"),
        },
    )


def _snapshot_inputs(
    *,
    header: object,
    checkpoint: object,
    validator_set: object,
    proposer_id: object,
    proposer_key_id: object,
    proposer_envelope: object,
    registry: object,
    envelopes: object,
) -> _FinalityInputSnapshotV1:
    header_value = _snapshot_plain_dict(header, name="header")
    checkpoint_value = _snapshot_plain_dict(checkpoint, name="checkpoint")
    validator_set_value = _snapshot_plain_dict(validator_set, name="validator_set")
    proposer_id_value = _require_nonempty_string(proposer_id, name="proposer_id")
    proposer_key_id_value = _require_nonempty_string(
        proposer_key_id,
        name="proposer_key_id",
    )
    proposer_envelope_value = _snapshot_plain_dict(
        proposer_envelope,
        name="proposer_envelope",
    )
    registry_value = _snapshot_plain_dict(registry, name="registry")
    if type(envelopes) is not tuple:
        raise TypeError("envelopes must be an exact tuple")
    if not envelopes or len(envelopes) > _MAX_FINALITY_QUORUM_SIGNERS_V1:
        raise ValueError("envelopes count is outside the governed bound")
    envelope_values = tuple(
        _snapshot_plain_dict(value, name=f"envelopes[{index}]")
        for index, value in enumerate(envelopes)
    )
    envelope_values = tuple(sorted(envelope_values, key=_envelope_order_key))
    _require_bounded_canonical_json(
        {
            "header": header_value,
            "checkpoint": checkpoint_value,
            "validator_set": validator_set_value,
            "proposer_id": proposer_id_value,
            "proposer_key_id": proposer_key_id_value,
            "proposer_envelope": proposer_envelope_value,
            "registry": registry_value,
            "envelopes": envelope_values,
        },
        name="checkpoint finality input",
    )
    return _FinalityInputSnapshotV1(
        header=header_value,
        checkpoint=checkpoint_value,
        validator_set=validator_set_value,
        proposer_id=proposer_id_value,
        proposer_key_id=proposer_key_id_value,
        proposer_envelope=proposer_envelope_value,
        registry=registry_value,
        envelopes=envelope_values,
    )


def _snapshot_plain_dict(value: object, *, name: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise TypeError(f"{name} must be an exact dict")
    encoded = _require_bounded_canonical_json(value, name=name)
    decoded = json.loads(encoded)
    if type(decoded) is not dict:
        raise TypeError(f"{name} did not decode to an exact dict")
    return decoded


def _require_bounded_canonical_json(value: object, *, name: str) -> bytes:
    _require_bounded_plain_json_tree(value, name=name)
    bounded_json_utf8_size(
        value,
        max_bytes=_MAX_FINALITY_INPUT_BYTES_V1,
        max_depth=_MAX_FINALITY_INPUT_DEPTH_V1 + 1,
        max_items=_MAX_FINALITY_INPUT_ITEMS_V1,
    )
    encoded = canonical_json_bytes_v0(value)
    if not encoded or len(encoded) > _MAX_FINALITY_INPUT_BYTES_V1:
        raise ValueError(f"{name} exceeds the governed canonical byte bound")
    return encoded


def _require_bounded_plain_json_tree(value: object, *, name: str) -> None:
    """Reject hostile depth, width, aliases, and primitives before JSON recursion."""

    pending: list[tuple[object, int]] = [(value, 0)]
    seen_containers: set[int] = set()
    visited = 0
    while pending:
        current, depth = pending.pop()
        visited += 1
        if visited > _MAX_FINALITY_INPUT_ITEMS_V1:
            raise ValueError(f"{name} exceeds the governed item bound")
        if depth > _MAX_FINALITY_INPUT_DEPTH_V1:
            raise ValueError(f"{name} exceeds the governed maximum depth")
        if type(current) is dict:
            _require_new_container(current, seen_containers, name=name)
            if visited + len(pending) + len(current) > _MAX_FINALITY_INPUT_ITEMS_V1:
                raise ValueError(f"{name} exceeds the governed item bound")
            for key, child in current.items():
                if type(key) is not str:
                    raise TypeError(f"{name} contains a non-string object key")
                _require_bounded_string(key, name=f"{name} object key")
                pending.append((child, depth + 1))
            continue
        if type(current) in (list, tuple):
            _require_new_container(current, seen_containers, name=name)
            children = cast(list[object] | tuple[object, ...], current)
            if visited + len(pending) + len(children) > _MAX_FINALITY_INPUT_ITEMS_V1:
                raise ValueError(f"{name} exceeds the governed item bound")
            pending.extend((child, depth + 1) for child in children)
            continue
        if type(current) is str:
            _require_bounded_string(current, name=f"{name} string")
            continue
        if type(current) is int:
            if current < -MAX_U64 or current > MAX_U64:
                raise ValueError(f"{name} integer exceeds the governed width")
            continue
        if current is None or type(current) is bool:
            continue
        raise TypeError(f"{name} contains a non-JSON value")


def _require_new_container(
    value: object,
    seen_containers: set[int],
    *,
    name: str,
) -> None:
    identity = id(value)
    if identity in seen_containers:
        raise ValueError(f"{name} contains a cycle or repeated container alias")
    seen_containers.add(identity)


def _require_bounded_string(value: str, *, name: str) -> None:
    try:
        encoded_length = len(value.encode("utf-8"))
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} is not valid UTF-8") from exc
    if encoded_length > _MAX_FINALITY_STRING_BYTES_V1:
        raise ValueError(f"{name} exceeds the governed string byte bound")


def _envelope_order_key(envelope: dict[str, Any]) -> tuple[str, str]:
    return (
        _require_nonempty_string(envelope.get("signer_id"), name="envelope.signer_id"),
        _require_nonempty_string(envelope.get("key_id"), name="envelope.key_id"),
    )


def _require_nonempty_string(value: object, *, name: str) -> str:
    if type(value) is not str or not value:
        raise ValueError(f"{name} must be an exact nonempty string")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")
    _hash_bytes(value, name=name)
    return value


def _require_positive_u64(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    _require_uint(value, name=name, minimum=1, maximum=MAX_U64)
    return value
