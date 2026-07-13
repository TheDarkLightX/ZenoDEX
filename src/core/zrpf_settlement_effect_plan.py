"""Pure, authority-neutral settlement-effect planning for ZRPF.

The public objects describe a bounded deterministic proposal that can later be
paired with authenticated semantic facts and committed with replay indexes.
Construction establishes internal shape, canonicalization, conservation, and
authorization-consumption consistency. It performs no receipt verification,
persistence, state-tree update, or settlement authorization.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, TypeVar

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ._zrpf_settlement_effect_common import (
    MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1,
    MAX_U64,
    MAX_U128,
    SETTLEMENT_EFFECT_PLAN_SCHEMA_V1,
    ZERO_HASH_V1,
    AssetEffectKindV1,
    CarryEffectKindV1,
    MessageEffectKindV1,
    SettlementEffectPlanRejectCodeV1,
    SettlementEffectPlanValidationError,
    _hash_bytes,
    _require_uint,
)
from ._zrpf_settlement_effect_records import (
    AssetEffectV1,
    AuthorizationConsumptionV1,
    CarryEffectV1,
    LedgerCellWriteV1,
    MessageEffectV1,
    RewardEffectV1,
)

_AUTHORIZATION_NULLIFIER_DOMAIN_V1 = b"zenodex.zrpf.authorization_consumption_nullifier.v1"
_AUTHORIZATION_GRANT_SPEND_DOMAIN_V1 = b"zenodex.zrpf.authorization_grant_spend_nullifier.v1"
_PLAN_COMMITMENT_DOMAIN = "zrpf_settlement_effect_plan"
_ACTION_IDS_ROOT_DOMAIN = "zrpf_settlement_effect_plan_action_ids"
_AUTHORIZATION_NULLIFIERS_ROOT_DOMAIN = "zrpf_settlement_effect_plan_authorization_nullifiers"
_AUTHORIZATION_GRANT_SPENDS_ROOT_DOMAIN = "zrpf_settlement_effect_plan_grant_spend_nullifiers"
_CELL_WRITES_ROOT_DOMAIN = "zrpf_settlement_effect_plan_cell_writes"
_ASSET_EFFECTS_ROOT_DOMAIN = "zrpf_settlement_effect_plan_asset_effects"
_AUTHORIZATIONS_ROOT_DOMAIN = "zrpf_settlement_effect_plan_authorizations"
_MESSAGES_ROOT_DOMAIN = "zrpf_settlement_effect_plan_messages"
_CARRIES_ROOT_DOMAIN = "zrpf_settlement_effect_plan_carries"
_REWARDS_ROOT_DOMAIN = "zrpf_settlement_effect_plan_rewards"


@dataclass(frozen=True, slots=True)
class ProposedSettlementEffectPlanV1:
    """Untrusted, authority-free input to the pure V1 constructor."""

    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    source_root_journal_hash: str
    public_policy_hash: str
    pre_state_root: str
    post_state_root: str
    economic_action_ids: tuple[str, ...]
    ledger_cell_writes: tuple[LedgerCellWriteV1, ...]
    asset_effects: tuple[AssetEffectV1, ...]
    authorization_consumptions: tuple[AuthorizationConsumptionV1, ...]
    message_effects: tuple[MessageEffectV1, ...]
    carry_effects: tuple[CarryEffectV1, ...]
    reward_effects: tuple[RewardEffectV1, ...]


@dataclass(frozen=True, slots=True)
class SettlementEffectPlanV1:
    """Canonical self-consistent plan without proof or ledger authority."""

    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    source_root_journal_hash: str
    public_policy_hash: str
    pre_state_root: str
    post_state_root: str
    economic_action_ids: tuple[str, ...]
    ledger_cell_writes: tuple[LedgerCellWriteV1, ...]
    asset_effects: tuple[AssetEffectV1, ...]
    authorization_consumptions: tuple[AuthorizationConsumptionV1, ...]
    message_effects: tuple[MessageEffectV1, ...]
    carry_effects: tuple[CarryEffectV1, ...]
    reward_effects: tuple[RewardEffectV1, ...]

    def __post_init__(self) -> None:
        from ._zrpf_settlement_effect_validation import validate_canonical_plan

        validate_canonical_plan(self)

    @property
    def economic_action_ids_root(self) -> str:
        return _identifier_root(_ACTION_IDS_ROOT_DOMAIN, self.economic_action_ids)

    @property
    def authorization_nullifiers_root(self) -> str:
        nullifiers = tuple(row.authorization_nullifier for row in self.authorization_consumptions)
        return _identifier_root(_AUTHORIZATION_NULLIFIERS_ROOT_DOMAIN, nullifiers)

    @property
    def authorization_grant_spend_nullifiers_root(self) -> str:
        nullifiers = tuple(
            sorted(
                row.authorization_grant_spend_nullifier for row in self.authorization_consumptions
            )
        )
        return _identifier_root(_AUTHORIZATION_GRANT_SPENDS_ROOT_DOMAIN, nullifiers)

    @property
    def ledger_cell_writes_root(self) -> str:
        return _record_root(_CELL_WRITES_ROOT_DOMAIN, self.ledger_cell_writes)

    @property
    def asset_effects_root(self) -> str:
        return _record_root(_ASSET_EFFECTS_ROOT_DOMAIN, self.asset_effects)

    @property
    def authorization_consumptions_root(self) -> str:
        return _record_root(_AUTHORIZATIONS_ROOT_DOMAIN, self.authorization_consumptions)

    @property
    def message_effects_root(self) -> str:
        return _record_root(_MESSAGES_ROOT_DOMAIN, self.message_effects)

    @property
    def carry_effects_root(self) -> str:
        return _record_root(_CARRIES_ROOT_DOMAIN, self.carry_effects)

    @property
    def reward_effects_root(self) -> str:
        return _record_root(_REWARDS_ROOT_DOMAIN, self.reward_effects)

    def to_commitment_obj(self) -> dict[str, Any]:
        return {
            "schema": SETTLEMENT_EFFECT_PLAN_SCHEMA_V1,
            "application_id": self.application_id,
            "chain_or_domain_id": self.chain_or_domain_id,
            "epoch_id": self.epoch_id,
            "source_root_journal_hash": self.source_root_journal_hash,
            "public_policy_hash": self.public_policy_hash,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "economic_action_ids": list(self.economic_action_ids),
            "economic_action_ids_root": self.economic_action_ids_root,
            "ledger_cell_writes": [row.to_commitment_obj() for row in self.ledger_cell_writes],
            "ledger_cell_writes_root": self.ledger_cell_writes_root,
            "asset_effects": [row.to_commitment_obj() for row in self.asset_effects],
            "asset_effects_root": self.asset_effects_root,
            "authorization_consumptions": [
                row.to_commitment_obj() for row in self.authorization_consumptions
            ],
            "authorization_consumptions_root": self.authorization_consumptions_root,
            "authorization_nullifiers_root": self.authorization_nullifiers_root,
            "authorization_grant_spend_nullifiers_root": (
                self.authorization_grant_spend_nullifiers_root
            ),
            "message_effects": [row.to_commitment_obj() for row in self.message_effects],
            "message_effects_root": self.message_effects_root,
            "carry_effects": [row.to_commitment_obj() for row in self.carry_effects],
            "carry_effects_root": self.carry_effects_root,
            "reward_effects": [row.to_commitment_obj() for row in self.reward_effects],
            "reward_effects_root": self.reward_effects_root,
        }

    def canonical_bytes(self) -> bytes:
        return canonical_json_bytes(self.to_commitment_obj())

    @property
    def commitment(self) -> str:
        return sha256_hex(
            domain_sep_bytes(_PLAN_COMMITMENT_DOMAIN, version=1) + self.canonical_bytes()
        )


def authorization_consumption_nullifier_v1(
    *,
    application_id: str,
    chain_or_domain_id: str,
    economic_action_id: str,
    authorization_subject_id: str,
    authorization_grant_id: str,
    authorization_scope_id: str,
    authorization_nonce: int,
    action_pre_state_root: str,
) -> str:
    """Derive the proof-system-neutral authorization-consumption nullifier."""

    hash_fields = (
        (application_id, "application_id"),
        (chain_or_domain_id, "chain_or_domain_id"),
        (economic_action_id, "economic_action_id"),
        (authorization_subject_id, "authorization_subject_id"),
        (authorization_grant_id, "authorization_grant_id"),
        (authorization_scope_id, "authorization_scope_id"),
        (action_pre_state_root, "action_pre_state_root"),
    )
    hashes = tuple(_hash_bytes(value, name=name) for value, name in hash_fields)
    nonce = _require_uint(
        authorization_nonce,
        name="authorization_nonce",
        maximum=MAX_U64,
    )
    preimage = b"".join(
        (
            len(_AUTHORIZATION_NULLIFIER_DOMAIN_V1).to_bytes(2, "big"),
            _AUTHORIZATION_NULLIFIER_DOMAIN_V1,
            (1).to_bytes(2, "big"),
            *hashes[:6],
            nonce.to_bytes(8, "big"),
            hashes[6],
        )
    )
    return "0x" + hashlib.sha256(preimage).hexdigest()


def authorization_grant_spend_nullifier_v1(
    *,
    application_id: str,
    chain_or_domain_id: str,
    authorization_grant_id: str,
    authorization_nonce: int,
) -> str:
    """Derive the action-independent grant-and-nonce spend nullifier."""

    hashes = (
        _hash_bytes(application_id, name="application_id"),
        _hash_bytes(chain_or_domain_id, name="chain_or_domain_id"),
        _hash_bytes(authorization_grant_id, name="authorization_grant_id"),
    )
    nonce = _require_uint(
        authorization_nonce,
        name="authorization_nonce",
        maximum=MAX_U64,
    )
    preimage = b"".join(
        (
            len(_AUTHORIZATION_GRANT_SPEND_DOMAIN_V1).to_bytes(2, "big"),
            _AUTHORIZATION_GRANT_SPEND_DOMAIN_V1,
            (1).to_bytes(2, "big"),
            *hashes,
            nonce.to_bytes(8, "big"),
        )
    )
    return "0x" + hashlib.sha256(preimage).hexdigest()


def build_settlement_effect_plan_v1(
    proposal: ProposedSettlementEffectPlanV1,
) -> SettlementEffectPlanV1:
    """Canonicalize and validate an authority-free proposed effect plan."""

    from ._zrpf_settlement_effect_validation import build_settlement_effect_plan_v1 as build

    return build(proposal)


def _identifier_root(domain: str, values: tuple[str, ...]) -> str:
    body = {"schema": f"zenodex/{domain}/v1", "identifiers": list(values)}
    return sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(body))


_RecordT = TypeVar(
    "_RecordT",
    LedgerCellWriteV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    MessageEffectV1,
    CarryEffectV1,
    RewardEffectV1,
)


def _record_root(domain: str, values: tuple[_RecordT, ...]) -> str:
    body = {
        "schema": f"zenodex/{domain}/v1",
        "records": [value.to_commitment_obj() for value in values],
    }
    return sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(body))


__all__ = [
    "MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1",
    "MAX_U64",
    "MAX_U128",
    "SETTLEMENT_EFFECT_PLAN_SCHEMA_V1",
    "ZERO_HASH_V1",
    "AssetEffectKindV1",
    "AssetEffectV1",
    "AuthorizationConsumptionV1",
    "CarryEffectKindV1",
    "CarryEffectV1",
    "LedgerCellWriteV1",
    "MessageEffectKindV1",
    "MessageEffectV1",
    "ProposedSettlementEffectPlanV1",
    "RewardEffectV1",
    "SettlementEffectPlanRejectCodeV1",
    "SettlementEffectPlanV1",
    "SettlementEffectPlanValidationError",
    "authorization_consumption_nullifier_v1",
    "authorization_grant_spend_nullifier_v1",
    "build_settlement_effect_plan_v1",
]
