"""Frozen record types for a ZRPF settlement-effect plan."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ._zrpf_settlement_effect_common import (
    MAX_U64,
    MAX_U128,
    ZERO_HASH_V1,
    AssetEffectKindV1,
    CarryEffectKindV1,
    MessageEffectKindV1,
    SettlementEffectPlanRejectCodeV1,
    _reject,
    _require_enum,
    _require_hash,
    _require_nonzero_hash,
    _require_positive_uint,
    _require_uint,
)


@dataclass(frozen=True, slots=True)
class LedgerCellWriteV1:
    """One exact pre-value to post-value commitment for a ledger cell."""

    economic_action_id: str
    cell_key: str
    pre_value_hash: str
    post_value_hash: str

    def __post_init__(self) -> None:
        _require_nonzero_hash(self.economic_action_id, name="cell_write.economic_action_id")
        _require_nonzero_hash(self.cell_key, name="cell_write.cell_key")
        _require_hash(self.pre_value_hash, name="cell_write.pre_value_hash", allow_zero=True)
        _require_hash(self.post_value_hash, name="cell_write.post_value_hash", allow_zero=True)
        if self.pre_value_hash == self.post_value_hash:
            _reject(
                SettlementEffectPlanRejectCodeV1.NON_CHANGING_CELL_WRITE,
                "cell write pre and post values must differ",
            )

    def to_commitment_obj(self) -> dict[str, Any]:
        return {
            "economic_action_id": self.economic_action_id,
            "cell_key": self.cell_key,
            "pre_value_hash": self.pre_value_hash,
            "post_value_hash": self.post_value_hash,
        }


@dataclass(frozen=True, slots=True)
class AssetEffectV1:
    """One bounded asset-flow row tied to a canonical economic action."""

    effect_id: str = field(init=False)
    kind: AssetEffectKindV1
    economic_action_id: str
    asset_id: str
    debit_atoms: int
    credit_atoms: int
    authorized_mint_atoms: int
    authorized_burn_atoms: int
    authority_scope_id: str = ZERO_HASH_V1
    authorization_nullifier: str = ZERO_HASH_V1

    def __post_init__(self) -> None:
        _require_enum(self.kind, AssetEffectKindV1, name="asset_effect.kind")
        _require_nonzero_hash(self.economic_action_id, name="asset_effect.economic_action_id")
        _require_nonzero_hash(self.asset_id, name="asset_effect.asset_id")
        for name in (
            "debit_atoms",
            "credit_atoms",
            "authorized_mint_atoms",
            "authorized_burn_atoms",
        ):
            _require_uint(getattr(self, name), name=f"asset_effect.{name}", maximum=MAX_U128)
        _require_hash(
            self.authority_scope_id, name="asset_effect.authority_scope_id", allow_zero=True
        )
        _require_hash(
            self.authorization_nullifier,
            name="asset_effect.authorization_nullifier",
            allow_zero=True,
        )
        self._validate_effect_shape()
        object.__setattr__(
            self,
            "effect_id",
            self.expected_id(),
        )

    def _validate_effect_shape(self) -> None:
        amounts = (
            self.debit_atoms,
            self.credit_atoms,
            self.authorized_mint_atoms,
            self.authorized_burn_atoms,
        )
        if not any(amounts):
            _reject(SettlementEffectPlanRejectCodeV1.ZERO_EFFECT, "asset effect is all zero")
        has_mint = self.authorized_mint_atoms != 0
        has_burn = self.authorized_burn_atoms != 0
        if has_mint and has_burn:
            _reject(
                SettlementEffectPlanRejectCodeV1.COMBINED_MINT_AND_BURN,
                "one asset effect cannot mint and burn",
            )
        if self.kind is AssetEffectKindV1.ORDINARY_TRANSFER:
            if has_mint or has_burn:
                _reject(
                    SettlementEffectPlanRejectCodeV1.INVALID_SUPPLY_EFFECT_SHAPE,
                    "ordinary transfer cannot change supply",
                )
            if (
                self.authority_scope_id != ZERO_HASH_V1
                or self.authorization_nullifier != ZERO_HASH_V1
            ):
                _reject(
                    SettlementEffectPlanRejectCodeV1.UNEXPECTED_AUTHORITY_MATERIAL,
                    "ordinary asset effect must use zero authority and nullifier",
                )
            return
        if self.authority_scope_id == ZERO_HASH_V1 or self.authorization_nullifier == ZERO_HASH_V1:
            _reject(
                SettlementEffectPlanRejectCodeV1.MISSING_AUTHORITY_MATERIAL,
                "supply effect requires nonzero authority scope and nullifier",
            )
        valid_shape = {
            AssetEffectKindV1.AUTHORIZED_MINT: (
                has_mint
                and not has_burn
                and self.debit_atoms == 0
                and self.credit_atoms == self.authorized_mint_atoms
            ),
            AssetEffectKindV1.AUTHORIZED_BURN: (
                has_burn
                and not has_mint
                and self.credit_atoms == 0
                and self.debit_atoms == self.authorized_burn_atoms
            ),
            AssetEffectKindV1.AUTHORIZED_REWARD: (
                not has_mint
                and not has_burn
                and self.debit_atoms > 0
                and self.debit_atoms == self.credit_atoms
            ),
        }.get(self.kind, False)
        if not valid_shape:
            _reject(
                SettlementEffectPlanRejectCodeV1.INVALID_SUPPLY_EFFECT_SHAPE,
                "authorized asset effect does not match its typed flow shape",
            )

    def _identity_obj(self) -> dict[str, Any]:
        return {
            "kind": self.kind.value,
            "economic_action_id": self.economic_action_id,
            "asset_id": self.asset_id,
            "debit_atoms": self.debit_atoms,
            "credit_atoms": self.credit_atoms,
            "authorized_mint_atoms": self.authorized_mint_atoms,
            "authorized_burn_atoms": self.authorized_burn_atoms,
            "authority_scope_id": self.authority_scope_id,
            "authorization_nullifier": self.authorization_nullifier,
        }

    def to_commitment_obj(self) -> dict[str, Any]:
        return {"effect_id": self.effect_id, **self._identity_obj()}

    def expected_id(self) -> str:
        return _derived_record_id("zrpf_asset_effect", self._identity_obj())

    @property
    def changes_supply(self) -> bool:
        return self.authorized_mint_atoms != 0 or self.authorized_burn_atoms != 0

    @property
    def requires_authorization(self) -> bool:
        return self.kind is not AssetEffectKindV1.ORDINARY_TRANSFER


@dataclass(frozen=True, slots=True)
class AuthorizationConsumptionV1:
    """Canonical authorization use independent of proof and signature encodings."""

    application_id: str
    chain_or_domain_id: str
    economic_action_id: str
    authorization_subject_id: str
    authorization_grant_id: str
    authorization_scope_id: str
    authorization_nonce: int
    action_pre_state_root: str
    authorization_nullifier: str
    authorization_grant_spend_nullifier: str = field(init=False)

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "economic_action_id",
            "authorization_subject_id",
            "authorization_grant_id",
            "authorization_scope_id",
            "action_pre_state_root",
            "authorization_nullifier",
        ):
            _require_nonzero_hash(getattr(self, name), name=f"authorization.{name}")
        _require_uint(
            self.authorization_nonce,
            name="authorization.authorization_nonce",
            maximum=MAX_U64,
        )
        object.__setattr__(
            self,
            "authorization_grant_spend_nullifier",
            self.expected_grant_spend_nullifier(),
        )

    def expected_nullifier(self) -> str:
        from .zrpf_settlement_effect_plan import authorization_consumption_nullifier_v1

        return authorization_consumption_nullifier_v1(
            application_id=self.application_id,
            chain_or_domain_id=self.chain_or_domain_id,
            economic_action_id=self.economic_action_id,
            authorization_subject_id=self.authorization_subject_id,
            authorization_grant_id=self.authorization_grant_id,
            authorization_scope_id=self.authorization_scope_id,
            authorization_nonce=self.authorization_nonce,
            action_pre_state_root=self.action_pre_state_root,
        )

    def expected_grant_spend_nullifier(self) -> str:
        from .zrpf_settlement_effect_plan import authorization_grant_spend_nullifier_v1

        return authorization_grant_spend_nullifier_v1(
            application_id=self.application_id,
            chain_or_domain_id=self.chain_or_domain_id,
            authorization_grant_id=self.authorization_grant_id,
            authorization_nonce=self.authorization_nonce,
        )

    def to_commitment_obj(self) -> dict[str, Any]:
        return {
            "application_id": self.application_id,
            "chain_or_domain_id": self.chain_or_domain_id,
            "economic_action_id": self.economic_action_id,
            "authorization_subject_id": self.authorization_subject_id,
            "authorization_grant_id": self.authorization_grant_id,
            "authorization_scope_id": self.authorization_scope_id,
            "authorization_nonce": self.authorization_nonce,
            "action_pre_state_root": self.action_pre_state_root,
            "authorization_nullifier": self.authorization_nullifier,
            "authorization_grant_spend_nullifier": self.authorization_grant_spend_nullifier,
        }


@dataclass(frozen=True, slots=True)
class MessageEffectV1:
    """One cross-domain message proposed by an economic action."""

    message_id: str = field(init=False)
    economic_action_id: str
    asset_effect_id: str
    source_domain_id: str
    destination_domain_id: str
    asset_id: str
    amount_atoms: int
    kind: MessageEffectKindV1

    def __post_init__(self) -> None:
        for name in (
            "economic_action_id",
            "asset_effect_id",
            "source_domain_id",
            "destination_domain_id",
            "asset_id",
        ):
            _require_nonzero_hash(getattr(self, name), name=f"message.{name}")
        _require_positive_uint(self.amount_atoms, name="message.amount_atoms", maximum=MAX_U128)
        _require_enum(self.kind, MessageEffectKindV1, name="message.kind")
        if self.source_domain_id == self.destination_domain_id:
            _reject(
                SettlementEffectPlanRejectCodeV1.MESSAGE_CARRY_MISMATCH,
                "cross-domain message source and destination must differ",
            )
        object.__setattr__(
            self,
            "message_id",
            self.expected_id(),
        )

    def _identity_obj(self) -> dict[str, Any]:
        return {
            "economic_action_id": self.economic_action_id,
            "asset_effect_id": self.asset_effect_id,
            "source_domain_id": self.source_domain_id,
            "destination_domain_id": self.destination_domain_id,
            "asset_id": self.asset_id,
            "amount_atoms": self.amount_atoms,
            "kind": self.kind.value,
        }

    def to_commitment_obj(self) -> dict[str, Any]:
        return {"message_id": self.message_id, **self._identity_obj()}

    def expected_id(self) -> str:
        return _derived_record_id("zrpf_message_effect", self._identity_obj())


@dataclass(frozen=True, slots=True)
class CarryEffectV1:
    """One lock or release paired exactly with a cross-domain message."""

    carry_id: str = field(init=False)
    economic_action_id: str
    message_id: str
    asset_id: str
    amount_atoms: int
    kind: CarryEffectKindV1

    def __post_init__(self) -> None:
        for name in ("economic_action_id", "message_id", "asset_id"):
            _require_nonzero_hash(getattr(self, name), name=f"carry.{name}")
        _require_positive_uint(self.amount_atoms, name="carry.amount_atoms", maximum=MAX_U128)
        _require_enum(self.kind, CarryEffectKindV1, name="carry.kind")
        object.__setattr__(
            self,
            "carry_id",
            self.expected_id(),
        )

    def _identity_obj(self) -> dict[str, Any]:
        return {
            "economic_action_id": self.economic_action_id,
            "message_id": self.message_id,
            "asset_id": self.asset_id,
            "amount_atoms": self.amount_atoms,
            "kind": self.kind.value,
        }

    def to_commitment_obj(self) -> dict[str, Any]:
        return {"carry_id": self.carry_id, **self._identity_obj()}

    def expected_id(self) -> str:
        return _derived_record_id("zrpf_carry_effect", self._identity_obj())


@dataclass(frozen=True, slots=True)
class RewardEffectV1:
    """One authorized reward credit bound to a cell write and asset effect."""

    reward_id: str = field(init=False)
    economic_action_id: str
    asset_effect_id: str
    recipient_cell_key: str
    asset_id: str
    amount_atoms: int
    authority_scope_id: str
    authorization_nullifier: str

    def __post_init__(self) -> None:
        for name in (
            "economic_action_id",
            "asset_effect_id",
            "recipient_cell_key",
            "asset_id",
            "authority_scope_id",
            "authorization_nullifier",
        ):
            _require_nonzero_hash(getattr(self, name), name=f"reward.{name}")
        _require_positive_uint(self.amount_atoms, name="reward.amount_atoms", maximum=MAX_U128)
        object.__setattr__(
            self,
            "reward_id",
            self.expected_id(),
        )

    def _identity_obj(self) -> dict[str, Any]:
        return {
            "economic_action_id": self.economic_action_id,
            "asset_effect_id": self.asset_effect_id,
            "recipient_cell_key": self.recipient_cell_key,
            "asset_id": self.asset_id,
            "amount_atoms": self.amount_atoms,
            "authority_scope_id": self.authority_scope_id,
            "authorization_nullifier": self.authorization_nullifier,
        }

    def to_commitment_obj(self) -> dict[str, Any]:
        return {"reward_id": self.reward_id, **self._identity_obj()}

    def expected_id(self) -> str:
        return _derived_record_id("zrpf_reward_effect", self._identity_obj())


def _derived_record_id(domain: str, body: dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(body))
