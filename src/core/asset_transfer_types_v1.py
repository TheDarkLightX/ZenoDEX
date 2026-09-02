"""Closed values for the research-only `ASSET_TRANSFER` module core."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    MAX_ASSET_BALANCE_ROWS_V1,
    MAX_ASSET_POLICY_ROWS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    _require_atoms_u128,
    _require_bool,
    _require_nonnegative_int,
    _require_ordered_objects,
    _require_root,
    _require_token,
    hash_economic_command_body_v1,
    hash_global_v1,
)

ASSET_TRANSFER_MODULE_SCHEMA_V1: Final = "zenodex/asset-transfer-module/v1"
ASSET_TRANSFER_COMMAND_KIND_V1: Final = "asset_transfer"
ACCOUNT_CUSTODY_DOMAIN_V1: Final = "accounts"


class AssetTransferRejectCodeV1(str, Enum):
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    UNKNOWN_ASSET = "UNKNOWN_ASSET"
    DISABLED_ASSET = "DISABLED_ASSET"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    SELF_TRANSFER = "SELF_TRANSFER"
    ZERO_AMOUNT = "ZERO_AMOUNT"
    FEE_LIMIT_EXCEEDED = "FEE_LIMIT_EXCEEDED"
    EFFECT_DELTA_OVERFLOW = "EFFECT_DELTA_OVERFLOW"
    INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
    BALANCE_OVERFLOW = "BALANCE_OVERFLOW"
    POST_STATE_RESOURCE_BOUND_EXCEEDED = "POST_STATE_RESOURCE_BOUND_EXCEEDED"


@dataclass(frozen=True, slots=True, order=True)
class AssetTransferPolicyV1:
    asset: str
    fee_owner: str
    transfer_fee_atoms: int
    enabled: bool

    def __post_init__(self) -> None:
        _require_token(self.asset, name="asset transfer policy asset")
        _require_token(self.fee_owner, name="asset transfer policy fee owner")
        _require_atoms_u128(self.transfer_fee_atoms, name="asset transfer policy fee atoms")
        _require_bool(self.enabled, name="asset transfer policy enabled")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "fee_owner": self.fee_owner,
            "transfer_fee_atoms": self.transfer_fee_atoms,
            "enabled": self.enabled,
        }


@dataclass(frozen=True, slots=True)
class AssetTransferStateV1:
    module_release_id: str
    policies: tuple[AssetTransferPolicyV1, ...]
    balances: tuple[EconomicAmountV1, ...]
    supplies: tuple[AssetSupplyV1, ...]

    def __post_init__(self) -> None:
        _require_root(self.module_release_id, name="asset transfer module release id")
        _require_ordered_objects(
            self.policies,
            name="asset transfer policies",
            expected_type=AssetTransferPolicyV1,
            key="asset",
            maximum=MAX_ASSET_POLICY_ROWS_V1,
        )
        _require_ordered_objects(
            self.balances,
            name="asset transfer balances",
            expected_type=EconomicAmountV1,
            key="key",
            maximum=MAX_ASSET_BALANCE_ROWS_V1,
        )
        _require_ordered_objects(
            self.supplies,
            name="asset transfer supplies",
            expected_type=AssetSupplyV1,
            key="asset",
            maximum=MAX_ASSET_POLICY_ROWS_V1,
        )
        policy_assets = tuple(policy.asset for policy in self.policies)
        if tuple(supply.asset for supply in self.supplies) != policy_assets:
            raise ValueError("asset transfer policies and supplies must cover the same assets")
        totals = {asset: 0 for asset in policy_assets}
        for balance in self.balances:
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1:
                raise ValueError("asset transfer balance has the wrong custody domain")
            if balance.amount_atoms == 0:
                raise ValueError("asset transfer state must omit zero balances")
            if balance.asset not in totals:
                raise ValueError("asset transfer balance references an unknown asset")
            totals[balance.asset] += balance.amount_atoms
        for supply in self.supplies:
            if totals[supply.asset] > supply.amount_atoms:
                raise ValueError("asset transfer account balances exceed supply")

    @property
    def state_root(self) -> str:
        return hash_global_v1("asset-transfer-state-v1", self.to_canonical())

    def balance_atoms(self, owner: str, asset: str) -> int:
        _require_token(owner, name="asset transfer balance owner")
        _require_token(asset, name="asset transfer balance asset")
        for row in self.balances:
            if row.owner == owner and row.asset == asset:
                return row.amount_atoms
        return 0

    def supply_atoms(self, asset: str) -> int:
        _require_token(asset, name="asset transfer supply asset")
        for row in self.supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown asset transfer supply")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_TRANSFER_MODULE_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "policies": self.policies,
            "balances": self.balances,
            "supplies": self.supplies,
        }


@dataclass(frozen=True, slots=True)
class AssetTransferContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    module_release_id: str
    command_occurrence_id: str
    subject_id: str
    grant_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="asset transfer context chain")
        _require_root(self.deployment_root, name="asset transfer context deployment")
        _require_root(self.profile_root, name="asset transfer context profile")
        _require_nonnegative_int(self.writer_epoch, name="asset transfer context writer epoch")
        _require_root(self.module_release_id, name="asset transfer context module release")
        _require_root(self.command_occurrence_id, name="asset transfer context occurrence")
        _require_token(self.subject_id, name="asset transfer context subject")
        _require_root(self.grant_root, name="asset transfer context grant")

    def to_canonical(self) -> dict[str, object]:
        return {
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "subject_id": self.subject_id,
            "grant_root": self.grant_root,
        }


@dataclass(frozen=True, slots=True)
class AssetTransferCommandV1:
    command_kind: str
    asset: str
    sender: str
    recipient: str
    amount_atoms: int
    max_fee_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.command_kind, name="asset transfer command kind")
        _require_token(self.asset, name="asset transfer command asset")
        _require_token(self.sender, name="asset transfer command sender")
        _require_token(self.recipient, name="asset transfer command recipient")
        _require_atoms_u128(self.amount_atoms, name="asset transfer command amount")
        _require_atoms_u128(self.max_fee_atoms, name="asset transfer command max fee")

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_kind": self.command_kind,
            "asset": self.asset,
            "sender": self.sender,
            "recipient": self.recipient,
            "amount_atoms": self.amount_atoms,
            "max_fee_atoms": self.max_fee_atoms,
        }

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v1(self.command_kind, self)


@dataclass(frozen=True, slots=True)
class AssetTransferAcceptedV1:
    post_state: AssetTransferStateV1
    effects: GlobalEconomicEffectPlanV1
    module_journal: LaneModuleTransitionJournalV1

    def __post_init__(self) -> None:
        # Opus P28 F1 audit: exact types for every root-bearing nested value; a
        # subclass could override state_root, effect_plan_root, or journal_root
        # while the equalities below read the genuine roots.
        if type(self.post_state) is not AssetTransferStateV1:
            raise TypeError("asset transfer accepted state must be the exact typed value")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("asset transfer accepted effects must be the exact typed value")
        if self.effects.is_empty:
            raise ValueError("asset transfer acceptance requires nonempty effects")
        if type(self.module_journal) is not LaneModuleTransitionJournalV1:
            raise TypeError("asset transfer accepted journal must be the exact typed value")
        if self.module_journal.lane_id is not LaneIdV1.ASSET_TRANSFER:
            raise ValueError("asset transfer journal has the wrong lane")
        if self.module_journal.module_release_id != self.post_state.module_release_id:
            raise ValueError("asset transfer journal has the wrong module release")
        if self.module_journal.post_lane_root != self.post_state.state_root:
            raise ValueError("asset transfer journal has the wrong post-state root")
        if self.module_journal.effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("asset transfer journal has the wrong effect-plan root")

    @property
    def receipt_root(self) -> str:
        return self.module_journal.receipt_root


@dataclass(frozen=True, slots=True)
class AssetTransferRejectedV1:
    code: AssetTransferRejectCodeV1
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if type(self.code) is not AssetTransferRejectCodeV1:
            raise TypeError("asset transfer reject code is not closed")
        _require_root(self.pre_state_root, name="asset transfer rejected pre-state")
        _require_root(self.post_state_root, name="asset transfer rejected post-state")
        if self.pre_state_root != self.post_state_root:
            raise ValueError("asset transfer rejection changed the state root")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("asset transfer rejected effects must be the exact typed value")
        if not self.effects.is_empty:
            raise ValueError("asset transfer rejection carried effects")


AssetTransferResultV1 = AssetTransferAcceptedV1 | AssetTransferRejectedV1


__all__ = [
    "ASSET_TRANSFER_MODULE_SCHEMA_V1",
    "ASSET_TRANSFER_COMMAND_KIND_V1",
    "ACCOUNT_CUSTODY_DOMAIN_V1",
    "AssetTransferRejectCodeV1",
    "AssetTransferPolicyV1",
    "AssetTransferStateV1",
    "AssetTransferContextV1",
    "AssetTransferCommandV1",
    "AssetTransferAcceptedV1",
    "AssetTransferRejectedV1",
    "AssetTransferResultV1",
]
