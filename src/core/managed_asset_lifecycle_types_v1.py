"""Closed values for generic managed-asset issue and burn research."""

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

MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1: Final = (
    "zenodex/managed-asset-lifecycle-module/v1"
)
MANAGED_ASSET_ISSUE_COMMAND_KIND_V1: Final = "managed_asset_issue"
MANAGED_ASSET_BURN_COMMAND_KIND_V1: Final = "managed_asset_burn"
ACCOUNT_CUSTODY_DOMAIN_V1: Final = "accounts"


class ManagedAssetClassV1(str, Enum):
    TAU_NATIVE_COIN = "tau_native_coin"
    CANONICAL_ZUSD = "canonical_zusd"
    LP_SHARE = "lp_share"
    ZDEX_PROTOCOL_TOKEN = "zdex_protocol_token"
    SEALED_BID_PAYMENT_OR_INVENTORY = "sealed_bid_payment_or_inventory"
    REGISTERED_ORDINARY_TOKEN = "registered_ordinary_token"


class ManagedAssetLifecycleRejectCodeV1(str, Enum):
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    UNKNOWN_ASSET = "UNKNOWN_ASSET"
    DISABLED_ASSET = "DISABLED_ASSET"
    GENERIC_AUTHORITY_FORBIDDEN = "GENERIC_AUTHORITY_FORBIDDEN"
    ISSUE_DISABLED = "ISSUE_DISABLED"
    BURN_DISABLED = "BURN_DISABLED"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    AUTHORITY_PROFILE_MISMATCH = "AUTHORITY_PROFILE_MISMATCH"
    ZERO_AMOUNT = "ZERO_AMOUNT"
    EFFECT_DELTA_OVERFLOW = "EFFECT_DELTA_OVERFLOW"
    INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
    BALANCE_OVERFLOW = "BALANCE_OVERFLOW"
    SUPPLY_OVERFLOW = "SUPPLY_OVERFLOW"


def _require_optional_authority(
    subject: str | None,
    root: str | None,
    *,
    name: str,
) -> None:
    if (subject is None) != (root is None):
        raise ValueError(f"{name} subject and policy root must be present together")
    if subject is not None:
        _require_token(subject, name=f"{name} subject")
        _require_root(root, name=f"{name} policy root")


@dataclass(frozen=True, slots=True, order=True)
class ManagedAssetLifecyclePolicyV1:
    asset: str
    asset_class: ManagedAssetClassV1
    issue_authority_subject: str | None
    issue_policy_root: str | None
    burn_policy_root: str | None
    enabled: bool

    def __post_init__(self) -> None:
        _require_token(self.asset, name="managed asset lifecycle policy asset")
        if not isinstance(self.asset_class, ManagedAssetClassV1):
            raise TypeError("managed asset lifecycle class is not closed")
        _require_optional_authority(
            self.issue_authority_subject,
            self.issue_policy_root,
            name="managed asset issue authority",
        )
        if self.burn_policy_root is not None:
            _require_root(
                self.burn_policy_root,
                name="managed asset self-burn policy root",
            )
        _require_bool(self.enabled, name="managed asset lifecycle policy enabled")
        if self.asset_class is not ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN and (
            self.issue_policy_root is not None or self.burn_policy_root is not None
        ):
            raise ValueError("generic authority configured for protocol-managed asset")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "asset_class": self.asset_class,
            "issue_authority_subject": self.issue_authority_subject,
            "issue_policy_root": self.issue_policy_root,
            "burn_policy_root": self.burn_policy_root,
            "enabled": self.enabled,
        }


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleStateV1:
    module_release_id: str
    policies: tuple[ManagedAssetLifecyclePolicyV1, ...]
    balances: tuple[EconomicAmountV1, ...]
    supplies: tuple[AssetSupplyV1, ...]

    def __post_init__(self) -> None:
        _require_root(self.module_release_id, name="managed asset module release id")
        _require_ordered_objects(
            self.policies,
            name="managed asset lifecycle policies",
            expected_type=ManagedAssetLifecyclePolicyV1,
            key="asset",
            maximum=MAX_ASSET_POLICY_ROWS_V1,
        )
        _require_ordered_objects(
            self.balances,
            name="managed asset lifecycle balances",
            expected_type=EconomicAmountV1,
            key="key",
            maximum=MAX_ASSET_BALANCE_ROWS_V1,
        )
        _require_ordered_objects(
            self.supplies,
            name="managed asset lifecycle supplies",
            expected_type=AssetSupplyV1,
            key="asset",
            maximum=MAX_ASSET_POLICY_ROWS_V1,
        )
        policy_assets = tuple(policy.asset for policy in self.policies)
        if tuple(supply.asset for supply in self.supplies) != policy_assets:
            raise ValueError("managed asset policies and supplies must cover the same assets")
        totals = {asset: 0 for asset in policy_assets}
        for balance in self.balances:
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1:
                raise ValueError("managed asset balance has the wrong custody domain")
            if balance.amount_atoms == 0:
                raise ValueError("managed asset state must omit zero balances")
            if balance.asset not in totals:
                raise ValueError("managed asset balance references an unknown asset")
            totals[balance.asset] += balance.amount_atoms
        for supply in self.supplies:
            account_total = totals[supply.asset]
            if account_total > supply.amount_atoms:
                raise ValueError("managed asset account balances exceed supply")

    @property
    def state_root(self) -> str:
        return hash_global_v1("managed-asset-lifecycle-state-v1", self.to_canonical())

    def balance_atoms(self, owner: str, asset: str) -> int:
        _require_token(owner, name="managed asset balance owner")
        _require_token(asset, name="managed asset balance asset")
        for row in self.balances:
            if row.owner == owner and row.asset == asset:
                return row.amount_atoms
        return 0

    def supply_atoms(self, asset: str) -> int:
        _require_token(asset, name="managed asset supply asset")
        for row in self.supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown managed asset supply")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "policies": self.policies,
            "balances": self.balances,
            "supplies": self.supplies,
        }


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    module_release_id: str
    command_occurrence_id: str
    subject_id: str
    grant_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="managed asset context chain")
        _require_root(self.deployment_root, name="managed asset context deployment")
        _require_root(self.profile_root, name="managed asset context profile")
        _require_nonnegative_int(self.writer_epoch, name="managed asset context writer epoch")
        _require_root(self.module_release_id, name="managed asset context module release")
        _require_root(self.command_occurrence_id, name="managed asset context occurrence")
        _require_token(self.subject_id, name="managed asset context subject")
        _require_root(self.grant_root, name="managed asset context grant")

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
class ManagedAssetLifecycleCommandV1:
    command_kind: str
    asset: str
    account_owner: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.command_kind, name="managed asset command kind")
        _require_token(self.asset, name="managed asset command asset")
        _require_token(self.account_owner, name="managed asset command account owner")
        _require_atoms_u128(self.amount_atoms, name="managed asset command amount")

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_kind": self.command_kind,
            "asset": self.asset,
            "account_owner": self.account_owner,
            "amount_atoms": self.amount_atoms,
        }

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v1(self.command_kind, self)


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleAcceptedV1:
    post_state: ManagedAssetLifecycleStateV1
    effects: GlobalEconomicEffectPlanV1
    module_journal: LaneModuleTransitionJournalV1

    def __post_init__(self) -> None:
        if not isinstance(self.post_state, ManagedAssetLifecycleStateV1):
            raise TypeError("managed asset accepted state is invalid")
        if not isinstance(self.effects, GlobalEconomicEffectPlanV1) or self.effects.is_empty:
            raise ValueError("managed asset acceptance requires nonempty effects")
        if not isinstance(self.module_journal, LaneModuleTransitionJournalV1):
            raise TypeError("managed asset module journal is invalid")
        if self.module_journal.lane_id is not LaneIdV1.ASSET_TRANSFER:
            raise ValueError("managed asset journal has the wrong lane")
        if self.module_journal.module_release_id != self.post_state.module_release_id:
            raise ValueError("managed asset journal has the wrong module release")
        if self.module_journal.post_lane_root != self.post_state.state_root:
            raise ValueError("managed asset journal has the wrong post-state root")
        if self.module_journal.effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("managed asset journal has the wrong effect-plan root")

    @property
    def receipt_root(self) -> str:
        return self.module_journal.receipt_root


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleRejectedV1:
    code: ManagedAssetLifecycleRejectCodeV1
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if not isinstance(self.code, ManagedAssetLifecycleRejectCodeV1):
            raise TypeError("managed asset reject code is not closed")
        _require_root(self.pre_state_root, name="managed asset rejected pre-state")
        _require_root(self.post_state_root, name="managed asset rejected post-state")
        if self.pre_state_root != self.post_state_root:
            raise ValueError("managed asset rejection changed the state root")
        if not isinstance(self.effects, GlobalEconomicEffectPlanV1) or not self.effects.is_empty:
            raise ValueError("managed asset rejection carried effects")


ManagedAssetLifecycleResultV1 = (
    ManagedAssetLifecycleAcceptedV1 | ManagedAssetLifecycleRejectedV1
)


__all__ = [
    "MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1",
    "MANAGED_ASSET_ISSUE_COMMAND_KIND_V1",
    "MANAGED_ASSET_BURN_COMMAND_KIND_V1",
    "ACCOUNT_CUSTODY_DOMAIN_V1",
    "ManagedAssetClassV1",
    "ManagedAssetLifecycleRejectCodeV1",
    "ManagedAssetLifecyclePolicyV1",
    "ManagedAssetLifecycleStateV1",
    "ManagedAssetLifecycleContextV1",
    "ManagedAssetLifecycleCommandV1",
    "ManagedAssetLifecycleAcceptedV1",
    "ManagedAssetLifecycleRejectedV1",
    "ManagedAssetLifecycleResultV1",
]
