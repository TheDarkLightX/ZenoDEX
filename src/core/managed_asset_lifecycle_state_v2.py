"""Foundational owned values for the managed-asset lifecycle V2 SHADOW core."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final, TypeAlias

from .asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    AssetClassV2,
    require_asset_class_namespace_v2,
)
from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    _snapshot_occurrence_v2,
)
from .global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    _require_bool_v2,
    _require_nonnegative_int_v2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
    hash_global_v2,
)

MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2: Final = "zenodex/managed-asset-lifecycle-module/v2"
_UNSET_OWNED_VALUE_V2: Final = object()

ManagedAssetClassV2: TypeAlias = AssetClassV2


def _require_optional_root(value: str | None, *, name: str) -> None:
    if value is not None:
        _require_root_v2(value, name=name)


@dataclass(frozen=True, slots=True, order=True)
class ManagedAssetLifecyclePolicyV2:
    asset: str
    asset_class: ManagedAssetClassV2
    asset_origin_root: str | None
    atom_decimals: int
    issue_authority_subject: str | None
    issue_authorization_root: str | None
    burn_authorization_root: str | None
    enabled: bool

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="managed asset policy asset")
        if type(self.asset_class) is not ManagedAssetClassV2:
            raise TypeError("managed asset policy class must be exact")
        _require_optional_root(self.asset_origin_root, name="managed asset origin root")
        if type(self.atom_decimals) is not int or self.atom_decimals != ASSET_ATOM_DECIMALS_V2:
            raise ValueError("managed asset atom decimals must equal 8")
        if (self.issue_authority_subject is None) != (self.issue_authorization_root is None):
            raise ValueError("managed asset issue subject and authorization root differ")
        if self.issue_authority_subject is not None:
            _require_token_v2(
                self.issue_authority_subject,
                name="managed asset issue authority subject",
            )
            _require_root_v2(
                self.issue_authorization_root,
                name="managed asset issue authorization root",
            )
        _require_optional_root(
            self.burn_authorization_root,
            name="managed asset burn authorization root",
        )
        _require_bool_v2(self.enabled, name="managed asset policy enabled")
        require_asset_class_namespace_v2(self.asset, self.asset_class)
        if self.asset_class is not ManagedAssetClassV2.REGISTERED_ORDINARY_TOKEN and (
            self.issue_authorization_root is not None or self.burn_authorization_root is not None
        ):
            raise ValueError("generic authority configured for protocol-managed asset")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "asset_class": self.asset_class,
            "asset_origin_root": self.asset_origin_root,
            "atom_decimals": self.atom_decimals,
            "issue_authority_subject": self.issue_authority_subject,
            "issue_authorization_root": self.issue_authorization_root,
            "burn_authorization_root": self.burn_authorization_root,
            "enabled": self.enabled,
        }


def _snapshot_policy_v2(policy: ManagedAssetLifecyclePolicyV2) -> ManagedAssetLifecyclePolicyV2:
    if type(policy) is not ManagedAssetLifecyclePolicyV2:
        raise TypeError("managed asset policy must be an exact typed value")
    return replace(policy)


@dataclass(frozen=True, slots=True, init=False)
class ManagedAssetLifecycleStateV2:
    module_release_id: str
    _policies: tuple[ManagedAssetLifecyclePolicyV2, ...]
    _balances: tuple[EconomicAmountV2, ...]
    _supplies: tuple[AssetSupplyV2, ...]

    def __init__(
        self,
        module_release_id: str,
        policies: tuple[ManagedAssetLifecyclePolicyV2, ...] | None = None,
        balances: tuple[EconomicAmountV2, ...] | None = None,
        supplies: tuple[AssetSupplyV2, ...] | None = None,
        *,
        _policies: tuple[ManagedAssetLifecyclePolicyV2, ...] | None = None,
        _balances: tuple[EconomicAmountV2, ...] | None = None,
        _supplies: tuple[AssetSupplyV2, ...] | None = None,
    ) -> None:
        selected_policies = policies if policies is not None else _policies
        selected_balances = balances if balances is not None else _balances
        selected_supplies = supplies if supplies is not None else _supplies
        if selected_policies is None or selected_balances is None or selected_supplies is None:
            raise TypeError("managed asset state requires all owned tables")
        if type(selected_policies) is not tuple:
            raise TypeError("managed asset policies must be an exact tuple")
        object.__setattr__(self, "module_release_id", module_release_id)
        _require_root_v2(self.module_release_id, name="managed asset module release id")
        object.__setattr__(
            self,
            "_policies",
            tuple(_snapshot_policy_v2(policy) for policy in selected_policies),
        )
        object.__setattr__(
            self,
            "_balances",
            _snapshot_dataclass_tuple_v2(
                selected_balances,
                EconomicAmountV2,
                "managed asset balances",
            ),
        )
        object.__setattr__(
            self,
            "_supplies",
            _snapshot_dataclass_tuple_v2(
                selected_supplies,
                AssetSupplyV2,
                "managed asset supplies",
            ),
        )
        _require_ordered_objects_v2(
            self._policies,
            name="managed asset policies",
            expected_type=ManagedAssetLifecyclePolicyV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self._balances,
            name="managed asset balances",
            expected_type=EconomicAmountV2,
            key="key",
        )
        _require_ordered_objects_v2(
            self._supplies,
            name="managed asset supplies",
            expected_type=AssetSupplyV2,
            key="asset",
        )
        assets = tuple(policy.asset for policy in self._policies)
        if tuple(supply.asset for supply in self._supplies) != assets:
            raise ValueError("managed asset policies and supplies must cover the same assets")
        totals = {asset: 0 for asset in assets}
        for balance in self._balances:
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V2:
                raise ValueError("managed asset balance has the wrong custody domain")
            if balance.amount_atoms == 0 or balance.asset not in totals:
                raise ValueError("managed asset balance is invalid")
            totals[balance.asset] += balance.amount_atoms
        for supply in self._supplies:
            if totals[supply.asset] > supply.amount_atoms:
                raise ValueError("managed asset balances exceed supply")

    @property
    def policies(self) -> tuple[ManagedAssetLifecyclePolicyV2, ...]:
        return tuple(_snapshot_policy_v2(policy) for policy in self._policies)

    @property
    def balances(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._balances,
            EconomicAmountV2,
            "managed asset balances",
        )

    @property
    def supplies(self) -> tuple[AssetSupplyV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._supplies,
            AssetSupplyV2,
            "managed asset supplies",
        )

    @property
    def state_root(self) -> str:
        return hash_global_v2("managed-asset-lifecycle-state-v2", self.to_canonical())

    def balance_atoms(self, owner: str, asset: str) -> int:
        _require_token_v2(owner, name="managed asset balance owner")
        _require_token_v2(asset, name="managed asset balance asset")
        return next(
            (
                row.amount_atoms
                for row in self._balances
                if row.owner == owner and row.asset == asset
            ),
            0,
        )

    def supply_atoms(self, asset: str) -> int:
        _require_token_v2(asset, name="managed asset supply asset")
        for row in self._supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown managed asset supply")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
            "module_release_id": self.module_release_id,
            "policies": self.policies,
            "balances": self.balances,
            "supplies": self.supplies,
        }


@dataclass(frozen=True, slots=True, init=False)
class ManagedAssetLifecycleContextV2:
    writer_epoch: int
    module_release_id: str
    global_pre_state_root: str
    _occurrence: EconomicCommandOccurrenceV2 | None

    def __init__(
        self,
        writer_epoch: int,
        module_release_id: str,
        global_pre_state_root: str,
        occurrence: EconomicCommandOccurrenceV2 | None | object = _UNSET_OWNED_VALUE_V2,
        *,
        _occurrence: EconomicCommandOccurrenceV2 | None | object = _UNSET_OWNED_VALUE_V2,
    ) -> None:
        selected_occurrence = occurrence if occurrence is not _UNSET_OWNED_VALUE_V2 else _occurrence
        if selected_occurrence is _UNSET_OWNED_VALUE_V2:
            raise TypeError("managed asset context requires an occurrence field")
        object.__setattr__(self, "writer_epoch", writer_epoch)
        object.__setattr__(self, "module_release_id", module_release_id)
        object.__setattr__(self, "global_pre_state_root", global_pre_state_root)
        _require_nonnegative_int_v2(self.writer_epoch, name="managed asset writer epoch")
        _require_root_v2(self.module_release_id, name="managed asset module release")
        _require_root_v2(
            self.global_pre_state_root,
            name="managed asset global pre-state root",
        )
        if selected_occurrence is not None:
            if type(selected_occurrence) is not EconomicCommandOccurrenceV2:
                raise TypeError("managed asset occurrence must be an exact typed value")
            object.__setattr__(
                self,
                "_occurrence",
                _snapshot_occurrence_v2(selected_occurrence),
            )
        else:
            object.__setattr__(self, "_occurrence", None)

    @property
    def occurrence(self) -> EconomicCommandOccurrenceV2 | None:
        if self._occurrence is None:
            return None
        return _snapshot_occurrence_v2(self._occurrence)

    def to_canonical(self) -> dict[str, object]:
        return {
            "writer_epoch": self.writer_epoch,
            "module_release_id": self.module_release_id,
            "global_pre_state_root": self.global_pre_state_root,
            "occurrence": self.occurrence,
        }


def _snapshot_state_v2(state: ManagedAssetLifecycleStateV2) -> ManagedAssetLifecycleStateV2:
    if type(state) is not ManagedAssetLifecycleStateV2:
        raise TypeError("managed asset state must be an exact typed value")
    return ManagedAssetLifecycleStateV2(
        state.module_release_id,
        tuple(_snapshot_policy_v2(policy) for policy in state.policies),
        _snapshot_dataclass_tuple_v2(state.balances, EconomicAmountV2, "managed asset balances"),
        _snapshot_dataclass_tuple_v2(state.supplies, AssetSupplyV2, "managed asset supplies"),
    )


def _snapshot_context_v2(
    context: ManagedAssetLifecycleContextV2,
) -> ManagedAssetLifecycleContextV2:
    if type(context) is not ManagedAssetLifecycleContextV2:
        raise TypeError("managed asset context must be an exact typed value")
    return ManagedAssetLifecycleContextV2(
        writer_epoch=context.writer_epoch,
        module_release_id=context.module_release_id,
        global_pre_state_root=context.global_pre_state_root,
        occurrence=context.occurrence,
    )


__all__ = [
    "ACCOUNT_CUSTODY_DOMAIN_V2",
    "MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2",
    "ManagedAssetClassV2",
    "ManagedAssetLifecyclePolicyV2",
    "ManagedAssetLifecycleStateV2",
    "ManagedAssetLifecycleContextV2",
    "_snapshot_state_v2",
    "_snapshot_context_v2",
]
