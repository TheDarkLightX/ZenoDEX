"""Explicit custody successor state over unchanged ABI V2 leaf values.

This schema commits the complete physical frame. It grants no authentication or
publication authority; claimant liabilities remain in the global state.
"""

from __future__ import annotations

from dataclasses import dataclass

from .asset_origin_registry_types_v2 import AssetOriginRegistryStateV2, _snapshot_registry_state_v2
from .asset_origin_registry_v2 import (
    validate_asset_transfer_policy_origin_v2,
    validate_managed_asset_policy_origin_v2,
)
from .asset_transfer_types_v2 import AssetTransferStateV2, _snapshot_asset_transfer_state_v2
from .global_settlement_resource_limits_v2 import (
    MAX_ASSETS_PER_ASSET_STATE_V2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    require_raw_tuple_ceiling_v2,
    require_rootable_asset_state_bytes_v2,
)
from .global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    ZERO_ROOT_V2,
    EconomicAmountV2,
    _require_ordered_objects_v2,
    _snapshot_dataclass_tuple_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleStateV2,
)

ASSET_LANE_CUSTODY_SCHEMA_V2 = "zenodex/asset-lane-custody-state/v2"
MAX_ASSET_LANE_CUSTODY_ROWS_V2 = MAX_BALANCE_ROWS_PER_ASSET_STATE_V2


@dataclass(frozen=True, slots=True, init=False)
class AssetLaneCustodyStateV2:
    _transfer_state: AssetTransferStateV2
    _origin_registry: AssetOriginRegistryStateV2
    _managed_policies: tuple[ManagedAssetLifecyclePolicyV2, ...]
    _custody: tuple[EconomicAmountV2, ...]

    def __init__(
        self,
        transfer_state: AssetTransferStateV2,
        origin_registry: AssetOriginRegistryStateV2,
        managed_policies: tuple[ManagedAssetLifecyclePolicyV2, ...],
        custody: tuple[EconomicAmountV2, ...],
    ) -> None:
        require_raw_tuple_ceiling_v2(
            managed_policies,
            name="custody lane managed policies",
            ceiling=MAX_ASSETS_PER_ASSET_STATE_V2,
        )
        require_raw_tuple_ceiling_v2(
            custody,
            name="custody lane rows",
            ceiling=MAX_ASSET_LANE_CUSTODY_ROWS_V2,
        )
        object.__setattr__(
            self, "_transfer_state", _snapshot_asset_transfer_state_v2(transfer_state)
        )
        object.__setattr__(self, "_origin_registry", _snapshot_registry_state_v2(origin_registry))
        object.__setattr__(
            self,
            "_managed_policies",
            _snapshot_dataclass_tuple_v2(
                managed_policies,
                ManagedAssetLifecyclePolicyV2,
                "custody lane managed policies",
            ),
        )
        object.__setattr__(
            self,
            "_custody",
            _snapshot_dataclass_tuple_v2(
                custody,
                EconomicAmountV2,
                "custody lane rows",
            ),
        )
        _require_ordered_objects_v2(
            self._managed_policies,
            name="custody lane managed policies",
            expected_type=ManagedAssetLifecyclePolicyV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self._custody,
            name="custody lane rows",
            expected_type=EconomicAmountV2,
            key="key",
        )
        self._validate_registry_coverage()
        self._validate_physical_holdings()
        require_rootable_asset_state_bytes_v2(
            canonical_global_bytes_v2(self.to_canonical()),
            name="custody lane state",
        )

    def _validate_registry_coverage(self) -> None:
        leaf, registry = self._transfer_state, self._origin_registry
        if registry.module_release_id != leaf.module_release_id:
            raise ValueError("custody lane registry release differs")
        if tuple(row.asset for row in registry.assets) != tuple(p.asset for p in leaf.policies):
            raise ValueError("custody lane registry and transfer coverage differ")
        expected_managed = tuple(
            row.asset for row in registry.assets if row.issue_policy_root != ZERO_ROOT_V2
        )
        if tuple(p.asset for p in self._managed_policies) != expected_managed:
            raise ValueError("custody lane managed policy coverage differs")
        transfers = {p.asset: p for p in leaf.policies}
        for managed in self._managed_policies:
            transfer = transfers[managed.asset]
            if (managed.asset_class, managed.asset_origin_root, managed.atom_decimals) != (
                transfer.asset_class,
                transfer.asset_origin_root,
                transfer.atom_decimals,
            ):
                raise ValueError("custody lane transfer and managed identities differ")

    def _validate_physical_holdings(self) -> None:
        totals = {row.asset: 0 for row in self._transfer_state.supplies}
        for row in self._custody:
            if row.custody_domain == "accounts" or row.amount_atoms == 0:
                raise ValueError("custody lane requires positive non-account custody rows")
        for row in (*self._transfer_state.balances, *self._custody):
            if row.asset not in totals:
                raise ValueError("custody lane holding references an unnamed supply")
            totals[row.asset] += row.amount_atoms
            if totals[row.asset] > MAX_ATOMS_V2:
                raise ValueError("custody lane physical total exceeds unsigned 128-bit bounds")
        if any(totals[row.asset] != row.amount_atoms for row in self._transfer_state.supplies):
            raise ValueError("custody lane account plus custody total must equal supply")

    @property
    def transfer_state(self) -> AssetTransferStateV2:
        return _snapshot_asset_transfer_state_v2(self._transfer_state)

    @property
    def origin_registry(self) -> AssetOriginRegistryStateV2:
        return _snapshot_registry_state_v2(self._origin_registry)

    @property
    def managed_policies(self) -> tuple[ManagedAssetLifecyclePolicyV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._managed_policies,
            ManagedAssetLifecyclePolicyV2,
            "custody lane managed policies",
        )

    @property
    def custody(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_dataclass_tuple_v2(self._custody, EconomicAmountV2, "custody lane rows")

    @property
    def state_root(self) -> str:
        return hash_global_v2("asset-lane-custody-state-v2", self.to_canonical())

    def managed_leaf_state(self) -> ManagedAssetLifecycleStateV2:
        assets = {p.asset for p in self._managed_policies}
        return ManagedAssetLifecycleStateV2(
            self._transfer_state.module_release_id,
            self.managed_policies,
            tuple(row for row in self._transfer_state.balances if row.asset in assets),
            tuple(row for row in self._transfer_state.supplies if row.asset in assets),
        )

    def account_atoms(self, asset: str) -> int:
        self._transfer_state.supply_atoms(asset)
        return sum(row.amount_atoms for row in self._transfer_state.balances if row.asset == asset)

    def physical_atoms(self, asset: str) -> int:
        return self.account_atoms(asset) + sum(
            row.amount_atoms for row in self._custody if row.asset == asset
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_LANE_CUSTODY_SCHEMA_V2,
            "transfer_state": self.transfer_state,
            "origin_registry": self.origin_registry,
            "managed_policies": self.managed_policies,
            "custody": self.custody,
        }


def snapshot_asset_lane_custody_state_v2(state: AssetLaneCustodyStateV2) -> AssetLaneCustodyStateV2:
    if type(state) is not AssetLaneCustodyStateV2:
        raise TypeError("custody lane state must be exact")
    return AssetLaneCustodyStateV2(
        state.transfer_state,
        state.origin_registry,
        state.managed_policies,
        state.custody,
    )


def custody_policy_origins_hold_v2(state: AssetLaneCustodyStateV2) -> bool:
    try:
        registry = state.origin_registry
        for policy in state.transfer_state.policies:
            validate_asset_transfer_policy_origin_v2(registry, policy)
        for managed in state.managed_policies:
            validate_managed_asset_policy_origin_v2(registry, managed)
    except (TypeError, ValueError):
        return False
    return True
