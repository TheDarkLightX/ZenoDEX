"""Owned aggregate state for the bounded V2 ``ASSET_TRANSFER`` lane.

The aggregate is the single state projected into the transfer and generic
managed-asset leaves.  Registry/profile authentication remains a SHADOW
premise; construction only establishes exact ownership, shape, and accounting.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .asset_origin_registry_types_v2 import (
    MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2,
    AssetOriginRegistryStateV2,
    _snapshot_registry_state_v2,
)
from .asset_origin_registry_v2 import (
    validate_asset_transfer_policy_origin_v2,
    validate_managed_asset_policy_origin_v2,
)
from .asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferStateV2,
)
from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    _snapshot_occurrence_v2,
)
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    _require_nonnegative_int_v2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleStateV2,
)

ASSET_LANE_STATE_SCHEMA_V2: Final = "zenodex/asset-lane-state/v2"
ASSET_LANE_PRODUCTION_AUTHORITY_V2: Final = "NONE"
ASSET_LANE_PROFILE_AUTHENTICATION_V2: Final = "SHADOW"
MAX_ASSET_LANE_ASSETS_V2: Final = MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2
MAX_ASSET_LANE_BALANCE_ROWS_V2: Final = 4_096
MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2: Final = 1_048_576
_UNSET_V2: Final = object()


def _snapshot_transfer_policies_v2(
    policies: object,
) -> tuple[AssetTransferPolicyV2, ...]:
    return _snapshot_dataclass_tuple_v2(
        policies,
        AssetTransferPolicyV2,
        "asset lane transfer policies",
    )


def _snapshot_managed_policies_v2(
    policies: object,
) -> tuple[ManagedAssetLifecyclePolicyV2, ...]:
    return _snapshot_dataclass_tuple_v2(
        policies,
        ManagedAssetLifecyclePolicyV2,
        "asset lane managed policies",
    )


@dataclass(frozen=True, slots=True, init=False)
class AssetLaneStateV2:
    """Privately owned aggregate of registry, policies, balances, and supply."""

    module_release_id: str
    _origin_registry: AssetOriginRegistryStateV2
    _transfer_policies: tuple[AssetTransferPolicyV2, ...]
    _managed_policies: tuple[ManagedAssetLifecyclePolicyV2, ...]
    _balances: tuple[EconomicAmountV2, ...]
    _supplies: tuple[AssetSupplyV2, ...]

    def __init__(
        self,
        module_release_id: str,
        origin_registry: AssetOriginRegistryStateV2,
        transfer_policies: tuple[AssetTransferPolicyV2, ...],
        managed_policies: tuple[ManagedAssetLifecyclePolicyV2, ...],
        balances: tuple[EconomicAmountV2, ...],
        supplies: tuple[AssetSupplyV2, ...],
    ) -> None:
        if type(origin_registry) is not AssetOriginRegistryStateV2:
            raise TypeError("asset lane origin registry must be exact")
        object.__setattr__(self, "module_release_id", module_release_id)
        object.__setattr__(
            self,
            "_origin_registry",
            _snapshot_registry_state_v2(origin_registry),
        )
        object.__setattr__(
            self,
            "_transfer_policies",
            _snapshot_transfer_policies_v2(transfer_policies),
        )
        object.__setattr__(
            self,
            "_managed_policies",
            _snapshot_managed_policies_v2(managed_policies),
        )
        object.__setattr__(
            self,
            "_balances",
            _snapshot_dataclass_tuple_v2(
                balances,
                EconomicAmountV2,
                "asset lane balances",
            ),
        )
        object.__setattr__(
            self,
            "_supplies",
            _snapshot_dataclass_tuple_v2(
                supplies,
                AssetSupplyV2,
                "asset lane supplies",
            ),
        )
        self._validate_structure()

    def _validate_structure(self) -> None:
        _require_root_v2(self.module_release_id, name="asset lane module release")
        if self._origin_registry.module_release_id != self.module_release_id:
            raise ValueError("asset lane registry release does not match")
        self._validate_table_shapes()
        transfer_assets = self._validate_asset_coverage()
        self._validate_owned_supply(transfer_assets)
        if (
            len(canonical_global_bytes_v2(self.to_canonical()))
            > MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2
        ):
            raise ValueError("asset lane state exceeds its canonical-byte ceiling")

    def _validate_table_shapes(self) -> None:
        tables = (
            (
                self._transfer_policies,
                "asset lane transfer policies",
                AssetTransferPolicyV2,
                "asset",
                MAX_ASSET_LANE_ASSETS_V2,
            ),
            (
                self._managed_policies,
                "asset lane managed policies",
                ManagedAssetLifecyclePolicyV2,
                "asset",
                MAX_ASSET_LANE_ASSETS_V2,
            ),
            (
                self._balances,
                "asset lane balances",
                EconomicAmountV2,
                "key",
                MAX_ASSET_LANE_BALANCE_ROWS_V2,
            ),
            (
                self._supplies,
                "asset lane supplies",
                AssetSupplyV2,
                "asset",
                MAX_ASSET_LANE_ASSETS_V2,
            ),
        )
        for values, name, expected_type, key, limit in tables:
            if len(values) > limit:
                raise ValueError(f"{name} exceeds its {limit}-item ceiling")
            _require_ordered_objects_v2(
                values,
                name=name,
                expected_type=expected_type,
                key=key,
            )

    def _validate_asset_coverage(self) -> tuple[str, ...]:
        transfer_assets = tuple(policy.asset for policy in self._transfer_policies)
        registry_assets = tuple(row.asset for row in self._origin_registry.assets)
        supply_assets = tuple(row.asset for row in self._supplies)
        managed_assets = tuple(policy.asset for policy in self._managed_policies)
        registered_managed_assets = tuple(
            row.asset
            for row in self._origin_registry.assets
            if row.issue_policy_root != ZERO_ROOT_V2
        )
        if transfer_assets != registry_assets or transfer_assets != supply_assets:
            raise ValueError("asset lane registry, transfer, and supply coverage differ")
        if managed_assets != registered_managed_assets:
            raise ValueError("asset lane managed policy coverage differs from its registry")

        transfer_by_asset = {policy.asset: policy for policy in self._transfer_policies}
        for managed in self._managed_policies:
            transfer = transfer_by_asset[managed.asset]
            if (
                managed.asset_class is not transfer.asset_class
                or managed.asset_origin_root != transfer.asset_origin_root
                or managed.atom_decimals != transfer.atom_decimals
            ):
                raise ValueError("asset lane transfer and managed identities differ")
        return transfer_assets

    def _validate_owned_supply(self, transfer_assets: tuple[str, ...]) -> None:
        totals = {asset: 0 for asset in transfer_assets}
        for row in self._balances:
            if row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V2:
                raise ValueError("asset lane balance has the wrong custody domain")
            if row.amount_atoms == 0 or row.asset not in totals:
                raise ValueError("asset lane balance is outside the declared asset set")
            totals[row.asset] += row.amount_atoms
        for supply in self._supplies:
            if totals[supply.asset] != supply.amount_atoms:
                raise ValueError("asset lane owned account total must equal supply")

    @property
    def origin_registry(self) -> AssetOriginRegistryStateV2:
        return _snapshot_registry_state_v2(self._origin_registry)

    @property
    def transfer_policies(self) -> tuple[AssetTransferPolicyV2, ...]:
        return _snapshot_transfer_policies_v2(self._transfer_policies)

    @property
    def managed_policies(self) -> tuple[ManagedAssetLifecyclePolicyV2, ...]:
        return _snapshot_managed_policies_v2(self._managed_policies)

    @property
    def balances(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._balances,
            EconomicAmountV2,
            "asset lane balances",
        )

    @property
    def supplies(self) -> tuple[AssetSupplyV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._supplies,
            AssetSupplyV2,
            "asset lane supplies",
        )

    @property
    def state_root(self) -> str:
        return hash_global_v2("asset-lane-state-v2", self.to_canonical())

    @property
    def production_authority(self) -> str:
        return ASSET_LANE_PRODUCTION_AUTHORITY_V2

    @property
    def profile_authentication(self) -> str:
        return ASSET_LANE_PROFILE_AUTHENTICATION_V2

    def balance_atoms(self, owner: str, asset: str) -> int:
        _require_token_v2(owner, name="asset lane balance owner")
        _require_token_v2(asset, name="asset lane balance asset")
        return next(
            (
                row.amount_atoms
                for row in self._balances
                if row.owner == owner and row.asset == asset
            ),
            0,
        )

    def supply_atoms(self, asset: str) -> int:
        _require_token_v2(asset, name="asset lane supply asset")
        for row in self._supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown asset lane supply")

    def transfer_leaf_state(self) -> AssetTransferStateV2:
        return AssetTransferStateV2(
            self.module_release_id,
            self.transfer_policies,
            self.balances,
            self.supplies,
        )

    def managed_leaf_state(self) -> ManagedAssetLifecycleStateV2:
        managed_assets = {policy.asset for policy in self._managed_policies}
        return ManagedAssetLifecycleStateV2(
            self.module_release_id,
            self.managed_policies,
            tuple(row for row in self.balances if row.asset in managed_assets),
            tuple(row for row in self.supplies if row.asset in managed_assets),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_LANE_STATE_SCHEMA_V2,
            "module_release_id": self.module_release_id,
            "origin_registry": self.origin_registry,
            "transfer_policies": self.transfer_policies,
            "managed_policies": self.managed_policies,
            "balances": self.balances,
            "supplies": self.supplies,
        }


def _snapshot_asset_lane_state_v2(state: AssetLaneStateV2) -> AssetLaneStateV2:
    if type(state) is not AssetLaneStateV2:
        raise TypeError("asset lane state must be an exact typed value")
    return AssetLaneStateV2(
        state.module_release_id,
        state.origin_registry,
        state.transfer_policies,
        state.managed_policies,
        state.balances,
        state.supplies,
    )


def _policy_origin_bindings_hold_v2(state: AssetLaneStateV2) -> bool:
    """Check snapshot-local origin membership without granting authentication."""

    if type(state) is not AssetLaneStateV2:
        raise TypeError("asset lane policy binding state must be exact")
    try:
        for policy in state.transfer_policies:
            validate_asset_transfer_policy_origin_v2(state.origin_registry, policy)
        for policy in state.managed_policies:
            validate_managed_asset_policy_origin_v2(state.origin_registry, policy)
    except (TypeError, ValueError):
        return False
    return True


@dataclass(frozen=True, slots=True, init=False)
class AssetLaneContextV2:
    """Common leaf context with a privately owned occurrence snapshot."""

    writer_epoch: int
    module_release_id: str
    global_pre_state_root: str
    _occurrence: EconomicCommandOccurrenceV2 | None

    def __init__(
        self,
        writer_epoch: int,
        module_release_id: str,
        global_pre_state_root: str,
        occurrence: EconomicCommandOccurrenceV2 | None | object = _UNSET_V2,
    ) -> None:
        if occurrence is _UNSET_V2:
            raise TypeError("asset lane context requires an occurrence field")
        object.__setattr__(self, "writer_epoch", writer_epoch)
        object.__setattr__(self, "module_release_id", module_release_id)
        object.__setattr__(self, "global_pre_state_root", global_pre_state_root)
        _require_nonnegative_int_v2(writer_epoch, name="asset lane writer epoch")
        _require_root_v2(module_release_id, name="asset lane context release")
        _require_root_v2(global_pre_state_root, name="asset lane global pre-state")
        if occurrence is not None and type(occurrence) is not EconomicCommandOccurrenceV2:
            raise TypeError("asset lane occurrence must be exact")
        object.__setattr__(
            self,
            "_occurrence",
            None if occurrence is None else _snapshot_occurrence_v2(occurrence),
        )

    @property
    def occurrence(self) -> EconomicCommandOccurrenceV2 | None:
        return None if self._occurrence is None else _snapshot_occurrence_v2(self._occurrence)

    def transfer_context(self) -> AssetTransferContextV2:
        return AssetTransferContextV2(
            self.writer_epoch,
            self.module_release_id,
            self.global_pre_state_root,
            self.occurrence,
        )

    def managed_context(self) -> ManagedAssetLifecycleContextV2:
        return ManagedAssetLifecycleContextV2(
            self.writer_epoch,
            self.module_release_id,
            self.global_pre_state_root,
            self.occurrence,
        )


def _snapshot_asset_lane_context_v2(context: AssetLaneContextV2) -> AssetLaneContextV2:
    if type(context) is not AssetLaneContextV2:
        raise TypeError("asset lane context must be an exact typed value")
    return AssetLaneContextV2(
        context.writer_epoch,
        context.module_release_id,
        context.global_pre_state_root,
        context.occurrence,
    )


__all__ = [
    "ASSET_LANE_STATE_SCHEMA_V2",
    "ASSET_LANE_PRODUCTION_AUTHORITY_V2",
    "ASSET_LANE_PROFILE_AUTHENTICATION_V2",
    "MAX_ASSET_LANE_ASSETS_V2",
    "MAX_ASSET_LANE_BALANCE_ROWS_V2",
    "MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2",
    "AssetLaneStateV2",
    "AssetLaneContextV2",
    "_snapshot_asset_lane_state_v2",
    "_snapshot_asset_lane_context_v2",
    "_policy_origin_bindings_hold_v2",
]
