"""Shared state and private-port values for the `ASSET_TRANSFER` lane.

These values are a deterministic research projection for lane composition.
They carry no receipt-verification or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .asset_transfer_types_v1 import AssetTransferStateV1
from .global_economic_proof_v1 import LaneCompositionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_dataclass_tuple_v1,
)
from .global_settlement_types_v1 import (
    MAX_ASSET_BALANCE_ROWS_V1,
    MAX_ASSET_CUSTODY_ROWS_V1,
    MAX_ASSET_POLICY_ROWS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    _require_nonnegative_int,
    _require_ordered_objects,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .managed_asset_lifecycle_types_v1 import ManagedAssetLifecycleStateV1

MAX_ASSET_LANE_BALANCE_ROWS_V1: Final = MAX_ASSET_BALANCE_ROWS_V1
"""The shared balance-row bound (Rust MAX_ASSET_BALANCE_ROWS_V1; Opus P19 N2, P20 NEW-2)."""

MAX_ASSET_LANE_CUSTODY_ROWS_V1: Final = MAX_ASSET_CUSTODY_ROWS_V1
"""The shared custody-row bound (Rust MAX_ASSET_CUSTODY_ROWS_V1; Opus P19 N2, P20 NEW-2)."""

MAX_ASSET_LANE_SUPPLY_ROWS_V1: Final = MAX_ASSET_POLICY_ROWS_V1
"""The shared policy/supply-row bound (Rust MAX_ASSET_POLICY_ROWS_V1; Opus P19 N2, P20 NEW-2)."""

ASSET_LANE_STATE_PROJECTION_SCHEMA_V1: Final = (
    "zenodex/asset-lane-state-projection/v1"
)
ASSET_LANE_PRIVATE_PORT_SCHEMA_V1: Final = "zenodex/asset-lane-private-port/v1"
ASSET_LANE_COORDINATOR_SCHEMA_V1: Final = "zenodex/asset-lane-coordinator/v1"
ACCOUNT_CUSTODY_DOMAIN_V1: Final = "accounts"


@dataclass(frozen=True, slots=True, order=True)
class AssetLaneModuleCompatibilityV1:
    module_release_id: str
    module_schema: str

    def __post_init__(self) -> None:
        _require_root(self.module_release_id, name="asset lane compatible module release")
        _require_token(self.module_schema, name="asset lane compatible module schema")

    def to_canonical(self) -> dict[str, object]:
        return {
            "module_release_id": self.module_release_id,
            "module_schema": self.module_schema,
        }


@dataclass(frozen=True, slots=True)
class AssetLaneStateProjectionV1:
    asset_policy_registry_root: str
    fee_policy_registry_root: str
    balances: tuple[EconomicAmountV1, ...]
    custody: tuple[EconomicAmountV1, ...]
    supplies: tuple[AssetSupplyV1, ...]

    def __post_init__(self) -> None:
        _require_root(
            self.asset_policy_registry_root,
            name="asset lane asset policy registry root",
        )
        _require_root(
            self.fee_policy_registry_root,
            name="asset lane fee policy registry root",
        )
        _require_ordered_objects(
            self.balances,
            name="asset lane balances",
            expected_type=EconomicAmountV1,
            key="key",
            maximum=MAX_ASSET_LANE_BALANCE_ROWS_V1,
        )
        _require_ordered_objects(
            self.custody,
            name="asset lane custody",
            expected_type=EconomicAmountV1,
            key="key",
            maximum=MAX_ASSET_LANE_CUSTODY_ROWS_V1,
        )
        _require_ordered_objects(
            self.supplies,
            name="asset lane supplies",
            expected_type=AssetSupplyV1,
            key="asset",
            maximum=MAX_ASSET_LANE_SUPPLY_ROWS_V1,
        )
        for row in self.balances:
            if row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1:
                raise ValueError("balance rows must use accounts custody domain")
            if row.amount_atoms == 0:
                raise ValueError("asset lane projection must omit zero balances")
        for row in self.custody:
            if row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V1:
                raise ValueError("custody rows must not use accounts custody domain")
            if row.amount_atoms == 0:
                raise ValueError("asset lane projection must omit zero custody rows")

        supply_by_asset = {row.asset: row.amount_atoms for row in self.supplies}
        total_by_asset = {asset: 0 for asset in supply_by_asset}
        for row in (*self.balances, *self.custody):
            if row.asset not in total_by_asset:
                raise ValueError("asset lane holding references an unnamed supply")
            total_by_asset[row.asset] += row.amount_atoms
        if any(
            total_by_asset[supply.asset] != supply.amount_atoms
            for supply in self.supplies
        ):
            raise ValueError("owned and custodied total must equal supply")

    @property
    def state_root(self) -> str:
        return hash_global_v1("asset-lane-state-projection-v1", self.to_canonical())

    def supply_atoms(self, asset: str) -> int:
        _require_token(asset, name="asset lane supply asset")
        for row in self.supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown asset lane supply")

    def owned_and_custodied_atoms(self, asset: str) -> int:
        _require_token(asset, name="asset lane holding asset")
        return sum(
            row.amount_atoms
            for row in (*self.balances, *self.custody)
            if row.asset == asset
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_LANE_STATE_PROJECTION_SCHEMA_V1,
            "asset_policy_registry_root": self.asset_policy_registry_root,
            "fee_policy_registry_root": self.fee_policy_registry_root,
            "balances": self.balances,
            "custody": self.custody,
            "supplies": self.supplies,
        }


def project_asset_transfer_state_v1(
    state: AssetTransferStateV1,
    *,
    asset_policy_registry_root: str,
    fee_policy_registry_root: str,
    custody: tuple[EconomicAmountV1, ...] = (),
) -> AssetLaneStateProjectionV1:
    if type(state) is not AssetTransferStateV1:
        raise TypeError("asset transfer projection source must be the exact typed value")
    return AssetLaneStateProjectionV1(
        asset_policy_registry_root,
        fee_policy_registry_root,
        state.balances,
        custody,
        state.supplies,
    )


def project_managed_asset_lifecycle_state_v1(
    state: ManagedAssetLifecycleStateV1,
    *,
    asset_policy_registry_root: str,
    fee_policy_registry_root: str,
    custody: tuple[EconomicAmountV1, ...] = (),
) -> AssetLaneStateProjectionV1:
    if type(state) is not ManagedAssetLifecycleStateV1:
        raise TypeError("managed asset projection source must be the exact typed value")
    return AssetLaneStateProjectionV1(
        asset_policy_registry_root,
        fee_policy_registry_root,
        state.balances,
        custody,
        state.supplies,
    )


@dataclass(frozen=True, slots=True)
class AssetLanePrivatePortV1:
    producer_module_schema: str
    module_release_id: str
    command_occurrence_id: str
    pre_state: AssetLaneStateProjectionV1
    post_state: AssetLaneStateProjectionV1
    module_effect_plan_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        _require_token(self.producer_module_schema, name="asset lane producer schema")
        _require_root(self.module_release_id, name="asset lane port module release")
        _require_root(self.command_occurrence_id, name="asset lane port occurrence")
        # Opus P28 F1: exact types, not isinstance -- a projection subclass can
        # skip validation or override state_root while the port hashes it.
        if type(self.pre_state) is not AssetLaneStateProjectionV1:
            raise TypeError("asset lane port pre-state must be the exact typed value")
        if type(self.post_state) is not AssetLaneStateProjectionV1:
            raise TypeError("asset lane port post-state must be the exact typed value")
        _require_root(self.module_effect_plan_root, name="asset lane port effect plan")
        _require_root(
            self.terminal_obligations_root,
            name="asset lane port terminal obligations",
            allow_zero=True,
        )

    @property
    def port_root(self) -> str:
        return hash_global_v1("asset-lane-private-port-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_LANE_PRIVATE_PORT_SCHEMA_V1,
            "producer_module_schema": self.producer_module_schema,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "pre_state": self.pre_state,
            "post_state": self.post_state,
            "module_effect_plan_root": self.module_effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


def _snapshot_asset_lane_state_projection_v1(
    state: AssetLaneStateProjectionV1,
) -> AssetLaneStateProjectionV1:
    if type(state) is not AssetLaneStateProjectionV1:
        raise TypeError("asset lane projection must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        state,
        name="asset lane projection",
        tuple_fields=frozenset({"balances", "custody", "supplies"}),
    )
    return replace(
        state,
        balances=_snapshot_dataclass_tuple_v1(
            state.balances,
            EconomicAmountV1,
            "asset lane projection balances",
        ),
        custody=_snapshot_dataclass_tuple_v1(
            state.custody,
            EconomicAmountV1,
            "asset lane projection custody",
        ),
        supplies=_snapshot_dataclass_tuple_v1(
            state.supplies,
            AssetSupplyV1,
            "asset lane projection supplies",
        ),
    )


def _snapshot_asset_lane_private_port_v1(
    port: AssetLanePrivatePortV1,
) -> AssetLanePrivatePortV1:
    if type(port) is not AssetLanePrivatePortV1:
        raise TypeError("asset lane private port must have the exact typed value")
    for field_name in (
        "producer_module_schema",
        "module_release_id",
        "command_occurrence_id",
        "module_effect_plan_root",
        "terminal_obligations_root",
    ):
        if type(getattr(port, field_name)) is not str:
            raise TypeError(f"asset lane private port {field_name} must be exact text")
    return AssetLanePrivatePortV1(
        producer_module_schema=port.producer_module_schema,
        module_release_id=port.module_release_id,
        command_occurrence_id=port.command_occurrence_id,
        pre_state=_snapshot_asset_lane_state_projection_v1(port.pre_state),
        post_state=_snapshot_asset_lane_state_projection_v1(port.post_state),
        module_effect_plan_root=port.module_effect_plan_root,
        terminal_obligations_root=port.terminal_obligations_root,
    )


@dataclass(frozen=True, slots=True)
class AssetLaneCoordinatorContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    coordinator_release_id: str
    command_occurrence_id: str
    asset_policy_registry_root: str
    fee_policy_registry_root: str
    compatible_modules: tuple[AssetLaneModuleCompatibilityV1, ...]

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="asset lane coordinator chain")
        for field_name in (
            "deployment_root",
            "profile_root",
            "coordinator_release_id",
            "command_occurrence_id",
            "asset_policy_registry_root",
            "fee_policy_registry_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"asset lane coordinator {field_name}",
            )
        _require_nonnegative_int(self.writer_epoch, name="asset lane coordinator epoch")
        _require_ordered_objects(
            self.compatible_modules,
            name="asset lane compatible modules",
            expected_type=AssetLaneModuleCompatibilityV1,
            key="module_release_id",
        )
        if not self.compatible_modules:
            raise ValueError("asset lane coordinator requires a compatible module")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_LANE_COORDINATOR_SCHEMA_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "coordinator_release_id": self.coordinator_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "asset_policy_registry_root": self.asset_policy_registry_root,
            "fee_policy_registry_root": self.fee_policy_registry_root,
            "compatible_modules": self.compatible_modules,
        }


class AssetLaneCoordinatorRejectCodeV1(str, Enum):
    CHAIN_MISMATCH = "CHAIN_MISMATCH"
    DEPLOYMENT_MISMATCH = "DEPLOYMENT_MISMATCH"
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    WRITER_EPOCH_MISMATCH = "WRITER_EPOCH_MISMATCH"
    WRONG_LANE = "WRONG_LANE"
    MODULE_NOT_REGISTERED = "MODULE_NOT_REGISTERED"
    MODULE_SCHEMA_MISMATCH = "MODULE_SCHEMA_MISMATCH"
    MODULE_RELEASE_MISMATCH = "MODULE_RELEASE_MISMATCH"
    OCCURRENCE_MISMATCH = "OCCURRENCE_MISMATCH"
    PRIVATE_PORT_UNBOUND = "PRIVATE_PORT_UNBOUND"
    PRIVATE_PORT_ROOT_MISMATCH = "PRIVATE_PORT_ROOT_MISMATCH"
    EFFECT_PLAN_MISMATCH = "EFFECT_PLAN_MISMATCH"
    TERMINAL_OBLIGATION_MISMATCH = "TERMINAL_OBLIGATION_MISMATCH"
    POLICY_ROOT_MISMATCH = "POLICY_ROOT_MISMATCH"
    OCCURRENCE_EFFECT_MISMATCH = "OCCURRENCE_EFFECT_MISMATCH"
    LANE_WRITE_SHAPE_MISMATCH = "LANE_WRITE_SHAPE_MISMATCH"
    EFFECT_KIND_FORBIDDEN = "EFFECT_KIND_FORBIDDEN"
    CONSERVATION_COVERAGE_MISMATCH = "CONSERVATION_COVERAGE_MISMATCH"
    CONSERVATION_STATE_MISMATCH = "CONSERVATION_STATE_MISMATCH"
    STATE_EFFECT_MISMATCH = "STATE_EFFECT_MISMATCH"
    EXTERNAL_OUTBOX_FORBIDDEN = "EXTERNAL_OUTBOX_FORBIDDEN"


@dataclass(frozen=True, slots=True)
class AssetLaneCompositionAcceptedV1:
    post_state: AssetLaneStateProjectionV1
    effects: GlobalEconomicEffectPlanV1
    lane_journal: LaneCompositionJournalV1

    def __post_init__(self) -> None:
        # Exact types (Opus P28 F1 audit, third site): the root comparisons below read
        # state_root / effect_plan_root / post_lane_root through properties a subclass
        # could override.
        if type(self.post_state) is not AssetLaneStateProjectionV1:
            raise TypeError("asset lane accepted post-state must be the exact typed value")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("asset lane accepted effects must be the exact typed value")
        if self.effects.is_empty:
            raise ValueError("asset lane acceptance requires effects")
        if type(self.lane_journal) is not LaneCompositionJournalV1:
            raise TypeError("asset lane accepted journal must be the exact typed value")
        if self.lane_journal.post_lane_root != self.post_state.state_root:
            raise ValueError("asset lane accepted post-state root mismatch")
        if self.lane_journal.effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("asset lane accepted effect-plan root mismatch")


@dataclass(frozen=True, slots=True)
class AssetLaneCompositionRejectedV1:
    code: AssetLaneCoordinatorRejectCodeV1
    pre_lane_root: str
    post_lane_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if type(self.code) is not AssetLaneCoordinatorRejectCodeV1:
            raise TypeError("asset lane reject code is not closed")
        _require_root(self.pre_lane_root, name="asset lane rejected pre-root")
        _require_root(self.post_lane_root, name="asset lane rejected post-root")
        if self.pre_lane_root != self.post_lane_root:
            raise ValueError("asset lane rejection changed state")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("asset lane rejected effects must be the exact typed value")
        if not self.effects.is_empty:
            raise ValueError("asset lane rejection carried effects")


AssetLaneCompositionResultV1 = (
    AssetLaneCompositionAcceptedV1 | AssetLaneCompositionRejectedV1
)


__all__ = [
    "ASSET_LANE_STATE_PROJECTION_SCHEMA_V1",
    "ASSET_LANE_PRIVATE_PORT_SCHEMA_V1",
    "ASSET_LANE_COORDINATOR_SCHEMA_V1",
    "AssetLaneModuleCompatibilityV1",
    "AssetLaneStateProjectionV1",
    "project_asset_transfer_state_v1",
    "project_managed_asset_lifecycle_state_v1",
    "AssetLanePrivatePortV1",
    "AssetLaneCoordinatorContextV1",
    "AssetLaneCoordinatorRejectCodeV1",
    "AssetLaneCompositionAcceptedV1",
    "AssetLaneCompositionRejectedV1",
    "AssetLaneCompositionResultV1",
]
