"""Closed owned result values for the V2 asset-lane coordinator."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias

from .asset_lane_state_v2 import (
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
    ASSET_LANE_PROFILE_AUTHENTICATION_V2,
    AssetLaneStateV2,
    _policy_origin_bindings_hold_v2,
    _snapshot_asset_lane_state_v2,
)
from .asset_transfer_types_v2 import (
    AssetTransferCommandV2,
    AssetTransferRejectCodeV2,
)
from .global_economic_proof_v2 import (
    LaneModuleTransitionJournalV2,
    _snapshot_module_journal_v2,
)
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_root_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleRejectCodeV2,
)

_ASSET_LANE_ACCEPTED_TOKEN_V2 = object()


class AssetLaneRouteV2(str, Enum):
    TRANSFER = "TRANSFER"
    MANAGED_LIFECYCLE = "MANAGED_LIFECYCLE"
    COORDINATOR = "COORDINATOR"


class AssetLaneCoordinatorRejectCodeV2(str, Enum):
    REGISTRY_BINDING_MISMATCH = "REGISTRY_BINDING_MISMATCH"
    CANDIDATE_BINDING_MISMATCH = "CANDIDATE_BINDING_MISMATCH"
    PROJECTION_MISMATCH = "PROJECTION_MISMATCH"


AssetLaneLeafRejectCodeV2: TypeAlias = (
    AssetTransferRejectCodeV2 | ManagedAssetLifecycleRejectCodeV2
)
AssetLaneRejectCodeV2: TypeAlias = (
    AssetLaneCoordinatorRejectCodeV2 | AssetLaneLeafRejectCodeV2
)
AssetLaneCommandV2: TypeAlias = (
    AssetTransferCommandV2 | ManagedAssetLifecycleCommandV2
)


def _snapshot_effects_v2(
    effects: GlobalEconomicEffectPlanV2,
) -> GlobalEconomicEffectPlanV2:
    if type(effects) is not GlobalEconomicEffectPlanV2:
        raise TypeError("asset lane effects must be exact")
    return GlobalEconomicEffectPlanV2(
        effects.rows,
        effects.asset_conservation,
        effects.fee_conservation,
        effects.lane_writes,
        effects.occurrence_consumptions,
        effects.external_outbox_enqueue,
    )


@dataclass(frozen=True, slots=True, init=False)
class AssetLaneAcceptedV2:
    route: AssetLaneRouteV2
    source_leaf_journal_root: str
    _post_state: AssetLaneStateV2
    _effects: GlobalEconomicEffectPlanV2
    _module_journal: LaneModuleTransitionJournalV2

    def __init__(
        self,
        token: object,
        route: AssetLaneRouteV2,
        source_leaf_journal_root: str,
        post_state: AssetLaneStateV2,
        effects: GlobalEconomicEffectPlanV2,
        module_journal: LaneModuleTransitionJournalV2,
    ) -> None:
        if token is not _ASSET_LANE_ACCEPTED_TOKEN_V2:
            raise TypeError("asset lane acceptance is checker-constructed")
        if type(route) is not AssetLaneRouteV2 or route is AssetLaneRouteV2.COORDINATOR:
            raise TypeError("asset lane accepted route must name a leaf")
        _require_root_v2(
            source_leaf_journal_root,
            name="asset lane source leaf journal",
        )
        object.__setattr__(self, "route", route)
        object.__setattr__(
            self,
            "source_leaf_journal_root",
            source_leaf_journal_root,
        )
        object.__setattr__(self, "_post_state", _snapshot_asset_lane_state_v2(post_state))
        object.__setattr__(self, "_effects", _snapshot_effects_v2(effects))
        object.__setattr__(
            self,
            "_module_journal",
            _snapshot_module_journal_v2(module_journal),
        )
        expected_write = (
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                self._module_journal.pre_lane_root,
                self._post_state.state_root,
            ),
        )
        if self._module_journal.lane_id is not LaneIdV2.ASSET_TRANSFER:
            raise ValueError("asset lane accepted journal names the wrong lane")
        if self._module_journal.post_lane_root != self._post_state.state_root:
            raise ValueError("asset lane accepted journal has the wrong post root")
        if self._module_journal.module_release_id != self._post_state.module_release_id:
            raise ValueError("asset lane accepted journal has the wrong module release")
        if self._effects.lane_writes != expected_write:
            raise ValueError("asset lane accepted effects have the wrong lane write")
        if self._module_journal.effect_plan_root != self._effects.effect_plan_root:
            raise ValueError("asset lane accepted effect root differs")
        if self._effects.occurrence_consumptions != (
            self._module_journal.command_occurrence_id,
        ):
            raise ValueError("asset lane accepted effects have the wrong occurrence")
        if self._effects.external_outbox_enqueue:
            raise ValueError("asset lane accepted candidate has an external outbox")
        if (
            self._module_journal.private_port_root != ZERO_ROOT_V2
            or self._module_journal.terminal_obligations_root != ZERO_ROOT_V2
            or self._module_journal.oracle_occurrence_plan_root != ZERO_ROOT_V2
        ):
            raise ValueError("asset lane accepted candidate has nonzero external roots")
        if not _policy_origin_bindings_hold_v2(self._post_state):
            raise ValueError("asset lane accepted registry binding differs")

    @property
    def post_state(self) -> AssetLaneStateV2:
        return _snapshot_asset_lane_state_v2(self._post_state)

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return _snapshot_effects_v2(self._effects)

    @property
    def module_journal(self) -> LaneModuleTransitionJournalV2:
        return _snapshot_module_journal_v2(self._module_journal)

    @property
    def receipt_root(self) -> str:
        return self._module_journal.receipt_root

    @property
    def production_authority(self) -> str:
        return ASSET_LANE_PRODUCTION_AUTHORITY_V2

    @property
    def profile_authentication(self) -> str:
        return ASSET_LANE_PROFILE_AUTHENTICATION_V2


@dataclass(frozen=True, slots=True, init=False)
class AssetLaneRejectedV2:
    route: AssetLaneRouteV2
    code: AssetLaneRejectCodeV2
    pre_state_root: str
    post_state_root: str
    _effects: GlobalEconomicEffectPlanV2

    def __init__(
        self,
        route: AssetLaneRouteV2,
        code: AssetLaneRejectCodeV2,
        pre_state_root: str,
        post_state_root: str,
        effects: GlobalEconomicEffectPlanV2,
    ) -> None:
        allowed_codes = (
            AssetLaneCoordinatorRejectCodeV2,
            AssetTransferRejectCodeV2,
            ManagedAssetLifecycleRejectCodeV2,
        )
        if type(route) is not AssetLaneRouteV2 or type(code) not in allowed_codes:
            raise TypeError("asset lane rejection is not closed")
        _require_root_v2(pre_state_root, name="asset lane rejected pre root")
        _require_root_v2(post_state_root, name="asset lane rejected post root")
        owned_effects = _snapshot_effects_v2(effects)
        if pre_state_root != post_state_root or not owned_effects.is_empty:
            raise ValueError("asset lane rejection must be an exact no-op")
        object.__setattr__(self, "route", route)
        object.__setattr__(self, "code", code)
        object.__setattr__(self, "pre_state_root", pre_state_root)
        object.__setattr__(self, "post_state_root", post_state_root)
        object.__setattr__(self, "_effects", owned_effects)

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return _snapshot_effects_v2(self._effects)

    @property
    def production_authority(self) -> str:
        return ASSET_LANE_PRODUCTION_AUTHORITY_V2

    @property
    def profile_authentication(self) -> str:
        return ASSET_LANE_PROFILE_AUTHENTICATION_V2


AssetLaneResultV2 = AssetLaneAcceptedV2 | AssetLaneRejectedV2


__all__ = [
    "AssetLaneRouteV2",
    "AssetLaneCoordinatorRejectCodeV2",
    "AssetLaneLeafRejectCodeV2",
    "AssetLaneRejectCodeV2",
    "AssetLaneCommandV2",
    "AssetLaneAcceptedV2",
    "AssetLaneRejectedV2",
    "AssetLaneResultV2",
]
