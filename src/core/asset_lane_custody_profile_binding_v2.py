"""Bind custody V2 inputs to an active V1 profile predecessor.

This is a pure compatibility check.  It creates no profile qualification,
signature, receipt, publication, or state-transition authority.
"""

from __future__ import annotations

from .asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_state_v2 import GlobalEconomicStateV2, snapshot_global_economic_state_v2
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
)


def require_asset_lane_custody_profile_binding_v2(
    profile: EconomicProfileSnapshotV1,
    context: AssetLaneContextV2,
    global_pre: GlobalEconomicStateV2,
) -> None:
    """Require the governed custody lane and predecessor-frame bindings."""

    owned_profile = snapshot_economic_profile_v1(profile)
    owned_context = _snapshot_asset_lane_context_v2(context)
    owned_global_pre = snapshot_global_economic_state_v2(global_pre)

    if owned_profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("custody profile requires an ACTIVE profile")
    occurrence = owned_context.occurrence
    if occurrence is None:
        raise ValueError("custody profile requires an occurrence")
    if owned_context.writer_epoch != owned_profile.authority_epoch:
        raise ValueError("custody profile writer epoch mismatch")

    route = owned_profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.ordered_lanes != (LaneIdV1.ASSET_TRANSFER,):
        raise ValueError("custody profile route lane name mismatch")

    custody_release = owned_profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    if owned_context.module_release_id != custody_release.release_id:
        raise ValueError("custody profile module release mismatch")

    _require_global_predecessor_binding_v2(owned_global_pre, owned_profile)


def _require_global_predecessor_binding_v2(
    global_pre: GlobalEconomicStateV2,
    profile: EconomicProfileSnapshotV1,
) -> None:
    if global_pre.profile_root != profile.profile_id:
        raise ValueError("custody profile predecessor profile mismatch")
    if global_pre.writer_epoch != profile.authority_epoch:
        raise ValueError("custody profile predecessor epoch mismatch")

    for lane_state, release in zip(
        global_pre.lane_roots,
        profile.lane_registry.releases,
        strict=True,
    ):
        if lane_state.lane_id.value != release.lane_id.value:
            raise ValueError("custody profile predecessor lane name mismatch")
        if lane_state.module_release_id != release.release_id:
            raise ValueError("custody profile predecessor lane release mismatch")
        expected_enabled = (
            release.status is ReleaseStatusV1.ACTIVE_NEW and release.accepts_new_objects
        )
        if lane_state.enabled is not expected_enabled:
            raise ValueError("custody profile predecessor enabled mismatch")


__all__ = ["require_asset_lane_custody_profile_binding_v2"]
