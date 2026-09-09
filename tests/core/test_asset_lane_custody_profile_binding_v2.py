"""Direct input-binding evidence for the V2 custody profile predicate."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from src.core.asset_lane_custody_profile_binding_v2 import (
    require_asset_lane_custody_profile_binding_v2,
)
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2
from src.core.global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
)
from tests.core.test_asset_lane_custody_statement_parity_v2 import CASES, typed_inputs
from tests.core.test_lane_module_release_route_binding_v1 import _profile


def _binding_inputs() -> tuple[
    EconomicProfileSnapshotV1,
    AssetLaneContextV2,
    GlobalEconomicStateV2,
]:
    profile, routes = _profile()
    context, _, _, global_pre, _ = typed_inputs(CASES[0])
    occurrence = context.occurrence
    if occurrence is None:
        raise AssertionError("the fixed custody vector must contain an occurrence")

    aligned_global_pre = replace(
        global_pre,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        lane_roots=tuple(
            replace(
                lane_state,
                module_release_id=release.release_id,
                enabled=(
                    release.status is ReleaseStatusV1.ACTIVE_NEW and release.accepts_new_objects
                ),
            )
            for lane_state, release in zip(
                global_pre.lane_roots,
                profile.lane_registry.releases,
                strict=True,
            )
        ),
    )
    governed_route = routes[occurrence.command_kind]
    aligned_occurrence = replace(
        occurrence,
        profile_root=profile.profile_id,
        route_release_id=governed_route.route_release_id,
        pre_state_root=aligned_global_pre.state_root,
    )
    asset_release = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    aligned_context = AssetLaneContextV2(
        profile.authority_epoch,
        asset_release.release_id,
        aligned_global_pre.state_root,
        aligned_occurrence,
    )
    return profile, aligned_context, aligned_global_pre


def test_active_profile_and_aligned_predecessor_bind_without_input_mutation() -> None:
    profile, context, global_pre = _binding_inputs()
    before = (
        profile.to_canonical(),
        context.to_canonical(),
        global_pre.to_canonical(),
    )

    assert (
        require_asset_lane_custody_profile_binding_v2(  # type: ignore[func-returns-value]
            profile,
            context,
            global_pre,
        )
        is None
    )

    assert (
        profile.to_canonical(),
        context.to_canonical(),
        global_pre.to_canonical(),
    ) == before


@pytest.mark.parametrize(
    ("profile_status", "occurrence", "message"),
    (
        (
            ProfileStatusV1.SHADOW,
            True,
            r"^custody profile requires an ACTIVE profile$",
        ),
        (
            ProfileStatusV1.ACTIVE,
            False,
            r"^custody profile requires an occurrence$",
        ),
    ),
)
def test_profile_status_and_occurrence_are_direct_preconditions(
    profile_status: ProfileStatusV1,
    occurrence: bool,
    message: str,
) -> None:
    profile, context, global_pre = _binding_inputs()
    checked_profile = replace(profile, status=profile_status)
    checked_context = context
    if not occurrence:
        checked_context = AssetLaneContextV2(
            context.writer_epoch,
            context.module_release_id,
            context.global_pre_state_root,
            None,
        )

    with pytest.raises(ValueError, match=message):
        require_asset_lane_custody_profile_binding_v2(
            checked_profile,
            checked_context,
            global_pre,
        )


@pytest.mark.parametrize(
    ("field", "message"),
    (
        ("profile", r"^custody profile predecessor profile mismatch$"),
        ("epoch", r"^custody profile predecessor epoch mismatch$"),
    ),
)
def test_predecessor_profile_coordinates_reject_isolated_drift(
    field: str,
    message: str,
) -> None:
    profile, context, global_pre = _binding_inputs()
    if field == "profile":
        forged_global_pre = replace(global_pre, profile_root=profile.root_image_id)
    else:
        forged_global_pre = replace(
            global_pre,
            writer_epoch=profile.authority_epoch + 1,
        )

    with pytest.raises(ValueError, match=message):
        require_asset_lane_custody_profile_binding_v2(profile, context, forged_global_pre)


def test_stale_content_addressed_profile_cannot_bypass_snapshot_reconstruction() -> None:
    profile, context, global_pre = _binding_inputs()
    object.__setattr__(profile, "authority_epoch", profile.authority_epoch + 1)

    with pytest.raises(ValueError, match=r"^profile_id is not the exact content-derived id$"):
        require_asset_lane_custody_profile_binding_v2(profile, context, global_pre)


@pytest.mark.parametrize(
    ("index", "message"),
    (
        (0, r"^economic profile snapshot must have the exact typed value$"),
        (1, r"^asset lane context must be an exact typed value$"),
        (2, r"^global economic state snapshot requires the exact V2 type$"),
    ),
    ids=("profile", "context", "global_pre"),
)
def test_direct_api_rejects_malformed_snapshot_inputs(index: int, message: str) -> None:
    inputs: list[object] = list(_binding_inputs())
    inputs[index] = object()
    with pytest.raises(TypeError, match=message):
        require_asset_lane_custody_profile_binding_v2(
            cast(EconomicProfileSnapshotV1, inputs[0]),
            cast(AssetLaneContextV2, inputs[1]),
            cast(GlobalEconomicStateV2, inputs[2]),
        )
