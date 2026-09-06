"""Semantic selection of the custody-complete ``ASSET_TRANSFER`` successor.

The reviewed custody specification subject lives at
``docs/specifications/asset-transfer-custody-semantic-bundle-v1.json``. Its
root is ``hash_global_v1`` over the decoded canonical JSON value under the
domain ``zenodex/asset-transfer-custody-semantic-bundle/v1``. This module
carries that root as a literal and performs no file IO; tests derive the same
literal independently from the committed canonical bytes.

Selection is a pure check over already-typed governed values. It requires the
occurrence-governed single-lane ``ASSET_TRANSFER`` route, the selected
``ASSET_TRANSFER`` module release, and the ``ASSET_TRANSFER`` coordinator from
the profile-bound registry to carry exactly this root. Version text, source and
toolchain roots, guest image ids, status flags, callbacks, and caller totals do
not select the successor. Passing this check mints no receipt, activation, or
publication authority; callers must still bind structurally and recompute.
"""

from __future__ import annotations

from typing import Final

from .asset_transfer_types_v1 import ASSET_TRANSFER_COMMAND_KIND_V1
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_settlement_types_v1 import EconomicProfileSnapshotV1, LaneIdV1

ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1: Final[str] = (
    "0x02e297f6d65affbae54509516e6c5816e60e994ef2c674495884072cd0939df1"
)
"""Root of the reviewed custody semantic bundle; the only root this selector accepts."""


def require_asset_transfer_custody_semantics_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> None:
    """Require the governed transfer route, module, and coordinator to carry the root.

    The route is the profile's governed ``asset_transfer`` route for the
    occurrence's claimed release id, and it must consume exactly the single
    ``ASSET_TRANSFER`` lane whose ``module_release_ids[0]`` is the selected
    module release. The module release, the coordinator release, and the route
    must each carry ``ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1`` as
    ``specification_root``; an unknown root or a mixed family rejects. Profile
    activation, context, journal, and policy binding remain the structural
    binder's responsibility, and this check conveys no authority by itself.
    """

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("custody semantics profile type is not closed")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("custody semantics occurrence type is not closed")
    if occurrence.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1:
        raise ValueError("custody semantics require an asset transfer command")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if len(route.ordered_lanes) != 1 or route.ordered_lanes[0] is not LaneIdV1.ASSET_TRANSFER:
        raise ValueError("custody semantics require the single-lane ASSET_TRANSFER route")
    module = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    if route.module_release_ids[0] != module.release_id:
        raise ValueError("custody semantics route module release mismatch")
    coordinator = profile.lane_coordinator_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    selected_roots = (
        (module.specification_root, "module"),
        (coordinator.specification_root, "coordinator"),
        (route.specification_root, "route"),
    )
    for actual, label in selected_roots:
        if actual != ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1:
            raise ValueError(f"custody semantics {label} specification root mismatch")


__all__ = [
    "ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1",
    "require_asset_transfer_custody_semantics_v1",
]
