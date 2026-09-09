"""Prepare the bounded V2 custody/global statement without publication authority."""

from __future__ import annotations

from typing import Final, cast

from .asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from .asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from .asset_lane_custody_global_v2 import refine_asset_lane_custody_global_v2
from .asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from .asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from .global_economic_state_v2 import GlobalEconomicStateV2
from .global_settlement_types_v2 import canonical_global_bytes_v2

ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2: Final = (
    "zenodex/asset-lane-custody-global-statement/v2"
)


def prepare_asset_lane_custody_global_statement_v2(
    context: AssetLaneContextV2,
    pre_state: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
    global_pre: GlobalEconomicStateV2,
    global_post: GlobalEconomicStateV2,
) -> bytes | AssetLaneRejectedV2:
    """Emit the exact global roots and custody journal after accepted refinement.

    A custody rejection is returned unchanged before either global value is
    consumed. This producer creates no witness, receipt, publication, or
    authorization authority.
    """

    owned_context = _snapshot_asset_lane_context_v2(context)
    result = transition_asset_lane_custody_v2(owned_context, pre_state, command)
    if type(result) is AssetLaneRejectedV2:
        return result
    accepted = cast(AssetLaneCustodyAcceptedV2, result)
    occurrence = owned_context.occurrence
    if occurrence is None:
        raise ValueError("accepted custody statement requires an occurrence")
    refinement = refine_asset_lane_custody_global_v2(
        pre_state,
        accepted,
        global_pre,
        global_post,
        occurrence,
    )
    return canonical_global_bytes_v2(
        {
            "schema": ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2,
            "module_journal": accepted.module_journal,
            "global_pre_state_root": refinement.pre_state_root,
            "global_post_state_root": refinement.post_state_root,
        }
    )


__all__ = [
    "ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2",
    "prepare_asset_lane_custody_global_statement_v2",
]
