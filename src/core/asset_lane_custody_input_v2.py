"""Pure canonical-input boundary for the custody-preserving V2 coordinator.

The route selects an existing command shape. Each input keeps its own existing
byte ceiling; bundling them must not narrow the admitted state domain. Decode
failure produces no transition result. Successful decoding establishes no
signature, profile, receipt or store authority.
"""

from typing import cast

from .asset_lane_coordinator_v2 import _route_and_owned_command_v2
from .asset_lane_coordinator_values_v2 import (
    AssetLaneCommandV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from .asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from .asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from .asset_lane_custody_frame_v2 import encode_asset_lane_custody_global_frame_v2
from .asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from .asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from .global_economic_state_v2 import GlobalEconomicStateV2, snapshot_global_economic_state_v2
from .global_settlement_abi_v2_codec import (
    GlobalSettlementCodecErrorV2,
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from .global_settlement_types_v2 import canonical_global_bytes_v2
from .global_settlement_wire_codec_v2 import (
    _decode_asset_lane_context_v2,
    _load_canonical_object_v2,
)


def _decode_context(raw: bytes) -> AssetLaneContextV2:
    return _decode_asset_lane_context_v2(_load_canonical_object_v2(raw)).to_domain_v2()


def transition_asset_lane_custody_bytes_v2(
    route: AssetLaneRouteV2,
    context_raw: bytes,
    pre_state_raw: bytes,
    command_raw: bytes,
) -> AssetLaneCustodyAcceptedV2 | AssetLaneRejectedV2:
    """Decode context, state, then command before the unchanged pure transition.

    Malformed inputs raise ``GlobalSettlementCodecErrorV2``. Well-formed inputs
    retain the coordinator's accepted or typed economic rejection outcome.
    """
    if type(route) is not AssetLaneRouteV2 or route not in (
        AssetLaneRouteV2.TRANSFER,
        AssetLaneRouteV2.MANAGED_LIFECYCLE,
    ):
        raise GlobalSettlementCodecErrorV2("custody input requires an exact leaf route")
    try:
        context = _decode_context(context_raw)
        state = decode_asset_lane_custody_state_v2(pre_state_raw)
        command: AssetLaneCommandV2
        if route is AssetLaneRouteV2.TRANSFER:
            command = decode_asset_transfer_command_v2(command_raw)
        else:
            command = decode_managed_asset_lifecycle_command_v2(command_raw)
    except GlobalSettlementCodecErrorV2:
        raise
    except (RecursionError, ValueError, TypeError) as error:
        raise GlobalSettlementCodecErrorV2("invalid custody input encoding") from error
    return transition_asset_lane_custody_v2(context, state, command)


def prepare_asset_lane_custody_global_prover_input_v2(
    context: AssetLaneContextV2,
    pre_state: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
    global_pre: GlobalEconomicStateV2,
) -> bytes | AssetLaneRejectedV2:
    """Execute from an owned predecessor and frame its derived global successor.

    Structural snapshot errors precede leaf execution. Leaf rejection returns
    unchanged; global-relation or frame bounds reject before any proving input
    is returned. The existing five-component guest format remains unchanged.
    This is deterministic witness preparation, without verification authority.
    """

    owned_context = _snapshot_asset_lane_context_v2(context)
    owned_pre = snapshot_asset_lane_custody_state_v2(pre_state)
    _, owned_command = _route_and_owned_command_v2(command)
    before = snapshot_global_economic_state_v2(global_pre)
    result = transition_asset_lane_custody_v2(owned_context, owned_pre, owned_command)
    if type(result) is AssetLaneRejectedV2:
        return result
    accepted = cast(AssetLaneCustodyAcceptedV2, result)
    occurrence = owned_context.occurrence
    if occurrence is None:
        raise ValueError("accepted custody prover input requires an occurrence")
    after = derive_asset_lane_custody_global_post_v2(owned_pre, accepted, before, occurrence)
    return encode_asset_lane_custody_global_frame_v2(
        accepted.route,
        canonical_global_bytes_v2(owned_context),
        canonical_global_bytes_v2(owned_pre),
        canonical_global_bytes_v2(owned_command),
        canonical_global_bytes_v2(before),
        canonical_global_bytes_v2(after),
    )
