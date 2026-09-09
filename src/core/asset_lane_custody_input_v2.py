"""Pure canonical-input boundary for the custody-preserving V2 coordinator.

The route selects an existing command shape. Each input keeps its own existing
byte ceiling; bundling them must not narrow the admitted state domain. Decode
failure produces no transition result. Successful decoding establishes no
signature, profile, receipt or store authority.
"""

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
from .asset_lane_state_v2 import AssetLaneContextV2
from .global_settlement_abi_v2_codec import (
    GlobalSettlementCodecErrorV2,
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
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
