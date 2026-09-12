"""Structural V2 framing for custody/global canonical input bytes.

The frame carries bounded byte components for a downstream semantic preparer.
It performs no JSON decoding and creates no authority, statement, or receipt.
"""

from __future__ import annotations

from typing import Final

from .asset_lane_coordinator_values_v2 import AssetLaneRouteV2
from .global_settlement_abi_v2_codec import (
    MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2,
    GlobalSettlementCodecErrorV2,
)

ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2: Final = b"ZDXCGV2\0"
MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2: Final = MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2
MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2: Final = (
    len(ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2)
    + 1
    + 5 * (4 + MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2)
)


def _route_tag_v2(route: object) -> int:
    if type(route) is not AssetLaneRouteV2:
        raise GlobalSettlementCodecErrorV2("custody global frame route must be exact")
    if route is AssetLaneRouteV2.TRANSFER:
        return 0
    if route is AssetLaneRouteV2.MANAGED_LIFECYCLE:
        return 1
    raise GlobalSettlementCodecErrorV2("custody global frame route must name a leaf")


def _frame_component_v2(raw: object, *, name: str) -> bytes:
    if type(raw) is not bytes:
        raise GlobalSettlementCodecErrorV2(f"custody global frame {name} must be exact bytes")
    if not raw:
        raise GlobalSettlementCodecErrorV2(f"custody global frame {name} must not be empty")
    if len(raw) > MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2:
        raise GlobalSettlementCodecErrorV2(
            f"custody global frame {name} exceeds the frame byte bound"
        )
    return len(raw).to_bytes(4, "little") + raw


def encode_asset_lane_custody_global_frame_v2(
    route: AssetLaneRouteV2,
    context_raw: bytes,
    pre_state_raw: bytes,
    command_raw: bytes,
    global_pre_raw: bytes,
    global_post_raw: bytes,
) -> bytes:
    """Frame exactly five bounded canonical inputs for the selected leaf route."""

    route_tag = _route_tag_v2(route)
    components = (
        _frame_component_v2(context_raw, name="context"),
        _frame_component_v2(pre_state_raw, name="pre_state"),
        _frame_component_v2(command_raw, name="command"),
        _frame_component_v2(global_pre_raw, name="global_pre"),
        _frame_component_v2(global_post_raw, name="global_post"),
    )
    return ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2 + bytes((route_tag,)) + b"".join(components)


def decode_asset_lane_custody_global_frame_v2(
    raw: bytes,
) -> tuple[AssetLaneRouteV2, bytes, bytes, bytes, bytes, bytes]:
    """Read the existing five-component frame, without interpreting its bytes."""
    if type(raw) is not bytes or len(raw) > MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2:
        raise GlobalSettlementCodecErrorV2("custody global frame exceeds its type or byte bound")
    magic_size = len(ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2)
    if not raw.startswith(ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2) or len(raw) <= magic_size:
        raise GlobalSettlementCodecErrorV2("custody global frame magic or route is absent")
    routes = (AssetLaneRouteV2.TRANSFER, AssetLaneRouteV2.MANAGED_LIFECYCLE)
    tag = raw[magic_size]
    if tag >= len(routes):
        raise GlobalSettlementCodecErrorV2("custody global frame route is unknown")
    cursor = magic_size + 1
    components: list[bytes] = []
    for _ in range(5):
        if cursor + 4 > len(raw):
            raise GlobalSettlementCodecErrorV2("custody global frame length is truncated")
        size = int.from_bytes(raw[cursor : cursor + 4], "little")
        cursor += 4
        if not 1 <= size <= MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2:
            raise GlobalSettlementCodecErrorV2("custody global frame component exceeds its bound")
        end = cursor + size
        if end > len(raw):
            raise GlobalSettlementCodecErrorV2("custody global frame component is truncated")
        components.append(raw[cursor:end])
        cursor = end
    if cursor != len(raw):
        raise GlobalSettlementCodecErrorV2("custody global frame has trailing bytes")
    return routes[tag], components[0], components[1], components[2], components[3], components[4]


__all__ = [
    "ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2",
    "MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2",
    "MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2",
    "decode_asset_lane_custody_global_frame_v2",
    "encode_asset_lane_custody_global_frame_v2",
]
