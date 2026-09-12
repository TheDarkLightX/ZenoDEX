from __future__ import annotations

import struct

import pytest

from src.core.asset_lane_coordinator_values_v2 import AssetLaneRouteV2
from src.core.asset_lane_custody_frame_v2 import (
    ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2,
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2,
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2,
    decode_asset_lane_custody_global_frame_v2,
    encode_asset_lane_custody_global_frame_v2,
)
from src.core.global_settlement_abi_v2_codec import GlobalSettlementCodecErrorV2

_PARTS = (b"ctx", b"pre", b"cmd", b"gpre", b"gpost")


def _literal_frame(tag: int, parts: tuple[bytes, ...] = _PARTS) -> bytes:
    return ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2 + bytes((tag,)) + b"".join(
        struct.pack("<I", len(part)) + part for part in parts
    )


@pytest.mark.parametrize(
    ("route", "tag"),
    (
        (AssetLaneRouteV2.TRANSFER, 0),
        (AssetLaneRouteV2.MANAGED_LIFECYCLE, 1),
    ),
)
def test_decoder_matches_independent_literal_layout_for_both_leaf_routes(
    route: AssetLaneRouteV2,
    tag: int,
) -> None:
    raw = _literal_frame(tag)

    decoded = decode_asset_lane_custody_global_frame_v2(raw)

    assert decoded == (route, *_PARTS)


@pytest.mark.parametrize(
    "route",
    (AssetLaneRouteV2.TRANSFER, AssetLaneRouteV2.MANAGED_LIFECYCLE),
)
def test_encoder_decoder_roundtrip_preserves_all_arbitrary_component_bytes(
    route: AssetLaneRouteV2,
) -> None:
    parts = (b"\x00\xff", b"{not-json", b"command", b"\x80", b"terminal")

    raw = encode_asset_lane_custody_global_frame_v2(route, *parts)

    assert decode_asset_lane_custody_global_frame_v2(raw) == (route, *parts)


def test_decoder_rejects_every_truncation_of_a_small_valid_frame() -> None:
    raw = _literal_frame(0)

    for end in range(len(raw)):
        with pytest.raises(GlobalSettlementCodecErrorV2):
            decode_asset_lane_custody_global_frame_v2(raw[:end])


def test_decoder_rejects_wrong_magic_and_all_unsupported_route_tags() -> None:
    wrong_magic = bytearray(_literal_frame(0))
    wrong_magic[0] ^= 1
    with pytest.raises(GlobalSettlementCodecErrorV2, match="magic"):
        decode_asset_lane_custody_global_frame_v2(bytes(wrong_magic))

    for tag in range(2, 256):
        with pytest.raises(GlobalSettlementCodecErrorV2, match="route"):
            decode_asset_lane_custody_global_frame_v2(_literal_frame(tag))


@pytest.mark.parametrize("component_index", range(5))
@pytest.mark.parametrize(
    ("length", "message"),
    (
        (0, "component exceeds its bound"),
        (
            MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2 + 1,
            "component exceeds its bound",
        ),
    ),
)
def test_decoder_rejects_zero_or_oversized_length_for_each_component(
    component_index: int,
    length: int,
    message: str,
) -> None:
    raw = bytearray(_literal_frame(0))
    length_offset = len(ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2) + 1
    for prior in range(component_index):
        length_offset += 4 + len(_PARTS[prior])
    raw[length_offset : length_offset + 4] = struct.pack("<I", length)

    with pytest.raises(GlobalSettlementCodecErrorV2, match=message):
        decode_asset_lane_custody_global_frame_v2(bytes(raw))


def test_decoder_accepts_exact_maximum_component_and_declared_frame_bound() -> None:
    component = b"x" * MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_COMPONENT_BYTES_V2
    raw = _literal_frame(1, (component,) * 5)

    assert len(raw) == MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2
    route, *decoded_parts = decode_asset_lane_custody_global_frame_v2(raw)

    assert route is AssetLaneRouteV2.MANAGED_LIFECYCLE
    assert tuple(decoded_parts) == (component,) * 5


def test_decoder_rejects_trailing_bytes_nonexact_input_and_oversized_frame() -> None:
    with pytest.raises(GlobalSettlementCodecErrorV2, match="trailing"):
        decode_asset_lane_custody_global_frame_v2(_literal_frame(0) + b"trailing")

    with pytest.raises(GlobalSettlementCodecErrorV2, match="type"):
        decode_asset_lane_custody_global_frame_v2(bytearray(_literal_frame(0)))

    with pytest.raises(GlobalSettlementCodecErrorV2, match="bound"):
        decode_asset_lane_custody_global_frame_v2(
            b"x" * (MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 + 1)
        )
