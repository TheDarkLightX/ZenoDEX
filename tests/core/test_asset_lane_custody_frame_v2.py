"""Independent structural wire evidence for custody/global frames."""

from __future__ import annotations

import hashlib
import json
import struct
from pathlib import Path
from typing import Any, cast

import pytest

from src.core.asset_lane_coordinator_values_v2 import AssetLaneRouteV2
from src.core.asset_lane_custody_frame_v2 import (
    ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2,
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2,
    encode_asset_lane_custody_global_frame_v2,
)
from src.core.global_settlement_abi_v2_codec import GlobalSettlementCodecErrorV2
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2

FIXTURE = Path(__file__).parents[1] / "data" / "asset_lane_custody_statement_v2_golden.json"
COMPONENT_FIELDS = ("context", "pre_state", "command", "global_pre", "global_post")
COMPONENT_MAX_BYTES = 1_048_576
FRAME_MAGIC = b"ZDXCGV2\0"
ROUTE_TAG = {
    AssetLaneRouteV2.TRANSFER: 0,
    AssetLaneRouteV2.MANAGED_LIFECYCLE: 1,
}
CASES = cast(dict[str, Any], json.loads(FIXTURE.read_text(encoding="utf-8")))["cases"]


def _components(case: dict[str, Any]) -> tuple[bytes, bytes, bytes, bytes, bytes]:
    return cast(
        tuple[bytes, bytes, bytes, bytes, bytes],
        tuple(canonical_global_bytes_v2(case[field]) for field in COMPONENT_FIELDS),
    )


def _reference_frame(route: AssetLaneRouteV2, components: tuple[bytes, ...]) -> bytes:
    return (
        FRAME_MAGIC
        + bytes((ROUTE_TAG[route],))
        + b"".join(struct.pack("<I", len(raw)) + raw for raw in components)
    )


@pytest.mark.parametrize("case", CASES, ids=lambda case: case["name"])
def test_five_golden_inputs_have_exact_independent_frame_bytes_and_hashes(
    case: dict[str, Any],
) -> None:
    route = AssetLaneRouteV2(case["route"])
    components = _components(case)

    frame = encode_asset_lane_custody_global_frame_v2(route, *components)

    assert frame == _reference_frame(route, components)
    assert hashlib.sha256(frame).hexdigest() == case["frame_sha256"]


@pytest.mark.parametrize(
    ("route", "tag"),
    (
        (AssetLaneRouteV2.TRANSFER, 0),
        (AssetLaneRouteV2.MANAGED_LIFECYCLE, 1),
    ),
)
def test_leaf_routes_have_the_fixed_single_byte_tags(route: AssetLaneRouteV2, tag: int) -> None:
    components = _components(CASES[0])

    frame = encode_asset_lane_custody_global_frame_v2(route, *components)

    assert frame[:8] == FRAME_MAGIC
    assert frame[8] == tag


@pytest.mark.parametrize(
    ("malformed", "message"),
    (
        (b"", "must not be empty"),
        (b"x" * (COMPONENT_MAX_BYTES + 1), "exceeds the frame byte bound"),
        (bytearray(b"x"), "must be exact bytes"),
    ),
    ids=("empty", "oversize", "mutable_alias"),
)
def test_every_frame_component_rejects_empty_oversize_and_nonexact_bytes(
    malformed: object, message: str
) -> None:
    components: list[object] = list(_components(CASES[0]))
    for index in range(len(components)):
        components[index] = malformed
        with pytest.raises(GlobalSettlementCodecErrorV2, match=message):
            encode_asset_lane_custody_global_frame_v2(
                AssetLaneRouteV2.TRANSFER,
                *cast(tuple[bytes, bytes, bytes, bytes, bytes], tuple(components)),
            )
        components[index] = _components(CASES[0])[index]


def test_exact_five_component_maximum_forms_the_declared_frame_bound() -> None:
    component = b"x" * COMPONENT_MAX_BYTES
    components = (component,) * len(COMPONENT_FIELDS)

    frame = encode_asset_lane_custody_global_frame_v2(AssetLaneRouteV2.TRANSFER, *components)

    assert ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2 == FRAME_MAGIC
    assert MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 == 5_242_909
    assert len(frame) == MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2
    offset = len(FRAME_MAGIC) + 1
    view = memoryview(frame)
    for _ in COMPONENT_FIELDS:
        assert struct.unpack("<I", view[offset : offset + 4])[0] == COMPONENT_MAX_BYTES
        offset += 4
        assert view[offset : offset + COMPONENT_MAX_BYTES] == component
        offset += COMPONENT_MAX_BYTES
    assert offset == len(frame)


@pytest.mark.parametrize(
    "route",
    (
        AssetLaneRouteV2.COORDINATOR,
        "TRANSFER",
        0,
        None,
    ),
    ids=("coordinator", "text_alias", "integer_alias", "none"),
)
def test_nonleaf_or_nonexact_route_values_are_rejected(route: object) -> None:
    components = _components(CASES[0])

    with pytest.raises(GlobalSettlementCodecErrorV2, match="route"):
        encode_asset_lane_custody_global_frame_v2(
            cast(AssetLaneRouteV2, route),
            *components,
        )
