from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import ALL_LANE_IDS_V1, LaneIdV1
from src.core.lane_capability_registry_v1 import (
    LANE_CAPABILITY_REGISTRY_V1,
    LaneCapabilityDispositionV1,
    lane_capability_registry_root_v1,
    resolve_lane_capability_v1,
)

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "docs" / "research" / "ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"


def test_registry_exactly_matches_the_normative_12_lane_103_capability_surface() -> None:
    # Arrange
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = tuple(
        (
            LaneIdV1(row["lane_id"]),
            tuple(row["capabilities"]),
            LaneCapabilityDispositionV1(row["disposition"]),
        )
        for row in manifest["lanes"]
    )

    # Act
    actual = tuple(
        (row.lane_id, row.capability_ids, row.disposition)
        for row in LANE_CAPABILITY_REGISTRY_V1
    )

    # Assert
    assert actual == expected
    assert tuple(row.lane_id for row in LANE_CAPABILITY_REGISTRY_V1) == ALL_LANE_IDS_V1
    assert sum(len(row.capability_ids) for row in LANE_CAPABILITY_REGISTRY_V1) == 103


def test_every_declared_capability_resolves_to_exactly_one_lane() -> None:
    # Arrange / Act
    resolutions = tuple(
        resolve_lane_capability_v1(row.lane_id, capability_id)
        for row in LANE_CAPABILITY_REGISTRY_V1
        for capability_id in row.capability_ids
    )

    # Assert
    assert len(resolutions) == 103
    assert all(
        resolution.capability_id in resolution.lane.capability_ids
        for resolution in resolutions
    )


def test_unknown_or_cross_lane_capability_fails_closed() -> None:
    # Arrange / Act / Assert
    with pytest.raises(ValueError, match="unknown lane capability"):
        resolve_lane_capability_v1(LaneIdV1.ASSET_TRANSFER, "teleport_supply")
    with pytest.raises(ValueError, match="unknown lane capability"):
        resolve_lane_capability_v1(LaneIdV1.FARM_INCENTIVES, "exact_in_swap")
    with pytest.raises(TypeError, match="lane id must be exact"):
        resolve_lane_capability_v1("ASSET_TRANSFER", "generic_transfer")  # type: ignore[arg-type]


def test_only_the_empty_external_lane_has_the_disabled_disposition() -> None:
    # Arrange / Act
    disabled = tuple(
        row
        for row in LANE_CAPABILITY_REGISTRY_V1
        if row.disposition is LaneCapabilityDispositionV1.DISABLED_PENDING_COMPLETE_PROFILE
    )

    # Assert
    assert tuple(row.lane_id for row in disabled) == (LaneIdV1.EXTERNAL_CUSTODY,)
    assert len(disabled[0].capability_ids) == 9


def test_registry_root_is_stable_across_python_and_rust() -> None:
    # Arrange / Act / Assert
    assert lane_capability_registry_root_v1() == (
        "0x9dc72bc86a0e6081ca3fbe6c371803119bc6bf623fd87ceee2deba0d4192e465"
    )
