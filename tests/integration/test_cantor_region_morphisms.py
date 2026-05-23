from __future__ import annotations

from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.cantor_region_morphisms import project_coordinates, pullback_coordinates
from src.integration.cantor_region_products import product_region
from src.integration.cantor_region_report import depth_cube_count
from src.integration.resource_load_shedding_regret_guard_regions import build_resource_load_shedding_regret_guard_regions
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def test_project_coordinates_supports_noncontiguous_quotients() -> None:
    region = CantorPrefixRegion.from_strings(["010*", "111*"])
    projected = project_coordinates(region, source_depth=3, coordinates=(0, 2))

    assert projected == CantorPrefixRegion.from_strings(["00*", "11*"])


def test_pullback_coordinates_is_boolean_homomorphism() -> None:
    left = CantorPrefixRegion.from_strings(["0*"])
    right = CantorPrefixRegion.from_strings(["1*"])
    coords = (0,)

    pull_left = pullback_coordinates(left, target_depth=1, source_depth=3, coordinates=coords)
    pull_right = pullback_coordinates(right, target_depth=1, source_depth=3, coordinates=coords)

    assert pullback_coordinates(left | right, target_depth=1, source_depth=3, coordinates=coords) == (pull_left | pull_right)
    assert pullback_coordinates(left & right, target_depth=1, source_depth=3, coordinates=coords) == (pull_left & pull_right)
    assert pullback_coordinates(~left, target_depth=1, source_depth=3, coordinates=coords) == ~pull_left


def test_project_after_pullback_recovers_region() -> None:
    region = CantorPrefixRegion.from_strings(["00*", "11*"])
    coords = (0, 2)
    lifted = pullback_coordinates(region, target_depth=2, source_depth=4, coordinates=coords)

    assert project_coordinates(lifted, source_depth=4, coordinates=coords) == region


def test_coordinate_morphisms_on_real_surface_product() -> None:
    zusd_regions = build_zusd_recovery_mode_gate_regions()
    resource_regions = build_resource_load_shedding_regret_guard_regions()
    combined = product_region(
        zusd_regions.action_allowed,
        left_depth=6,
        right=resource_regions.final_admission_ok,
        right_depth=12,
    )

    assert project_coordinates(combined, source_depth=18, coordinates=tuple(range(6))) == zusd_regions.action_allowed
    assert project_coordinates(combined, source_depth=18, coordinates=tuple(range(6, 18))) == resource_regions.final_admission_ok

    lifted = pullback_coordinates(zusd_regions.action_allowed, target_depth=6, source_depth=18, coordinates=tuple(range(6)))
    assert depth_cube_count(lifted, 18) == depth_cube_count(zusd_regions.action_allowed, 6) * (1 << 12)
