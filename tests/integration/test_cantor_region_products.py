from __future__ import annotations

from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.cantor_region_products import (
    enumerate_depth_words,
    product_region,
    project_left,
    project_right,
)
from src.integration.cantor_region_report import depth_cube_count
from src.integration.resource_load_shedding_regret_guard_regions import (
    build_resource_load_shedding_regret_guard_regions,
)
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def test_enumerate_depth_words_matches_cube_count() -> None:
    region = CantorPrefixRegion.from_strings(["0*", "11*"])
    words = enumerate_depth_words(region, 3)

    assert len(words) == depth_cube_count(region, 3)
    assert (0, 0, 0) in words
    assert (0, 1, 1) in words
    assert (1, 1, 0) in words
    assert (1, 0, 0) not in words


def test_product_region_count_multiplies_factor_counts() -> None:
    left = CantorPrefixRegion.from_strings(["0*"])
    right = CantorPrefixRegion.from_strings(["1*"])
    combined = product_region(left, left_depth=2, right=right, right_depth=3)

    assert depth_cube_count(combined, 5) == depth_cube_count(left, 2) * depth_cube_count(right, 3)


def test_product_region_projections_recover_factors() -> None:
    left = CantorPrefixRegion.from_strings(["0*", "11*"])
    right = CantorPrefixRegion.from_strings(["00*", "1*"])
    combined = product_region(left, left_depth=3, right=right, right_depth=3)

    assert project_left(combined, left_depth=3, right_depth=3) == left
    assert project_right(combined, left_depth=3, right_depth=3) == right


def test_product_region_on_real_surfaces_has_exact_count_and_projections() -> None:
    zusd_regions = build_zusd_recovery_mode_gate_regions()
    resource_regions = build_resource_load_shedding_regret_guard_regions()

    combined = product_region(
        zusd_regions.action_allowed,
        left_depth=6,
        right=resource_regions.final_admission_ok,
        right_depth=12,
    )

    combined_count = depth_cube_count(combined, 18)
    expected_count = depth_cube_count(zusd_regions.action_allowed, 6) * depth_cube_count(
        resource_regions.final_admission_ok,
        12,
    )

    assert combined_count == expected_count
    assert project_left(combined, left_depth=6, right_depth=12) == zusd_regions.action_allowed
    assert project_right(combined, left_depth=6, right_depth=12) == resource_regions.final_admission_ok
