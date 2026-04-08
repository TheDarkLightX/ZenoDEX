from __future__ import annotations

from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.region_ba import RegionElement, build_cantor_region_ba
from src.integration.resource_load_shedding_regret_guard_regions import build_resource_load_shedding_regret_guard_regions
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def test_cantor_region_ba_exposes_expected_zero_one_and_boolean_ops() -> None:
    ba = build_cantor_region_ba()
    left = CantorPrefixRegion.from_strings(["0*"])
    right = CantorPrefixRegion.from_strings(["11*"])

    assert isinstance(ba.zero(), RegionElement)
    assert ba.zero().is_empty()
    assert ba.one().is_top()
    assert ba.join(left, right) == CantorPrefixRegion.from_strings(["0*", "11*"])
    assert ba.meet(left, right).is_empty()
    assert ba.disjoint(left, right) is True
    assert ba.leq(left, ba.one()) is True


def test_cantor_region_ba_partition_and_cube_count_match_backend() -> None:
    ba = build_cantor_region_ba()
    parts = CantorPrefixRegion.depth_partition(3)

    assert ba.partition_ok(parts) is True
    assert ba.cube_count(CantorPrefixRegion.from_strings(["0*", "11*"]), depth=3) == 6


def test_cantor_region_ba_product_projection_and_pullback_match_real_surfaces() -> None:
    ba = build_cantor_region_ba()
    zusd = build_zusd_recovery_mode_gate_regions()
    resource = build_resource_load_shedding_regret_guard_regions()

    combined = ba.product(
        zusd.action_allowed,
        left_depth=6,
        right=resource.final_admission_ok,
        right_depth=12,
    )

    assert ba.cube_count(combined, depth=18) == ba.cube_count(zusd.action_allowed, depth=6) * ba.cube_count(
        resource.final_admission_ok,
        depth=12,
    )
    assert ba.project(combined, source_depth=18, coordinates=tuple(range(6))) == zusd.action_allowed
    assert ba.project(combined, source_depth=18, coordinates=tuple(range(6, 18))) == resource.final_admission_ok

    lifted = ba.pullback(zusd.action_allowed, target_depth=6, source_depth=18, coordinates=tuple(range(6)))
    assert ba.leq(combined, lifted) is True
    assert ba.project(lifted, source_depth=18, coordinates=tuple(range(6))) == zusd.action_allowed
