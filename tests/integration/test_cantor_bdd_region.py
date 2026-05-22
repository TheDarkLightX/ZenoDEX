from __future__ import annotations

from src.integration.cantor_bdd_region import CantorBDDRegion, build_cantor_bdd_region_ba
from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.cantor_region_morphism_receipts import (
    build_cantor_region_product_projection_receipt,
    build_cantor_region_projection_receipt,
)
from src.integration.cantor_region_report import build_cantor_region_report
from src.integration.resource_load_shedding_regret_guard_regions import build_resource_load_shedding_regret_guard_regions
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def _bdd(region: CantorPrefixRegion) -> CantorBDDRegion:
    return CantorBDDRegion.from_strings(region.to_strings())


def test_cantor_bdd_region_matches_prefix_backend_on_basic_boolean_ops() -> None:
    left = CantorPrefixRegion.from_strings(["0*", "111*"])
    right = CantorPrefixRegion.from_strings(["01*", "10*"])

    left_bdd = _bdd(left)
    right_bdd = _bdd(right)

    assert left_bdd.to_strings() == left.to_strings()
    assert right_bdd.to_strings() == right.to_strings()
    assert (left_bdd | right_bdd).to_strings() == (left | right).to_strings()
    assert (left_bdd & right_bdd).to_strings() == (left & right).to_strings()
    assert (~left_bdd).covers_word((1, 0, 0)) == (~left).covers_word((1, 0, 0))
    assert (left_bdd <= right_bdd) == (left <= right)


def test_cantor_bdd_region_preserves_skipped_variable_semantics() -> None:
    ba = build_cantor_bdd_region_ba()
    prefix_region = CantorPrefixRegion.from_strings(["01*", "11*"])
    bdd_region = _bdd(prefix_region)

    assert bdd_region.to_strings() == prefix_region.to_strings()
    assert bdd_region.covers_word((0, 1, 0)) is True
    assert bdd_region.covers_word((1, 0, 0)) is False
    assert ba.cube_count(bdd_region, depth=2) == 2
    assert ba.cube_count(bdd_region, depth=1) == 0


def test_cantor_bdd_region_ba_matches_real_surface_product_and_projection() -> None:
    ba = build_cantor_bdd_region_ba()
    zusd = build_zusd_recovery_mode_gate_regions()
    resource = build_resource_load_shedding_regret_guard_regions()

    left = _bdd(zusd.action_allowed)
    right = _bdd(resource.final_admission_ok)
    combined = ba.product(left, left_depth=6, right=right, right_depth=12)

    assert ba.cube_count(combined, depth=18) == ba.cube_count(left, depth=6) * ba.cube_count(right, depth=12)
    assert ba.project(combined, source_depth=18, coordinates=tuple(range(6))) == left
    assert ba.project(combined, source_depth=18, coordinates=tuple(range(6, 18))) == right

    lifted = ba.pullback(left, target_depth=6, source_depth=18, coordinates=tuple(range(6)))
    assert ba.leq(combined, lifted) is True


def test_cantor_bdd_region_ba_drives_reports_and_receipts() -> None:
    ba = build_cantor_bdd_region_ba()
    zusd = build_zusd_recovery_mode_gate_regions()
    resource = build_resource_load_shedding_regret_guard_regions()

    report = build_cantor_region_report(
        depth=6,
        regions={
            "risky_action_allowed": _bdd(zusd.risky_action_allowed),
            "safe_non_risky_action_allowed": _bdd(zusd.safe_non_risky_action_allowed),
            "denied": _bdd(zusd.denied),
            "action_allowed": _bdd(zusd.action_allowed),
        },
        partition=("risky_action_allowed", "safe_non_risky_action_allowed", "denied"),
        refinements=(("risky_action_allowed", "action_allowed"),),
        disjoint_pairs=(("risky_action_allowed", "denied"),),
        ba=ba,
    )
    projection_receipt = build_cantor_region_projection_receipt(
        name="synthetic",
        source_region=CantorBDDRegion.from_strings(["000*", "011*", "101*"]),
        source_depth=3,
        coordinates=(0, 2),
        ba=ba,
    )
    product_receipt = build_cantor_region_product_projection_receipt(
        product_name="admission_product",
        left_name="zusd_action_allowed",
        left_region=_bdd(zusd.action_allowed),
        left_depth=6,
        right_name="resource_final_admission",
        right_region=_bdd(resource.final_admission_ok),
        right_depth=12,
        ba=ba,
    )

    assert report.partition_total is True
    assert report.refinements[0].holds is True
    assert report.disjoint_pairs[0].holds is True
    assert projection_receipt.project_after_lift_recovers_projection is True
    assert product_receipt.product_cube_count_matches_factor_counts is True
