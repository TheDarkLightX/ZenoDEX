from __future__ import annotations

from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.cantor_region_morphism_receipts import (
    build_cantor_region_product_projection_receipt,
    build_cantor_region_projection_receipt,
)
from src.integration.cantor_region_report import build_cantor_region_report
from src.integration.region_ba import build_cantor_region_ba
from src.integration.resource_load_shedding_regret_guard_regions import build_resource_load_shedding_regret_guard_regions
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def test_region_ba_driven_report_matches_partition_and_refinement_laws() -> None:
    ba = build_cantor_region_ba()
    zusd = build_zusd_recovery_mode_gate_regions()

    report = build_cantor_region_report(
        depth=6,
        regions={
            "risky_action_allowed": zusd.risky_action_allowed,
            "safe_non_risky_action_allowed": zusd.safe_non_risky_action_allowed,
            "denied": zusd.denied,
            "action_allowed": zusd.action_allowed,
        },
        partition=("risky_action_allowed", "safe_non_risky_action_allowed", "denied"),
        refinements=(("risky_action_allowed", "action_allowed"),),
        disjoint_pairs=(("risky_action_allowed", "denied"),),
        ba=ba,
    )

    assert report.partition_total is True
    assert report.refinements[0].holds is True
    assert report.disjoint_pairs[0].holds is True


def test_region_ba_driven_projection_receipt_matches_synthetic_surface() -> None:
    ba = build_cantor_region_ba()
    region = CantorPrefixRegion.from_strings(["000*", "011*", "101*"])

    receipt = build_cantor_region_projection_receipt(
        name="synthetic",
        source_region=region,
        source_depth=3,
        coordinates=(0, 2),
        ba=ba,
    )

    assert receipt.source_refines_lifted_projection is True
    assert receipt.project_after_lift_recovers_projection is True
    assert receipt.lift_cube_count_matches_factor is True


def test_region_ba_driven_product_receipt_matches_real_surface_product() -> None:
    ba = build_cantor_region_ba()
    zusd = build_zusd_recovery_mode_gate_regions()
    resource = build_resource_load_shedding_regret_guard_regions()

    receipt = build_cantor_region_product_projection_receipt(
        product_name="admission_product",
        left_name="zusd_action_allowed",
        left_region=zusd.action_allowed,
        left_depth=6,
        right_name="resource_final_admission",
        right_region=resource.final_admission_ok,
        right_depth=12,
        ba=ba,
    )

    assert receipt.product_cube_count_matches_factor_counts is True
    assert receipt.left_projection.project_after_lift_recovers_projection is True
    assert receipt.right_projection.project_after_lift_recovers_projection is True
