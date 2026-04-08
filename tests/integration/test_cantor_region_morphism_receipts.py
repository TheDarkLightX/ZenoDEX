from __future__ import annotations

import json

from src.integration.cantor_prefix_algebra import CantorPrefixRegion
from src.integration.cantor_region_morphism_receipts import (
    build_cantor_region_product_projection_receipt,
    build_cantor_region_projection_receipt,
)
from src.integration.cantor_region_report import depth_cube_count
from src.integration.resource_load_shedding_regret_guard_regions import (
    build_resource_load_shedding_regret_guard_regions,
)
from src.integration.zusd_recovery_mode_gate_regions import build_zusd_recovery_mode_gate_regions


def test_projection_receipt_records_constructive_quotient_laws() -> None:
    source = CantorPrefixRegion.from_strings(["000*", "011*", "101*"])

    receipt = build_cantor_region_projection_receipt(
        name="synthetic",
        source_region=source,
        source_depth=3,
        coordinates=(0, 2),
    )

    assert receipt.target_depth == 2
    assert receipt.source_refines_lifted_projection is True
    assert receipt.project_after_lift_recovers_projection is True
    assert receipt.projected_cube_bound_holds is True
    assert receipt.lift_cube_factor == 2
    assert receipt.lift_cube_count_matches_factor is True


def test_projection_receipt_is_json_ready() -> None:
    source = CantorPrefixRegion.from_strings(["0*", "11*"])
    receipt = build_cantor_region_projection_receipt(
        name="jsonable",
        source_region=source,
        source_depth=3,
        coordinates=(0, 2),
    )

    payload = receipt.to_dict()

    assert payload["coordinates"] == [0, 2]
    assert payload["project_after_lift_recovers_projection"] is True
    assert json.loads(json.dumps(payload, sort_keys=True))["name"] == "jsonable"


def test_product_projection_receipt_on_real_surfaces_has_exact_factor_counts() -> None:
    zusd_regions = build_zusd_recovery_mode_gate_regions()
    resource_regions = build_resource_load_shedding_regret_guard_regions()

    receipt = build_cantor_region_product_projection_receipt(
        product_name="admission_product",
        left_name="zusd_action_allowed",
        left_region=zusd_regions.action_allowed,
        left_depth=6,
        right_name="resource_final_admission",
        right_region=resource_regions.final_admission_ok,
        right_depth=12,
    )

    assert receipt.product_cube_count_matches_factor_counts is True
    assert receipt.left_projection.projected.depth_cube_count == depth_cube_count(zusd_regions.action_allowed, 6)
    assert receipt.right_projection.projected.depth_cube_count == depth_cube_count(
        resource_regions.final_admission_ok,
        12,
    )
    assert receipt.left_projection.source_refines_lifted_projection is True
    assert receipt.right_projection.source_refines_lifted_projection is True
    assert receipt.left_projection.project_after_lift_recovers_projection is True
    assert receipt.right_projection.project_after_lift_recovers_projection is True
