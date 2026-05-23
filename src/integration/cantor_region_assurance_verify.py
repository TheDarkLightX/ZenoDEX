from __future__ import annotations

from typing import Any, Mapping

from .cantor_region_assurance_bundle import (
    CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA,
    build_default_cantor_region_assurance_bundle,
)


_DEFAULT_SURFACE_DEPTHS = {
    "settlement_witness_lifecycle": 7,
    "exact_out_adaptive_liveness": 14,
    "resource_load_shedding_regret_guard": 12,
    "zusd_recovery_mode_gate": 6,
}


def verify_cantor_region_assurance_bundle_payload(
    payload: Mapping[str, Any],
    *,
    require_current_default: bool = False,
) -> tuple[bool, str | None]:
    if not isinstance(payload, Mapping):
        return False, "bundle payload must be an object"
    if payload.get("schema") != CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA:
        return False, "unsupported bundle schema"

    surfaces = payload.get("surfaces")
    product_receipts = payload.get("product_receipts")
    if not isinstance(surfaces, list) or not surfaces:
        return False, "surfaces must be a non-empty list"
    if not isinstance(product_receipts, list):
        return False, "product_receipts must be a list"
    if payload.get("surface_count") != len(surfaces):
        return False, "surface_count mismatch"
    if payload.get("product_receipt_count") != len(product_receipts):
        return False, "product_receipt_count mismatch"

    surface_names = set()
    for surface in surfaces:
        if not isinstance(surface, Mapping):
            return False, "surface entries must be objects"
        name = surface.get("name")
        depth = surface.get("depth")
        report = surface.get("report")
        if name not in _DEFAULT_SURFACE_DEPTHS:
            return False, f"unexpected surface name: {name!r}"
        if name in surface_names:
            return False, f"duplicate surface name: {name!r}"
        surface_names.add(str(name))
        if depth != _DEFAULT_SURFACE_DEPTHS[name]:
            return False, f"surface depth mismatch for {name!r}"
        if not isinstance(report, Mapping):
            return False, f"surface report missing for {name!r}"
        if report.get("partition_total") is not True:
            return False, f"surface partition failed for {name!r}"
        refinements = report.get("refinements")
        disjoint_pairs = report.get("disjoint_pairs")
        if not isinstance(refinements, list) or not isinstance(disjoint_pairs, list):
            return False, f"surface relations malformed for {name!r}"
        if any(not isinstance(rel, Mapping) or rel.get("holds") is not True for rel in refinements):
            return False, f"surface refinement failed for {name!r}"
        if any(not isinstance(rel, Mapping) or rel.get("holds") is not True for rel in disjoint_pairs):
            return False, f"surface disjointness failed for {name!r}"

    if surface_names != set(_DEFAULT_SURFACE_DEPTHS):
        return False, "surface set mismatch"

    for receipt in product_receipts:
        if not isinstance(receipt, Mapping):
            return False, "product receipt entries must be objects"
        if receipt.get("product_cube_count_matches_factor_counts") is not True:
            return False, "product factor-count law failed"
        left_projection = receipt.get("left_projection")
        right_projection = receipt.get("right_projection")
        if not isinstance(left_projection, Mapping) or not isinstance(right_projection, Mapping):
            return False, "product receipt projections malformed"
        for side_name, projection in (("left", left_projection), ("right", right_projection)):
            if projection.get("source_refines_lifted_projection") is not True:
                return False, f"{side_name} projection refinement failed"
            if projection.get("project_after_lift_recovers_projection") is not True:
                return False, f"{side_name} projection roundtrip failed"
            if projection.get("lift_cube_count_matches_factor") is not True:
                return False, f"{side_name} lift cube factor law failed"
            if projection.get("projected_cube_bound_holds") is not True:
                return False, f"{side_name} projected cube bound failed"

    if require_current_default:
        expected = build_default_cantor_region_assurance_bundle().to_dict()
        if dict(payload) != expected:
            return False, "bundle payload differs from current default construction"

    return True, None
