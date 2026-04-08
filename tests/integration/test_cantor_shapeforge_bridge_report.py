from __future__ import annotations

import json

from src.integration.cantor_shapeforge_bridge_report import (
    SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA,
    build_cantor_shapeforge_bridge_report,
)


def test_cantor_shapeforge_bridge_report_is_json_ready() -> None:
    report = build_cantor_shapeforge_bridge_report()
    payload = report.to_dict()

    assert payload["schema"] == SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA
    assert payload["world_model_id"] == "zenodex_shape_reference_v3"
    assert payload["mapped_surface_count"] == 4
    assert payload["unmapped_surface_count"] == 0
    assert json.loads(json.dumps(payload, sort_keys=True))["schema"] == SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA


def test_cantor_shapeforge_bridge_report_maps_known_overlaps() -> None:
    report = build_cantor_shapeforge_bridge_report()
    mapped = {surface.surface_name: surface for surface in report.mapped_surfaces}

    assert mapped["settlement_witness_lifecycle"].primary_slice_id == "settlement_strong_validation"
    assert mapped["exact_out_adaptive_liveness"].primary_slice_id == "exact_out_audited_bounds_contract"
    assert mapped["exact_out_adaptive_liveness"].related_slice_ids == ("exact_out_adaptive_gate",)
    assert mapped["zusd_recovery_mode_gate"].primary_slice_id == "zusd_oracle_pending_gate"
    assert mapped["resource_load_shedding_regret_guard"].primary_slice_id == "resource_load_shedding_regret_guard"


def test_cantor_shapeforge_bridge_report_preserves_contract_laws() -> None:
    report = build_cantor_shapeforge_bridge_report()
    mapped = {surface.surface_name: surface for surface in report.mapped_surfaces}

    exact_out = mapped["exact_out_adaptive_liveness"]
    assert exact_out.partition_total is True
    assert ("liveness_ok", "coherent_surface") in exact_out.refinement_pairs
    assert ("budget_blocked", "coherent_surface") in exact_out.refinement_pairs

    settlement = mapped["settlement_witness_lifecycle"]
    assert ("accepted", "lifecycle_ok") in settlement.refinement_pairs
    assert ("accepted", "rejected") in settlement.disjoint_pairs


def test_cantor_shapeforge_bridge_report_maps_resource_shell() -> None:
    report = build_cantor_shapeforge_bridge_report()
    mapped = {surface.surface_name: surface for surface in report.mapped_surfaces}

    resource = mapped["resource_load_shedding_regret_guard"]
    assert resource.partition_total is True
    assert ("proof_gated", "final") in resource.refinement_pairs
    assert ("normal_only", "shed_only") in resource.disjoint_pairs


def test_cantor_shapeforge_bridge_report_includes_backend_invariance_receipt() -> None:
    report = build_cantor_shapeforge_bridge_report()

    assert report.backend_invariance["payload_equal"] is True
    assert report.backend_invariance["shared_bundle_sha256"] == report.backend_invariance["left_bundle_sha256"]
