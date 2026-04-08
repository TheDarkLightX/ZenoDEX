from __future__ import annotations

import json

from src.integration.cantor_bdd_region import build_cantor_bdd_region_ba
from src.integration.cantor_region_assurance_bundle import (
    CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA,
    build_default_cantor_region_assurance_bundle,
)

def test_default_cantor_region_assurance_bundle_is_json_ready() -> None:
    bundle = build_default_cantor_region_assurance_bundle()
    payload = bundle.to_dict()

    assert payload["schema"] == CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA
    assert payload["surface_count"] == 4
    assert payload["product_receipt_count"] == 1
    assert json.loads(json.dumps(payload, sort_keys=True))["schema"] == CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA

def test_default_bundle_surface_partitions_and_product_receipt_hold() -> None:
    bundle = build_default_cantor_region_assurance_bundle()
    surface_payloads = {surface["name"]: surface["report"] for surface in bundle.to_dict()["surfaces"]}

    assert surface_payloads["settlement_witness_lifecycle"]["partition_total"] is True
    assert surface_payloads["exact_out_adaptive_liveness"]["partition_total"] is True
    assert surface_payloads["resource_load_shedding_regret_guard"]["partition_total"] is True
    assert surface_payloads["zusd_recovery_mode_gate"]["partition_total"] is True

    product_receipt = bundle.to_dict()["product_receipts"][0]
    assert product_receipt["product_cube_count_matches_factor_counts"] is True
    assert product_receipt["left_projection"]["project_after_lift_recovers_projection"] is True
    assert product_receipt["right_projection"]["project_after_lift_recovers_projection"] is True

def test_default_bundle_preserves_expected_depths() -> None:
    bundle = build_default_cantor_region_assurance_bundle()
    depths = {surface.name: surface.depth for surface in bundle.surfaces}

    assert depths == {
        "settlement_witness_lifecycle": 7,
        "exact_out_adaptive_liveness": 14,
        "resource_load_shedding_regret_guard": 12,
        "zusd_recovery_mode_gate": 6,
    }

def test_bdd_backend_emits_same_assurance_bundle_payload() -> None:
    prefix_payload = build_default_cantor_region_assurance_bundle().to_dict()
    bdd_payload = build_default_cantor_region_assurance_bundle(ba=build_cantor_bdd_region_ba()).to_dict()

    assert bdd_payload == prefix_payload
