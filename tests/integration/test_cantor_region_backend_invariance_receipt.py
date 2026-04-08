from __future__ import annotations

from src.integration.cantor_region_backend_invariance_receipt import (
    CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA,
    build_cantor_region_backend_invariance_receipt,
)


def test_backend_invariance_receipt_is_json_ready_and_equal_for_prefix_vs_bdd() -> None:
    receipt = build_cantor_region_backend_invariance_receipt(left_backend="prefix", right_backend="bdd")
    payload = receipt.to_dict()

    assert payload["schema"] == CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA
    assert payload["left_backend"] == "prefix"
    assert payload["right_backend"] == "bdd"
    assert payload["payload_equal"] is True
    assert payload["shared_bundle_sha256"] == payload["left_bundle_sha256"] == payload["right_bundle_sha256"]
    assert payload["left_surface_count"] == payload["right_surface_count"] == 4
    assert payload["left_product_receipt_count"] == payload["right_product_receipt_count"] == 1
