from __future__ import annotations

from src.integration.cantor_region_assurance_bundle import build_default_cantor_region_assurance_bundle
from src.integration.cantor_region_assurance_verify import verify_cantor_region_assurance_bundle_payload


def test_verify_accepts_default_bundle() -> None:
    payload = build_default_cantor_region_assurance_bundle().to_dict()

    ok, err = verify_cantor_region_assurance_bundle_payload(payload)

    assert ok is True
    assert err is None


def test_verify_rejects_broken_partition_total() -> None:
    payload = build_default_cantor_region_assurance_bundle().to_dict()
    payload["surfaces"][0]["report"]["partition_total"] = False

    ok, err = verify_cantor_region_assurance_bundle_payload(payload)

    assert ok is False
    assert "partition failed" in str(err)


def test_verify_rejects_default_mismatch_when_required() -> None:
    payload = build_default_cantor_region_assurance_bundle().to_dict()
    payload["product_receipts"][0]["product_name"] = "tampered"

    ok, err = verify_cantor_region_assurance_bundle_payload(payload, require_current_default=True)

    assert ok is False
    assert err == "bundle payload differs from current default construction"
