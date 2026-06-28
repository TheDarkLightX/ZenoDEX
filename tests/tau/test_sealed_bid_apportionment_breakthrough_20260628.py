from __future__ import annotations

import json

from tools.zenodex_sealed_bid_apportionment_breakthrough_20260628 import (
    build_cases,
    build_certificate,
    build_report,
    owner_consolidated_fill_totals,
    split_bid_witness,
    verify_certificate,
)


def test_marginal_bucket_certificates_verify_quota_and_parity() -> None:
    certificates = [
        build_certificate(case_id=case_id, units_for_sale=units, bids=bids)
        for case_id, (units, bids) in build_cases().items()
    ]

    assert all(verify_certificate(certificate) for certificate in certificates)
    assert any(not certificate["single_bidder_scope_ok"] for certificate in certificates)


def test_certificate_rejects_privacy_and_quota_mutations() -> None:
    certificate = build_certificate(case_id="quota_parity", units_for_sale=5, bids=build_cases()["quota_parity"][1])

    leaked = json.loads(json.dumps(certificate))
    leaked["public_receipts"][0]["body"]["quantity"] = 3
    try:
        verify_certificate(leaked)
    except ValueError as exc:
        assert str(exc) == "public receipt rejected: private_field_leaked_quantity"
    else:
        raise AssertionError("private receipt leak accepted")

    bad_hash = json.loads(json.dumps(certificate))
    bad_hash["domain_hash"] = "0" * 64
    try:
        verify_certificate(bad_hash)
    except ValueError as exc:
        assert str(exc) == "domain hash mismatch"
    else:
        raise AssertionError("bad domain hash accepted")


def test_split_bid_witness_and_owner_consolidation_mitigation() -> None:
    witness = split_bid_witness()
    split_units, split_bids = build_cases()["split_bid_witness"]
    consolidated = owner_consolidated_fill_totals(units_for_sale=split_units, bids=split_bids)

    assert witness["base_alice_fill"] == 1
    assert witness["split_alice_fill"] == 2
    assert consolidated["alice"] == witness["base_alice_fill"]


def test_report_replays_tau_and_records_non_authority_boundary() -> None:
    report = build_report()

    assert report["ok"] is True
    assert report["tau"]["ok"] is True
    assert "Runtime sealed-bid settlement is unchanged" in report["breakthrough"]["authority_boundary"]
