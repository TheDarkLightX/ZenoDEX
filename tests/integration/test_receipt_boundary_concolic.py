from __future__ import annotations

from tools.receipt_boundary_concolic import explore_all_targets, explore_target

# These are discovery-atlas guardrails, not correctness proofs. They pin the
# current deterministic explorer's distinct traced paths so future refactors
# cannot silently shrink the malformed-receipt frontier.
MIN_PATHS = {
    "quote_receipt_verify": 12,
    "quote_receipt_verify_exact_in_certificate": 5,
    "confidential_receipt_verify": 16,
}

MIN_CASES = {
    "quote_receipt_verify": 26,
    "quote_receipt_verify_exact_in_certificate": 12,
    "confidential_receipt_verify": 52,
}


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def test_quote_receipt_boundary_concolic_discovers_reject_paths() -> None:
    report = explore_target("quote_receipt_verify")
    labels = _labels(report)
    assert "ok" in labels
    assert "reject:bad_receipt_type" in labels
    assert "reject:missing_body" in labels
    assert "reject:missing_receipt_hash" in labels
    assert "reject:hash_mismatch" in labels
    assert "reject:bad_kind" in labels
    assert "reject:unexpected_canonical_route_certificate" in labels
    assert "reject:bad_quote_epoch" in labels
    assert "reject:bad_pools" in labels
    assert "reject:bad_legs" in labels
    assert "reject:bad_pool_fingerprint" in labels
    assert "reject:missing_pool" in labels
    assert "reject:pool_snapshot_mismatch" in labels
    assert "reject:bad_leg" in labels
    assert "reject:bad_hops" in labels
    assert "reject:bad_leg_amounts" in labels
    assert "reject:bad_pool_id" in labels
    assert "reject:bad_assets" in labels
    assert "reject:leg_asset_in_mismatch" in labels
    assert "reject:bad_pool_direction" in labels
    assert "reject:hop_quote_error" in labels
    assert "reject:hop_quote_mismatch" in labels
    assert "reject:bad_body_amounts" in labels
    assert "reject:totals_mismatch" in labels
    assert report.unique_path_count >= MIN_PATHS["quote_receipt_verify"]



def test_exact_in_quote_receipt_boundary_concolic_discovers_certificate_reject_paths() -> None:
    report = explore_target("quote_receipt_verify_exact_in_certificate")
    labels = _labels(report)
    assert "ok" in labels
    assert "reject:bad_receipt_type" in labels
    assert "reject:missing_body" in labels
    assert "reject:missing_receipt_hash" in labels
    assert "reject:hash_mismatch" in labels
    assert "reject:bad_canonical_route_certificate:certificate payload must be a dict" in labels
    assert "reject:canonical_route_certificate_asset_in_mismatch" in labels
    assert "reject:canonical_route_certificate_asset_out_mismatch" in labels
    assert "reject:canonical_route_certificate_amount_in_mismatch" in labels
    assert "reject:canonical_route_certificate_amount_out_mismatch" in labels
    assert "reject:canonical_route_certificate_legs_mismatch" in labels
    assert report.unique_path_count >= MIN_PATHS["quote_receipt_verify_exact_in_certificate"]



def test_confidential_receipt_boundary_concolic_discovers_reject_paths() -> None:
    report = explore_target("confidential_receipt_verify")
    labels = _labels(report)
    assert "ok" in labels
    assert "reject:bad_receipt_type" in labels
    assert "reject:missing_body" in labels
    assert "reject:missing_receipt_hash" in labels
    assert "reject:hash_mismatch" in labels
    assert "reject:bad_schema" in labels
    assert "reject:bad_extension_id" in labels
    assert "reject:bad_provider_id" in labels
    assert "reject:bad_request_id" in labels
    assert "reject:bad_policy_version" in labels
    assert "reject:bad_policy_digest" in labels
    assert "reject:bad_measurement" in labels
    assert "reject:measurement_not_approved" in labels
    assert "reject:bad_host" in labels
    assert "reject:bad_attestation" in labels
    assert "reject:bad_accounting" in labels
    assert "reject:bad_numeric_field" in labels
    assert "reject:bad_do_execute" in labels
    assert "reject:bad_policy_ok" in labels
    assert "reject:bad_nonce_unused" in labels
    assert "reject:bad_output_bound_ok" in labels
    assert "reject:stale_attestation" in labels
    assert "reject:attestation_guard_failed" in labels
    assert "reject:accounting_guard_failed" in labels
    assert report.unique_path_count >= MIN_PATHS["confidential_receipt_verify"]



def test_receipt_boundary_concolic_all_targets_are_covered() -> None:
    reports = explore_all_targets()
    by_name = {report.target: report for report in reports}
    assert set(by_name) == {
        "quote_receipt_verify",
        "quote_receipt_verify_exact_in_certificate",
        "confidential_receipt_verify",
    }
    assert by_name["quote_receipt_verify"].total_cases >= MIN_CASES["quote_receipt_verify"]
    assert by_name["quote_receipt_verify_exact_in_certificate"].total_cases >= MIN_CASES["quote_receipt_verify_exact_in_certificate"]
    assert by_name["confidential_receipt_verify"].total_cases >= MIN_CASES["confidential_receipt_verify"]
