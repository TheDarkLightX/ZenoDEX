from __future__ import annotations

from pathlib import Path

from tools.quote_receipt_cross_surface_sequence_grammar_fuzz import explore_target, minimize_case


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_quote_receipt_cross_surface_sequence_reaches_transport_certificate_and_stale_surfaces() -> None:
    report = explore_target(
        max_depth=1,
        max_frontier=8,
        target_manifest=str(MANIFEST_PATH),
    )
    assert report.reached_target_ids == (
        "quote_receipt_certificate_boundary",
        "quote_receipt_transport_boundary",
        "stale_quote_receipt_boundary",
    )
    labels = {case.outcome_label for case in report.cases}
    assert "reject:step=1:missing_receipt_hash" in labels
    assert "reject:step=1:pool_snapshot_mismatch" in labels
    assert "reject:step=1:bad_canonical_route_certificate:certificate payload mismatch" in labels


def test_quote_receipt_cross_surface_minimize_preserves_certificate_mismatch() -> None:
    witness = minimize_case("tamper_then_rehash")
    assert witness.target == "quote_receipt_cross_surface_sequence"
    assert witness.derivation == "tamper_then_rehash"
    assert witness.outcome_label == "reject:step=2:canonical_route_certificate_amount_out_mismatch"
    assert witness.path_id == "d74077898ae7d4fb"
    assert witness.path_length == 2
    assert witness.original_size == 118
    assert witness.minimized_size == 118


def test_quote_receipt_cross_surface_minimize_preserves_stale_snapshot_mismatch() -> None:
    witness = minimize_case("drift_pool_snapshot")
    assert witness.outcome_label == "reject:step=1:pool_snapshot_mismatch"


def test_quote_receipt_cross_surface_minimize_preserves_transport_repair_then_stale_snapshot() -> None:
    witness = minimize_case("drop_hash_then_rehash_then_drift")
    assert witness.target == "quote_receipt_cross_surface_sequence"
    assert witness.derivation == "drop_hash_then_rehash_then_drift"
    assert witness.outcome_label == "reject:step=3:pool_snapshot_mismatch"
    assert witness.path_id == "4f849d8b45d19c8b"
    assert witness.path_length == 3
    assert witness.original_size == 140
    assert witness.minimized_size == 140
