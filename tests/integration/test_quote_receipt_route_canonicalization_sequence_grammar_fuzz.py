from __future__ import annotations

from pathlib import Path

from tools.quote_receipt_route_canonicalization_sequence_grammar_fuzz import explore_target, minimize_case


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_quote_receipt_route_canonicalization_sequence_reaches_receipt_and_route_surfaces() -> None:
    report = explore_target(
        max_depth=4,
        max_frontier=48,
        target_manifest=str(MANIFEST_PATH),
    )
    assert report.reached_target_ids == (
        "quote_receipt_certificate_boundary",
        "quote_receipt_pool_envelope_boundary",
        "route_canonicalization_boundary",
    )
    labels = {case.outcome_label for case in report.cases}
    assert "reject:step=1:bad_canonical_route_certificate:candidate_set_hash mismatch" in labels
    assert "reject:step=2:canonical_route_certificate_amount_out_mismatch" in labels
    assert "reject:step=4:missing_pool_fingerprint" in labels


def test_quote_receipt_route_canonicalization_minimize_preserves_candidate_set_hash_mismatch() -> None:
    witness = minimize_case("reorder_candidates_rehash")
    assert witness.outcome_label == "reject:step=1:bad_canonical_route_certificate:candidate_set_hash mismatch"


def test_quote_receipt_route_canonicalization_minimize_preserves_missing_pool_fingerprint() -> None:
    witness = minimize_case("drop_winner_rebuild_sync_body")
    assert witness.outcome_label == "reject:step=3:missing_pool_fingerprint"
    assert witness.path_id == "8d78016c8960bfea"
    assert witness.minimized_size == 232


def test_quote_receipt_route_canonicalization_minimize_preserves_full_repair_ok_path() -> None:
    witness = minimize_case("drop_winner_rebuild_sync_body_sync_pools")
    assert witness.outcome_label == "ok:steps=4"
