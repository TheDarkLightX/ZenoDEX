from __future__ import annotations

from pathlib import Path

from tools.receipt_boundary_concolic_stateful import explore_target


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_receipt_boundary_concolic_stateful_reaches_certificate_surface() -> None:
    report = explore_target(
        "quote_receipt_verify_exact_in_certificate",
        max_depth=1,
        max_frontier=64,
        target_manifest=str(MANIFEST_PATH),
        target_id="quote_receipt_certificate_boundary",
    )
    assert report.reached_target_ids == ("quote_receipt_certificate_boundary",)
    assert report.unique_transition_count >= 10
    labels = {case.outcome_label for case in report.cases}
    assert "ok" in labels
    assert "reject:bad_canonical_route_certificate:certificate payload must be a dict" in labels
