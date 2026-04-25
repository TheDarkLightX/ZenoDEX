from __future__ import annotations

from pathlib import Path

from tools.quote_receipt_sequence_grammar_fuzz import explore_target


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_quote_receipt_sequence_reaches_transport_and_stale_boundaries() -> None:
    report = explore_target(
        max_depth=1,
        max_frontier=16,
        target_manifest=str(MANIFEST_PATH),
    )
    assert report.reached_target_ids == (
        "quote_receipt_transport_boundary",
        "stale_quote_receipt_boundary",
    )
    labels = {case.outcome_label for case in report.cases}
    assert "ok:pools=2:nonces=aaaaaaaa=1" in labels
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert any("verifier_error='pool_snapshot_mismatch'" in label for label in labels)
    assert any("missing quote receipt witness:" in label for label in labels)
    assert any("quote receipt hash mismatch:" in label for label in labels)
