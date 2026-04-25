from __future__ import annotations

from pathlib import Path

from tools.stale_settlement_sequence_grammar_fuzz import explore_target


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_stale_settlement_sequence_reaches_stale_settlement_boundary() -> None:
    report = explore_target(
        max_depth=1,
        max_frontier=16,
        target_manifest=str(MANIFEST_PATH),
        target_id="stale_settlement_boundary",
    )
    assert report.reached_target_ids == ("stale_settlement_boundary",)
    labels = {case.outcome_label for case in report.cases}
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert "reject:step=1:settlement mismatch" in labels
    assert "reject:step=1:missing settlement" in labels
