from __future__ import annotations

from pathlib import Path

from tools.operations_signature_sequence_grammar_fuzz import explore_target


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_operations_signature_sequence_reaches_signature_reuse_boundary() -> None:
    report = explore_target(
        max_depth=1,
        max_frontier=16,
        target_manifest=str(MANIFEST_PATH),
        target_id="operations_signature_reuse_boundary",
    )
    assert report.reached_target_ids == ("operations_signature_reuse_boundary",)
    labels = {case.outcome_label for case in report.cases}
    assert "ok:1" in labels
    assert "ValueError:Failed to parse signed intent 0: signature provided twice (envelope + field)" in labels
    assert "ValueError:Failed to parse signed intent 0: signature provided twice (envelope + field) and differs" in labels
