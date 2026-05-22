from __future__ import annotations

from pathlib import Path

from tools.check_zenoenergy_synthetic_data_limits import (
    check_synthetic_data_limits,
)


ROOT = Path(__file__).resolve().parents[2]


def test_synthetic_data_limits_note_preserves_replay_boundary() -> None:
    report = check_synthetic_data_limits(root=ROOT)

    assert report["schema"] == "zenodex/energy/synthetic_data_limits_receipt/v1"
    assert report["ok"] is True
    assert report["passed_count"] == 6
    assert report["failed_count"] == 0
    assert report["source_count"] == 8
    assert report["decision"] == "synthetic_data_research_only_until_real_replay_gate"

    check_ids = {str(check["check_id"]) for check in report["checks"]}
    assert {
        "sources.model_collapse",
        "sources.transfer_and_solver_guidance",
        "boundary.verifier_labels",
        "boundary.no_real_replay_replacement",
        "coverage.tail_families",
        "gate.research_vs_production",
    } == check_ids

    negative = " ".join(str(item) for item in report["negative_knowledge"])
    assert "not production distribution evidence" in negative
    assert "Recursive synthetic replacement" in negative
    assert "Real replay" in negative
