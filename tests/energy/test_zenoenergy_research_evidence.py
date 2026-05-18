from __future__ import annotations

from pathlib import Path

from tools.check_zenoenergy_research_evidence import replay_zenoenergy_evidence


ROOT = Path(__file__).resolve().parents[2]


def test_research_evidence_replay_receipt_passes_without_doctor() -> None:
    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)
    check_ids = {str(check["check_id"]) for check in report["checks"]}

    assert report["schema"] == "zenodex/energy/research_evidence_replay_receipt/v1"
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["passed_count"] == report["check_count"] == 33
    assert {
        "set_aware.negative_knowledge_recorded",
        "neighborhood.call_cost_negative",
        "repair_selector_cross_seed.compression_all_pairs",
        "repair_selector_cross_seed.hand_negative",
        "formal_boundary.names",
        "popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517",
    }.issubset(check_ids)
