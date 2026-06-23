from __future__ import annotations

from pathlib import Path

from tools.check_zenoenergy_epiplexity_literature import (
    check_epiplexity_literature,
)


ROOT = Path(__file__).resolve().parents[2]


def test_epiplexity_literature_note_preserves_task_boundary() -> None:
    report = check_epiplexity_literature(root=ROOT)

    assert report["schema"] == "zenodex/energy/epiplexity_literature_receipt/v1"
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["passed_count"] == 7
    assert report["source_count"] == 6
    assert report["decision"] == "use_epiplexity_for_training_data_selection_only"

    check_ids = {str(check["check_id"]) for check in report["checks"]}
    assert {
        "sources.primary_epiplexity",
        "sources.proxy_counterexample",
        "mapping.task_relevance_gate",
        "mapping.proxy_boundary",
        "curriculum.proxy_receipt",
    }.issubset(check_ids)

    proxy = report["proxy"]
    assert proxy["classification"] == "measurable_bounded_structure"
    assert proxy["score"] == 0.358265
    assert proxy["policy_separation"] == 0.375

    negative = " ".join(str(item) for item in report["negative_knowledge"])
    assert "task-relevant heldout ranking improvement" in negative
    assert "not a correctness certificate" in negative
