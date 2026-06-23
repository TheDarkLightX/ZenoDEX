from __future__ import annotations

from pathlib import Path

from tools.check_zeno_oracle_disaster_frontier import (
    _build_live_inputs,
    frontier_content_hash,
    sample_frontier,
)
from tools.check_zeno_oracle_frontier_obligation_projection import (
    build_projection,
    check_projection,
)


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tools" / "zeno_oracle_disaster_obligation_certificate_manifest.json"


def _refresh_id(frontier: dict[str, object]) -> None:
    frontier["frontier_id"] = frontier_content_hash(frontier)


def test_frontier_obligation_projection_accepts_current_frontier() -> None:
    result = build_projection(manifest_path=MANIFEST)

    assert result["schema"] == "zenodex.oracle.frontier_obligation_projection.v1"
    assert result["status"] == "accepted"
    assert result["frontier_family_count"] == 35
    assert result["projected_family_count"] == 35
    assert result["closed_family_count"] == 30
    assert result["blocked_or_backlog_count"] == 5
    assert result["new_obligation_family_count"] == 0
    assert result["projection_relation_counts"]["unprojected"] == 0

    families = {row["family_id"]: row for row in result["families"]}
    settlement = families["settlement_execution_total_drift"]
    assert settlement["projection_relation"] == "dominated_class"
    assert settlement["dominated_by"]
    assert settlement["evidence_ok"] is True


def test_frontier_obligation_projection_rejects_frontier_evidence_drift() -> None:
    manifest, corpus_receipt, harness_receipt = _build_live_inputs(MANIFEST)
    frontier = sample_frontier()
    for family in frontier["families"]:
        assert isinstance(family, dict)
        if family.get("family_id") == "settlement_execution_total_drift":
            family["corpus_class_id"] = "missing_settlement_execution_total_drift"
            break
    else:  # pragma: no cover
        raise AssertionError("missing settlement drift frontier family")
    _refresh_id(frontier)

    result = check_projection(
        frontier,
        manifest=manifest,
        corpus_receipt=corpus_receipt,
        harness_receipt=harness_receipt,
    )

    assert result["status"] == "rejected"
    assert "frontier_rejected" in result["errors"]
    assert any(error.startswith("frontier:missing_corpus_class:settlement_execution_total_drift") for error in result["errors"])
