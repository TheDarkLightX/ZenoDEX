from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_negative_frontier_entropy_scheduler_20260628" / "report.json"


def _run_scheduler() -> dict:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_negative_frontier_entropy_scheduler_20260628.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    return json.loads(REPORT_JSON.read_text(encoding="utf-8"))


def test_negative_frontier_entropy_scheduler_replay() -> None:
    report = _run_scheduler()
    result = {
        "entropy_unique_families": report["schedules"]["entropy"]["unique_family_count"],
        "recency_unique_families": report["schedules"]["recency"]["unique_family_count"],
        "stable_random_unique_families": report["schedules"]["stable_random"]["unique_family_count"],
        "priority_min": report["schedules"]["entropy"]["priority_min"],
    }
    assert result["entropy_unique_families"] > result["recency_unique_families"]
    assert result["entropy_unique_families"] >= result["stable_random_unique_families"]
    assert result["priority_min"] >= 50

    assert report["ok"] is True
    assert report["policy"]["bounded_corpus_axis_count"] == 125
    assert report["policy"]["budget"] == 10
    assert report["schedules"]["entropy"]["axis_count"] == 10
    assert all(control["ok"] for control in report["negative_controls"])


def test_entropy_schedule_is_deterministic_and_severity_bounded() -> None:
    first = _run_scheduler()
    second = _run_scheduler()

    assert first["schedules"]["entropy"]["axis_ids"] == second["schedules"]["entropy"]["axis_ids"]
    assert first["schedules"]["entropy"]["priority_min"] >= first["policy"]["min_priority_score"]
    assert second["schedules"]["entropy"]["priority_min"] >= second["policy"]["min_priority_score"]


def test_scheduler_beats_collapsed_recency_baseline_on_unique_families() -> None:
    report = _run_scheduler()
    entropy = report["schedules"]["entropy"]
    recency = report["schedules"]["recency"]

    assert entropy["unique_family_count"] > recency["unique_family_count"]
    assert entropy["post_schedule_entropy_nats"] > recency["post_schedule_entropy_nats"]
    assert "route_certificate" in recency["discovered_families"]
    assert set(entropy["discovered_families"]) - set(recency["discovered_families"])


def test_scheduler_preserves_advisory_authority_boundary() -> None:
    report = _run_scheduler()
    boundary = report["authority_boundary"]
    non_claims = "\n".join(report["non_claims"])

    assert boundary["advisory_only"] is True
    assert boundary["no_runtime_authority"] is True
    assert boundary["no_settlement_authority"] is True
    assert boundary["no_governance_authority"] is True
    assert "does not authorize settlement" in non_claims
    assert "does not prove that selected tasks will find real bugs" in non_claims
