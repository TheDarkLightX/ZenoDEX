from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_oracle_polytope_box_refuter_20260627" / "report.json"
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_polytope_box_refuter_20260627 import run_refuter  # noqa: E402


def _probe(report: dict, probe_id: str) -> dict:
    for row in report["probes"]:
        if row["probe_id"] == probe_id:
            return row
    raise AssertionError(f"missing probe {probe_id}")


def test_oracle_polytope_box_refuter_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_polytope_box_refuter_20260627.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["cartesian_promotion_refuted"] is True
    assert result["counterexample_count"] == 3

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["cartesian_promotion_refuted"] is True
    assert all(row["probe_matches_expectation"] for row in report["probes"])


def test_attack_margin_cartesian_counterexample_is_inside_one_field_intervals() -> None:
    report = run_refuter()
    probe = _probe(report, "attack_margin_cartesian_counterexample")
    assert probe["all_varied_fields_inside_one_field_intervals"] is True
    assert probe["actual_ok"] is False
    assert probe["cartesian_counterexample"] is True
    assert "attack_cost_floor_below_required_margin" in probe["errors"]


def test_reward_and_slash_cartesian_counterexamples_are_pinned() -> None:
    report = run_refuter()
    reward = _probe(report, "reporter_reward_cartesian_counterexample")
    slash = _probe(report, "slash_coverage_cartesian_counterexample")

    assert reward["all_varied_fields_inside_one_field_intervals"] is True
    assert reward["actual_ok"] is False
    assert "reporter_reward_budget_exceeded" in reward["errors"]

    assert slash["all_varied_fields_inside_one_field_intervals"] is True
    assert slash["actual_ok"] is False
    assert "slash_deterrence_below_required_margin" in slash["errors"]


def test_box_refuter_preserves_positive_controls_and_non_claims() -> None:
    report = run_refuter()
    baseline = _probe(report, "baseline_sample_accepts")
    lower_corner = _probe(report, "all_lower_bounds_control")
    non_claims = "\n".join(report["non_claims"])

    assert baseline["actual_ok"] is True
    assert lower_corner["actual_ok"] is True
    assert "does not invalidate the one-field interval compiler" in non_claims
    assert "does not construct the maximal coupled feasible region" in non_claims
