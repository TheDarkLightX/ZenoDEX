from __future__ import annotations

import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"


def ensure_report() -> dict:
    if not REPORT.exists():
        subprocess.run(["python3", "run_cycle.py"], cwd=ROOT, check=True)
    return json.loads(REPORT.read_text())


def test_noarb_graphs_certified_and_injected_rejected() -> None:
    report = ensure_report()
    summary = report["summary"]
    assert summary["total_noarb_graphs"] == summary["total_noarb_certified"]
    assert summary["total_injected_graphs"] == summary["total_injected_rejected"]


def test_route_pruning_has_no_false_prunes() -> None:
    report = ensure_report()
    summary = report["summary"]
    assert summary["total_pruneable_candidates"] > 0
    assert summary["total_false_prunes"] == 0


def test_cpmm_floor_error_interval_has_no_violations() -> None:
    report = ensure_report()
    assert report["summary"]["total_floor_violations"] == 0
    for metrics in report["floor_metrics"].values():
        assert metrics["max_error_lt_one"] is True


def test_claim_tier_is_not_overstated() -> None:
    report = ensure_report()
    assert report["tier"] == "symbolic_state_compiler"
    assert report["oracle_dependent"] is True
    assert "not a production router" in report["non_claims"]
