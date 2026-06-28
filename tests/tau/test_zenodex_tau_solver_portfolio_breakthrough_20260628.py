from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_solver_portfolio_breakthrough_20260628" / "report.json"


def test_tau_solver_portfolio_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["spec_id"] == "solver_portfolio_upgrade_certificate_v1"
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert len(report["tau"]["case_results"]) == 8
    assert all(case["ok"] for case in report["tau"]["case_results"])
    assert all(value == 1 for value in report["portfolio_facts"].values())

    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}
    assert cases["portfolio_pass"]["got"]["o6"] == 1
    assert cases["ab_parity_reject"]["got"]["o6"] == 0
    assert cases["cow_scope_reject"]["got"]["o6"] == 0
    assert cases["negative_replay_reject"]["got"]["o6"] == 0
    assert cases["authority_reject"]["got"]["o6"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 1

    assert report["work_items"]["1_ab_ordering"]["status"] == "covered"
    assert report["work_items"]["2_cow_matching"]["status"] == "covered"
    assert report["supporting_reports"]["ab_cow_ok"] is True
    assert report["supporting_reports"]["cow_capacity_ok"] is True
    assert report["supporting_reports"]["cow_capacity_exact_mismatch_count"] == 0
    assert report["supporting_reports"]["cow_capacity_core_mismatch_count"] == 0
    assert "compressed Held-Karp" in report["work_items"]["1_ab_ordering"]["non_claim"]
    assert "arbitrary grouped-capacity CoW matching" in report["work_items"]["2_cow_matching"]["non_claim"]
