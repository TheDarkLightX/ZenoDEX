from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[1]
REPORT_JSON = ROOT / "generated" / "zenodex_ab_frontier_dp_breakthrough_20260628" / "report.json"


def test_ab_frontier_dp_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_ab_frontier_dp_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["authority_boundary"] == (
        "No production ordering path changes; host/kernel verifiers remain authoritative for clearing and settlement."
    )
    assert report["frontier_dp"]["ok"] is True
    assert report["frontier_dp"]["dominance_pruning_observed"] is True
    assert report["frontier_dp"]["state_reduction_observed"] is False
    assert report["frontier_dp"]["total_state_reduction"] == 0
    assert report["frontier_dp"]["total_dominated_prunes"] > 0
    assert all(case["ok"] for case in report["frontier_dp"]["cases"])
    for case in report["frontier_dp"]["cases"]:
        assert case["bruteforce_key"] == case["full_state_key"] == case["frontier_key"]

    assert report["negative_replay"]["ok"] is True
    assert report["negative_replay"]["objective_loss_amount_a"] == 32

    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}
    assert cases["frontier_dp_pass"]["got"]["o4"] == 1
    assert cases["no_pruning_reject"]["got"]["o4"] == 0
    assert cases["parity_reject"]["got"]["o4"] == 0
    assert cases["dominance_loss_reject"]["got"]["o4"] == 0
    assert cases["authority_reject"]["got"]["o4"] == 0
    assert cases["inactive_safe"]["got"]["o5"] == 1

    assert "exact-in same-direction" in " ".join(report["non_claims"])
    assert "one-record-per-subset Held-Karp compression" in " ".join(report["non_claims"])
    assert "negative knowledge" in " ".join(report["non_claims"])
