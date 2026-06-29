from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629 import (
    REPORT_JSON,
    find_tau_bin,
)

ROOT = Path(__file__).resolve().parents[2]


def test_ab_reserve_state_child_frontier_tau_certificate_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["breakthrough"]["spec_id"] == "ab_reserve_state_child_frontier_certificate_v1"
    assert report["lean"]["ok"] is True
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert all(value == 1 for value in report["facts"].values())

    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}
    assert cases["child_frontier_certificate_pass"]["got"]["o6"] == 1
    for case_id in (
        "missing_n7_child_frontier_reject",
        "missing_n8_sample_reject",
        "missing_transition_projection_reject",
        "missing_observed_summary_bridge_reject",
        "missing_lean_contract_reject",
        "missing_negative_controls_reject",
        "missing_scope_nonclaims_reject",
        "missing_bounded_n8_scope_reject",
        "authority_reject",
    ):
        assert cases[case_id]["got"]["o6"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 1

    nonclaims = "\n".join(report["non_claims"])
    assert "Python-to-Lean refinement" in nonclaims
    assert "exhaustive n=8 coverage" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
