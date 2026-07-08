from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.zenodex_cpss_bc_research_scope_certificate_20260628 import (
    REPORT_JSON,
    find_tau_bin,
)


ROOT = Path(__file__).resolve().parents[2]


def test_cpss_bc_research_scope_certificate_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_cpss_bc_research_scope_certificate_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["breakthrough"]["spec_id"] == "cpss_bc_research_scope_certificate_v1"
    assert report["lean"]["compile_ok"] is True
    assert report["lean"]["no_forbidden_tokens"] is True
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert all(value == 1 for value in report["facts"].values())

    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}
    assert cases["research_scope_certificate_pass"]["got"]["o5"] == 1
    for case_id in (
        "missing_window_scope_reject",
        "missing_group_sp_falsification_reject",
        "missing_precommit_collusion_reject",
        "missing_cpss_falsification_reject",
        "authority_reject",
        "missing_replay_execution_reject",
    ):
        assert cases[case_id]["got"]["o5"] == 0
    assert cases["inactive_safe"]["got"]["o6"] == 1

    assert "group strategyproofness" in "\n".join(report["non_claims"])
    assert "universal CPSS greedy dominance" in "\n".join(report["non_claims"])
