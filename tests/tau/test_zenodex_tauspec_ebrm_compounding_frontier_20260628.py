from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_tauspec_ebrm_compounding_frontier_20260628 import (
    COMPOUNDING_TARGETS,
    REPORT_JSON,
)


ROOT = Path(__file__).resolve().parents[2]


def test_tauspec_ebrm_compounding_frontier_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["breakthrough"]["spec_id"] == "tauspec_ebrm_compounding_frontier_certificate_v1"
    assert report["candidate_count"] >= 13
    assert report["breakthrough"]["invalid_accepts"] == 0
    assert report["selection_tau"]["ok"] is True
    assert report["selection_tau"]["invalid_accepts"] == 0
    assert all(value == 1 for value in report["selector_facts"].values())
    assert all(row["latest"]["ok"] for row in report["candidates"])

    top_ten = set(report["rankings"]["tau_spec_ebrm_v2"][:10])
    assert COMPOUNDING_TARGETS <= top_ten
    assert all(report["coverage_top10"].values())

    selector_cases = {case["case_id"]: case for case in report["selection_tau"]["case_results"]}
    for case_id in (
        "invalid_accepts_reject",
        "baseline_score_reject",
        "staircase_coverage_reject",
        "negative_frontier_reject",
        "evidence_dag_reject",
        "tokenomics_reject",
        "authority_reject",
    ):
        assert selector_cases[case_id]["got"]["o6"] == 0
    assert selector_cases["inactive_safe"]["got"]["o7"] == 1

    ebrm = report["ranking_metrics"]["tau_spec_ebrm_v2"]
    baselines = {
        name: metrics
        for name, metrics in report["ranking_metrics"].items()
        if name != "tau_spec_ebrm_v2"
    }
    assert ebrm["invalid_accepts_topk"] == 0
    assert ebrm["topk_frontier_score"] >= max(
        metrics["topk_frontier_score"] for metrics in baselines.values()
    )
