from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tauspec_ebrm_baseline_breakthrough_20260628" / "report.json"


def test_tauspec_ebrm_baseline_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tauspec_ebrm_baseline_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["breakthrough"]["spec_id"] == "tauspec_ebrm_frontier_selection_certificate_v1"
    assert report["candidate_count"] >= 8
    assert report["breakthrough"]["invalid_accepts"] == 0
    assert report["selection_tau"]["ok"] is True
    assert report["selection_tau"]["invalid_accepts"] == 0
    assert all(value == 1 for value in report["selector_facts"].values())
    assert all(row["latest"]["ok"] for row in report["candidates"])

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

    top_four = set(report["rankings"]["tau_spec_ebrm_v2"][:4])
    assert {"optimizer_quotient_certificate_v1", "route_split_window_certificate_v1"} <= top_four
    assert report["algorithm_work_items"]["1"]["ranking_status"] == "covered in TauSpecEBRM top-4"
    assert report["algorithm_work_items"]["2"]["ranking_status"] == "covered in TauSpecEBRM top-4"
