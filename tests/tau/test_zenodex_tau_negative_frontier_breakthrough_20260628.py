from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_negative_frontier_breakthrough_20260628" / "report.json"
_REPORT_CACHE: dict | None = None


def _run_breakthrough() -> dict:
    global _REPORT_CACHE
    if _REPORT_CACHE is not None:
        return _REPORT_CACHE
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_negative_frontier_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    summary = json.loads(proc.stdout)
    assert summary["ok"] is True
    _REPORT_CACHE = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    return _REPORT_CACHE


def test_tau_negative_frontier_breakthrough_replay() -> None:
    report = _run_breakthrough()
    assert report["ok"] is True
    assert report["breakthrough"]["spec_id"] == "negative_frontier_entropy_campaign_certificate_v1"
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert len(report["tau"]["case_results"]) == 11
    assert all(case["ok"] for case in report["tau"]["case_results"])
    assert all(value == 1 for value in report["certificate_facts"].values())

    scheduler = report["scheduler"]
    assert scheduler["bounded_corpus_axis_count"] == 125
    assert scheduler["budget"] == 10
    assert scheduler["entropy_unique_family_count"] > scheduler["recency_unique_family_count"]
    assert scheduler["entropy_unique_family_count"] >= scheduler["stable_random_unique_family_count"]
    assert scheduler["priority_min"] >= 50
    assert all(control["ok"] for control in scheduler["negative_controls"])

    work = report["work_items"]
    assert work["1_ab_ordering"]["status"] == "covered"
    assert work["2_cow_matching"]["status"] == "covered"
    assert work["solver_portfolio_tau_invalid_accepts"] == 0
    assert work["tauspec_ebrm_work_items"]["AB"] is True
    assert work["tauspec_ebrm_work_items"]["CoW"] is True


def test_tau_negative_frontier_certificate_rejects_missing_rails() -> None:
    report = _run_breakthrough()
    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}

    assert cases["campaign_pass"]["got"]["o4"] == 1
    assert cases["recency_baseline_reject"]["got"]["o4"] == 0
    assert cases["random_baseline_reject"]["got"]["o4"] == 0
    assert cases["determinism_reject"]["got"]["o4"] == 0
    assert cases["severity_floor_reject"]["got"]["o4"] == 0
    assert cases["ab_work_item_reject"]["got"]["o2"] == 0
    assert cases["cow_work_item_reject"]["got"]["o2"] == 0
    assert cases["tau_runtime_subset_reject"]["got"]["o3"] == 0
    assert cases["negative_controls_reject"]["got"]["o4"] == 0
    assert cases["authority_reject"]["got"]["o4"] == 0
    assert cases["inactive_safe"]["got"]["o5"] == 1


def test_tau_negative_frontier_report_names_new_tau_specifications() -> None:
    report = _run_breakthrough()
    specs = {item["spec"] for item in report["new_tau_specifications"]}

    assert "src/tau_specs/recommended/negative_frontier_entropy_campaign_certificate_v1.tau" in specs
    assert "src/tau_specs/recommended/solver_portfolio_upgrade_certificate_v1.tau" in specs
    assert "src/tau_specs/recommended/tauspec_ebrm_frontier_selection_certificate_v1.tau" in specs
    assert report["tau_runtime_frontier"]["latest_stream_compat_ok"] is True
    assert "stream add/sub are rejected" in report["tau_runtime_frontier"]["runtime_rule"]
