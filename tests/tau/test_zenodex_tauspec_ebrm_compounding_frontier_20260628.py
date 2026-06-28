from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_tauspec_ebrm_compounding_frontier_20260628 import (
    CANDIDATES,
    REPORT_JSON,
    build_report,
    ranking_report,
    selector_facts,
    tau_cases,
)


ROOT = Path(__file__).resolve().parents[2]


def test_tauspec_ebrm_compounding_frontier_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["schema"] == "zenodex.tauspec_ebrm_compounding_frontier_report.v1"
    assert all(value == 1 for value in report["selector_facts"].values())
    assert report["ranking"]["candidate_count"] == len(CANDIDATES)
    assert report["ranking"]["top3_frontier_score"] >= report["ranking"]["baseline_max_top3_frontier_score"]
    assert report["ranking"]["coverage_top10"]["AB"] is True
    assert report["ranking"]["coverage_top10"]["CoW"] is True
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert report["tau"]["false_rejects"] == 0


def test_tauspec_ebrm_compounding_frontier_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0


def test_tauspec_ebrm_required_fact_mutations_cover_all_selector_inputs() -> None:
    report = build_report()
    case_ids = {case["case_id"] for case in report["tau"]["case_results"]}

    for input_index in range(2, 12):
        assert f"missing_i{input_index}_reject" in case_ids
    assert "inactive_safe" in case_ids
    assert all(case["ok"] for case in report["tau"]["case_results"])


def test_tauspec_ebrm_selector_facts_drop_when_ab_or_cow_is_missing() -> None:
    ranking = ranking_report()
    facts = selector_facts(ranking, {"all_present": True, "all_ok": True})
    cases = {case.case_id: case for case in tau_cases(facts)}

    assert facts["work_item_1_ab_covered"] == 1
    assert facts["work_item_2_cow_covered"] == 1
    assert cases["missing_i6_reject"].step["i6"] == 0
    assert cases["missing_i6_reject"].expected["o5"] == 0
    assert cases["missing_i7_reject"].step["i7"] == 0
    assert cases["missing_i7_reject"].expected["o5"] == 0
