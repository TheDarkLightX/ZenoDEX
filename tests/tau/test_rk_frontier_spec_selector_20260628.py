from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_rk_frontier_spec_selector import (
    AXES,
    REPORT_JSON,
    build_report,
    build_selector_report,
    exact_dp_select,
    frontier_candidates,
    priority_baseline,
    single_lens_baseline,
)


ROOT = Path(__file__).resolve().parents[2]


def test_rk_frontier_spec_selector_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "rk_frontier_spec_selector_v1"
    assert all(value == 1 for value in report["flags"].values())
    assert report["tau"]["ok"] is True
    assert all(not row["accepted"] for row in report["mutation_checks"])
    assert report["selector"]["bruteforce_oracle"]["matches_dp"] is True
    assert report["selector"]["dp"]["selection"]["missing_axes"] == []


def test_rk_frontier_spec_selector_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_rk_frontier_spec_selector.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["selector"]["candidate_count"] == len(frontier_candidates())


def test_rk_frontier_dp_dominates_baselines_without_tau() -> None:
    candidates = frontier_candidates()
    dp = exact_dp_select(candidates)["selection"]
    priority = priority_baseline(candidates)
    single_lens = single_lens_baseline(candidates)
    selector = build_selector_report()

    assert len(candidates) >= 8
    assert len(selector["dp"]["selection"]["covered_axes"]) == len(AXES)
    assert selector["selector_checks"]["dominates_priority_baseline"] == 1
    assert selector["selector_checks"]["dominates_single_lens_baseline"] == 1
    assert set(selector["dp"]["selection"]["missing_axes"]) == set()
    assert set(selector["baselines"]["priority_order"]["missing_axes"])
    assert set(selector["baselines"]["single_lens"]["missing_axes"])
    assert sum(candidate.cost for candidate in dp) <= selector["budget"]
    assert sum(candidate.cost for candidate in priority) <= selector["budget"]
    assert sum(candidate.cost for candidate in single_lens) <= selector["budget"]
