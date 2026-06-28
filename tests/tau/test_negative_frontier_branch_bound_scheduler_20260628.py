from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_negative_frontier_branch_bound_scheduler import (
    REPORT_JSON,
    branch_bound_schedule,
    branch_bound_scenarios,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


def test_negative_frontier_branch_bound_scheduler_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "negative_frontier_branch_bound_scheduler_v1"
    assert report["scenario_count"] >= 9
    assert report["oracle_compared_count"] >= 8
    assert report["oracle_skipped_count"] >= 1
    assert report["max_combination_count"] > 1_000_000
    assert report["max_leaf_reduction_ratio"] > 50.0
    assert report["tau"]["ok"] is True
    assert all(row["branch_bound"]["unsafe_prune_count"] == 0 for row in report["scenarios"])
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_negative_frontier_branch_bound_scheduler_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_negative_frontier_branch_bound_scheduler.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["scenario_count"] == len(branch_bound_scenarios())


def test_branch_bound_scheduler_is_deterministic() -> None:
    for scenario in branch_bound_scenarios():
        first, first_metrics = branch_bound_schedule(scenario.tasks)
        second, second_metrics = branch_bound_schedule(scenario.tasks)

        assert first == second
        assert first_metrics["selected_task_ids"] == second_metrics["selected_task_ids"]
        assert len(first) == 5
