from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_negative_frontier_exact_scheduler import (
    REPORT_JSON,
    build_report,
    exact_schedule,
    scheduler_scenarios,
)


ROOT = Path(__file__).resolve().parents[2]


def test_negative_frontier_exact_scheduler_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "negative_frontier_exact_scheduler_v1"
    assert report["scenario_count"] >= 6
    assert report["total_combinations"] > 10_000
    assert report["strict_dominance_counts"]["greedy"] >= 3
    assert report["strict_dominance_counts"]["recency"] >= 3
    assert report["strict_dominance_counts"]["stable_random"] >= 3
    assert report["tau"]["ok"] is True
    assert all(row["exact_search_complete"] for row in report["scenarios"])
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_negative_frontier_exact_scheduler_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_negative_frontier_exact_scheduler.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["scenario_count"] == len(scheduler_scenarios())


def test_exact_scheduler_is_deterministic() -> None:
    for scenario in scheduler_scenarios():
        first, first_count = exact_schedule(scenario.tasks)
        second, second_count = exact_schedule(scenario.tasks)

        assert first == second
        assert first_count == second_count
        assert len(first) == 5
