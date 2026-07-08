from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_negative_frontier_entropy_scheduler_20260628 import (
    REPORT_JSON,
    build_report,
    campaign_tasks,
    entropy_schedule,
    recency_schedule,
    stable_random_schedule,
)


ROOT = Path(__file__).resolve().parents[2]


def test_negative_frontier_entropy_scheduler_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "negative_frontier_entropy_scheduler_v1"
    assert report["tau"]["ok"] is True
    assert report["baseline_lift"]["unique_family_lift_vs_recency"] > 0
    assert report["baseline_lift"]["unique_family_lift_vs_stable_random"] > 0
    assert report["flags"]["ab_frontier_covered"] == 1
    assert report["flags"]["cow_frontier_covered"] == 1
    assert report["flags"]["no_authority_effect"] == 1
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_negative_frontier_entropy_scheduler_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_negative_frontier_entropy_scheduler_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["candidate_count"] == len(campaign_tasks())


def test_negative_frontier_entropy_scheduler_is_deterministic() -> None:
    tasks = campaign_tasks()

    assert entropy_schedule(tasks) == entropy_schedule(tasks)
    assert recency_schedule(tasks) == recency_schedule(tasks)
    assert stable_random_schedule(tasks) == stable_random_schedule(tasks)
    assert entropy_schedule(tasks) != recency_schedule(tasks)
