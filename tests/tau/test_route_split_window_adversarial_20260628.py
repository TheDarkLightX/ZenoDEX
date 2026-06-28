from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_route_split_window_adversarial import (
    REPORT_JSON,
    adversarial_split_cases,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


def test_route_split_window_adversarial_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["case_count"] == 24
    assert report["mismatch_count"] == 0
    assert report["tau"]["ok"] is True
    assert report["naive_first_difference_monotonicity_failure_count"] >= 20
    assert report["min_quote_call_reduction_ratio"] > 3.0
    assert report["max_quote_call_reduction_ratio"] > 15.0
    assert {"interior", "left_endpoint", "right_endpoint"}.issubset(set(report["winner_kinds"]))
    assert all(row["ok"] for row in report["cases"])
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_route_split_window_adversarial_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_route_split_window_adversarial.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["case_count"] == len(adversarial_split_cases())
    assert report["mismatch_count"] == 0
