from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_cow_capacity_dp_adversarial import build_report as build_adversarial_report
from tools.zenodex_cow_capacity_dp_breakthrough_20260627 import build_report


ROOT = Path(__file__).resolve().parents[1]
REPORT_JSON = ROOT / "generated" / "zenodex_cow_capacity_dp_breakthrough_20260627" / "report.json"


def test_cow_capacity_dp_report_matches_bruteforce_and_finds_lift() -> None:
    report = build_report()
    assert report["ok"] is True
    assert report["case_count"] == 5
    assert report["exact_mismatch_count"] == 0
    assert report["core_mismatch_count"] == 0
    assert report["greedy_lift_case_count"] >= 2
    assert report["max_total_candidates"] == 9
    assert all(not row["assignment_balance_safe"] for row in report["cases"])


def test_cow_capacity_dp_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_cow_capacity_dp_breakthrough_20260627.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["exact_mismatch_count"] == 0
    assert report["core_mismatch_count"] == 0


def test_cow_capacity_dp_adversarial_report_matches_bruteforce() -> None:
    report = build_adversarial_report()
    assert report["ok"] is True
    assert report["case_count"] == 20
    assert report["exact_mismatch_count"] == 0
    assert report["core_mismatch_count"] == 0
    assert report["assignment_safe_case_count"] == 0
    assert report["greedy_lift_case_count"] >= 8
    assert report["max_candidate_count"] == 14


def test_cow_capacity_dp_adversarial_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_cow_capacity_dp_adversarial.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["exact_mismatch_count"] == 0
    assert report["core_mismatch_count"] == 0
