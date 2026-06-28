from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_ab_strict_zero_min_economic_refuter import REPORT_JSON, build_report


ROOT = Path(__file__).resolve().parents[2]


def test_ab_strict_zero_min_economic_refuter_report() -> None:
    report = build_report()
    search = report["search"]

    assert report["ok"] is True
    assert search["case_count"] == 600
    assert search["strict_scope_count"] == 330
    assert search["mismatch_count"] == 0
    assert search["brute_mismatch_count"] == 0
    assert search["brute_checked_count"] == 80
    assert search["ascending_amount_greedy_failure_count"] > 0
    assert search["descending_amount_greedy_failure_count"] > 0
    assert search["first_mismatch"] is None
    assert search["first_brute_mismatch"] is None
    assert report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_economic_refuter_non_claims() -> None:
    report = build_report()
    non_claims = "\n".join(report["non_claims"])

    assert "not a proof" in non_claims
    assert "Canonical tie order remains outside" in non_claims
    assert "Amount-sorted greedy orders are refuted" in non_claims
    assert "No settlement authority" in non_claims


def test_ab_strict_zero_min_economic_refuter_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_economic_refuter.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["mismatch_count"] == 0
