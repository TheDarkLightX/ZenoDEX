from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from tools.check_ab_strict_zero_min_exhaustive_small import REPORT_JSON, build_report


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def exhaustive_report() -> dict[str, Any]:
    return build_report()


def test_ab_strict_zero_min_exhaustive_small_report(exhaustive_report: dict[str, Any]) -> None:
    report = exhaustive_report
    search = report["search"]

    assert report["ok"] is True
    assert search["case_count"] == 15_300
    assert search["strict_scope_count"] > 0
    assert search["strict_mismatch_count"] == 0
    assert search["first_strict_mismatch"] is None
    assert search["overbroad_zero_min_boundary_count"] > 0
    assert search["first_overbroad_zero_min_boundary"] is not None
    assert report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_exhaustive_small_non_claims(exhaustive_report: dict[str, Any]) -> None:
    report = exhaustive_report
    non_claims = "\n".join(report["non_claims"])

    assert "not a proof" in non_claims
    assert "grid is finite" in non_claims
    assert "compressed full-mask execution fails" in non_claims
    assert "No settlement authority" in non_claims


def test_ab_strict_zero_min_exhaustive_small_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_exhaustive_small.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["strict_mismatch_count"] == 0
