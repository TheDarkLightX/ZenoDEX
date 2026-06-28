from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_oracle_assumption_boundary_refuter_20260627" / "report.json"
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_assumption_boundary_refuter_20260627 import run_refuter  # noqa: E402


def _require_latest_tau() -> None:
    if not find_tau_bin(REPO, profile="latest"):
        pytest.skip("latest Tau binary not found")


def _case(report: dict, case_id: str) -> dict:
    for row in report["cases"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing case {case_id}")


def test_oracle_assumption_boundary_refuter_replay() -> None:
    _require_latest_tau()
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_assumption_boundary_refuter_20260627.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["case_count"] == 8
    assert result["false_declared_admit_count"] == 7
    assert result["computed_false_admit_count"] == 0

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["negative_case_count"] == 7
    assert report["host_certificate_ok"] is True


def test_computed_flags_reject_each_hidden_assumption_and_authority_gap() -> None:
    _require_latest_tau()
    report = run_refuter()
    expected_failures = {
        "missing_boundary_walls_rejects": ["i7"],
        "hidden_mev_assumption_rejects": ["i8"],
        "hidden_probability_assumption_rejects": ["i9"],
        "oracle_update_authority_rejects": ["i10"],
        "missing_fail_closed_default_rejects": ["i11"],
        "point_verifier_parity_missing_rejects": ["i6"],
        "honest_challenge_interval_missing_rejects": ["i3"],
    }

    valid = _case(report, "valid_oracle_envelope_accepts")
    assert valid["host_ok"] is True
    assert valid["declared_tau_accepts"] is True
    assert valid["computed_tau_accepts"] is True
    assert valid["failed_flags"] == []

    for case_id, failed_flags in expected_failures.items():
        row = _case(report, case_id)
        assert row["host_ok"] is False
        assert row["declared_tau_accepts"] is True
        assert row["computed_tau_accepts"] is False
        assert row["failed_flags"] == failed_flags
        assert row["expected_failed_flags_match"] is True


def test_oracle_assumption_boundary_non_claims_preserve_authority_boundary() -> None:
    report = run_refuter()
    non_claims = "\n".join(report["non_claims"])

    assert "does not estimate MEV" in non_claims
    assert "Forged all-true flags can still admit" in non_claims
    assert "pointwise economic-security verifier remains authoritative" in non_claims
