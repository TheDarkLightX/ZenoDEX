from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_staircase_hostile_certificate_20260628" / "report.json"
_REPORT_CACHE: dict | None = None


def _run_certificate() -> dict:
    global _REPORT_CACHE
    if _REPORT_CACHE is not None:
        return _REPORT_CACHE
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_staircase_hostile_certificate_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    summary = json.loads(proc.stdout)
    assert summary["ok"] is True
    _REPORT_CACHE = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    return _REPORT_CACHE


def test_staircase_hostile_certificate_replay() -> None:
    report = _run_certificate()

    assert report["ok"] is True
    assert report["breakthrough"]["authority_boundary"].startswith("Advisory routing evidence only")
    assert all(value == 1 for value in report["certificate_facts"].values())
    assert report["hostile_corpus"]["case_count"] >= 120
    assert report["hostile_corpus"]["ok_case_count"] >= 110
    assert report["hostile_corpus"]["mismatch_count"] == 0
    assert report["hostile_corpus"]["leftmost_tie_break_mismatch_count"] == 0
    assert len(report["hostile_corpus"]["family_counts"]) >= 10
    assert report["profile_benchmark"]["summary"]["staircase_exact"]["oracle_match_count"] == report["profile_benchmark"]["case_count"]
    assert report["profile_benchmark"]["staircase_quote_count_total"] < report["profile_benchmark"]["oracle_quote_count_total"]
    assert report["known_gap"]["baseline_gap_observed"] is True
    assert report["known_gap"]["staircase_recovers_gap"] is True
    assert report["guarded_packet"]["guard_ok"] is True
    assert report["guarded_packet"]["payload_verify_ok"] is True


def test_staircase_hostile_tau_rejects_missing_rails() -> None:
    report = _run_certificate()
    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}

    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert len(cases) == 10
    assert cases["certificate_pass"]["got"]["o4"] == 1
    assert cases["parity_reject"]["got"]["o4"] == 0
    assert cases["tie_break_reject"]["got"]["o4"] == 0
    assert cases["quote_lift_reject"]["got"]["o4"] == 0
    assert cases["gap_recovery_reject"]["got"]["o4"] == 0
    assert cases["baseline_gap_reject"]["got"]["o4"] == 0
    assert cases["guarded_packet_reject"]["got"]["o4"] == 0
    assert cases["default_change_reject"]["got"]["o4"] == 0
    assert cases["authority_reject"]["got"]["o4"] == 0
    assert cases["inactive_safe"]["got"]["o5"] == 1


def test_staircase_certificate_preserves_non_claims() -> None:
    report = _run_certificate()
    non_claims = "\n".join(report["non_claims"])

    assert "does not change the live default" in non_claims
    assert "not a general CFMM network optimizer" in non_claims
    assert "bounded profile benchmark" in non_claims
