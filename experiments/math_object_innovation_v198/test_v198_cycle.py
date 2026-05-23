#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"


def load_report() -> dict:
    subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
    return json.loads(REPORT.read_text(encoding="utf-8"))


def cases_by_id(report: dict) -> dict[str, dict]:
    return {case["case_id"]: case for case in report["cases"]}


def test_disaster_potential_counts_and_audit() -> None:
    report = load_report()

    assert report["case_count"] == 108
    assert report["accepted_count"] == 54
    assert report["rejected_count"] == 54
    assert report["direct_repair_count"] == 12
    assert report["certified_recovery_count"] == 42
    assert report["catastrophic_rejection_count"] == 12
    assert report["model_audit"]["total_disaster_potential_invariant_failures"] == 0


def test_accepted_increasing_cases_require_recovery_certificate() -> None:
    report = load_report()

    for case in report["cases"]:
        if case["accepted"] and case["risk_delta"] > 0:
            assert case["recovery_certificate"] is True
            assert case["post_risk_score"] <= report["discovery_domain"]["recovery_cap"]


def test_nonincreasing_repairs_are_never_rejected() -> None:
    report = load_report()

    for case in report["cases"]:
        if case["risk_nonincrease"]:
            assert case["accepted"] is True


def test_missing_guards_reject_risk_increasing_cases() -> None:
    report = load_report()

    for case in report["cases"]:
        if case["risk_delta"] > 0 and case["guard_mode"] in {"none", "missing_first"}:
            assert case["accepted"] is False


def test_catastrophic_compound_rejects_even_with_all_guards() -> None:
    rows = cases_by_id(load_report())

    for state_id in ("clean", "edge_stale", "edge_resource"):
        case = rows[f"{state_id}::catastrophic_compound::all_known"]
        assert case["accepted"] is False
        assert case["post_risk_score"] > 48
