from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_cow_hungarian_matching_certificate import (
    REPORT_JSON,
    _evidence_flags,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


def test_cow_hungarian_matching_certificate_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "cow_hungarian_matching_certificate_v1"
    assert all(value == 1 for value in report["flags"].values())
    assert report["core"]["case_count"] == 25
    assert report["core"]["assignment_safe_case_count"] == 25
    assert report["core"]["mismatch_count"] == 0
    assert report["core"]["dual_violation_count"] == 0
    assert report["core"]["certified_assignment_mismatch_count"] == 0
    assert report["core"]["pair_tie_mismatch_count"] == 0
    assert report["core"]["coupled_boundary"]["naive_assignment_would_overdraw"] is True
    assert report["tau"]["ok"] is True
    assert report["tau"]["case_count"] == 13
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_cow_hungarian_matching_certificate_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_cow_hungarian_matching_certificate.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    summary = json.loads(proc.stdout)
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert summary["ok"] is True
    assert summary["tau_ok"] is True
    assert summary["mutation_accepts"] == 0
    assert report["ok"] is True
    assert report["tau"]["ok"] is True


def test_cow_hungarian_matching_certificate_flags_require_scope_and_authority() -> None:
    core = {
        "case_count": 25,
        "assignment_safe_case_count": 25,
        "mismatch_count": 0,
        "certified_assignment_mismatch_count": 0,
        "dual_violation_count": 0,
        "pair_tie_mismatch_count": 0,
        "max_candidate_count": 12,
        "coupled_boundary": {"naive_assignment_would_overdraw": True},
    }
    flags = _evidence_flags(core, {"ok": True})
    assert all(value == 1 for value in flags.values())

    missing_scope = dict(core)
    missing_scope["coupled_boundary"] = {"naive_assignment_would_overdraw": False}
    assert _evidence_flags(missing_scope, {"ok": True})["uncoupled_capacity_scope_ok"] == 0
    assert _evidence_flags(missing_scope, {"ok": True})["grouped_capacity_fallback_ok"] == 0

    missing_dual = dict(core)
    missing_dual["dual_violation_count"] = 1
    assert _evidence_flags(missing_dual, {"ok": True})["dual_certificate_ok"] == 0

    missing_replay = _evidence_flags(core, {"ok": False})
    assert missing_replay["replay_evidence_ok"] == 0
