from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_cow_capacity_dp_certificate import (
    REPORT_JSON,
    build_report,
    evidence_flags,
)


ROOT = Path(__file__).resolve().parents[2]


def test_cow_capacity_dp_certificate_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "cow_capacity_dp_certificate_v1"
    assert all(value == 1 for value in report["flags"].values())
    assert report["tau"]["ok"] is True
    assert report["evidence"]["capacity_breakthrough"]["case_count"] == 5
    assert report["evidence"]["capacity_adversarial"]["case_count"] == 20
    assert report["evidence"]["capacity_adversarial"]["assignment_safe_case_count"] == 0
    assert report["evidence"]["capacity_adversarial"]["greedy_lift_case_count"] >= 8
    assert all(row["same"] for row in report["deterministic_replay"]["rows"])
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_cow_capacity_dp_certificate_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_cow_capacity_dp_certificate.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau"]["ok"] is True


def test_cow_capacity_dp_certificate_requires_boundaries() -> None:
    evidence = {
        "capacity_breakthrough": {
            "ok": True,
            "case_count": 1,
            "exact_mismatch_count": 0,
            "core_mismatch_count": 0,
            "greedy_lift_case_count": 2,
            "max_total_candidates": 9,
            "cases": [{"dp_matches_bruteforce": True, "core_selector_matches_dp": True}],
            "breakthrough": {
                "authority_boundary": "Settlement materialization still performs fail-closed aggregate balance checks."
            },
            "non_claims": [
                "This is a bounded exact DP for small grouped-capacity CoW batches, not a polynomial algorithm for arbitrary grouped-capacity matching.",
                "Uncoupled large batches still use Hungarian assignment; large coupled batches still retain the greedy/fail-closed fallback.",
                "No settlement authority is derived from this research report.",
            ],
        },
        "capacity_adversarial": {
            "ok": True,
            "case_count": 20,
            "pattern_count": 5,
            "variants_per_pattern": 4,
            "exact_mismatch_count": 0,
            "core_mismatch_count": 0,
            "assignment_safe_case_count": 0,
            "greedy_lift_case_count": 8,
            "max_candidate_count": 14,
            "max_volume_lift": 1,
            "max_surplus_lift": 1,
            "cases": [{"dp_matches_bruteforce": True, "core_selector_matches_dp": True}],
            "non_claims": [
                "The result is bounded to small coupled-capacity CoW batches.",
                "Settlement authority remains with fail-closed materialization and balance checks.",
            ],
        },
        "shared_ab_cow_envelope": {
            "ok": True,
            "cow_matching": {"ok": True},
            "tau_envelope": {
                "ok": True,
                "cases": [
                    {"case_id": "cow_item_2_pass", "ok": True},
                    {"case_id": "coupled_capacity_reject", "ok": True},
                ],
            },
        },
    }
    flags = evidence_flags(evidence, {"ok": True})

    assert flags["grouped_capacity_scope_ok"] == 1
    assert flags["fallback_boundary_ok"] == 1
    assert flags["no_settlement_authority"] == 1
    assert flags["exact_assignment_boundary_ok"] == 1

    missing_fallback = dict(evidence)
    main = dict(missing_fallback["capacity_breakthrough"])
    main["non_claims"] = [main["non_claims"][0], main["non_claims"][2]]
    missing_fallback["capacity_breakthrough"] = main
    assert evidence_flags(missing_fallback, {"ok": True})["fallback_boundary_ok"] == 0

    missing_assignment_boundary = dict(evidence)
    shared = dict(missing_assignment_boundary["shared_ab_cow_envelope"])
    shared["tau_envelope"] = {"ok": True, "cases": [{"case_id": "cow_item_2_pass", "ok": True}]}
    missing_assignment_boundary["shared_ab_cow_envelope"] = shared
    assert evidence_flags(missing_assignment_boundary, {"ok": True})["exact_assignment_boundary_ok"] == 0
