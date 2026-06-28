from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_ab_subset_dp_dominance_certificate import (
    REPORT_JSON,
    build_report,
    evidence_flags,
)


ROOT = Path(__file__).resolve().parents[2]


def test_ab_subset_dp_dominance_certificate_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "ab_subset_dp_dominance_certificate_v1"
    assert all(value == 1 for value in report["flags"].values())
    assert report["tau"]["ok"] is True
    assert report["evidence"]["dominance_refuter"]["stats"]["dominance_pairs_checked"] > 0
    assert report["evidence"]["parity_reduction"]["summary"]["case_count"] == 24
    assert report["evidence"]["adversarial_corpus"]["summary"]["case_count"] == 33
    assert report["evidence"]["boundary_refuter"]["exact_out_counterexample_found"] is True
    assert report["evidence"]["boundary_refuter"]["mixed_direction_counterexample_found"] is True
    assert all(row["same"] for row in report["deterministic_replay"]["rows"])
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_ab_subset_dp_dominance_certificate_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_ab_subset_dp_dominance_certificate.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau"]["ok"] is True


def test_ab_subset_dp_boundary_refuters_are_required() -> None:
    evidence = {
        "dominance_refuter": {
            "ok": True,
            "first_counterexample": None,
            "candidate_rule": {"domain": "same-pool, same-direction, exact-in AB subset-DP states"},
            "stats": {"dominance_pairs_checked": 1, "suffix_permutations_checked": 1},
            "non_claims": ["No settlement authority is derived from this research artifact."],
        },
        "parity_reduction": {
            "ok": True,
            "summary": {
                "case_count": 1,
                "mismatch_count": 0,
                "brute_mismatch_count": 0,
                "total_dominated_insertions_skipped": 1,
            },
            "aggregate_reductions": {"state_insertion": 2.0, "transitions": 2.0},
            "non_claims": ["No settlement authority is derived from this artifact."],
        },
        "adversarial_corpus": {
            "ok": True,
            "summary": {
                "case_count": 1,
                "mismatch_count": 0,
                "brute_mismatch_count": 0,
                "total_dominated_insertions_skipped": 1,
            },
            "aggregate_reductions": {"state_insertion": 2.0, "transitions": 2.0},
            "non_claims": ["No settlement authority is derived from this artifact."],
        },
        "boundary_refuter": {
            "ok": True,
            "exact_out": {"counterexample_found": True},
            "mixed_direction": {"counterexample_found": True},
            "non_claims": ["No settlement authority is derived from this research artifact."],
        },
    }
    deterministic = {"ok": True}
    flags = evidence_flags(evidence, deterministic)

    assert flags["boundary_refuters_ok"] == 1
    assert flags["no_authority_effect"] == 1

    missing_exact_out = dict(evidence)
    boundary = dict(missing_exact_out["boundary_refuter"])
    exact_out = dict(boundary["exact_out"])
    exact_out["counterexample_found"] = False
    boundary["exact_out"] = exact_out
    missing_exact_out["boundary_refuter"] = boundary

    mutated_flags = evidence_flags(missing_exact_out, deterministic)
    assert mutated_flags["boundary_refuters_ok"] == 0

    missing_authority_rail = dict(evidence)
    candidate = dict(missing_authority_rail["dominance_refuter"])
    candidate["non_claims"] = []
    missing_authority_rail["dominance_refuter"] = candidate
    assert evidence_flags(missing_authority_rail, deterministic)["no_authority_effect"] == 0
