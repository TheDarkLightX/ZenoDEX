from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_ab_zero_min_economic_compression_certificate import (
    REPORT_JSON,
    build_report,
    evidence_flags,
)


ROOT = Path(__file__).resolve().parents[2]


def test_ab_zero_min_economic_compression_certificate_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "ab_zero_min_economic_compression_certificate_v1"
    assert all(value == 1 for value in report["flags"].values())
    assert report["tau"]["ok"] is True
    assert report["evidence"]["zero_min_support"]["case_count"] == 50
    assert report["evidence"]["zero_min_support"]["mismatch_count"] == 0
    assert report["evidence"]["zero_min_support"]["canonical_tie_mismatch_count"] > 0
    assert report["evidence"]["nonzero_min_boundary"]["counterexample_found"] is True
    assert report["evidence"]["rounding_boundary"]["counterexample_found"] is True
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_ab_zero_min_economic_compression_certificate_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_ab_zero_min_economic_compression_certificate.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau"]["ok"] is True


def test_ab_zero_min_economic_compression_certificate_rejects_missing_boundaries() -> None:
    evidence = {
        "zero_min_support": {"ok": True, "mismatch_count": 0, "case_count": 50, "canonical_tie_mismatch_count": 1},
        "nonzero_min_boundary": {"counterexample_found": True},
        "rounding_boundary": {"counterexample_found": True},
        "non_claims": [
            "This is a research certificate, not a production ordering change.",
            "No settlement authority is derived from this artifact.",
        ],
    }
    deterministic = {"ok": True}
    flags = evidence_flags(evidence, deterministic)

    assert flags["canonical_tie_nonclaim_witness_ok"] == 1
    assert flags["nonzero_min_boundary_witness_ok"] == 1
    assert flags["no_authority_effect"] == 1

    missing_tie = dict(evidence)
    missing_tie["zero_min_support"] = dict(evidence["zero_min_support"])
    missing_tie["zero_min_support"]["canonical_tie_mismatch_count"] = 0
    assert evidence_flags(missing_tie, deterministic)["canonical_tie_nonclaim_witness_ok"] == 0

    missing_nonzero_boundary = dict(evidence)
    missing_nonzero_boundary["nonzero_min_boundary"] = {"counterexample_found": False}
    assert evidence_flags(missing_nonzero_boundary, deterministic)["nonzero_min_boundary_witness_ok"] == 0

    missing_authority_rail = dict(evidence)
    missing_authority_rail["non_claims"] = []
    assert evidence_flags(missing_authority_rail, deterministic)["no_authority_effect"] == 0
