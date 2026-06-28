from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_ab_bounded_oracle_pruning_certificate import REPORT_JSON, build_report, evidence_flags


ROOT = Path(__file__).resolve().parents[2]


def test_ab_bounded_oracle_pruning_certificate_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "ab_bounded_oracle_pruning_certificate_v1"
    assert all(value == 1 for value in report["flags"].values())
    assert report["tau"]["ok"] is True
    assert report["evidence"]["summary"]["case_count"] == 14
    assert report["evidence"]["summary"]["mismatch_count"] == 0
    assert report["evidence"]["summary"]["brute_mismatch_count"] == 0
    assert report["evidence"]["summary"]["total_certified_prunes"] > 0
    assert report["evidence"]["aggregate_reductions"]["state_insertion"] > 1.0
    assert report["deterministic_replay"]["ok"] is True
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_ab_bounded_oracle_pruning_certificate_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_ab_bounded_oracle_pruning_certificate.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau"]["ok"] is True


def test_ab_bounded_oracle_pruning_certificate_rejects_missing_certification() -> None:
    evidence = {
        "ok": True,
        "suffix_max": 4,
        "case_plan": [{"n": 4, "variants": 1}],
        "summary": {
            "case_count": 1,
            "mismatch_count": 0,
            "brute_mismatch_count": 0,
            "total_certified_prunes": 1,
            "total_suffix_permutations_checked": 1,
        },
        "aggregate_reductions": {"state_insertion": 2.0},
        "non_claims": [
            "This is a research certificate, not a production ordering change.",
            "No settlement authority is derived from this artifact.",
        ],
    }
    deterministic = {"ok": True}
    flags = evidence_flags(evidence, deterministic)

    assert flags["all_prunes_suffix_certified"] == 1
    assert flags["no_authority_effect"] == 1

    no_prunes = dict(evidence)
    no_prunes["summary"] = dict(evidence["summary"])
    no_prunes["summary"]["total_certified_prunes"] = 0
    assert evidence_flags(no_prunes, deterministic)["all_prunes_suffix_certified"] == 0

    no_authority = dict(evidence)
    no_authority["non_claims"] = []
    assert evidence_flags(no_authority, deterministic)["no_authority_effect"] == 0
