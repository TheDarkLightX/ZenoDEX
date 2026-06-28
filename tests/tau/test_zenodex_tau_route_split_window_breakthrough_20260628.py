from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_tau_route_split_window_breakthrough_20260628 import (
    REPORT_JSON,
    build_split_certificate,
    split_cases,
    verify_split_certificate,
)


ROOT = Path(__file__).resolve().parents[2]


def test_route_split_window_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_route_split_window_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["spec_id"] == "route_split_window_certificate_v1"
    assert report["tau"]["ok"] is True
    assert report["split_cases"]["case_count"] == 4
    assert report["split_cases"]["min_quote_call_reduction_ratio"] > 3.0
    assert report["split_cases"]["max_quote_call_reduction_ratio"] > 10.0
    assert report["split_cases"]["naive_discrete_convex_failures"]
    assert all(row["ok"] for row in report["split_cases"]["cases"])
    assert all(not row["accepted"] for row in report["mutation_checks"])
    assert {case["case_id"] for case in report["tau"]["cases"]} == {
        "route_split_window_pass",
        "parity_reject",
        "local_window_reject",
        "authority_reject",
        "inactive_safe",
    }


def test_route_split_certificate_mutations_fail_closed() -> None:
    case = split_cases()[1]
    certificate = build_split_certificate(case)

    assert verify_split_certificate(case, certificate)["ok"] is True

    bad_hash = dict(certificate)
    bad_hash["domain_hash"] = "0" * 64
    bad_hash_result = verify_split_certificate(case, bad_hash)
    assert bad_hash_result["ok"] is False
    assert "window_search_replayed" in bad_hash_result["failed_flags"]

    bad_q0 = dict(certificate)
    bad_q0["selected_q0"] = int(certificate["selected_q0"]) + 1
    bad_q0_result = verify_split_certificate(case, bad_q0)
    assert bad_q0_result["ok"] is False
    assert "full_oracle_parity_ok" in bad_q0_result["failed_flags"]


def test_integer_rounding_refutes_naive_discrete_convex_shortcut() -> None:
    failures = []
    for case in split_cases():
        certificate = build_split_certificate(case)
        result = verify_split_certificate(case, certificate)
        if not result["full_scan"]["integer_rounding_shape"]["first_differences_nondecreasing"]:
            failures.append(case.case_id)

    assert failures
