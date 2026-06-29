from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629 import (
    EXPECTED_DETERMINISTIC_HASH,
    EXPECTED_LINKED_BOUND_ROWS_DIGEST,
    EXPECTED_TRANSITION_ROW_COUNT,
    EXPECTED_TRANSITION_ROWS_DIGEST,
    REPORT_JSON,
    build_report,
    find_tau_bin,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def tau_certificate_report() -> dict[str, object]:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")
    return build_report()


def test_ab_child_frontier_bidirectional_transition_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    transition = tau_certificate_report["transition_corpus"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_child_frontier_bidirectional_transition_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_child_frontier_bidirectional_transition_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 14
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert transition["case_count"] == 4
    assert transition["child_mask_count"] == 508
    assert transition["transition_row_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["expected_transition_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["covered_transition_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["unique_transition_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["unique_generated_child_count"] == 864
    assert transition["linked_child_coverage_witness_count"] == 864
    assert transition["negative_control_count"] == 9
    assert transition["negative_control_accept_count"] == 0


def test_ab_child_frontier_bidirectional_transition_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["bidirectional_transition_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "missing_source_report_reject",
        "wrong_scope_reject",
        "transition_counts_reject",
        "generated_child_count_reject",
        "linked_child_coverage_reject",
        "transition_digest_reject",
        "linked_digest_reject",
        "nondeterministic_replay_reject",
        "negative_controls_missing_reject",
        "authority_boundary_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
    ):
        assert cases[case_id]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 1


def test_ab_child_frontier_bidirectional_transition_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    transition = tau_certificate_report["transition_corpus"]

    assert transition["transition_rows_digest"] == EXPECTED_TRANSITION_ROWS_DIGEST
    assert transition["linked_bound_rows_digest"] == EXPECTED_LINKED_BOUND_ROWS_DIGEST
    assert transition["deterministic_replay_hash"] == EXPECTED_DETERMINISTIC_HASH
    assert "bounded to the committed n=7 zero-min bidirectional transition report" in nonclaims
    assert "links the child coverage direction" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_ab_child_frontier_bidirectional_transition_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert report["transition_corpus"]["transition_row_count"] == EXPECTED_TRANSITION_ROW_COUNT
