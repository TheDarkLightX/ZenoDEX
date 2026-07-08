from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_20260629 import (
    EXPECTED_DETERMINISTIC_HASH,
    EXPECTED_LINKED_MERKLE_DIGEST,
    EXPECTED_LINKED_WITNESS_DIGEST,
    EXPECTED_SOURCE_REPORT_HASH,
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


def test_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    transition = tau_certificate_report["transition_corpus"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_child_frontier_bidirectional_transition_n8_sample_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 17
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert transition["case_count"] == 3
    assert transition["valid_case_count"] == 3
    assert transition["sampled_child_mask_count"] == 51
    assert transition["transition_row_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["expected_transition_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["covered_transition_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["unique_transition_count"] == EXPECTED_TRANSITION_ROW_COUNT
    assert transition["unique_generated_child_count"] == 88
    assert transition["linked_child_coverage_witness_count"] == 88
    assert transition["linked_canonical_membership_count"] == 88
    assert transition["negative_control_count"] == 11
    assert transition["negative_control_accept_count"] == 0


def test_ab_child_frontier_bidirectional_transition_n8_sample_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["bidirectional_transition_n8_sample_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "missing_source_report_reject",
        "wrong_scope_reject",
        "transition_counts_reject",
        "generated_child_count_reject",
        "linked_child_coverage_reject",
        "linked_canonical_membership_reject",
        "transition_digest_reject",
        "linked_witness_digest_reject",
        "linked_merkle_digest_reject",
        "nondeterministic_replay_reject",
        "negative_controls_missing_reject",
        "authority_boundary_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
        "source_hash_reject",
    ):
        assert cases[case_id]["got"]["o7"] == 0
    assert cases["source_hash_reject"]["got"]["o9"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 1


def test_ab_child_frontier_bidirectional_transition_n8_sample_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    transition = tau_certificate_report["transition_corpus"]
    source_report = tau_certificate_report["source_report"]

    assert source_report["sha256"] == EXPECTED_SOURCE_REPORT_HASH
    assert source_report["expected_sha256"] == EXPECTED_SOURCE_REPORT_HASH
    assert transition["transition_rows_digest"] == EXPECTED_TRANSITION_ROWS_DIGEST
    assert transition["linked_witness_rows_digest"] == EXPECTED_LINKED_WITNESS_DIGEST
    assert (
        transition["linked_merkle_membership_rows_digest"]
        == EXPECTED_LINKED_MERKLE_DIGEST
    )
    assert transition["deterministic_replay_hash"] == EXPECTED_DETERMINISTIC_HASH
    assert "bounded to the deterministic sampled n=8 zero-min" in nonclaims
    assert "predecessor-witness and canonical-Merkle evidence" in nonclaims
    assert "does not prove exhaustive n=8 coverage" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_ab_child_frontier_bidirectional_transition_n8_sample_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert report["transition_corpus"]["transition_row_count"] == EXPECTED_TRANSITION_ROW_COUNT
