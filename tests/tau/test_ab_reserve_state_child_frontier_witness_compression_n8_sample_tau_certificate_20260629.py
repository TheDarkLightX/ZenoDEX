from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629 import (
    EXPECTED_COMPRESSION_RATIO,
    EXPECTED_DETERMINISTIC_HASH,
    EXPECTED_LINKED_FRONTIER_DIGEST,
    EXPECTED_NORMALIZED_SOURCE_HASH,
    EXPECTED_PREDECESSOR_TRANSITION_COUNT,
    EXPECTED_WITNESS_COUNT,
    EXPECTED_WITNESS_ROWS_DIGEST,
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


def test_ab_witness_compression_n8_sample_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    witness = tau_certificate_report["witness_corpus"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_reserve_state_child_frontier_witness_compression_n8_sample_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 16
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert witness["case_count"] == 3
    assert witness["valid_case_count"] == 3
    assert witness["sampled_child_mask_count"] == 51
    assert witness["witness_count"] == EXPECTED_WITNESS_COUNT
    assert witness["expected_sampled_child_state_count"] == EXPECTED_WITNESS_COUNT
    assert witness["covered_sampled_child_state_count"] == EXPECTED_WITNESS_COUNT
    assert witness["missing_sampled_child_state_witness_count"] == 0
    assert witness["extra_sampled_child_state_witness_count"] == 0
    assert witness["invalid_witness_count"] == 0
    assert witness["duplicate_witness_count"] == 0
    assert witness["predecessor_transition_count"] == EXPECTED_PREDECESSOR_TRANSITION_COUNT
    assert witness["witness_transition_checks_saved"] == 180
    assert witness["witness_compression_ratio"] == EXPECTED_COMPRESSION_RATIO
    assert witness["negative_control_count"] == 9
    assert witness["negative_control_accept_count"] == 0


def test_ab_witness_compression_n8_sample_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["witness_compression_n8_sample_certificate_pass"]["got"]["o8"] == 1
    for case_id in (
        "missing_source_report_reject",
        "wrong_scope_reject",
        "witness_counts_reject",
        "compression_metrics_reject",
        "linked_frontier_reject",
        "witness_digest_reject",
        "linked_frontier_digest_reject",
        "nondeterministic_replay_reject",
        "negative_controls_missing_reject",
        "authority_boundary_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
        "normalized_source_hash_reject",
        "volatile_elapsed_not_ignored_reject",
    ):
        assert cases[case_id]["got"]["o8"] == 0
    assert cases["normalized_source_hash_reject"]["got"]["o10"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 0
    assert cases["inactive_safe"]["got"]["o9"] == 1


def test_ab_witness_compression_n8_sample_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    source_report = tau_certificate_report["source_report"]
    witness = tau_certificate_report["witness_corpus"]

    assert source_report["normalized_sha256"] == EXPECTED_NORMALIZED_SOURCE_HASH
    assert source_report["expected_normalized_sha256"] == EXPECTED_NORMALIZED_SOURCE_HASH
    assert source_report["normalization"] == "del(search.elapsed_ms)"
    assert witness["witness_rows_digest"] == EXPECTED_WITNESS_ROWS_DIGEST
    assert witness["linked_frontier_rows_digest"] == EXPECTED_LINKED_FRONTIER_DIGEST
    assert witness["deterministic_replay_hash"] == EXPECTED_DETERMINISTIC_HASH
    assert "bounded to the deterministic sampled n=8 zero-min" in nonclaims
    assert "does not prove exhaustive n=8 coverage" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "child-frontier generation in Lean" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_ab_witness_compression_n8_sample_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629.py",
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
    assert report["witness_corpus"]["witness_count"] == EXPECTED_WITNESS_COUNT
