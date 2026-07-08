from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629 import (
    EXPECTED_DETERMINISTIC_HASH,
    EXPECTED_FRONTIER_ROWS_DIGEST,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    EXPECTED_NORMALIZED_SOURCE_HASH,
    EXPECTED_PREDECESSOR_EDGE_COUNT,
    EXPECTED_PREDECESSOR_TRANSITION_COUNT,
    EXPECTED_SAMPLED_CHILD_MASK_COUNT,
    EXPECTED_SAMPLED_CHILD_STATE_COUNT,
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


def test_generation_n8_sample_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    corpus = tau_certificate_report["generation_corpus"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_reserve_state_child_frontier_generation_n8_sample_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 18
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert corpus["sampled_child_mask_count"] == EXPECTED_SAMPLED_CHILD_MASK_COUNT
    assert corpus["frontier_equal_count"] == EXPECTED_SAMPLED_CHILD_MASK_COUNT
    assert corpus["predecessor_edge_count"] == EXPECTED_PREDECESSOR_EDGE_COUNT
    assert corpus["predecessor_transition_count"] == EXPECTED_PREDECESSOR_TRANSITION_COUNT
    assert (
        corpus["predecessor_transition_executable_count"]
        == EXPECTED_PREDECESSOR_TRANSITION_COUNT
    )
    assert corpus["sampled_child_state_count"] == EXPECTED_SAMPLED_CHILD_STATE_COUNT
    assert corpus["generated_state_count"] == EXPECTED_SAMPLED_CHILD_STATE_COUNT
    assert corpus["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert corpus["negative_control_accept_count"] == 0


def test_generation_n8_sample_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["generation_n8_sample_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "missing_source_report_reject",
        "wrong_scope_reject",
        "sample_plan_reject",
        "frontier_counts_reject",
        "predecessor_counts_reject",
        "state_counts_reject",
        "generation_clean_reject",
        "frontier_digest_reject",
        "nondeterministic_replay_reject",
        "negative_controls_missing_reject",
        "lean_contract_reject",
        "authority_boundary_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
        "source_hash_reject",
        "hash_normalization_reject",
    ):
        assert cases[case_id]["got"]["o7"] == 0
    assert cases["source_hash_reject"]["got"]["o9"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 1


def test_generation_n8_sample_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    source_report = tau_certificate_report["source_report"]
    corpus = tau_certificate_report["generation_corpus"]

    assert source_report["normalized_sha256"] == EXPECTED_NORMALIZED_SOURCE_HASH
    assert source_report["expected_normalized_sha256"] == EXPECTED_NORMALIZED_SOURCE_HASH
    assert corpus["frontier_rows_digest"] == EXPECTED_FRONTIER_ROWS_DIGEST
    assert corpus["deterministic_replay_hash"] == EXPECTED_DETERMINISTIC_HASH
    assert corpus["missing_child_state_count"] == 0
    assert corpus["extra_generated_state_count"] == 0
    assert "bounded to the deterministic sampled n=8 zero-min" in nonclaims
    assert "normalized source hash" in nonclaims
    assert "does not prove exhaustive n=8 coverage" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "child-frontier generation in Lean" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_generation_n8_sample_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629.py",
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
    assert report["breakthrough"]["tau_cases"] == 18
