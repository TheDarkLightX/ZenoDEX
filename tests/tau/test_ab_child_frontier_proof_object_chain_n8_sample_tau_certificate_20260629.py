from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629 import (
    EXPECTED_CANONICAL_MEMBERSHIP_DIGEST,
    EXPECTED_CANONICAL_ROOTS_DIGEST,
    EXPECTED_CHAIN_INDEX_HASH,
    EXPECTED_CHILD_STATE_COUNT,
    EXPECTED_GENERATION_DIGEST,
    EXPECTED_MANIFEST_HASH,
    EXPECTED_SAMPLED_CHILD_MASK_COUNT,
    EXPECTED_TRANSITION_COUNT,
    EXPECTED_TRANSITION_DIGEST,
    EXPECTED_WITNESS_DIGEST,
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


def test_proof_object_chain_n8_sample_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    counts = tau_certificate_report["chain_counts"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_child_frontier_proof_object_chain_n8_sample_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 18
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert counts["stage_tau_report_count"] == 5
    assert counts["sampled_child_mask_count"] == EXPECTED_SAMPLED_CHILD_MASK_COUNT
    assert counts["sampled_child_state_count"] == EXPECTED_CHILD_STATE_COUNT
    assert counts["predecessor_transition_count"] == EXPECTED_TRANSITION_COUNT


def test_proof_object_chain_n8_sample_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["proof_object_chain_n8_sample_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "generation_tau_reject",
        "canonical_merkle_tau_reject",
        "witness_compression_tau_reject",
        "bidirectional_transition_tau_reject",
        "producer_tau_reject",
        "shared_scope_reject",
        "stage_counts_reject",
        "cross_stage_digest_reject",
        "producer_links_reject",
        "negative_cases_reject",
        "deterministic_replay_reject",
        "stage_report_hash_reject",
        "chain_index_hash_reject",
        "authority_boundary_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
    ):
        assert cases[case_id]["got"]["o7"] == 0
    assert cases["chain_index_hash_reject"]["got"]["o6"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 1


def test_proof_object_chain_n8_sample_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    digests = tau_certificate_report["chain_digests"]
    stage_summary = tau_certificate_report["stage_summary"]

    assert tau_certificate_report["chain_index_sha256"] == EXPECTED_CHAIN_INDEX_HASH
    assert (
        tau_certificate_report["expected_chain_index_sha256"]
        == EXPECTED_CHAIN_INDEX_HASH
    )
    assert digests["generation_frontier_rows_digest"] == EXPECTED_GENERATION_DIGEST
    assert digests["canonical_frontier_roots_digest"] == EXPECTED_CANONICAL_ROOTS_DIGEST
    assert (
        digests["canonical_membership_rows_digest"]
        == EXPECTED_CANONICAL_MEMBERSHIP_DIGEST
    )
    assert digests["witness_rows_digest"] == EXPECTED_WITNESS_DIGEST
    assert digests["transition_rows_digest"] == EXPECTED_TRANSITION_DIGEST
    assert digests["producer_manifest_hash"] == EXPECTED_MANIFEST_HASH
    assert all(summary["tau_ok"] is True for summary in stage_summary.values())
    assert all(summary["invalid_accepts"] == 0 for summary in stage_summary.values())
    assert "bounded to the deterministic sampled n=8 zero-min" in nonclaims
    assert "existing stage Tau reports" in nonclaims
    assert "does not prove exhaustive n=8 coverage" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "child-frontier generation in Lean" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_proof_object_chain_n8_sample_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py",
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
