from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629 import (
    EXPECTED_CANONICAL_DIGEST,
    EXPECTED_GENERATED_CHILD_COUNT,
    EXPECTED_GENERATION_DIGEST,
    EXPECTED_MANIFEST_HASH,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    EXPECTED_SAMPLED_CHILD_MASK_COUNT,
    EXPECTED_SOURCE_REPORT_HASH,
    EXPECTED_TRANSITION_DIGEST,
    EXPECTED_TRANSITION_ROW_COUNT,
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


def test_generated_image_producer_n8_sample_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    manifest = tau_certificate_report["producer_manifest"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_child_frontier_generated_image_producer_n8_sample_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 20
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert manifest["manifest_hash"] == EXPECTED_MANIFEST_HASH
    assert manifest["stage_count"] == 4
    assert manifest["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert manifest["negative_control_accept_count"] == 0


def test_generated_image_producer_n8_sample_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["generated_image_producer_n8_sample_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "missing_source_report_reject",
        "wrong_scope_reject",
        "stage_order_reject",
        "stage_hashes_reject",
        "stage_outputs_reject",
        "stage_replay_reject",
        "cross_stage_links_reject",
        "source_seed_reject",
        "manifest_hash_reject",
        "generation_digest_reject",
        "canonical_digest_reject",
        "witness_digest_reject",
        "transition_digest_reject",
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


def test_generated_image_producer_n8_sample_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    source_report = tau_certificate_report["source_report"]
    stage_outputs = tau_certificate_report["stage_outputs"]
    digests = tau_certificate_report["digests"]

    assert source_report["sha256"] == EXPECTED_SOURCE_REPORT_HASH
    assert source_report["expected_sha256"] == EXPECTED_SOURCE_REPORT_HASH
    assert stage_outputs["generation"]["sampled_child_mask_count"] == (
        EXPECTED_SAMPLED_CHILD_MASK_COUNT
    )
    assert stage_outputs["generation"]["generated_state_count"] == (
        EXPECTED_GENERATED_CHILD_COUNT
    )
    assert stage_outputs["bidirectional_transition"]["transition_row_count"] == (
        EXPECTED_TRANSITION_ROW_COUNT
    )
    assert digests["generation_frontier_rows_digest"] == EXPECTED_GENERATION_DIGEST
    assert digests["canonical_membership_rows_digest"] == EXPECTED_CANONICAL_DIGEST
    assert digests["witness_rows_digest"] == EXPECTED_WITNESS_DIGEST
    assert digests["transition_rows_digest"] == EXPECTED_TRANSITION_DIGEST
    assert "bounded to the deterministic sampled n=8 zero-min" in nonclaims
    assert "does not prove exhaustive n=8 coverage" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_generated_image_producer_n8_sample_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629.py",
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
    assert report["breakthrough"]["tau_cases"] == 20
