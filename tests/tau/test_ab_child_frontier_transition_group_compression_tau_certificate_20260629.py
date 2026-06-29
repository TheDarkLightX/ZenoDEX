from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_transition_group_compression_tau_certificate_20260629 import (
    EXPECTED_BYTE_REDUCTION_RATIO,
    EXPECTED_COMPRESSED_ROWS,
    EXPECTED_COMPRESSED_ROWS_DIGEST,
    EXPECTED_DETERMINISTIC_HASH,
    EXPECTED_SOURCE_TRANSITION_ROWS,
    EXPECTED_TRANSITION_GROUPS_DIGEST,
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


def test_transition_group_compression_tau_certificate_report(
    tau_certificate_report: dict[str, object],
) -> None:
    compression = tau_certificate_report["compression"]

    assert tau_certificate_report["schema"] == (
        "zenodex.ab_child_frontier_transition_group_compression_tau_certificate_report.v1"
    )
    assert tau_certificate_report["breakthrough"]["spec_id"] == (
        "ab_child_frontier_transition_group_compression_scope_certificate_v1"
    )
    assert tau_certificate_report["tau"]["ok"] is True
    assert tau_certificate_report["tau"]["invalid_accepts"] == 0
    assert tau_certificate_report["breakthrough"]["tau_cases"] == 15
    assert all(value == 1 for value in tau_certificate_report["facts"].values())
    assert compression["source_transition_row_count"] == EXPECTED_SOURCE_TRANSITION_ROWS
    assert compression["compressed_row_count"] == EXPECTED_COMPRESSED_ROWS
    assert compression["row_reduction_count"] == 1_913
    assert compression["row_reduction_ratio"] == 0.688873
    assert compression["source_transition_json_bytes"] == 2_296_999
    assert compression["compressed_json_bytes"] == 841_376
    assert compression["byte_reduction_count"] == 1_455_623
    assert compression["byte_reduction_ratio"] == EXPECTED_BYTE_REDUCTION_RATIO
    assert compression["expected_group_count"] == EXPECTED_COMPRESSED_ROWS
    assert compression["covered_group_count"] == EXPECTED_COMPRESSED_ROWS
    assert compression["negative_control_count"] == 8
    assert compression["negative_control_accept_count"] == 0


def test_transition_group_compression_tau_negative_cases(
    tau_certificate_report: dict[str, object],
) -> None:
    cases = {case["case_id"]: case for case in tau_certificate_report["tau"]["case_results"]}

    assert cases["transition_group_compression_certificate_pass"]["got"]["o7"] == 1
    for case_id in (
        "missing_compression_report_reject",
        "wrong_scope_reject",
        "source_bidirectional_binding_reject",
        "compression_counts_reject",
        "generated_group_coverage_reject",
        "compression_digest_reject",
        "nondeterministic_replay_reject",
        "negative_controls_missing_reject",
        "case_rows_unbound_reject",
        "authority_boundary_reject",
        "authority_effect_reject",
        "empty_corpus_reject",
        "host_recomputation_nonclaim_reject",
    ):
        assert cases[case_id]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o7"] == 0
    assert cases["inactive_safe"]["got"]["o8"] == 1


def test_transition_group_compression_tau_scope_and_pins(
    tau_certificate_report: dict[str, object],
) -> None:
    nonclaims = "\n".join(tau_certificate_report["non_claims"])
    compression = tau_certificate_report["compression"]
    source = tau_certificate_report["source_bidirectional_report"]

    assert source["transition_row_count"] == EXPECTED_SOURCE_TRANSITION_ROWS
    assert source["unique_generated_child_count"] == EXPECTED_COMPRESSED_ROWS
    assert compression["transition_groups_digest"] == EXPECTED_TRANSITION_GROUPS_DIGEST
    assert compression["compressed_rows_digest"] == EXPECTED_COMPRESSED_ROWS_DIGEST
    assert compression["deterministic_replay_hash"] == EXPECTED_DETERMINISTIC_HASH
    assert "bounded to the committed n=7 zero-min" in nonclaims
    assert "does not recompute transition groups in Tau" in nonclaims
    assert "does not remove host recomputation" in nonclaims
    assert "Python-to-Lean refinement" in nonclaims
    assert "nonzero min_amount_out" in nonclaims
    assert "does not authorize settlement" in nonclaims


def test_transition_group_compression_tau_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_transition_group_compression_tau_certificate_20260629.py",
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
    assert report["compression"]["source_transition_row_count"] == EXPECTED_SOURCE_TRANSITION_ROWS
    assert report["compression"]["compressed_row_count"] == EXPECTED_COMPRESSED_ROWS
