from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_bidirectional_transition_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def bidirectional_report() -> dict[str, object]:
    return build_report()


def test_bidirectional_transition_certificate_report(
    bidirectional_report: dict[str, object],
) -> None:
    search = bidirectional_report["search"]

    assert bidirectional_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["child_mask_count"] == 508
    assert search["transition_row_count"] == 2_777
    assert search["expected_transition_count"] == 2_777
    assert search["covered_transition_count"] == 2_777
    assert search["unique_transition_count"] == 2_777
    assert search["unique_generated_child_count"] == 864
    assert search["missing_transition_count"] == 0
    assert search["extra_transition_count"] == 0
    assert search["invalid_transition_row_count"] == 0
    assert search["duplicate_transition_row_count"] == 0
    assert search["linked_child_coverage_witness_count"] == 864
    assert search["transition_to_child_witness_ratio"] == 3.21412
    assert search["transition_rows_digest"] == (
        "fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert bidirectional_report["deterministic_replay"]["ok"] is True


def test_bidirectional_transition_linked_coverage_report(
    bidirectional_report: dict[str, object],
) -> None:
    linked = bidirectional_report["search"]["linked_witness_merkle_summary"]

    assert linked["available"] is True
    assert linked["ok"] is True
    assert linked["schema"] == "zenodex.ab_reserve_state_child_frontier_witness_merkle_report.v1"
    assert linked["case_count"] == 4
    assert linked["valid_case_count"] == 4
    assert linked["child_mask_count"] == 508
    assert linked["bound_row_count"] == 864
    assert linked["witness_count"] == 864
    assert linked["membership_count"] == 864
    assert linked["negative_control_accept_count"] == 0
    assert linked["bound_rows_digest"] == (
        "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
    )


def test_bidirectional_transition_coverage(
    bidirectional_report: dict[str, object],
) -> None:
    coverage = bidirectional_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["fee_bps_counts"] == {"1": 1, "100": 2, "9000": 1}
    assert coverage["pattern_counts"] == {
        "high_fee_deep_out/rand_stair": 1,
        "near_domain_in/rand_burst": 1,
        "near_zero_positive/rand_tie": 1,
        "thin_positive_boundary/high_fee9000": 1,
    }
    assert coverage["reason_classes"] == [
        "afterstep_generated_child_mismatch",
        "authority_effect_present",
        "extra_predecessor_transition_row",
        "generated_child_not_in_child_frontier",
        "generated_state_root_mismatch",
        "linked_witness_merkle_bound_row_count_mismatch",
        "linked_witness_merkle_summary_mismatch",
        "membership_proof_hash_mismatch",
        "missing_predecessor_transition_row",
        "packet_hash_mismatch",
        "packet_transition_summary_mismatch",
        "transition_parent_state_not_in_parent_frontier",
        "transition_step_bit_out_of_range",
    ]


def test_bidirectional_transition_case_rows(
    bidirectional_report: dict[str, object],
) -> None:
    rows = bidirectional_report["search"]["cases"]

    assert [
        (row["transition_row_count"], row["child_mask_count"], row["unique_generated_child_count"])
        for row in rows
    ] == [
        (448, 127, 127),
        (1_004, 127, 320),
        (877, 127, 290),
        (448, 127, 127),
    ]
    assert [row["transition_rows_digest"] for row in rows] == [
        "ce88df5af288e0d989f47ad3739c8ca0f90ecf813c20e0d26c6014a97c44c33a",
        "52156b78e1b71ff93bd584ff358ce959a3a94a7fa2e8d2d4d31c21173034e36b",
        "760e74560c7d8b8ae27ec73af46b4770efa976d975fa7c2e8213f57c53f4b147",
        "3e0b201dcc9c017bab65e9a9cd3bc884def0b8afcbb28e05377055ec5f585118",
    ]


def test_bidirectional_transition_negative_controls(
    bidirectional_report: dict[str, object],
) -> None:
    controls = bidirectional_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "missing_predecessor_transition_row",
        "transition_parent_state_not_in_parent_frontier",
        "afterstep_generated_child_mismatch",
        "transition_step_bit_out_of_range",
        "generated_state_root_mismatch",
        "membership_proof_hash_mismatch",
        "linked_witness_merkle_bound_row_count_mismatch",
        "authority_effect_present",
    }


def test_bidirectional_transition_non_claims(
    bidirectional_report: dict[str, object],
) -> None:
    non_claims = "\n".join(bidirectional_report["non_claims"])

    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "zero-min exact-in cases" in non_claims
    assert "links the child coverage direction" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_bidirectional_transition_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_bidirectional_transition_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["transition_row_count"] == 2_777
    assert report["search"]["negative_control_accept_count"] == 0
