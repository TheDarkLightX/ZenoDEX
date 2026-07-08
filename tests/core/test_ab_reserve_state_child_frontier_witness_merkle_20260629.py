from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_witness_merkle_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def witness_merkle_report() -> dict[str, object]:
    return build_report()


def test_ab_reserve_state_child_frontier_witness_merkle_report(
    witness_merkle_report: dict[str, object],
) -> None:
    search = witness_merkle_report["search"]

    assert witness_merkle_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["child_mask_count"] == 508
    assert search["expected_child_state_count"] == 864
    assert search["bound_row_count"] == 864
    assert search["witness_count"] == 864
    assert search["membership_count"] == 864
    assert search["covered_child_state_count"] == 864
    assert search["missing_child_bound_count"] == 0
    assert search["extra_child_bound_count"] == 0
    assert search["invalid_bound_row_count"] == 0
    assert search["duplicate_bound_row_count"] == 0
    assert search["predecessor_transition_count"] == 2_777
    assert search["witness_merkle_compression_ratio"] == 3.21412
    assert search["witness_transition_checks_saved"] == 1_913
    assert search["bound_rows_digest"] == (
        "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert witness_merkle_report["deterministic_replay"]["ok"] is True


def test_ab_reserve_state_child_frontier_witness_merkle_linked_reports(
    witness_merkle_report: dict[str, object],
) -> None:
    witness = witness_merkle_report["search"]["linked_witness_summary"]
    merkle = witness_merkle_report["search"]["linked_merkle_summary"]

    assert witness["available"] is True
    assert witness["ok"] is True
    assert witness["case_count"] == 4
    assert witness["valid_case_count"] == 4
    assert witness["child_mask_count"] == 508
    assert witness["child_state_count"] == 864
    assert witness["negative_control_accept_count"] == 0
    assert witness["digest"] == (
        "d689dd569b28abf3cb2636def322fa9d8185c2eb1fe4843bd83d07bce69138c3"
    )

    assert merkle["available"] is True
    assert merkle["ok"] is True
    assert merkle["case_count"] == 4
    assert merkle["valid_case_count"] == 4
    assert merkle["child_mask_count"] == 508
    assert merkle["child_state_count"] == 864
    assert merkle["negative_control_accept_count"] == 0
    assert merkle["digest"] == (
        "84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559"
    )


def test_ab_reserve_state_child_frontier_witness_merkle_coverage(
    witness_merkle_report: dict[str, object],
) -> None:
    coverage = witness_merkle_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["fee_bps_counts"] == {"1": 1, "100": 2, "9000": 1}
    assert coverage["pattern_counts"] == {
        "high_fee_deep_out/rand_stair": 1,
        "near_domain_in/rand_burst": 1,
        "near_zero_positive/rand_tie": 1,
        "thin_positive_boundary/high_fee9000": 1,
    }
    assert coverage["reason_classes"] == [
        "authority_effect_present",
        "bound_child_state_not_in_frontier",
        "canonical_leaf_index_mismatch",
        "cross_bound_child_state_mismatch",
        "duplicate_bound_row",
        "extra_child_bound_row",
        "generated_state_root_mismatch",
        "membership_proof_hash_mismatch",
        "membership_proof_shape_mismatch",
        "missing_child_bound_row",
        "packet_hash_mismatch",
        "packet_witness_merkle_summary_mismatch",
        "witness_afterstep_mismatch",
        "witness_child_state_not_in_child_frontier",
        "witness_parent_state_not_in_parent_frontier",
        "witness_step_bit_out_of_range",
    ]


def test_ab_reserve_state_child_frontier_witness_merkle_case_rows(
    witness_merkle_report: dict[str, object],
) -> None:
    rows = witness_merkle_report["search"]["cases"]

    assert [
        (
            row["bound_row_count"],
            row["predecessor_transition_count"],
            row["frontier_witness_compression_ratio"],
        )
        for row in rows
    ] == [
        (127, 448, 3.527559),
        (320, 1_004, 3.1375),
        (290, 877, 3.024138),
        (127, 448, 3.527559),
    ]
    assert [row["bound_rows_digest"] for row in rows] == [
        "4720d06a30a7707eec19b08a83ff2c5802b3d8d8d12183017d479a0ec2e9f6b2",
        "e84f09be2040986a317dc98c31f967b97703c36ca2d356e286b6f9f5de4871ed",
        "896337c7e1edb9c4416b04d1755bb1b01ee1fa2d4eb5e3a86584052a74e150ba",
        "f30f66bf6fddcc14268e9e1ada910dd285f61e0663045ccf6738fc7a230f5080",
    ]


def test_ab_reserve_state_child_frontier_witness_merkle_negative_controls(
    witness_merkle_report: dict[str, object],
) -> None:
    controls = witness_merkle_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["mutation_id"] for control in controls} == {
        "packet_hash_mismatch",
        "missing_child_bound_row",
        "witness_parent_state_not_in_parent_frontier",
        "witness_step_bit_out_of_range",
        "generated_state_root_mismatch",
        "canonical_leaf_index_mismatch",
        "membership_proof_hash_mismatch",
        "cross_bound_child_state_mismatch",
        "duplicate_bound_row",
        "authority_effect_present",
    }


def test_ab_reserve_state_child_frontier_witness_merkle_hypothesis_card(
    witness_merkle_report: dict[str, object],
) -> None:
    card = witness_merkle_report["hypothesis_card"]
    non_claims = "\n".join(witness_merkle_report["non_claims"])

    assert card["status"] == "supported_bounded"
    assert "same child mask and child state" in card["mechanism_change"]
    assert "Python-to-Lean refinement" in card["formal_obligations"]
    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "zero-min exact-in cases" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "No settlement" in non_claims


def test_ab_reserve_state_child_frontier_witness_merkle_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_witness_merkle_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_CASE_COUNT
    assert report["search"]["negative_control_accept_count"] == 0
