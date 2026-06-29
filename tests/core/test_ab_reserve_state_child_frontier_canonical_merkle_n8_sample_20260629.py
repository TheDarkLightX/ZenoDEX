from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629 import (
    BIT_COUNT,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def canonical_merkle_report() -> dict[str, object]:
    return build_report()


def test_child_frontier_canonical_merkle_n8_report(
    canonical_merkle_report: dict[str, object],
) -> None:
    search = canonical_merkle_report["search"]

    assert canonical_merkle_report["ok"] is True
    assert search["sample_plan"]["bit_count"] == BIT_COUNT
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["sampled_child_mask_count"] == 51
    assert search["frontier_root_count"] == 51
    assert search["sampled_child_state_count"] == 88
    assert search["membership_count"] == 88
    assert search["expected_sampled_child_mask_count"] == 51
    assert search["expected_sampled_child_state_count"] == 88
    assert search["covered_sampled_child_state_count"] == 88
    assert search["missing_frontier_row_count"] == 0
    assert search["extra_frontier_row_count"] == 0
    assert search["duplicate_frontier_row_count"] == 0
    assert search["missing_membership_proof_count"] == 0
    assert search["extra_membership_proof_count"] == 0
    assert search["invalid_membership_proof_count"] == 0
    assert search["root_mismatch_count"] == 0
    assert search["max_leaf_count"] == 7
    assert search["frontier_roots_digest"] == (
        "53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4"
    )
    assert search["membership_rows_digest"] == (
        "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert canonical_merkle_report["deterministic_replay"]["ok"] is True


def test_child_frontier_canonical_merkle_n8_linked_report(
    canonical_merkle_report: dict[str, object],
) -> None:
    linked = canonical_merkle_report["search"]["linked_frontier_summary"]

    assert linked["available"] is True
    assert linked["ok"] is True
    assert linked["sampled_child_mask_count"] == 51
    assert linked["sampled_child_state_count"] == 88
    assert linked["generated_state_count"] == 88
    assert linked["missing_child_state_count"] == 0
    assert linked["extra_generated_state_count"] == 0
    assert linked["frontier_rows_digest"] == (
        "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
    )


def test_child_frontier_canonical_merkle_n8_coverage(
    canonical_merkle_report: dict[str, object],
) -> None:
    coverage = canonical_merkle_report["search"]["coverage"]

    assert coverage["n_counts"] == {"8": 3}
    assert coverage["fee_bps_counts"] == {"2500": 1, "30": 1, "9000": 1}
    assert coverage["pattern_counts"] == {
        "n8_deep_low_fee/tie": 1,
        "n8_deep_mid_fee/front_burst": 1,
        "n8_thin_high_fee/stair": 1,
    }
    assert coverage["reason_classes"] == [
        "authority_effect_present",
        "canonical_leaf_index_mismatch",
        "frontier_generated_state_root_mismatch",
        "linked_frontier_extra_generated_state",
        "linked_frontier_summary_mismatch",
        "membership_proof_hash_mismatch",
        "missing_membership_proof",
        "packet_hash_mismatch",
        "packet_sample_plan_mismatch",
        "sampled_n8_bound_missing",
    ]


def test_child_frontier_canonical_merkle_n8_case_rows(
    canonical_merkle_report: dict[str, object],
) -> None:
    rows = canonical_merkle_report["search"]["cases"]

    assert [
        (row["frontier_root_count"], row["membership_count"], row["max_leaf_count"])
        for row in rows
    ] == [
        (17, 17, 1),
        (17, 34, 6),
        (17, 37, 7),
    ]
    assert [row["frontier_roots_digest"] for row in rows] == [
        "6d0dd4f4f879d8691432670cadeb62c9ab48a1eb5408781e0257e80c7ee3a6b3",
        "55c378c91efe854ca580c4807a4eb83e87bf54498f99db9efc6332e4c952c1db",
        "88f2fcb17af25aa8af166ee21a84b0cb63c02758fb7171e078ee605026f17f60",
    ]
    assert [row["membership_rows_digest"] for row in rows] == [
        "b7ff3e35887fa45919fb1808dbdf6ebb0f08cf4dc6f617da70375d87df64a184",
        "807bbd43f61d88ad5908082696811351e15fae299d3881119dcad3a70d3060fd",
        "0684e5b00deeeef7835d29e5dbcc051da86cb3d43984b4cd9b54d1f170db6489",
    ]


def test_child_frontier_canonical_merkle_n8_negative_controls(
    canonical_merkle_report: dict[str, object],
) -> None:
    controls = canonical_merkle_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "sampled_n8_bound_missing",
        "packet_sample_plan_mismatch",
        "frontier_generated_state_root_mismatch",
        "canonical_leaf_index_mismatch",
        "missing_membership_proof",
        "membership_proof_hash_mismatch",
        "linked_frontier_extra_generated_state",
        "authority_effect_present",
    }


def test_child_frontier_canonical_merkle_n8_non_claims(
    canonical_merkle_report: dict[str, object],
) -> None:
    non_claims = "\n".join(canonical_merkle_report["non_claims"])

    assert "bounded to the deterministic n=8 sample" in non_claims
    assert "sampled zero-min exact-in cases" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_child_frontier_canonical_merkle_n8_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_CASE_COUNT
    assert report["search"]["negative_control_accept_count"] == 0
