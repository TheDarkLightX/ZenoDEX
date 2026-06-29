from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_bidirectional_transition_n8_sample_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def bidirectional_n8_report() -> dict[str, object]:
    return build_report()


def test_bidirectional_n8_transition_certificate_report(
    bidirectional_n8_report: dict[str, object],
) -> None:
    search = bidirectional_n8_report["search"]

    assert bidirectional_n8_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["sampled_child_mask_count"] == 51
    assert search["transition_row_count"] == 268
    assert search["expected_transition_count"] == 268
    assert search["covered_transition_count"] == 268
    assert search["unique_transition_count"] == 268
    assert search["unique_generated_child_count"] == 88
    assert search["missing_transition_count"] == 0
    assert search["extra_transition_count"] == 0
    assert search["invalid_transition_row_count"] == 0
    assert search["duplicate_transition_row_count"] == 0
    assert search["linked_child_coverage_witness_count"] == 88
    assert search["linked_canonical_membership_count"] == 88
    assert search["transition_to_child_witness_ratio"] == 3.045455
    assert search["transition_rows_digest"] == (
        "0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert bidirectional_n8_report["deterministic_replay"]["ok"] is True


def test_bidirectional_n8_transition_linked_reports(
    bidirectional_n8_report: dict[str, object],
) -> None:
    witness = bidirectional_n8_report["search"]["linked_witness_summary"]
    merkle = bidirectional_n8_report["search"]["linked_canonical_merkle_summary"]

    assert witness["available"] is True
    assert witness["ok"] is True
    assert witness["case_count"] == 3
    assert witness["valid_case_count"] == 3
    assert witness["sampled_child_mask_count"] == 51
    assert witness["witness_count"] == 88
    assert witness["predecessor_transition_count"] == 268
    assert witness["negative_control_accept_count"] == 0
    assert witness["witness_rows_digest"] == (
        "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
    )

    assert merkle["available"] is True
    assert merkle["ok"] is True
    assert merkle["case_count"] == 3
    assert merkle["valid_case_count"] == 3
    assert merkle["sampled_child_mask_count"] == 51
    assert merkle["frontier_root_count"] == 51
    assert merkle["sampled_child_state_count"] == 88
    assert merkle["membership_count"] == 88
    assert merkle["negative_control_accept_count"] == 0
    assert merkle["frontier_roots_digest"] == (
        "53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4"
    )
    assert merkle["membership_rows_digest"] == (
        "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2"
    )


def test_bidirectional_n8_transition_coverage(
    bidirectional_n8_report: dict[str, object],
) -> None:
    coverage = bidirectional_n8_report["search"]["coverage"]

    assert coverage["n_counts"] == {"8": 3}
    assert coverage["fee_bps_counts"] == {"2500": 1, "30": 1, "9000": 1}
    assert coverage["pattern_counts"] == {
        "n8_deep_low_fee/tie": 1,
        "n8_deep_mid_fee/front_burst": 1,
        "n8_thin_high_fee/stair": 1,
    }
    assert coverage["reason_classes"] == [
        "afterstep_generated_child_mismatch",
        "authority_effect_present",
        "extra_predecessor_transition_row",
        "generated_child_not_in_sampled_child_frontier",
        "generated_state_root_mismatch",
        "linked_canonical_merkle_membership_count_mismatch",
        "linked_canonical_merkle_summary_mismatch",
        "linked_witness_count_mismatch",
        "linked_witness_summary_mismatch",
        "membership_proof_hash_mismatch",
        "missing_predecessor_transition_row",
        "packet_hash_mismatch",
        "packet_transition_summary_mismatch",
        "sampled_n8_bound_missing",
        "transition_parent_state_not_in_parent_frontier",
        "transition_step_bit_out_of_range",
    ]


def test_bidirectional_n8_transition_case_rows(
    bidirectional_n8_report: dict[str, object],
) -> None:
    rows = bidirectional_n8_report["search"]["cases"]

    assert [
        (
            row["transition_row_count"],
            row["sampled_child_mask_count"],
            row["unique_generated_child_count"],
        )
        for row in rows
    ] == [(48, 17, 17), (104, 17, 34), (116, 17, 37)]
    assert [row["transition_rows_digest"] for row in rows] == [
        "2a63f35abcbc298e94cafc56ce6cdfdf3b5ae0ab19bb6160ee9aee79ab9608eb",
        "94c699f544cd4b6b998483d449b7d9aa660e95f61df18d8b791585a51d778514",
        "1255b42eb0ac23db74412c95d136c934e1654417799c0bcde48123ca0148fdde",
    ]


def test_bidirectional_n8_transition_negative_controls(
    bidirectional_n8_report: dict[str, object],
) -> None:
    controls = bidirectional_n8_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "sampled_n8_bound_missing",
        "missing_predecessor_transition_row",
        "transition_parent_state_not_in_parent_frontier",
        "afterstep_generated_child_mismatch",
        "transition_step_bit_out_of_range",
        "generated_state_root_mismatch",
        "membership_proof_hash_mismatch",
        "linked_witness_count_mismatch",
        "linked_canonical_merkle_membership_count_mismatch",
        "authority_effect_present",
    }


def test_bidirectional_n8_transition_non_claims(
    bidirectional_n8_report: dict[str, object],
) -> None:
    non_claims = "\n".join(bidirectional_n8_report["non_claims"])

    assert "bounded to the deterministic sampled n=8 corpus" in non_claims
    assert "sampled zero-min exact-in cases" in non_claims
    assert "sampled n=8 predecessor-witness report" in non_claims
    assert "sampled n=8 canonical-Merkle report" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_bidirectional_n8_transition_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_bidirectional_transition_n8_sample_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["transition_row_count"] == 268
    assert report["search"]["negative_control_accept_count"] == 0
