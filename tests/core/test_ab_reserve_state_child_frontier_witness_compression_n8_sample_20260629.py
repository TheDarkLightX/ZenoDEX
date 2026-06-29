from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629 import (
    BIT_COUNT,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def witness_report() -> dict[str, object]:
    return build_report()


def test_child_frontier_witness_compression_n8_report(
    witness_report: dict[str, object],
) -> None:
    search = witness_report["search"]

    assert witness_report["ok"] is True
    assert search["sample_plan"]["bit_count"] == BIT_COUNT
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["sampled_child_mask_count"] == 51
    assert search["expected_sampled_child_state_count"] == 88
    assert search["witness_count"] == 88
    assert search["covered_sampled_child_state_count"] == 88
    assert search["missing_sampled_child_state_witness_count"] == 0
    assert search["extra_sampled_child_state_witness_count"] == 0
    assert search["invalid_witness_count"] == 0
    assert search["duplicate_witness_count"] == 0
    assert search["predecessor_transition_count"] == 268
    assert search["witness_transition_checks_saved"] == 180
    assert search["witness_compression_ratio"] == 3.045455
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert witness_report["deterministic_replay"]["ok"] is True


def test_child_frontier_witness_compression_n8_linked_report(
    witness_report: dict[str, object],
) -> None:
    linked = witness_report["search"]["linked_frontier_summary"]

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


def test_child_frontier_witness_compression_n8_coverage(
    witness_report: dict[str, object],
) -> None:
    coverage = witness_report["search"]["coverage"]

    assert coverage["n_counts"] == {"8": 3}
    assert coverage["fee_bps_counts"] == {"2500": 1, "30": 1, "9000": 1}
    assert coverage["pattern_counts"] == {
        "n8_deep_low_fee/tie": 1,
        "n8_deep_mid_fee/front_burst": 1,
        "n8_thin_high_fee/stair": 1,
    }
    assert coverage["reason_classes"] == [
        "authority_effect_present",
        "duplicate_witness_row",
        "extra_sampled_child_state_witness",
        "linked_frontier_extra_generated_state",
        "linked_frontier_summary_mismatch",
        "missing_sampled_child_state_witness",
        "packet_hash_mismatch",
        "packet_witness_summary_mismatch",
        "sampled_n8_bound_missing",
        "witness_afterstep_mismatch",
        "witness_child_state_not_in_sampled_child_frontier",
        "witness_parent_state_not_in_parent_frontier",
        "witness_step_bit_out_of_range",
    ]


def test_child_frontier_witness_compression_n8_case_rows(
    witness_report: dict[str, object],
) -> None:
    rows = witness_report["search"]["cases"]

    assert [
        (row["witness_count"], row["predecessor_transition_count"])
        for row in rows
    ] == [
        (17, 48),
        (34, 104),
        (37, 116),
    ]
    assert [row["frontier_witness_compression_ratio"] for row in rows] == [
        2.823529,
        3.058824,
        3.135135,
    ]
    assert [row["witness_rows_digest"] for row in rows] == [
        "01b7aa20267ddaa7ee1d95f5d43665fac7b425bb55d42897114235af183dba8c",
        "86e46ec5497b34f1be427434f64d4ad48966cbc4e7fff8c6ab7d3f03fd3174c1",
        "7f7dcc7e2ca3ec335620b1a50eb57b2778b9dc3d25a6c7544820bc399a2f5e80",
    ]


def test_child_frontier_witness_compression_n8_negative_controls(
    witness_report: dict[str, object],
) -> None:
    controls = witness_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "missing_sampled_child_state_witness",
        "witness_parent_state_not_in_parent_frontier",
        "witness_child_state_not_in_sampled_child_frontier",
        "witness_step_bit_out_of_range",
        "duplicate_witness_row",
        "sampled_n8_bound_missing",
        "linked_frontier_extra_generated_state",
        "authority_effect_present",
    }


def test_child_frontier_witness_compression_n8_non_claims(
    witness_report: dict[str, object],
) -> None:
    non_claims = "\n".join(witness_report["non_claims"])

    assert "bounded to the deterministic n=8 sample" in non_claims
    assert "sampled zero-min exact-in cases" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "no-extra generated-state fact is linked" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_child_frontier_witness_compression_n8_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_CASE_COUNT
    assert report["search"]["negative_control_accept_count"] == 0
