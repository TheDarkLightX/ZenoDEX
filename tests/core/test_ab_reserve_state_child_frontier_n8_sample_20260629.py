from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_n8_sample_20260629 import (
    BIT_COUNT,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def frontier_report() -> dict[str, object]:
    return build_report()


def test_ab_reserve_state_child_frontier_n8_sample_report(
    frontier_report: dict[str, object],
) -> None:
    search = frontier_report["search"]

    assert frontier_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["sample_plan"]["bit_count"] == BIT_COUNT
    assert search["sample_plan"]["full_dp_generated_all_masks"] is True
    assert search["sampled_child_mask_count"] == 51
    assert search["frontier_equal_count"] == 51
    assert search["predecessor_edge_count"] == 144
    assert search["predecessor_transition_count"] == 268
    assert search["predecessor_transition_executable_count"] == 268
    assert search["sampled_child_state_count"] == 88
    assert search["generated_state_count"] == 88
    assert search["missing_child_state_count"] == 0
    assert search["extra_generated_state_count"] == 0
    assert search["max_child_state_count"] == 7
    assert search["max_generated_state_count"] == 7
    assert search["frontier_rows_digest"] == (
        "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert frontier_report["deterministic_replay"]["ok"] is True


def test_ab_reserve_state_child_frontier_n8_sample_coverage(
    frontier_report: dict[str, object],
) -> None:
    coverage = frontier_report["search"]["coverage"]

    assert coverage["n_counts"] == {"8": 3}
    assert coverage["fee_bps_counts"] == {"2500": 1, "30": 1, "9000": 1}
    assert coverage["pattern_counts"] == {
        "n8_deep_low_fee/tie": 1,
        "n8_deep_mid_fee/front_burst": 1,
        "n8_thin_high_fee/stair": 1,
    }
    assert coverage["reason_classes"] == [
        "authority_effect_present",
        "generated_frontier_extra_child_state",
        "generated_frontier_missing_child_state",
        "packet_hash_mismatch",
        "packet_lean_contract_mismatch",
        "packet_sample_plan_mismatch",
        "sampled_n8_bound_missing",
    ]


def test_ab_reserve_state_child_frontier_n8_sample_first_row(
    frontier_report: dict[str, object],
) -> None:
    first_case = frontier_report["search"]["first_case"]
    first_frontier = first_case["first_frontier"]

    assert first_case["case_id"] == "n8_sample_000_thin_fee9000_stair"
    assert first_case["sampled_child_mask_count"] == 17
    assert first_case["sampled_child_state_count"] == 17
    assert first_case["generated_state_count"] == 17
    assert first_case["frontier_rows_digest"] == (
        "9407ad4a9115e87cee1ab9ab04dee9325570fb0d3009d2c8e8bf65493166537c"
    )
    assert first_frontier["child_mask_id"] == 1
    assert first_frontier["frontier_equal"] is True
    assert first_frontier["child_state_count"] == 1
    assert first_frontier["generated_state_count"] == 1
    assert first_frontier["missing_child_state_count"] == 0
    assert first_frontier["extra_generated_state_count"] == 0
    assert first_frontier["predecessor_count"] == 1
    assert first_frontier["predecessor_transition_count"] == 1
    assert first_frontier["predecessor_transition_executable_count"] == 1
    assert first_frontier["first_predecessor"]["parent_mask_id"] == 0
    assert first_frontier["first_predecessor"]["step_bit_index"] == 0


def test_ab_reserve_state_child_frontier_n8_sample_case_rows(
    frontier_report: dict[str, object],
) -> None:
    rows = frontier_report["search"]["cases"]

    assert [
        (row["case_id"], row["sampled_child_mask_count"], row["sampled_child_state_count"])
        for row in rows
    ] == [
        ("n8_sample_000_thin_fee9000_stair", 17, 17),
        ("n8_sample_001_deep_fee30_tie", 17, 34),
        ("n8_sample_002_burst_fee2500", 17, 37),
    ]
    assert [row["generated_state_count"] for row in rows] == [17, 34, 37]
    assert [row["frontier_rows_digest"] for row in rows] == [
        "9407ad4a9115e87cee1ab9ab04dee9325570fb0d3009d2c8e8bf65493166537c",
        "e59508b450bdd39a089fd82316bf5beefa5ff702fff21f7a5f8ad52043b76889",
        "24030620909166d67911962010ba393906c9ec7a52e1a3b5702e16a2edccf7aa",
    ]
    assert all(row["ok"] is True for row in rows)
    assert all(row["reasons"] == [] for row in rows)


def test_ab_reserve_state_child_frontier_n8_sample_negative_controls(
    frontier_report: dict[str, object],
) -> None:
    controls = frontier_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert all(control["accepted"] is False for control in controls)
    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "sampled_n8_bound_missing",
        "packet_sample_plan_mismatch",
        "packet_lean_contract_mismatch",
        "authority_effect_present",
        "generated_frontier_missing_child_state",
        "generated_frontier_extra_child_state",
    }
    for control in controls:
        assert control["expected_reason"] in control["reasons"]


def test_ab_reserve_state_child_frontier_n8_sample_non_claims(
    frontier_report: dict[str, object],
) -> None:
    non_claims = "\n".join(frontier_report["non_claims"])

    assert "bounded deterministic n=8 sample" in non_claims
    assert "sampled zero-min exact-in cases and sampled child masks" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "No settlement" in non_claims


def test_ab_reserve_state_child_frontier_n8_sample_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_reserve_state_child_frontier_n8_sample_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_CASE_COUNT
    assert report["search"]["negative_control_accept_count"] == 0
