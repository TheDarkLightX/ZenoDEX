from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_generation_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def frontier_report() -> dict[str, object]:
    return build_report()


def test_ab_reserve_state_child_frontier_generation_report(
    frontier_report: dict[str, object],
) -> None:
    search = frontier_report["search"]

    assert frontier_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["child_mask_count"] == 508
    assert search["frontier_equal_count"] == 508
    assert search["predecessor_edge_count"] == 1_792
    assert search["predecessor_transition_count"] == 2_777
    assert search["predecessor_transition_executable_count"] == 2_777
    assert search["child_state_count"] == 864
    assert search["generated_state_count"] == 864
    assert search["missing_child_state_count"] == 0
    assert search["extra_generated_state_count"] == 0
    assert search["max_child_state_count"] == 5
    assert search["max_generated_state_count"] == 5
    assert search["frontier_rows_digest"] == (
        "b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert frontier_report["deterministic_replay"]["ok"] is True


def test_ab_reserve_state_child_frontier_generation_coverage(
    frontier_report: dict[str, object],
) -> None:
    coverage = frontier_report["search"]["coverage"]

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
        "generated_frontier_extra_child_state",
        "generated_frontier_missing_child_state",
        "packet_frontier_summary_mismatch",
        "packet_hash_mismatch",
        "packet_lean_contract_mismatch",
    ]


def test_ab_reserve_state_child_frontier_generation_first_row(
    frontier_report: dict[str, object],
) -> None:
    first_case = frontier_report["search"]["first_case"]
    first_frontier = first_case["first_frontier"]

    assert first_case["case_id"] == "n7_randomized_boundary_000_thin_fee9000_rout1100"
    assert first_case["child_mask_count"] == 127
    assert first_case["child_state_count"] == 127
    assert first_case["generated_state_count"] == 127
    assert first_case["frontier_rows_digest"] == (
        "54eb4c9f2a58c5e51cd19c34c1ac7cfb371f9fea6ebbd33686e702b2e8a5ef93"
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
    assert first_frontier["first_predecessor"]["generated_state_count"] == 1


def test_ab_reserve_state_child_frontier_generation_case_rows(
    frontier_report: dict[str, object],
) -> None:
    rows = frontier_report["search"]["cases"]

    assert [
        (row["child_mask_count"], row["child_state_count"], row["generated_state_count"])
        for row in rows
    ] == [
        (127, 127, 127),
        (127, 320, 320),
        (127, 290, 290),
        (127, 127, 127),
    ]
    assert [row["frontier_rows_digest"] for row in rows] == [
        "54eb4c9f2a58c5e51cd19c34c1ac7cfb371f9fea6ebbd33686e702b2e8a5ef93",
        "91b737dab0b90442284b0c82628d618f098c4d013d19180f2cdba16aa28cfa0a",
        "622e453b599d8b5c769628078bef4d95a1d8c8af5a8eaa68db8743b49f461354",
        "bfb56c51fe16b20de441b102c7473142449cda8515d9851d3ef79813769e0cef",
    ]


def test_ab_reserve_state_child_frontier_generation_negative_controls(
    frontier_report: dict[str, object],
) -> None:
    controls = frontier_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    expected_reasons = {control["expected_reason"] for control in controls}
    assert expected_reasons == {
        "packet_hash_mismatch",
        "packet_lean_contract_mismatch",
        "packet_frontier_summary_mismatch",
        "authority_effect_present",
        "generated_frontier_missing_child_state",
        "generated_frontier_extra_child_state",
    }


def test_ab_reserve_state_child_frontier_generation_non_claims(
    frontier_report: dict[str, object],
) -> None:
    non_claims = "\n".join(frontier_report["non_claims"])

    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "covers only zero-min exact-in cases" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "No settlement" in non_claims


def test_ab_reserve_state_child_frontier_generation_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_reserve_state_child_frontier_generation_20260629.py"],
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
