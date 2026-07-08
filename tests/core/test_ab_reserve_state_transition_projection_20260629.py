from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_transition_projection_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def transition_report() -> dict[str, object]:
    return build_report()


def test_ab_reserve_state_transition_projection_report(
    transition_report: dict[str, object],
) -> None:
    search = transition_report["search"]

    assert transition_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["mask_count"] == 508
    assert search["transition_projection_count"] == 1_792
    assert search["selected_transition_count"] == 1_792
    assert search["selected_child_membership_count"] == 1_792
    assert search["candidate_transition_count"] == 2_777
    assert search["candidate_transition_executable_count"] == 2_777
    assert search["candidate_child_membership_count"] == 2_777
    assert search["candidate_processed_match_count"] == 2_777
    assert search["candidate_min_reserve_check_count"] == 2_777
    assert search["transition_rows_digest"] == (
        "e0feabfd435cc7f0045831dd4d2f379b74e29dbd6a260457a519e3fd0214f32c"
    )
    assert search["max_parent_state_count"] == 5
    assert search["max_child_state_count"] == 5
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert transition_report["deterministic_replay"]["ok"] is True


def test_ab_reserve_state_transition_projection_coverage(
    transition_report: dict[str, object],
) -> None:
    coverage = transition_report["search"]["coverage"]

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
        "candidate_transition_child_not_in_child_quotient",
        "packet_hash_mismatch",
        "packet_lean_contract_mismatch",
        "packet_transition_summary_mismatch",
        "selected_transition_child_not_in_child_quotient",
        "transition_min_reserve_failure",
    ]


def test_ab_reserve_state_transition_projection_first_transition(
    transition_report: dict[str, object],
) -> None:
    first_case = transition_report["search"]["first_case"]
    first_transition = first_case["first_transition"]

    assert first_case["case_id"] == "n7_randomized_boundary_000_thin_fee9000_rout1100"
    assert first_case["mask_count"] == 127
    assert first_case["transition_projection_count"] == 448
    assert first_case["candidate_transition_count"] == 448
    assert first_case["transition_rows_digest"] == (
        "cfdc1ebf66e4f20f843ef56fdb7f024e8cd8e1019300edce40eb5511b6e19449"
    )
    assert first_transition["lean_transition_def"] == "ReserveState.afterStep"
    assert first_transition["lean_invariant_endpoint"] == (
        "reserveStateQuotientInvariant_afterStep"
    )
    assert first_transition["lean_executability_endpoint"] == (
        "reserveStateQuotientInvariant_familySuffixExecutable"
    )
    assert first_transition["mask_id"] == 0
    assert first_transition["child_mask_id"] == 1
    assert first_transition["step_bit_index"] == 0
    assert first_transition["parent_selected_state"] == {
        "processed_reserve_in": 10_000,
        "reserve_out": 1_100,
    }
    assert first_transition["selected_child_state"] == {
        "processed_reserve_in": 10_100,
        "reserve_out": 1_099,
    }
    assert first_transition["selected_child_in_child_family"] is True
    assert first_transition["candidate_transition_count"] == 1
    assert first_transition["candidate_child_membership_count"] == 1
    assert first_transition["candidate_processed_match_count"] == 1
    assert first_transition["candidate_min_reserve_check_count"] == 1


def test_ab_reserve_state_transition_projection_case_rows(
    transition_report: dict[str, object],
) -> None:
    rows = transition_report["search"]["cases"]

    assert [
        (row["mask_count"], row["transition_projection_count"], row["candidate_transition_count"])
        for row in rows
    ] == [
        (127, 448, 448),
        (127, 448, 1_004),
        (127, 448, 877),
        (127, 448, 448),
    ]
    assert [row["transition_rows_digest"] for row in rows] == [
        "cfdc1ebf66e4f20f843ef56fdb7f024e8cd8e1019300edce40eb5511b6e19449",
        "e1c923a7c019cfae11620defaf81a4e803165b3d6ea794ae4c7f670c1fcf76e5",
        "dc3bab24b57a6e9a0182d19957435fbeee7d601e9da9041486044f88d3803845",
        "fb21bc939edb669a5784b0319074ca4213deec191e652a30c62a69f725efd183",
    ]


def test_ab_reserve_state_transition_projection_negative_controls(
    transition_report: dict[str, object],
) -> None:
    controls = transition_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    expected_reasons = {control["expected_reason"] for control in controls}
    assert expected_reasons == {
        "packet_hash_mismatch",
        "packet_lean_contract_mismatch",
        "packet_transition_summary_mismatch",
        "authority_effect_present",
        "selected_transition_child_not_in_child_quotient",
        "candidate_transition_child_not_in_child_quotient",
        "transition_min_reserve_failure",
    }


def test_ab_reserve_state_transition_projection_non_claims(
    transition_report: dict[str, object],
) -> None:
    non_claims = "\n".join(transition_report["non_claims"])

    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove full child-frontier generation in Lean" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "No settlement" in non_claims


def test_ab_reserve_state_transition_projection_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_reserve_state_transition_projection_20260629.py"],
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
