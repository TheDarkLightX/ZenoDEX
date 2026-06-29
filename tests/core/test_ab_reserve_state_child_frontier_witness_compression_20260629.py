from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_witness_compression_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def witness_report() -> dict[str, object]:
    return build_report()


def test_child_frontier_witness_compression_report(witness_report: dict[str, object]) -> None:
    search = witness_report["search"]

    assert witness_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["child_mask_count"] == 508
    assert search["expected_child_state_count"] == 864
    assert search["witness_count"] == 864
    assert search["covered_child_state_count"] == 864
    assert search["missing_child_state_witness_count"] == 0
    assert search["extra_child_state_witness_count"] == 0
    assert search["invalid_witness_count"] == 0
    assert search["duplicate_witness_count"] == 0
    assert search["predecessor_transition_count"] == 2_777
    assert search["witness_transition_checks_saved"] == 1_913
    assert search["witness_compression_ratio"] == 3.21412
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert witness_report["deterministic_replay"]["ok"] is True


def test_child_frontier_witness_compression_linked_report(
    witness_report: dict[str, object],
) -> None:
    linked = witness_report["search"]["linked_frontier_summary"]

    assert linked["available"] is True
    assert linked["ok"] is True
    assert linked["child_mask_count"] == 508
    assert linked["child_state_count"] == 864
    assert linked["generated_state_count"] == 864
    assert linked["missing_child_state_count"] == 0
    assert linked["extra_generated_state_count"] == 0
    assert linked["frontier_rows_digest"] == (
        "b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4"
    )


def test_child_frontier_witness_compression_coverage(
    witness_report: dict[str, object],
) -> None:
    coverage = witness_report["search"]["coverage"]

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
        "duplicate_witness_row",
        "extra_child_state_witness",
        "linked_frontier_extra_generated_state",
        "linked_frontier_summary_mismatch",
        "missing_child_state_witness",
        "packet_hash_mismatch",
        "packet_witness_summary_mismatch",
        "witness_afterstep_mismatch",
        "witness_child_state_not_in_child_frontier",
        "witness_parent_state_not_in_parent_frontier",
        "witness_step_bit_out_of_range",
    ]


def test_child_frontier_witness_compression_case_rows(
    witness_report: dict[str, object],
) -> None:
    rows = witness_report["search"]["cases"]

    assert [
        (row["witness_count"], row["predecessor_transition_count"])
        for row in rows
    ] == [
        (127, 448),
        (320, 1_004),
        (290, 877),
        (127, 448),
    ]
    assert [row["frontier_witness_compression_ratio"] for row in rows] == [
        3.527559,
        3.1375,
        3.024138,
        3.527559,
    ]
    assert [row["witness_rows_digest"] for row in rows] == [
        "50e7a607c536bb6f412b123bb273540fe96902b00f28a0f51d721f2c5cd248ce",
        "11e64226723ba7faaa9266eba37cbbbe93b13f2160650bdbffad32fe9758905a",
        "059a8d4c8307a3580c6c5231b702bfd03059cb1ba9c187ccee474f4b1d32409d",
        "3d8d97f2a7cf35d5d0eb251ee1634695f82ad9b96763ffe788f0511dfe682e24",
    ]


def test_child_frontier_witness_compression_negative_controls(
    witness_report: dict[str, object],
) -> None:
    controls = witness_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "missing_child_state_witness",
        "witness_parent_state_not_in_parent_frontier",
        "witness_child_state_not_in_child_frontier",
        "witness_step_bit_out_of_range",
        "duplicate_witness_row",
        "linked_frontier_extra_generated_state",
        "authority_effect_present",
    }


def test_child_frontier_witness_compression_non_claims(
    witness_report: dict[str, object],
) -> None:
    non_claims = "\n".join(witness_report["non_claims"])

    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "zero-min exact-in cases" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "no-extra generated-state fact is linked" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_child_frontier_witness_compression_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_witness_compression_20260629.py",
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
