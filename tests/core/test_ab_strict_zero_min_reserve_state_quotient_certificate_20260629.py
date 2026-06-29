from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_reserve_state_quotient_certificate import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def quotient_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_reserve_state_quotient_report(
    quotient_report: dict[str, object],
) -> None:
    search = quotient_report["search"]

    assert quotient_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["mask_count"] == 512
    assert search["full_record_count"] == 54_800
    assert search["quotient_state_count"] == 868
    assert search["record_compression_saved"] == 53_932
    assert search["record_compression_ratio"] == 63.133641
    assert search["quotient_table_obligation_count"] == 54_800
    assert search["selected_suffix_executable_count"] == 54_800
    assert search["baseline_full_dominance_check_count"] == 161_280
    assert search["quotient_dominance_check_count"] == 59_987
    assert search["quotient_runtime_completion_count"] == 59_987
    assert search["dominance_check_compression_saved"] == 101_293
    assert search["dominance_check_compression_ratio"] == 2.688583
    assert search["max_full_records_per_mask"] == 5_040
    assert search["max_quotient_states_per_mask"] == 5
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert quotient_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_reserve_state_quotient_coverage(
    quotient_report: dict[str, object],
) -> None:
    coverage = quotient_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["fee_bps_counts"] == {"1": 1, "100": 2, "9000": 1}
    assert coverage["pattern_counts"] == {
        "high_fee_deep_out/rand_stair": 1,
        "near_domain_in/rand_burst": 1,
        "near_zero_positive/rand_tie": 1,
        "thin_positive_boundary/high_fee9000": 1,
    }
    assert "selected_state_not_in_quotient_family" in coverage["reason_classes"]
    assert "selected_suffix_not_executable" in coverage["reason_classes"]
    assert "packet_quotient_summary_mismatch" in coverage["reason_classes"]


def test_ab_strict_zero_min_reserve_state_quotient_first_case(
    quotient_report: dict[str, object],
) -> None:
    first_case = quotient_report["search"]["first_case"]

    assert first_case["case_id"] == "n7_randomized_boundary_000_thin_fee9000_rout1100"
    assert first_case["ok"] is True
    assert first_case["reasons"] == []
    assert first_case["full_record_count"] == 13_700
    assert first_case["quotient_state_count"] == 128
    assert first_case["record_compression_saved"] == 13_572
    assert first_case["baseline_full_dominance_check_count"] == 40_320
    assert first_case["quotient_dominance_check_count"] == 13_700
    assert first_case["full_mask_selected_state"] == {
        "processed_reserve_in": 10_721,
        "reserve_out": 1_093,
    }


def test_ab_strict_zero_min_reserve_state_quotient_case_ratios(
    quotient_report: dict[str, object],
) -> None:
    rows = quotient_report["search"]["cases"]

    assert [(row["full_record_count"], row["quotient_state_count"]) for row in rows] == [
        (13_700, 128),
        (13_700, 321),
        (13_700, 291),
        (13_700, 128),
    ]
    assert [row["quotient_dominance_check_count"] for row in rows] == [
        13_700,
        16_815,
        15_772,
        13_700,
    ]


def test_ab_strict_zero_min_reserve_state_quotient_negative_controls(
    quotient_report: dict[str, object],
) -> None:
    controls = quotient_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    expected_reasons = {control["expected_reason"] for control in controls}
    assert expected_reasons == {
        "packet_hash_mismatch",
        "packet_hash_bound_missing",
        "authority_effect_present",
        "quotient_family_bound_missing",
        "reserve_state_only_bound_missing",
        "compressed_record_missing",
        "selected_state_not_in_quotient_family",
        "selected_reserve_out_not_min",
        "selected_suffix_not_executable",
        "packet_quotient_summary_mismatch",
    }


def test_ab_strict_zero_min_reserve_state_quotient_non_claims(
    quotient_report: dict[str, object],
) -> None:
    non_claims = "\n".join(quotient_report["non_claims"])

    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "does not cover nonzero min_amount_out certificates" in non_claims
    assert "not a Lean endpoint or production ABI" in non_claims
    assert "No settlement" in non_claims


def test_ab_strict_zero_min_reserve_state_quotient_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_reserve_state_quotient_certificate.py"],
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
