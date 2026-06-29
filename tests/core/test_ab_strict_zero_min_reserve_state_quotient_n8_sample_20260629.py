from __future__ import annotations

import json
import subprocess
import sys

import pytest

from tools.check_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629 import (
    BIT_COUNT,
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPO_ROOT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)


@pytest.fixture(scope="module")
def n8_sample_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_report(
    n8_sample_report: dict[str, object],
) -> None:
    search = n8_sample_report["search"]

    assert n8_sample_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["sample_plan"]["bit_count"] == BIT_COUNT
    assert search["sample_plan"]["suffix_sample_limit"] == 24
    assert search["sample_plan"]["full_dp_generated_all_masks"] is True

    assert search["full_record_count_all"] == 328_803
    assert search["quotient_state_count_all"] == 1_683
    assert search["all_record_compression_saved"] == 327_120
    assert search["all_record_compression_ratio"] == 195.367201

    assert search["sampled_mask_count"] == 54
    assert search["sampled_full_record_count"] == 121_563
    assert search["sampled_quotient_state_count"] == 91
    assert search["sampled_suffix_count"] == 1_227
    assert search["lean_observed_summary_count"] == 1_227
    assert search["lean_observed_summary_count"] == search["sampled_suffix_count"]
    assert search["lean_observed_summary_digest"] == (
        "eab4ae228e9ff9fe78393f55d8ec0fce3435600f8555cedfe7908f780402bd9b"
    )
    assert search["suffix_universe_count"] == 242_499
    assert search["selected_suffix_executable_count"] == 1_227

    assert search["baseline_full_dominance_check_count"] == 135_432
    assert search["quotient_dominance_check_count"] == 1_862
    assert search["quotient_runtime_completion_count"] == 1_862
    assert search["dominance_check_compression_saved"] == 133_570
    assert search["dominance_check_compression_ratio"] == 72.734694
    assert search["max_full_records_per_sampled_mask"] == 40_320
    assert search["max_quotient_states_per_sampled_mask"] == 7
    assert search["max_suffix_universe_per_mask"] == 40_320

    assert n8_sample_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_cases(
    n8_sample_report: dict[str, object],
) -> None:
    rows = n8_sample_report["search"]["cases"]

    assert [row["case_id"] for row in rows] == [
        "n8_sample_000_thin_fee9000_stair",
        "n8_sample_001_deep_fee30_tie",
        "n8_sample_002_burst_fee2500",
    ]
    assert [row["quotient_state_count_all"] for row in rows] == [256, 682, 745]
    assert [row["sampled_quotient_state_count"] for row in rows] == [18, 35, 38]
    assert [row["quotient_dominance_check_count"] for row in rows] == [409, 702, 751]
    assert [row["sampled_suffix_count"] for row in rows] == [409, 409, 409]
    assert [row["fee_bps"] for row in rows] == [9_000, 30, 2_500]
    assert all(row["ok"] is True for row in rows)
    assert all(row["reasons"] == [] for row in rows)
    assert all(row["stress"]["seed"] == 2_026_062_908 for row in rows)
    assert rows[0]["full_mask_selected_state"] == {
        "processed_reserve_in": 10_828,
        "reserve_out": 1_592,
    }


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_coverage(
    n8_sample_report: dict[str, object],
) -> None:
    coverage = n8_sample_report["search"]["coverage"]

    assert coverage["n_counts"] == {"8": 3}
    assert coverage["fee_bps_counts"] == {"30": 1, "2500": 1, "9000": 1}
    assert coverage["sampled_remaining_counts"] == {
        "0": 3,
        "1": 0,
        "2": 0,
        "3": 0,
        "4": 24,
        "5": 0,
        "6": 0,
        "7": 24,
        "8": 3,
    }
    assert "selected_state_not_in_quotient_family" in coverage["reason_classes"]
    assert "selected_reserve_out_not_min" in coverage["reason_classes"]
    assert "selected_suffix_not_executable" in coverage["reason_classes"]
    assert "packet_sample_plan_mismatch" in coverage["reason_classes"]
    assert "packet_lean_contract_mismatch" in coverage["reason_classes"]
    assert "packet_lean_observed_summary_mismatch" in coverage["reason_classes"]
    assert "sampled_n8_bound_missing" in coverage["reason_classes"]


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_negative_controls(
    n8_sample_report: dict[str, object],
) -> None:
    search = n8_sample_report["search"]
    controls = search["negative_controls"]

    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert all(control["accepted"] is False for control in controls)
    assert {control["mutation_id"] for control in controls} == {
        "packet_hash_mismatch",
        "authority_effect_present",
        "quotient_family_bound_missing",
        "reserve_state_only_bound_missing",
        "sampled_n8_bound_missing",
        "packet_sample_plan_mismatch",
        "packet_lean_contract_mismatch",
        "packet_lean_observed_summary_mismatch",
        "compressed_record_missing",
        "selected_state_not_in_quotient_family",
        "selected_reserve_out_not_min",
        "selected_suffix_not_executable",
    }
    for control in controls:
        assert control["expected_reason"] in control["reasons"]


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_lean_projection(
    n8_sample_report: dict[str, object],
) -> None:
    first_case = n8_sample_report["search"]["first_case"]
    lean_summary = first_case["lean_observed_summary"]

    assert n8_sample_report["lean_contract"]["projection_shape"] == (
        "one_digest_row_per_sampled_mask_sampled_suffix"
    )
    assert lean_summary["contract"]["summary_endpoint"] == (
        "reserveStateQuotientObservedSummary_validates"
    )
    assert lean_summary["row_count"] == first_case["sampled_suffix_count"]
    assert lean_summary["digest"] == (
        "13f6ae624e4cf4d3086e69c3f4530f4733346f15fba22636e84787e764e4a95b"
    )
    assert lean_summary["first_row"] == {
        "mask_id": 0,
        "suffix_order_ids": [
            "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c1",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c2",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c3",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c4",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c5",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c6",
            "0x00000000000000000000000000000000000000000000000000000000006cf5c7",
        ],
        "suffix_short": ["f5c0", "f5c1", "f5c2", "f5c3", "f5c4", "f5c5", "f5c6", "f5c7"],
        "lean_structure": "ReserveStateQuotientObservedSummary",
        "lean_endpoint": "reserveStateQuotientObservedSummary_validates",
        "observed_state_count": 1,
        "observed_selected_reserve_in": 10_000,
        "observed_selected_reserve_out": 1_600,
        "observed_executed_input": 828,
        "observed_initial_reserve_out": 1_600,
        "selected_state_digest": "04599cb8fbe86d40a4749171f9837cdde73cfa4f248b55f7a700c5f1207190b9",
        "table_state_digest": "def37c5bc34f6776c10da1a4ba66aef1c4a1031129bd81de8bae8909a73ed586",
    }


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_non_claims(
    n8_sample_report: dict[str, object],
) -> None:
    non_claims = "\n".join(n8_sample_report["non_claims"])

    assert "bounded deterministic n=8 sample" in non_claims
    assert "not exhaustive n=8 coverage" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "does not cover nonzero min_amount_out" in non_claims
    assert "no settlement, state-root, production, routing, matching, or governance authority" in non_claims


def test_ab_strict_zero_min_reserve_state_quotient_n8_sample_cli_replay() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629.py",
            "--no-markdown",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    payload = json.loads(result.stdout)
    assert payload["ok"] is True
    assert payload["report"] == str(REPORT_JSON.relative_to(REPO_ROOT))

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_CASE_COUNT
