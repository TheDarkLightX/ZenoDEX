from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_emitter_witness_stress import CASE_COUNT
from tools.check_ab_strict_zero_min_subset_induction_witness import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    build_report,
    verify_case,
)
from tools.check_ab_strict_zero_min_emitter_witness_stress import _iter_cases


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def subset_induction_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_subset_induction_report(
    subset_induction_report: dict[str, object],
) -> None:
    search = subset_induction_report["search"]

    assert subset_induction_report["ok"] is True
    assert search["case_count"] == CASE_COUNT
    assert search["strict_case_count"] == 180
    assert search["valid_case_count"] == 180
    assert search["first_invalid_case"] is None
    assert search["mask_count"] == 4_464
    assert search["record_count"] == 85_284
    assert search["suffix_check_count"] == 212_760
    assert search["executable_completion_count"] == 212_760
    assert search["max_records_per_mask"] == 720
    assert search["max_suffix_per_record"] == 720
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert subset_induction_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_subset_induction_coverage(
    subset_induction_report: dict[str, object],
) -> None:
    coverage = subset_induction_report["search"]["coverage"]

    assert coverage["n_counts"] == {"2": 36, "3": 36, "4": 36, "5": 36, "6": 36}
    assert coverage["fee_bps_counts"] == {
        "0": 26,
        "1": 26,
        "2": 26,
        "5": 26,
        "30": 26,
        "75": 25,
        "100": 25,
    }
    assert coverage["pattern_counts"] == {
        "alternating": 20,
        "ascending": 20,
        "descending": 20,
        "fibonacci": 20,
        "flat": 20,
        "near_tie_pairs": 20,
        "one_large_prefix": 20,
        "one_large_suffix": 20,
        "seeded_random": 20,
    }


def test_ab_strict_zero_min_subset_induction_first_case_shape(
    subset_induction_report: dict[str, object],
) -> None:
    first_case = subset_induction_report["search"]["cases"][0]

    assert first_case["case_id"] == "stress_000_flat_n2_fee0"
    assert first_case["ok"] is True
    assert first_case["reasons"] == []
    assert first_case["mask_count"] == 4
    assert first_case["record_count"] == 5
    assert first_case["suffix_check_count"] == 6
    assert first_case["executable_completion_count"] == 6
    assert first_case["full_mask_selected"]["processed_reserve_in"] == 528
    assert first_case["full_mask_selected"]["reserve_out"] == 32020


def test_ab_strict_zero_min_subset_induction_negative_controls_fail_closed(
    subset_induction_report: dict[str, object],
) -> None:
    controls = {
        row["mutation_id"]: row
        for row in subset_induction_report["search"]["negative_controls"]
    }

    for mutation_id, row in controls.items():
        assert row["accepted"] is False, mutation_id
        assert row["expected_reason"] in row["reasons"]

    assert "compressed_record_missing" in controls["compressed_record_missing"]["reasons"]
    assert (
        "full_record_processed_reserve_in_mismatch"
        in controls["full_record_processed_reserve_in_mismatch"]["reasons"]
    )
    assert "selected_reserve_out_not_min" in controls["selected_reserve_out_not_min"]["reasons"]
    assert (
        "selected_record_not_in_full_state_records"
        in controls["selected_record_not_in_full_state_records"]["reasons"]
    )
    assert "selected_suffix_executability_gap" in controls["selected_suffix_executability_gap"]["reasons"]
    assert (
        "selected_final_reserve_dominance_failure"
        in controls["selected_final_reserve_dominance_failure"]["reasons"]
    )


def test_ab_strict_zero_min_subset_induction_direct_case_verifier() -> None:
    first_case = _iter_cases()[0]
    verification = verify_case(first_case)

    assert verification["ok"] is True
    assert verification["mask_count"] == 4
    assert verification["record_count"] == 5
    assert verification["suffix_check_count"] == 6
    assert verification["first_failure"] is None


def test_ab_strict_zero_min_subset_induction_non_claims(
    subset_induction_report: dict[str, object],
) -> None:
    non_claims = "\n".join(subset_induction_report["non_claims"])

    assert "not a Lean proof of the full subset-mask induction theorem" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "Nonzero min_amount_out batches are outside" in non_claims
    assert "deterministic and finite" in non_claims
    assert "No settlement authority" in non_claims


def test_ab_strict_zero_min_subset_induction_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_subset_induction_witness.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == 180
    assert report["search"]["negative_control_accept_count"] == 0
