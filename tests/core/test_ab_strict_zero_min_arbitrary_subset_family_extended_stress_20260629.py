from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_arbitrary_subset_family_extended_stress import (
    CASE_COUNT,
    REPORT_JSON,
    SCOPE_PROBE_COUNT,
    build_report,
    iter_extended_cases,
    run_search,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def extended_stress_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_extended_stress_report(
    extended_stress_report: dict[str, object],
) -> None:
    search = extended_stress_report["search"]

    assert extended_stress_report["ok"] is True
    assert search["case_count"] == CASE_COUNT
    assert search["valid_case_count"] == CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["mask_count"] == 2_232
    assert search["record_count"] == 42_642
    assert search["singleton_table_obligation_count"] == 42_642
    assert search["selected_suffix_executable_count"] == 42_642
    assert search["dominance_check_count"] == 106_380
    assert search["full_runtime_completion_count"] == 106_380
    assert search["max_records_per_mask"] == 720
    assert search["max_suffix_per_mask"] == 720
    assert search["scope_probe_count"] == SCOPE_PROBE_COUNT
    assert search["scope_probe_accept_count"] == 0
    assert extended_stress_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_extended_stress_coverage(
    extended_stress_report: dict[str, object],
) -> None:
    coverage = extended_stress_report["search"]["coverage"]

    assert coverage["n_counts"] == {"2": 18, "3": 18, "4": 18, "5": 18, "6": 18}
    assert coverage["fee_bps_counts"] == {
        "0": 9,
        "1": 9,
        "5": 9,
        "30": 9,
        "75": 9,
        "100": 9,
        "500": 9,
        "2500": 9,
        "5000": 9,
        "9000": 9,
    }
    assert len(coverage["pattern_counts"]) == 90
    assert coverage["pattern_counts"]["skewed_in/high_fee_safe"] == 1
    assert coverage["pattern_counts"]["near_domain_reserve_in/ascending_stair"] == 1
    assert coverage["pattern_counts"]["low_in_high_out/near_tie_stagger"] == 1
    assert coverage["pattern_counts"]["tight_out_positive/descending_stair"] == 1


def test_ab_strict_zero_min_extended_stress_first_case_shape(
    extended_stress_report: dict[str, object],
) -> None:
    first_case = extended_stress_report["search"]["first_case"]

    assert first_case["case_id"] == "extended_000_balanced_mid_tie_heavy_flat_n2_fee0"
    assert first_case["ok"] is True
    assert first_case["reasons"] == []
    assert first_case["mask_count"] == 4
    assert first_case["record_count"] == 5
    assert first_case["singleton_table_obligation_count"] == 5
    assert first_case["dominance_check_count"] == 6
    assert first_case["full_mask_selected"]["processed_reserve_in"] == 964


def test_ab_strict_zero_min_extended_stress_scope_probes_reject(
    extended_stress_report: dict[str, object],
) -> None:
    probes = extended_stress_report["search"]["scope_probes"]

    assert len(probes) == SCOPE_PROBE_COUNT
    for probe in probes:
        assert probe["accepted"] is False
        assert probe["expected_reason"] == "nonzero_min_amount_out_out_of_scope"
        assert probe["reason"] == "nonzero_min_amount_out_out_of_scope"


def test_ab_strict_zero_min_extended_stress_non_claims(
    extended_stress_report: dict[str, object],
) -> None:
    non_claims = "\n".join(extended_stress_report["non_claims"])

    assert "deterministic and finite" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not cover nonzero min_amount_out certificates" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "does not add settlement" in non_claims


def test_ab_strict_zero_min_extended_stress_direct_search() -> None:
    search = run_search()
    cases = iter_extended_cases()

    assert len(cases) == CASE_COUNT
    assert search["valid_case_count"] == CASE_COUNT
    assert search["scope_probe_accept_count"] == 0
    assert search["dominance_check_count"] == search["full_runtime_completion_count"]


def test_ab_strict_zero_min_extended_stress_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_arbitrary_subset_family_extended_stress.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == CASE_COUNT
    assert report["search"]["scope_probe_accept_count"] == 0
