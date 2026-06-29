from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_arbitrary_subset_family_n7_randomized import (
    BOUNDARY_REJECTION_RESERVE_OUTS,
    REPORT_JSON,
    SCOPE_PROBE_COUNT,
    TARGET_VALID_CASE_COUNT,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def n7_randomized_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_n7_randomized_report(
    n7_randomized_report: dict[str, object],
) -> None:
    search = n7_randomized_report["search"]

    assert n7_randomized_report["ok"] is True
    assert search["positive_case_count"] == TARGET_VALID_CASE_COUNT
    assert search["valid_case_count"] == TARGET_VALID_CASE_COUNT
    assert search["first_invalid_positive_case"] is None
    assert search["candidate_rejection_count"] == 0
    assert search["mask_count"] == 512
    assert search["record_count"] == 54_800
    assert search["singleton_table_obligation_count"] == 54_800
    assert search["selected_suffix_executable_count"] == 54_800
    assert search["dominance_check_count"] == 161_280
    assert search["full_runtime_completion_count"] == 161_280
    assert search["max_records_per_mask"] == 5_040
    assert search["max_suffix_per_mask"] == 5_040
    assert search["scope_probe_count"] == SCOPE_PROBE_COUNT
    assert search["scope_probe_accept_count"] == 0
    assert search["strict_rejection_probe_count"] == len(BOUNDARY_REJECTION_RESERVE_OUTS)
    assert search["strict_rejection_accept_count"] == 0
    assert n7_randomized_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_n7_randomized_coverage(
    n7_randomized_report: dict[str, object],
) -> None:
    coverage = n7_randomized_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["fee_bps_counts"] == {"1": 1, "100": 2, "9000": 1}
    assert coverage["pattern_counts"] == {
        "high_fee_deep_out/rand_stair": 1,
        "near_domain_in/rand_burst": 1,
        "near_zero_positive/rand_tie": 1,
        "thin_positive_boundary/high_fee9000": 1,
    }


def test_ab_strict_zero_min_n7_boundary_case_shape(
    n7_randomized_report: dict[str, object],
) -> None:
    first_case = n7_randomized_report["search"]["first_case"]

    assert first_case["case_id"] == "n7_randomized_boundary_000_thin_fee9000_rout1100"
    assert first_case["ok"] is True
    assert first_case["reasons"] == []
    assert first_case["mask_count"] == 128
    assert first_case["record_count"] == 13_700
    assert first_case["singleton_table_obligation_count"] == 13_700
    assert first_case["dominance_check_count"] == 40_320
    assert first_case["full_mask_selected"]["processed_reserve_in"] == 10_721
    assert first_case["full_mask_selected"]["reserve_out"] == 1_093


def test_ab_strict_zero_min_n7_scope_probes_reject(
    n7_randomized_report: dict[str, object],
) -> None:
    probes = n7_randomized_report["search"]["scope_probes"]

    assert len(probes) == SCOPE_PROBE_COUNT
    for probe in probes:
        assert probe["accepted"] is False
        assert probe["expected_reason"] == "nonzero_min_amount_out_out_of_scope"
        assert probe["reason"] == "nonzero_min_amount_out_out_of_scope"


def test_ab_strict_zero_min_n7_strict_executability_probes_reject(
    n7_randomized_report: dict[str, object],
) -> None:
    probes = n7_randomized_report["search"]["strict_rejection_probes"]

    assert [probe["case_id"] for probe in probes] == [
        "n7_randomized_boundary_000_thin_fee9000_rout7",
        "n7_randomized_boundary_000_thin_fee9000_rout20",
        "n7_randomized_boundary_000_thin_fee9000_rout100",
    ]
    for probe in probes:
        assert probe["ok"] is False
        assert probe["reasons"][:2] == [
            "compressed_full_mask_not_executable",
            "singleton_table_suffix_not_executable",
        ]
        assert probe["first_failure"]["reason"] == "compressed_full_mask_not_executable"


def test_ab_strict_zero_min_n7_non_claims(
    n7_randomized_report: dict[str, object],
) -> None:
    non_claims = "\n".join(n7_randomized_report["non_claims"])

    assert "bounded and finite" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not cover nonzero min_amount_out certificates" in non_claims
    assert "scope controls" in non_claims
    assert "does not add settlement" in non_claims


def test_ab_strict_zero_min_n7_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_arbitrary_subset_family_n7_randomized.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_VALID_CASE_COUNT
    assert report["search"]["scope_probe_accept_count"] == 0
