from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_observed_frontier_n7_randomized_20260629 import (
    EXPECTED_CHILDREN_PER_CASE,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def observed_n7_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_observed_frontier_n7_report(
    observed_n7_report: dict[str, object],
) -> None:
    search = observed_n7_report["search"]

    assert observed_n7_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["strict_packet_count"] == TARGET_CASE_COUNT
    assert search["valid_observed_packet_count"] == TARGET_CASE_COUNT
    assert search["skipped_count"] == 0
    assert search["first_invalid_packet"] is None
    assert search["mutation_count"] == 52
    assert search["mutation_accept_count"] == 0
    assert search["first_mutation_accept"] is None
    assert search["total_children_count"] == 20_160
    assert search["total_packet_canonical_bytes"] == 28_151_362
    assert search["max_packet_canonical_bytes"] == 7_104_239
    assert observed_n7_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_observed_frontier_n7_coverage(
    observed_n7_report: dict[str, object],
) -> None:
    coverage = observed_n7_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["fee_bps_counts"] == {"1": 1, "100": 2, "9000": 1}
    assert coverage["pattern_counts"] == {
        "high_fee_deep_out/rand_stair": 1,
        "near_domain_in/rand_burst": 1,
        "near_zero_positive/rand_tie": 1,
        "thin_positive_boundary/high_fee9000": 1,
    }
    assert coverage["min_children_count"] == EXPECTED_CHILDREN_PER_CASE
    assert coverage["max_children_count"] == EXPECTED_CHILDREN_PER_CASE
    assert coverage["max_bit_count"] == 7
    assert "base_witness_packet_invalid" in coverage["reason_classes"]
    assert "child_missing_full_mask_coverage" in coverage["reason_classes"]
    assert "child_local_pruning_selected_not_record" in coverage["reason_classes"]
    assert "child_local_pruning_processed_reserve_in_mismatch" in coverage["reason_classes"]
    assert "child_local_pruning_reserve_out_not_min" in coverage["reason_classes"]
    assert "observed_winner_not_in_children" in coverage["reason_classes"]
    assert "observed_winner_not_selected_family_dominator" in coverage["reason_classes"]
    assert "observed_empty_suffix_not_executable" in coverage["reason_classes"]
    assert "observed_economic_key_mismatch" in coverage["reason_classes"]


def test_ab_strict_zero_min_observed_frontier_n7_cases(
    observed_n7_report: dict[str, object],
) -> None:
    rows = observed_n7_report["search"]["cases"]

    assert [row["case_id"] for row in rows] == [
        "n7_randomized_boundary_000_thin_fee9000_rout1100",
        "n7_randomized_000_near_zero_positive_rand_tie_fee1",
        "n7_randomized_001_high_fee_deep_out_rand_stair_fee100",
        "n7_randomized_002_near_domain_in_rand_burst_fee100",
    ]
    assert [row["packet_canonical_bytes"] for row in rows] == [
        6_991_872,
        7_032_729,
        7_022_522,
        7_104_239,
    ]
    assert [row["children_count"] for row in rows] == [5_040, 5_040, 5_040, 5_040]
    assert [row["economic_keys"]["compressed"] for row in rows] == [
        [721, 7],
        [313, 2922],
        [411, 17320],
        [735, 652],
    ]
    assert rows[0]["winner_selected"] == {"processed_reserve_in": 10_721, "reserve_out": 1_093}
    assert all(row["ok"] is True for row in rows)
    assert all(row["reasons"] == [] for row in rows)
    assert all(row["checks"]["base_witness_packet_ok"] is True for row in rows)
    assert all(row["checks"]["all_children_cover_full_mask"] is True for row in rows)
    assert all(row["checks"]["all_children_locally_pruned"] is True for row in rows)
    assert all(row["checks"]["winner_member_of_observed_children"] is True for row in rows)
    assert all(row["checks"]["winner_selected_family_dominator"] is True for row in rows)
    assert all(row["checks"]["economic_key_matches_witness"] is True for row in rows)


def test_ab_strict_zero_min_observed_frontier_n7_first_packet_brief(
    observed_n7_report: dict[str, object],
) -> None:
    first_packet = observed_n7_report["search"]["first_packet"]

    assert first_packet["case_id"] == "n7_randomized_boundary_000_thin_fee9000_rout1100"
    assert first_packet["children_count"] == 5_040
    assert first_packet["bit_count"] == 7
    assert first_packet["full_mask"] == 127
    assert first_packet["stress"] == {
        "seed": 2_026_062_907,
        "pattern": "thin_positive_boundary/high_fee9000",
        "case_count": 4,
    }
    assert "children" not in first_packet
    assert first_packet["winner"]["processed_reserve_in"] == 10_721
    assert first_packet["winner"]["reserve_out"] == 1_093


def test_ab_strict_zero_min_observed_frontier_n7_mutations_fail_closed(
    observed_n7_report: dict[str, object],
) -> None:
    mutations = observed_n7_report["search"]["mutations"]
    mutation_ids = {row["mutation_id"] for row in mutations}

    assert len(mutations) == 52
    assert all(row["accepted"] is False for row in mutations)
    assert mutation_ids == {
        "bad_packet_hash",
        "authority_effect_present",
        "winner_missing_full_mask_bit",
        "winner_removed_from_children",
        "selected_no_longer_dominates",
        "economic_key_mismatch",
        "executed_input_mismatch",
        "child_mask_missing_bit",
        "child_selected_not_record",
        "child_processed_reserve_in_mismatch",
        "child_selected_not_local_min",
        "child_selected_family_beats_winner",
        "winner_empty_suffix",
    }


def test_ab_strict_zero_min_observed_frontier_n7_non_claims(
    observed_n7_report: dict[str, object],
) -> None:
    non_claims = "\n".join(observed_n7_report["non_claims"])

    assert "bounded to the committed four-case n=7 randomized corpus" in non_claims
    assert "does not prove generation of the full child frontier in Lean" in non_claims
    assert "does not prove recursive subset-mask induction" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "Nonzero min_amount_out batches are outside" in non_claims
    assert "does not cover n=8 observed-frontier packets" in non_claims
    assert "No settlement, state-root, production, routing, matching, or governance authority" in non_claims


def test_ab_strict_zero_min_observed_frontier_n7_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_strict_zero_min_observed_frontier_n7_randomized_20260629.py",
            "--json-only",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_observed_packet_count"] == TARGET_CASE_COUNT
    assert report["search"]["mutation_accept_count"] == 0
