from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_observed_frontier_witness import (
    EXPECTED_OBSERVED_MUTATION_COUNT,
    REPORT_JSON,
    build_report,
    verify_observed_frontier_packet,
)
from tools.check_ab_strict_zero_min_emitter_witness_stress import CASE_COUNT


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def observed_frontier_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_observed_frontier_report(
    observed_frontier_report: dict[str, object],
) -> None:
    search = observed_frontier_report["search"]

    assert observed_frontier_report["ok"] is True
    assert search["case_count"] == CASE_COUNT
    assert search["strict_packet_count"] == 180
    assert search["valid_observed_packet_count"] == 180
    assert search["skipped_count"] == 0
    assert search["first_invalid_packet"] is None
    assert search["observed_mutation_count_per_packet"] == EXPECTED_OBSERVED_MUTATION_COUNT
    assert search["mutation_count"] == 2_340
    assert search["mutation_accept_count"] == 0
    assert search["first_mutation_accept"] is None
    assert observed_frontier_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_observed_frontier_coverage(
    observed_frontier_report: dict[str, object],
) -> None:
    coverage = observed_frontier_report["search"]["coverage"]

    assert coverage["n_counts"] == {"2": 36, "3": 36, "4": 36, "5": 36, "6": 36}
    assert coverage["max_bit_count"] == 6
    assert coverage["max_children_count"] == 720
    assert "child_all_records_digest_mismatch" in coverage["reason_classes"]
    assert "child_missing_full_mask_coverage" in coverage["reason_classes"]
    assert "child_local_pruning_selected_not_record" in coverage["reason_classes"]
    assert "child_local_pruning_processed_reserve_in_mismatch" in coverage["reason_classes"]
    assert "child_local_pruning_reserve_out_not_min" in coverage["reason_classes"]
    assert "observed_winner_not_selected_family_dominator" in coverage["reason_classes"]
    assert "observed_empty_suffix_not_executable" in coverage["reason_classes"]


def test_ab_strict_zero_min_observed_frontier_first_packet_shape(
    observed_frontier_report: dict[str, object],
) -> None:
    packet = observed_frontier_report["search"]["first_packet"]
    verification = verify_observed_frontier_packet(packet)

    assert verification["ok"] is True
    assert packet["scope"] == "stress_same_pool_same_direction_exact_in_zero_min_strict_executable"
    assert packet["authority_boundary"] == "research_only_no_settlement_or_state_authority"
    assert packet["no_authority_effect"] is True
    assert verification["checks"]["base_witness_packet_ok"] is True
    assert verification["checks"]["all_children_cover_full_mask"] is True
    assert verification["checks"]["all_children_locally_pruned"] is True
    assert verification["checks"]["winner_member_of_observed_children"] is True
    assert verification["checks"]["winner_selected_family_dominator"] is True
    assert verification["checks"]["empty_suffix_executable"] is True
    assert verification["checks"]["economic_key_matches_witness"] is True


def test_ab_strict_zero_min_observed_frontier_mutations_fail_closed(
    observed_frontier_report: dict[str, object],
) -> None:
    first_case = observed_frontier_report["search"]["first_packet"]["case_id"]
    mutation_reasons = {
        row["mutation_id"]: set(row["reasons"])
        for row in observed_frontier_report["search"]["mutations"]
        if row["case_id"] == first_case
    }

    assert "base_witness_packet_invalid" in mutation_reasons["bad_packet_hash"]
    assert "base_witness_packet_invalid" in mutation_reasons["authority_effect_present"]
    assert "base_witness_packet_invalid" in mutation_reasons["winner_missing_full_mask_bit"]
    assert "base_witness_packet_invalid" in mutation_reasons["winner_removed_from_children"]
    assert (
        "observed_winner_not_selected_family_dominator"
        in mutation_reasons["selected_no_longer_dominates"]
    )
    assert "observed_economic_key_mismatch" in mutation_reasons["economic_key_mismatch"]
    assert "child_missing_full_mask_coverage" in mutation_reasons["child_mask_missing_bit"]
    assert "child_local_pruning_selected_not_record" in mutation_reasons["child_selected_not_record"]
    assert (
        "child_local_pruning_processed_reserve_in_mismatch"
        in mutation_reasons["child_processed_reserve_in_mismatch"]
    )
    assert "child_local_pruning_reserve_out_not_min" in mutation_reasons["child_selected_not_local_min"]
    assert (
        "observed_winner_not_selected_family_dominator"
        in mutation_reasons["child_selected_family_beats_winner"]
    )
    assert "observed_empty_suffix_not_executable" in mutation_reasons["winner_empty_suffix"]


def test_ab_strict_zero_min_observed_frontier_non_claims(
    observed_frontier_report: dict[str, object],
) -> None:
    non_claims = "\n".join(observed_frontier_report["non_claims"])

    assert "does not prove generation of the full child frontier" in non_claims
    assert "does not prove recursive subset-mask induction" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "Nonzero min_amount_out batches are outside" in non_claims
    assert "No settlement authority" in non_claims


def test_ab_strict_zero_min_observed_frontier_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_observed_frontier_witness.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["strict_packet_count"] == 180
    assert report["search"]["valid_observed_packet_count"] == 180
    assert report["search"]["mutation_accept_count"] == 0
