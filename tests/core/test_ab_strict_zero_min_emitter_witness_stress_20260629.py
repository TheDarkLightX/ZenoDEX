from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_emitter_witness import verify_witness_packet
from tools.check_ab_strict_zero_min_emitter_witness_stress import (
    CASE_COUNT,
    REPORT_JSON,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def stress_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_emitter_witness_stress_report(stress_report: dict[str, object]) -> None:
    search = stress_report["search"]

    assert stress_report["ok"] is True
    assert search["case_count"] == CASE_COUNT
    assert search["strict_packet_count"] == 180
    assert search["valid_packet_count"] == 180
    assert search["skipped_count"] == 0
    assert search["first_invalid_packet"] is None
    assert search["mutation_count"] == 1_260
    assert search["mutation_accept_count"] == 0
    assert search["first_mutation_accept"] is None
    assert stress_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_emitter_witness_stress_coverage(stress_report: dict[str, object]) -> None:
    coverage = stress_report["search"]["coverage"]

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
    assert coverage["max_bit_count"] == 6
    assert coverage["max_children_count"] == 720


def test_ab_strict_zero_min_emitter_witness_stress_first_packet_shape(
    stress_report: dict[str, object],
) -> None:
    packet = stress_report["search"]["first_packet"]
    verification = verify_witness_packet(packet)

    assert verification["ok"] is True
    assert packet["scope"] == "stress_same_pool_same_direction_exact_in_zero_min_strict_executable"
    assert packet["stress"]["seed"] == 2_026_062_901
    assert packet["winner"]["mask_id"] == packet["full_mask"]
    assert packet["winner"]["selected"]["processed_reserve_in"] == (
        packet["initial_reserve_in"] + packet["executed_input"]
    )
    assert verification["checks"]["winner_covers_full_mask"] is True
    assert verification["checks"]["winner_member_of_children"] is True
    assert verification["checks"]["selected_key_dominates_full_frontier"] is True
    assert verification["checks"]["host_economic_key_parity"] is True
    assert verification["checks"]["no_authority_effect"] is True


def test_ab_strict_zero_min_emitter_witness_stress_mutations_fail_closed(
    stress_report: dict[str, object],
) -> None:
    first_case = stress_report["search"]["first_packet"]["case_id"]
    mutation_reasons = {
        row["mutation_id"]: set(row["reasons"])
        for row in stress_report["search"]["mutations"]
        if row["case_id"] == first_case
    }

    assert "packet_hash_mismatch" in mutation_reasons["bad_packet_hash"]
    assert "authority_effect_present" in mutation_reasons["authority_effect_present"]
    assert "winner_missing_full_mask_bits" in mutation_reasons["winner_missing_full_mask_bit"]
    assert "winner_not_in_child_frontier" in mutation_reasons["winner_removed_from_children"]
    assert (
        "selected_key_does_not_dominate_full_frontier"
        in mutation_reasons["selected_no_longer_dominates"]
    )
    assert "winner_processed_reserve_in_mismatch" in mutation_reasons["executed_input_mismatch"]
    assert "compressed_key_mismatch_with_witness" in mutation_reasons["economic_key_mismatch"]


def test_ab_strict_zero_min_emitter_witness_stress_non_claims(
    stress_report: dict[str, object],
) -> None:
    non_claims = "\n".join(stress_report["non_claims"])

    assert "not a proof of full compressed-DP induction" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "Nonzero min_amount_out batches are outside" in non_claims
    assert "No settlement authority" in non_claims


def test_ab_strict_zero_min_emitter_witness_stress_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_emitter_witness_stress.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["strict_packet_count"] == 180
    assert report["search"]["mutation_accept_count"] == 0
