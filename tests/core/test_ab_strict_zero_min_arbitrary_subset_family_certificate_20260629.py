from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_strict_zero_min_arbitrary_subset_family_certificate import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    build_case_packet,
    build_report,
    verify_case_packet,
)
from tools.check_ab_strict_zero_min_emitter_witness_stress import (
    CASE_COUNT,
    _StressCase,
    _iter_cases,
)
from tools.check_ab_zero_min_economic_compression_certificate import _case


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def arbitrary_subset_family_report() -> dict[str, object]:
    return build_report()


def test_ab_strict_zero_min_arbitrary_subset_family_report(
    arbitrary_subset_family_report: dict[str, object],
) -> None:
    search = arbitrary_subset_family_report["search"]

    assert arbitrary_subset_family_report["ok"] is True
    assert search["case_count"] == CASE_COUNT
    assert search["strict_case_count"] == 180
    assert search["valid_case_count"] == 180
    assert search["first_invalid_case"] is None
    assert search["mask_count"] == 4_464
    assert search["record_count"] == 85_284
    assert search["singleton_table_obligation_count"] == 85_284
    assert search["selected_suffix_executable_count"] == 85_284
    assert search["dominance_check_count"] == 212_760
    assert search["full_runtime_completion_count"] == 212_760
    assert search["max_records_per_mask"] == 720
    assert search["max_suffix_per_mask"] == 720
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert arbitrary_subset_family_report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_arbitrary_subset_family_coverage(
    arbitrary_subset_family_report: dict[str, object],
) -> None:
    coverage = arbitrary_subset_family_report["search"]["coverage"]

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
    assert "packet_hash_mismatch" in coverage["reason_classes"]
    assert "authority_effect_present" in coverage["reason_classes"]
    assert "winner_membership_bound_missing" in coverage["reason_classes"]
    assert "packet_nonzero_min_amount_out_out_of_scope" in coverage["reason_classes"]
    assert "selected_final_reserve_dominance_failure" in coverage["reason_classes"]


def test_ab_strict_zero_min_arbitrary_subset_family_first_packet_shape(
    arbitrary_subset_family_report: dict[str, object],
) -> None:
    packet = arbitrary_subset_family_report["search"]["first_packet"]
    verification = verify_case_packet(_iter_cases()[0], packet)

    assert verification["ok"] is True
    assert packet["schema"] == "zenodex.ab_strict_zero_min_arbitrary_subset_family_certificate_packet.v1"
    assert packet["authority_boundary"] == "research_only_no_settlement_or_state_authority"
    assert packet["packet_hash_bound"] is True
    assert packet["no_authority_effect"] is True
    assert packet["winner_membership_bound"] is True
    assert packet["lean_contract"]["structure"] == "StrictSubsetFamilyHostTable"
    assert packet["lean_contract"]["endpoint"] == "strictSubsetFamilyHostTable_validates"
    assert packet["lean_contract"]["family_shape"] == "singleton_per_reachable_mask_suffix"
    assert packet["obligation_summary"]["mask_count"] == 4
    assert packet["obligation_summary"]["singleton_table_obligation_count"] == 5
    assert packet["obligation_summary"]["dominance_check_count"] == 6
    assert packet["first_obligation"]["singleton_family"] == [0]
    assert packet["first_obligation"]["winner"]["processed_reserve_in"] == 512
    assert packet["first_obligation"]["winner"]["reserve_out"] == 33020


def test_ab_strict_zero_min_arbitrary_subset_family_negative_controls_fail_closed(
    arbitrary_subset_family_report: dict[str, object],
) -> None:
    controls = {
        row["mutation_id"]: row
        for row in arbitrary_subset_family_report["search"]["negative_controls"]
    }

    for mutation_id, row in controls.items():
        assert row["accepted"] is False, mutation_id
        assert row["expected_reason"] in row["reasons"]

    assert "packet_hash_mismatch" in controls["packet_hash_mismatch"]["reasons"]
    assert "packet_hash_bound_missing" in controls["packet_hash_bound_missing"]["reasons"]
    assert "authority_effect_present" in controls["authority_effect_present"]["reasons"]
    assert (
        "winner_membership_bound_missing"
        in controls["winner_membership_bound_missing"]["reasons"]
    )
    assert (
        "packet_nonzero_min_amount_out_out_of_scope"
        in controls["packet_nonzero_min_amount_out_out_of_scope"]["reasons"]
    )
    assert "compressed_record_missing" in controls["compressed_record_missing"]["reasons"]
    assert (
        "mask_pruning_full_record_processed_reserve_in_mismatch"
        in controls["mask_pruning_full_record_processed_reserve_in_mismatch"]["reasons"]
    )
    assert (
        "mask_pruning_selected_reserve_out_not_min"
        in controls["mask_pruning_selected_reserve_out_not_min"]["reasons"]
    )
    assert (
        "selected_record_not_in_full_state_records"
        in controls["selected_record_not_in_full_state_records"]["reasons"]
    )
    assert (
        "singleton_table_suffix_not_executable"
        in controls["singleton_table_suffix_not_executable"]["reasons"]
    )
    assert (
        "selected_final_reserve_dominance_failure"
        in controls["selected_final_reserve_dominance_failure"]["reasons"]
    )


def test_ab_strict_zero_min_arbitrary_subset_family_case_summary(
    arbitrary_subset_family_report: dict[str, object],
) -> None:
    first_case = arbitrary_subset_family_report["search"]["cases"][0]

    assert first_case["case_id"] == "stress_000_flat_n2_fee0"
    assert first_case["ok"] is True
    assert first_case["reasons"] == []
    assert first_case["mask_count"] == 4
    assert first_case["record_count"] == 5
    assert first_case["singleton_table_obligation_count"] == 5
    assert first_case["selected_suffix_executable_count"] == 5
    assert first_case["dominance_check_count"] == 6
    assert first_case["full_runtime_completion_count"] == 6
    assert first_case["first_obligation"]["singleton_family"] == [0]
    assert first_case["full_mask_selected"]["processed_reserve_in"] == 528
    assert first_case["full_mask_selected"]["reserve_out"] == 32020


def test_ab_strict_zero_min_arbitrary_subset_family_non_claims(
    arbitrary_subset_family_report: dict[str, object],
) -> None:
    non_claims = "\n".join(arbitrary_subset_family_report["non_claims"])

    assert "not a Lean proof of the concrete Python emitter" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not prove exhaustive coverage" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "Nonzero min_amount_out batches are outside" in non_claims
    assert "not a production ABI" in non_claims
    assert "No settlement" in non_claims


def test_ab_strict_zero_min_arbitrary_subset_family_rejects_nonzero_min_scope() -> None:
    pool, intents, balances = _case(2, 0, min_pattern="half")
    case = _StressCase(
        case_id="nonzero_min_scope_boundary",
        pool=pool,
        intents=intents,
        balances=balances,
        pattern="half_min",
    )

    with pytest.raises(ValueError, match="nonzero_min_amount_out_out_of_scope"):
        build_case_packet(case)


def test_ab_strict_zero_min_arbitrary_subset_family_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_arbitrary_subset_family_certificate.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == 180
    assert report["search"]["singleton_table_obligation_count"] == 85_284
    assert report["search"]["negative_control_accept_count"] == 0
