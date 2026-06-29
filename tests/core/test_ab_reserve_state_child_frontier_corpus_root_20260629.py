from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_corpus_root_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def corpus_root_report() -> dict[str, object]:
    return build_report()


def test_ab_reserve_state_child_frontier_corpus_root_report(
    corpus_root_report: dict[str, object],
) -> None:
    search = corpus_root_report["search"]

    assert corpus_root_report["ok"] is True
    assert search["verification"]["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["expected_case_count"] == TARGET_CASE_COUNT
    assert search["row_receipt_count"] == 864
    assert search["expected_row_receipt_count"] == 864
    assert search["covered_row_receipt_count"] == 864
    assert search["missing_row_receipt_count"] == 0
    assert search["extra_row_receipt_count"] == 0
    assert search["invalid_row_receipt_count"] == 0
    assert search["duplicate_row_receipt_count"] == 0
    assert search["case_root_mismatch_count"] == 0
    assert search["corpus_root_mismatch_count"] == 0
    assert search["row_membership_mismatch_count"] == 0
    assert search["corpus_root_matches"] is True
    assert search["corpus_root"] == (
        "8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0"
    )
    assert search["case_summaries_digest"] == (
        "afd7706fd7ea10cee0df44d7578dabf44fc82a26d238f814d717c5fee3b5bc28"
    )
    assert search["row_receipts_digest"] == (
        "d52f8c24411e841ae777999d6bfd3ec3fef5bb0a26cd98887f4e0a5902c0f092"
    )
    assert search["max_case_row_count"] == 320
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert corpus_root_report["deterministic_replay"]["ok"] is True


def test_ab_reserve_state_child_frontier_corpus_root_linked_report(
    corpus_root_report: dict[str, object],
) -> None:
    linked = corpus_root_report["search"]["linked_cross_binding_summary"]

    assert linked["available"] is True
    assert linked["ok"] is True
    assert linked["case_count"] == 4
    assert linked["valid_case_count"] == 4
    assert linked["child_mask_count"] == 508
    assert linked["bound_row_count"] == 864
    assert linked["witness_count"] == 864
    assert linked["membership_count"] == 864
    assert linked["negative_control_accept_count"] == 0
    assert linked["bound_rows_digest"] == (
        "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551"
    )


def test_ab_reserve_state_child_frontier_corpus_root_case_summaries(
    corpus_root_report: dict[str, object],
) -> None:
    summaries = corpus_root_report["search"]["case_summaries"]

    assert [
        (
            summary["case_id"],
            summary["case_index"],
            summary["row_count"],
            summary["row_root"],
            summary["bound_rows_digest"],
        )
        for summary in summaries
    ] == [
        (
            "n7_randomized_000_near_zero_positive_rand_tie_fee1",
            0,
            320,
            "0e1a448b555283325f371ec0ad418bb40b7caca6307bc86040ac5e35e8a0ad1f",
            "e84f09be2040986a317dc98c31f967b97703c36ca2d356e286b6f9f5de4871ed",
        ),
        (
            "n7_randomized_001_high_fee_deep_out_rand_stair_fee100",
            1,
            290,
            "aa5d2b22032a56aef109a471d7e504a51806133804f6e0fd9f5a1206aa53d295",
            "896337c7e1edb9c4416b04d1755bb1b01ee1fa2d4eb5e3a86584052a74e150ba",
        ),
        (
            "n7_randomized_002_near_domain_in_rand_burst_fee100",
            2,
            127,
            "f62062f1d7a38eaa896ec93b610c4c1aa4554896f11501d31045b9298bd64fad",
            "f30f66bf6fddcc14268e9e1ada910dd285f61e0663045ccf6738fc7a230f5080",
        ),
        (
            "n7_randomized_boundary_000_thin_fee9000_rout1100",
            3,
            127,
            "6ab43ed0917e309ad273b99321df188a37854dd1a56c01d958c12f74f04dc829",
            "4720d06a30a7707eec19b08a83ff2c5802b3d8d8d12183017d479a0ec2e9f6b2",
        ),
    ]


def test_ab_reserve_state_child_frontier_corpus_root_coverage(
    corpus_root_report: dict[str, object],
) -> None:
    coverage = corpus_root_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["case_row_count_histogram"] == {"127": 2, "290": 1, "320": 1}
    assert coverage["reason_classes"] == [
        "authority_effect_present",
        "case_index_out_of_range",
        "case_membership_hash_mismatch",
        "case_row_root_mismatch",
        "corpus_summary_mismatch",
        "duplicate_row_receipt",
        "extra_row_receipt",
        "linked_cross_binding_bound_row_count_mismatch",
        "linked_cross_binding_summary_mismatch",
        "missing_row_receipt",
        "packet_hash_mismatch",
        "row_hash_mismatch",
        "row_membership_hash_mismatch",
        "row_receipt_index_out_of_range",
    ]


def test_ab_reserve_state_child_frontier_corpus_root_negative_controls(
    corpus_root_report: dict[str, object],
) -> None:
    controls = corpus_root_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["mutation_id"] for control in controls} == {
        "packet_hash_mismatch",
        "row_hash_mismatch",
        "row_membership_hash_mismatch",
        "case_row_root_mismatch",
        "case_membership_hash_mismatch",
        "missing_row_receipt",
        "duplicate_row_receipt",
        "case_index_out_of_range",
        "linked_cross_binding_bound_row_count_mismatch",
        "authority_effect_present",
    }


def test_ab_reserve_state_child_frontier_corpus_root_hypothesis_card(
    corpus_root_report: dict[str, object],
) -> None:
    card = corpus_root_report["hypothesis_card"]
    non_claims = "\n".join(corpus_root_report["non_claims"])

    assert card["status"] == "supported_bounded"
    assert "one corpus root" in card["mechanism_change"]
    assert "Lean or Tau-level statement" in card["formal_obligations"]
    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "zero-min exact-in cases" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "No settlement" in non_claims


def test_ab_reserve_state_child_frontier_corpus_root_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_corpus_root_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["corpus_root"] == (
        "8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0"
    )
    assert report["search"]["negative_control_accept_count"] == 0
