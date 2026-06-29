from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools import check_ab_reserve_state_child_frontier_bidirectional_transition_20260629 as bidir
from tools.check_ab_child_frontier_transition_group_compression_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    _packet_compression_summary,
    _verify_compressed_packet,
    build_case_packet,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def compression_report() -> dict[str, object]:
    return build_report()


def test_transition_group_compression_report(compression_report: dict[str, object]) -> None:
    search = compression_report["search"]

    assert compression_report["ok"] is True
    assert compression_report["schema"] == (
        "zenodex.ab_child_frontier_transition_group_compression_report.v1"
    )
    assert search["case_count"] == 4
    assert search["valid_case_count"] == 4
    assert search["first_invalid_case"] is None
    assert search["source_transition_row_count"] == 2_777
    assert search["compressed_row_count"] == 864
    assert search["expected_group_count"] == 864
    assert search["covered_group_count"] == 864
    assert search["missing_group_count"] == 0
    assert search["extra_group_count"] == 0
    assert search["invalid_compressed_row_count"] == 0
    assert search["duplicate_group_count"] == 0
    assert search["row_reduction_count"] == 1_913
    assert search["row_reduction_ratio"] == 0.688873
    assert search["source_transition_json_bytes"] == 2_296_999
    assert search["compressed_json_bytes"] == 841_376
    assert search["byte_reduction_count"] == 1_455_623
    assert search["byte_reduction_ratio"] == 0.633706
    assert search["transition_groups_digest"] == (
        "280c2b23775977485dd12bd7a7b8c3db1c023577881fd1580b1210912261939b"
    )
    assert search["compressed_rows_digest"] == (
        "08588cdb923ad12571dc729b13ad99b2888bebe8e5d6983fabd723b32d2bb2a4"
    )
    assert compression_report["deterministic_replay"]["ok"] is True


def test_transition_group_compression_case_rows(compression_report: dict[str, object]) -> None:
    cases = compression_report["search"]["cases"]

    assert [
        (row["source_transition_row_count"], row["compressed_row_count"], row["row_reduction_count"])
        for row in cases
    ] == [
        (448, 127, 321),
        (1_004, 320, 684),
        (877, 290, 587),
        (448, 127, 321),
    ]
    assert [row["transition_groups_digest"] for row in cases] == [
        "f6c3435447fab89fb78933aea273ef4a4b7baa99f5771aa63495feec9fdc0d2a",
        "89a7dfc7f1003c897e90eb3881627439e55ea2bfcc880174fc3b91f4965a10fe",
        "8f9e88877dc6b6aa7784ebca5977e0d47d830a1cff2468aaaab37cf6e8333af4",
        "bb3a97245295af27b49d8a42367bc51fe896b12ae568a21dd1018fd2d7f1cb22",
    ]


def test_transition_group_compression_negative_controls(
    compression_report: dict[str, object],
) -> None:
    controls = compression_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert compression_report["search"]["negative_control_accept_count"] == 0
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]
    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "missing_generated_image_witness",
        "extra_generated_image_witness",
        "transition_group_count_mismatch",
        "transition_group_digest_mismatch",
        "transition_parent_state_not_in_parent_frontier",
        "membership_proof_hash_mismatch",
        "authority_effect_present",
    }


def test_transition_group_compression_mutation_rejects_missing_group() -> None:
    case = bidir._first_n7_positive_cases()[0]
    full_dp = bidir._full_state_records(case.intents, bidir._case_context(case))
    packet = build_case_packet(case, full_dp=full_dp)
    transition_rows = bidir._build_transition_rows(case, full_dp=full_dp)

    mutated = copy.deepcopy(packet)
    mutated["compressed_transition_groups"] = mutated["compressed_transition_groups"][1:]
    mutated["compression_summary"] = _packet_compression_summary(
        transition_rows=transition_rows,
        compressed_rows=mutated["compressed_transition_groups"],
    )
    mutated = bidir._with_packet_hash(mutated)

    verification = _verify_compressed_packet(case, full_dp=full_dp, packet=mutated)
    assert verification["ok"] is False
    assert "missing_generated_image_witness" in verification["reasons"]


def test_transition_group_compression_mutation_rejects_stale_group_digest() -> None:
    case = bidir._first_n7_positive_cases()[0]
    full_dp = bidir._full_state_records(case.intents, bidir._case_context(case))
    packet = build_case_packet(case, full_dp=full_dp)
    transition_rows = bidir._build_transition_rows(case, full_dp=full_dp)

    mutated = copy.deepcopy(packet)
    mutated["compressed_transition_groups"][0]["transition_group_digest"] = "0" * 64
    mutated["compression_summary"] = _packet_compression_summary(
        transition_rows=transition_rows,
        compressed_rows=mutated["compressed_transition_groups"],
    )
    mutated = bidir._with_packet_hash(mutated)

    verification = _verify_compressed_packet(case, full_dp=full_dp, packet=mutated)
    assert verification["ok"] is False
    assert "transition_group_digest_mismatch" in verification["reasons"]


def test_transition_group_compression_non_claims(compression_report: dict[str, object]) -> None:
    non_claims = "\n".join(compression_report["non_claims"])

    assert "bounded to the committed n=7 zero-min bidirectional transition report" in non_claims
    assert "does not remove host recomputation" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "does not authorize settlement" in non_claims


def test_transition_group_compression_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_transition_group_compression_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["source_transition_row_count"] == 2_777
    assert report["search"]["compressed_row_count"] == 864
    assert report["search"]["negative_control_accept_count"] == 0
