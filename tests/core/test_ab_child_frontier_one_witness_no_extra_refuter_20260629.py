from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_one_witness_no_extra_refuter_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def refuter_report() -> dict[str, object]:
    return build_report()


def test_one_witness_no_extra_refuter_report(refuter_report: dict[str, object]) -> None:
    search = refuter_report["search"]

    assert refuter_report["ok"] is True
    assert search["countermodel_valid"] is True
    assert search["same_packet_hash_for_both_worlds"] is True
    assert search["child_state_count"] == 2
    assert search["witness_count"] == 2
    assert search["baseline_generated_state_count"] == 2
    assert search["extra_generated_state_count"] == 3
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert refuter_report["deterministic_replay"]["ok"] is True


def test_one_witness_no_extra_refuter_indistinguishability(
    refuter_report: dict[str, object],
) -> None:
    search = refuter_report["search"]

    assert search["coverage_only_baseline"]["ok"] is True
    assert search["coverage_only_extra_world"]["ok"] is True
    assert search["coverage_only_baseline"] == search["coverage_only_extra_world"]
    assert search["full_baseline"]["ok"] is True
    assert search["full_extra_world"]["ok"] is False
    assert search["full_extra_world"]["extra_generated_state_count"] == 1
    assert search["full_extra_world"]["reasons"] == [
        "generated_frontier_extra_child_state"
    ]


def test_one_witness_no_extra_refuter_hidden_state(
    refuter_report: dict[str, object],
) -> None:
    search = refuter_report["search"]

    assert search["hidden_extra_state"] == {
        "processed_reserve_in": 170,
        "reserve_out": 9830,
    }
    assert search["full_extra_world"]["extra_generated_states"] == [
        {"processed_reserve_in": 170, "reserve_out": 9830}
    ]


def test_one_witness_no_extra_refuter_negative_controls(
    refuter_report: dict[str, object],
) -> None:
    controls = refuter_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "missing_child_state_witness",
        "duplicate_witness_row",
        "witness_child_not_in_frontier",
        "forbidden_standalone_no_extra_claim",
        "authority_effect_present",
    }


def test_one_witness_no_extra_refuter_hypothesis_card(
    refuter_report: dict[str, object],
) -> None:
    card = refuter_report["hypothesis_card"]
    recommendations = "\n".join(refuter_report["design_recommendation"])
    non_claims = "\n".join(refuter_report["non_claims"])

    assert card["status"] == "falsified"
    assert "One predecessor witness per child state" in card["null_hypothesis"]
    assert "coverage certificates" in card["mechanism_change"]
    assert "generated-image digest" in recommendations
    assert "does not invalidate n=7 or n=8 witness-coverage evidence" in non_claims
    assert "No settlement" in non_claims


def test_one_witness_no_extra_refuter_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_one_witness_no_extra_refuter_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["countermodel_valid"] is True
    assert report["search"]["negative_control_accept_count"] == 0
