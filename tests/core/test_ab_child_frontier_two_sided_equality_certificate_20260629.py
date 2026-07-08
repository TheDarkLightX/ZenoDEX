from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_two_sided_equality_certificate_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def equality_report() -> dict[str, object]:
    return build_report()


def test_two_sided_equality_certificate_report(
    equality_report: dict[str, object],
) -> None:
    search = equality_report["search"]

    assert equality_report["ok"] is True
    assert search["baseline_ok"] is True
    assert search["extra_world_rejected"] is True
    assert search["stale_digest_rejected"] is True
    assert search["coverage_only_rejected"] is True
    assert search["equality_certificate_valid"] is True
    assert search["child_state_count"] == 2
    assert search["generated_state_count"] == 2
    assert search["witness_count"] == 2
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert equality_report["deterministic_replay"]["ok"] is True


def test_two_sided_equality_certificate_hidden_extra_rejected(
    equality_report: dict[str, object],
) -> None:
    search = equality_report["search"]
    extra_world = search["extra_world"]

    assert search["hidden_extra_state"] == {
        "processed_reserve_in": 170,
        "reserve_out": 9830,
    }
    assert extra_world["ok"] is False
    assert extra_world["reasons"] == ["generated_frontier_extra_child_state"]
    assert extra_world["extra_generated_state_count"] == 1
    assert extra_world["extra_generated_states"] == [
        {"processed_reserve_in": 170, "reserve_out": 9830}
    ]


def test_two_sided_equality_certificate_stale_and_coverage_only_rejected(
    equality_report: dict[str, object],
) -> None:
    search = equality_report["search"]
    stale_digest = search["stale_digest"]
    coverage_only = search["coverage_only"]

    assert stale_digest["ok"] is False
    assert stale_digest["reasons"] == ["generated_state_digest_mismatch"]
    assert coverage_only["ok"] is False
    assert coverage_only["reasons"] == [
        "frontier_equality_bound_missing",
        "generated_state_binding_missing",
        "generated_state_digest_mismatch",
        "generated_frontier_missing_child_state",
    ]


def test_two_sided_equality_certificate_negative_controls(
    equality_report: dict[str, object],
) -> None:
    controls = equality_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "packet_hash_mismatch",
        "child_state_digest_mismatch",
        "generated_state_digest_mismatch",
        "generated_frontier_missing_child_state",
        "generated_frontier_extra_child_state",
        "missing_child_state_witness",
        "frontier_equality_bound_missing",
        "authority_effect_present",
    }


def test_two_sided_equality_certificate_hypothesis_card(
    equality_report: dict[str, object],
) -> None:
    card = equality_report["hypothesis_card"]
    recommendations = "\n".join(equality_report["design_recommendation"])
    non_claims = "\n".join(equality_report["non_claims"])

    assert card["status"] == "supported_bounded"
    assert "generated-image binding" in card["mechanism_change"]
    assert "coverage_witnesses + generated_state_digest" in recommendations
    assert "bounded certificate-boundary design" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "No settlement" in non_claims


def test_two_sided_equality_certificate_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_two_sided_equality_certificate_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["equality_certificate_valid"] is True
    assert report["search"]["negative_control_accept_count"] == 0
