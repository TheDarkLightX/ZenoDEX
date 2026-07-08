from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_count_aware_merkle_certificate_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def merkle_report() -> dict[str, object]:
    return build_report()


def test_count_aware_merkle_report(merkle_report: dict[str, object]) -> None:
    search = merkle_report["search"]

    assert merkle_report["ok"] is True
    assert search["naive_countermodel_valid"] is True
    assert search["count_aware_rejects_lying_count"] is True
    assert search["count_aware_rejects_honest_extra"] is True
    assert search["coverage_only_rejected"] is True
    assert search["child_state_count"] == 2
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert merkle_report["deterministic_replay"]["ok"] is True


def test_count_aware_merkle_naive_countermodel(
    merkle_report: dict[str, object],
) -> None:
    search = merkle_report["search"]

    assert search["hidden_extra_state"] == {
        "processed_reserve_in": 170,
        "reserve_out": 9830,
    }
    assert search["naive_baseline"]["ok"] is True
    assert search["naive_honest_extra"]["ok"] is False
    assert search["naive_honest_extra"]["reasons"] == ["generated_state_count_mismatch"]
    assert search["naive_lying_count"]["ok"] is True
    assert search["naive_lying_count"]["generated_state_count"] == 2
    assert search["naive_lying_count"]["valid_membership_count"] == 2


def test_count_aware_merkle_rejects_false_count(
    merkle_report: dict[str, object],
) -> None:
    search = merkle_report["search"]
    count_aware_lying = search["count_aware_lying_count"]
    count_aware_honest_extra = search["count_aware_honest_extra"]

    assert count_aware_lying["ok"] is False
    assert count_aware_lying["generated_state_count"] == 2
    assert count_aware_lying["reasons"] == ["membership_proof_shape_mismatch"]
    assert count_aware_lying["valid_membership_count"] == 0
    assert count_aware_honest_extra["ok"] is False
    assert count_aware_honest_extra["generated_state_count"] == 3
    assert count_aware_honest_extra["reasons"] == ["generated_state_count_mismatch"]


def test_count_aware_merkle_coverage_only_rejected(
    merkle_report: dict[str, object],
) -> None:
    coverage_only = merkle_report["search"]["count_aware_coverage_only"]

    assert coverage_only["ok"] is False
    assert coverage_only["reasons"] == [
        "count_aware_membership_bound_missing",
        "generated_state_root_malformed",
        "membership_rows_digest_mismatch",
        "missing_membership_proof",
    ]


def test_count_aware_merkle_negative_controls(
    merkle_report: dict[str, object],
) -> None:
    controls = merkle_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["mutation_id"] for control in controls} == {
        "packet_hash_mismatch",
        "generated_state_root_stale",
        "generated_state_count_mismatch",
        "membership_proof_hash_mismatch",
        "missing_membership_proof",
        "duplicate_membership_proof",
        "missing_child_state_witness",
        "generated_count_bound_missing",
        "count_aware_membership_bound_missing",
        "authority_effect_present",
    }


def test_count_aware_merkle_hypothesis_card(
    merkle_report: dict[str, object],
) -> None:
    card = merkle_report["hypothesis_card"]
    recommendations = "\n".join(merkle_report["design_recommendation"])
    non_claims = "\n".join(merkle_report["non_claims"])

    assert card["status"] == "supported_bounded"
    assert "generated_state_count" in card["mechanism_change"]
    assert "count-aware Merkle membership verification" in recommendations
    assert "bounded certificate-boundary countermodel" in non_claims
    assert "does not replace a deterministic generated-image producer" in non_claims
    assert "No settlement" in non_claims


def test_count_aware_merkle_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_count_aware_merkle_certificate_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["naive_countermodel_valid"] is True
    assert report["search"]["negative_control_accept_count"] == 0
