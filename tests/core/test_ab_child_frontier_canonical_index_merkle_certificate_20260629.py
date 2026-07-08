from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_child_frontier_canonical_index_merkle_certificate_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def canonical_index_report() -> dict[str, object]:
    return build_report()


def test_canonical_index_merkle_report(
    canonical_index_report: dict[str, object],
) -> None:
    search = canonical_index_report["search"]

    assert canonical_index_report["ok"] is True
    assert search["root_malleability_countermodel_valid"] is True
    assert search["count_aware_accepts_permuted_root"] is True
    assert search["canonical_index_rejects_permuted_root"] is True
    assert search["canonical_index_rejects_missing_bound"] is True
    assert search["child_state_count"] == 2
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert canonical_index_report["deterministic_replay"]["ok"] is True


def test_canonical_index_merkle_countermodel(
    canonical_index_report: dict[str, object],
) -> None:
    search = canonical_index_report["search"]

    assert search["canonical_generated_state_root"] == (
        "aa7ec0b30917784becf3806b06fc63fe831e14ed94eb227d958f83a08b3e0e7a"
    )
    assert search["permuted_generated_state_root"] == (
        "adf4287256b1851a33f0dc425cd194bdf429fdc39f5599ab665cf88d7d11a32c"
    )
    assert search["canonical_generated_state_root"] != search["permuted_generated_state_root"]
    assert search["count_aware_canonical"]["ok"] is True
    assert search["count_aware_permuted"]["ok"] is True
    assert search["canonical_index_canonical"]["ok"] is True
    assert search["canonical_index_permuted"]["ok"] is False
    assert search["canonical_index_permuted"]["reasons"] == [
        "canonical_leaf_index_mismatch"
    ]


def test_canonical_index_merkle_missing_bound_rejected(
    canonical_index_report: dict[str, object],
) -> None:
    missing_bound = canonical_index_report["search"]["canonical_index_missing_bound"]

    assert missing_bound["ok"] is False
    assert missing_bound["reasons"] == ["canonical_leaf_index_bound_missing"]


def test_canonical_index_merkle_negative_controls(
    canonical_index_report: dict[str, object],
) -> None:
    controls = canonical_index_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["mutation_id"] for control in controls} == {
        "packet_hash_mismatch",
        "generated_state_root_stale",
        "canonical_leaf_index_mismatch",
        "duplicate_leaf_index",
        "missing_membership_proof",
        "membership_proof_hash_mismatch",
        "missing_child_state_witness",
        "canonical_leaf_index_bound_missing",
        "count_aware_membership_bound_missing",
        "authority_effect_present",
    }


def test_canonical_index_merkle_hypothesis_card(
    canonical_index_report: dict[str, object],
) -> None:
    card = canonical_index_report["hypothesis_card"]
    recommendations = "\n".join(canonical_index_report["design_recommendation"])
    non_claims = "\n".join(canonical_index_report["non_claims"])

    assert card["status"] == "supported_bounded"
    assert "canonical sorted leaf index" in card["mechanism_change"]
    assert "canonical sorted leaf-index binding" in recommendations
    assert "bounded certificate-boundary countermodel" in non_claims
    assert "does not replace a deterministic generated-image producer" in non_claims
    assert "No settlement" in non_claims


def test_canonical_index_merkle_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_child_frontier_canonical_index_merkle_certificate_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["root_malleability_countermodel_valid"] is True
    assert report["search"]["negative_control_accept_count"] == 0
