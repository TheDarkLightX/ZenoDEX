from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_reserve_state_child_frontier_canonical_merkle_20260629 import (
    EXPECTED_NEGATIVE_CONTROL_COUNT,
    REPORT_JSON,
    TARGET_CASE_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def canonical_merkle_report() -> dict[str, object]:
    return build_report()


def test_ab_reserve_state_child_frontier_canonical_merkle_report(
    canonical_merkle_report: dict[str, object],
) -> None:
    search = canonical_merkle_report["search"]

    assert canonical_merkle_report["ok"] is True
    assert search["case_count"] == TARGET_CASE_COUNT
    assert search["valid_case_count"] == TARGET_CASE_COUNT
    assert search["first_invalid_case"] is None
    assert search["child_mask_count"] == 508
    assert search["frontier_root_count"] == 508
    assert search["child_state_count"] == 864
    assert search["membership_count"] == 864
    assert search["covered_child_state_count"] == 864
    assert search["missing_frontier_row_count"] == 0
    assert search["extra_frontier_row_count"] == 0
    assert search["missing_membership_proof_count"] == 0
    assert search["extra_membership_proof_count"] == 0
    assert search["invalid_membership_proof_count"] == 0
    assert search["root_mismatch_count"] == 0
    assert search["max_leaf_count"] == 5
    assert search["frontier_roots_digest"] == (
        "42f3e7f10918fa3497183812cb316955c3382f4f3b4a4bb5309e47ec5855008b"
    )
    assert search["membership_rows_digest"] == (
        "84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559"
    )
    assert search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert canonical_merkle_report["deterministic_replay"]["ok"] is True


def test_ab_reserve_state_child_frontier_canonical_merkle_linked_report(
    canonical_merkle_report: dict[str, object],
) -> None:
    linked = canonical_merkle_report["search"]["linked_frontier_summary"]

    assert linked["available"] is True
    assert linked["ok"] is True
    assert linked["child_mask_count"] == 508
    assert linked["child_state_count"] == 864
    assert linked["generated_state_count"] == 864
    assert linked["missing_child_state_count"] == 0
    assert linked["extra_generated_state_count"] == 0
    assert linked["frontier_rows_digest"] == (
        "b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4"
    )


def test_ab_reserve_state_child_frontier_canonical_merkle_coverage(
    canonical_merkle_report: dict[str, object],
) -> None:
    coverage = canonical_merkle_report["search"]["coverage"]

    assert coverage["n_counts"] == {"7": 4}
    assert coverage["fee_bps_counts"] == {"1": 1, "100": 2, "9000": 1}
    assert coverage["pattern_counts"] == {
        "high_fee_deep_out/rand_stair": 1,
        "near_domain_in/rand_burst": 1,
        "near_zero_positive/rand_tie": 1,
        "thin_positive_boundary/high_fee9000": 1,
    }
    assert coverage["reason_classes"] == [
        "authority_effect_present",
        "canonical_leaf_index_mismatch",
        "duplicate_leaf_index",
        "frontier_generated_state_root_mismatch",
        "linked_frontier_extra_generated_state",
        "linked_frontier_summary_mismatch",
        "membership_proof_hash_mismatch",
        "membership_proof_shape_mismatch",
        "missing_membership_proof",
        "packet_canonical_merkle_summary_mismatch",
        "packet_hash_mismatch",
    ]


def test_ab_reserve_state_child_frontier_canonical_merkle_case_rows(
    canonical_merkle_report: dict[str, object],
) -> None:
    rows = canonical_merkle_report["search"]["cases"]

    assert [
        (
            row["child_mask_count"],
            row["child_state_count"],
            row["membership_count"],
            row["max_leaf_count"],
        )
        for row in rows
    ] == [
        (127, 127, 127, 1),
        (127, 320, 320, 5),
        (127, 290, 290, 5),
        (127, 127, 127, 1),
    ]
    assert [row["frontier_roots_digest"] for row in rows] == [
        "f47a70da3731aa57fbf3bf01ff9268eadc480bcd910b506a9b89f1ffa6679527",
        "dc12956f646d77d98bf70f633889fd2f560b0ac69a1a09d52a3b2601a63c9cf3",
        "c2674d784996837329606fc1bb1eca22e554969e69ab850efa83382290196610",
        "d279e590987d5ddd6379d3dad9566ae7784df0120f92cbfa43acb4364d0befa4",
    ]
    assert [row["membership_rows_digest"] for row in rows] == [
        "daa9b73e98e261c2cbd00ce3c76764658761b7eeb809deee31c9acef4e534375",
        "52defabafdf1ee63eca95332824785e5a9a072540821ffd635b8dd0204368cb1",
        "94c8a2413ecb702ef9ce6ce24e82e537b1d1eb775fc18dc151bce4e38b2d6f1f",
        "31655a39eaeea232ce3f66473ff1b0694668bc9ba39dbd6eee30c2b388457737",
    ]


def test_ab_reserve_state_child_frontier_canonical_merkle_permutation_countermodel(
    canonical_merkle_report: dict[str, object],
) -> None:
    countermodel = canonical_merkle_report["search"]["permutation_countermodel"]

    assert canonical_merkle_report["search"]["permutation_countermodel_valid"] is True
    assert countermodel["case_id"] == "n7_randomized_000_near_zero_positive_rand_tie_fee1"
    assert countermodel["child_mask_id"] == 3
    assert countermodel["leaf_count"] == 2
    assert countermodel["roots_differ"] is True
    assert countermodel["count_aware_accepts_permuted"] is True
    assert countermodel["canonical_index_reject_reason"] == (
        "canonical_leaf_index_mismatch"
    )
    assert countermodel["canonical_root"] == (
        "9cd0be237e72fe99e3d42aca275cba7000b414b91c6f5a84c0680a4bd066120f"
    )
    assert countermodel["permuted_root"] == (
        "2fd97652cbc53111628bb724095f6faa02f61816e37ea73638f64340ad5378c3"
    )


def test_ab_reserve_state_child_frontier_canonical_merkle_negative_controls(
    canonical_merkle_report: dict[str, object],
) -> None:
    controls = canonical_merkle_report["search"]["negative_controls"]

    assert len(controls) == EXPECTED_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["mutation_id"] for control in controls} == {
        "packet_hash_mismatch",
        "frontier_generated_state_root_mismatch",
        "canonical_leaf_index_mismatch",
        "missing_membership_proof",
        "duplicate_leaf_index",
        "packet_canonical_merkle_summary_mismatch",
        "linked_frontier_extra_generated_state",
        "authority_effect_present",
    }


def test_ab_reserve_state_child_frontier_canonical_merkle_non_claims(
    canonical_merkle_report: dict[str, object],
) -> None:
    non_claims = "\n".join(canonical_merkle_report["non_claims"])

    assert "bounded to the committed n=7 randomized corpus" in non_claims
    assert "zero-min exact-in cases" in non_claims
    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not prove child-frontier generation in Lean" in non_claims
    assert "does not replace a deterministic generated-image producer" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_ab_reserve_state_child_frontier_canonical_merkle_cli_replay() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_ab_reserve_state_child_frontier_canonical_merkle_20260629.py",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["valid_case_count"] == TARGET_CASE_COUNT
    assert report["search"]["negative_control_accept_count"] == 0
