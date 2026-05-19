from __future__ import annotations

import pytest

from tools.run_zenoenergy_wes_dominance_search import (
    WES_SRC,
    build_wes_dominance_candidates,
    check_wes_dominance_candidate,
    run_zenoenergy_wes_dominance_search,
)


pytestmark = pytest.mark.skipif(
    not WES_SRC.exists(),
    reason="external/WitnessEnergySearch is required for the WES bridge",
)


def test_wes_dominance_candidates_are_wes_rows() -> None:
    candidates = build_wes_dominance_candidates(
        batches=2,
        candidates_per_batch=12,
        seed=20260539,
    )

    assert len(candidates) == 6
    assert {candidate.schema for candidate in candidates} == {"witness_candidate.v1"}
    assert {candidate.expected_checker for candidate in candidates} == {
        "zenoenergy_upba_v2_dominance_cover_checker"
    }
    assert {
        candidate.payload["mode"] for candidate in candidates if isinstance(candidate.payload, dict)
    } == {"winner_only", "hand_top1", "weak_pruned"}


def test_wes_dominance_checker_labels_positive_and_negative_controls() -> None:
    candidates = build_wes_dominance_candidates(
        batches=1,
        candidates_per_batch=24,
        seed=20260539,
    )
    by_mode = {
        candidate.payload["mode"]: candidate
        for candidate in candidates
        if isinstance(candidate.payload, dict)
    }

    winner_check = check_wes_dominance_candidate(by_mode["winner_only"])
    weak_check = check_wes_dominance_candidate(by_mode["weak_pruned"])

    assert winner_check.result.value == "near_miss"
    assert winner_check.telemetry["certificate_ok"] is True
    assert weak_check.result.value in {"invariant_violation", "checked_safe"}
    if weak_check.result.value == "invariant_violation":
        assert weak_check.telemetry["uncovered_full_count"] > 0


def test_wes_dominance_policy_comparison_smoke(tmp_path) -> None:
    report = run_zenoenergy_wes_dominance_search(
        batches=3,
        candidates_per_batch=12,
        budget=6,
        top_k=4,
        seed=20260539,
        out_dir=tmp_path / "wes_dominance",
        candidates_jsonl=tmp_path / "candidates.jsonl",
    )

    assert report["schema"] == "zenodex/energy/zenoenergy_wes_dominance_search/v1"
    assert report["ok"] is True
    assert report["safety"]["verifier_authoritative"] is True
    assert report["safety"]["scorer_authorizes_settlement"] is False
    assert report["summary"]["model_online_useful_at_k"] > 0
