from __future__ import annotations

from random import Random

from src.energy.upba_v2_dominance_cover import (
    DOMINANCE_COVER_SCHEMA,
    build_upba_v2_dominance_cover_certificate,
    verify_upba_v2_dominance_cover_certificate,
    weakly_dominates_verified,
)
from src.energy.upba_v2_ranker import (
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_winner_only_dominance_cover_passes_over_verified_full_list() -> None:
    batch = generate_synthetic_batch(
        rng=Random(900),
        batch_index=0,
        target_candidate_count=20,
    )
    full_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=tuple(item.candidate for item in batch.candidates),
    )
    winner = deterministic_best_verified_candidate(full_results)
    assert winner is not None

    pruned_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=(winner.candidate,),
    )
    report = build_upba_v2_dominance_cover_certificate(
        full_results=full_results,
        pruned_results=pruned_results,
        winner_hash=winner.certificate_hash,
        full_list_complete_for_claim=True,
        scope="unit-test-full-list",
    )

    assert report["schema"] == DOMINANCE_COVER_SCHEMA
    assert report["ok"] is True
    assert report["global_claim_ok"] is True
    assert report["pruned_sound_ok"] is True
    assert report["dominance_cover_ok"] is True
    assert report["uncovered_full_count"] == 0
    assert verify_upba_v2_dominance_cover_certificate(report) is True


def test_weak_pruned_set_fails_when_better_verified_candidate_is_uncovered() -> None:
    batch = generate_synthetic_batch(
        rng=Random(900),
        batch_index=0,
        target_candidate_count=20,
    )
    full_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=tuple(item.candidate for item in batch.candidates),
    )
    accepted = sorted(
        (result for result in full_results if result.ok),
        key=lambda result: (result.volume, result.surplus, result.certificate_hash),
    )
    assert len(accepted) >= 2
    weak = accepted[0]
    strong = accepted[-1]
    assert weakly_dominates_verified(strong, weak)
    assert not weakly_dominates_verified(weak, strong)

    pruned_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=(weak.candidate,),
    )
    report = build_upba_v2_dominance_cover_certificate(
        full_results=full_results,
        pruned_results=pruned_results,
        winner_hash=weak.certificate_hash,
        full_list_complete_for_claim=True,
        scope="unit-test-full-list",
    )

    assert report["ok"] is False
    assert report["dominance_cover_ok"] is False
    assert report["global_claim_ok"] is False
    assert report["uncovered_full_count"] >= 1
    assert strong.certificate_hash in report["uncovered_full_hashes"]
    assert verify_upba_v2_dominance_cover_certificate(report) is False


def test_invalid_pruned_candidate_fails_soundness_even_if_full_has_winner() -> None:
    batch = generate_synthetic_batch(
        rng=Random(901),
        batch_index=1,
        target_candidate_count=20,
    )
    full_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=tuple(item.candidate for item in batch.candidates),
    )
    winner = deterministic_best_verified_candidate(full_results)
    invalid_candidate = next(
        item.candidate
        for item in batch.candidates
        if item.candidate_type.startswith("invalid")
    )
    assert winner is not None

    pruned_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=(winner.candidate, invalid_candidate),
    )
    report = build_upba_v2_dominance_cover_certificate(
        full_results=full_results,
        pruned_results=pruned_results,
        winner_hash=winner.certificate_hash,
        full_list_complete_for_claim=True,
        scope="unit-test-full-list",
    )

    assert report["ok"] is False
    assert report["pruned_sound_ok"] is False
    assert report["pruned_invalid_count"] == 1
    assert verify_upba_v2_dominance_cover_certificate(report) is False
