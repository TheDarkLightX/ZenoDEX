from __future__ import annotations

from random import Random

from src.energy.upba_v2_energy_model import initial_hand_weight_model
from src.energy.upba_v2_ranker import advisory_candidate_hash, search_best_with_deterministic_fallback
from tools.benchmark_upba_energy_search import benchmark_modes
from tools.generate_upba_energy_dataset import generate_dataset_rows, generate_synthetic_batch


def test_learned_mode_falls_back_when_model_missing() -> None:
    report = benchmark_modes(
        batches=2,
        candidates_per_batch=12,
        seed=401,
        model=None,
        top_k=5,
    )

    assert report["learned_model_present"] is False
    assert report["invalid_accept_count"] == 0
    assert report["modes"]["learned"]["fallback_recovered_count"] == 2  # type: ignore[index]
    assert report["modes"]["hybrid"]["fallback_recovered_count"] == 2  # type: ignore[index]
    assert report["modes"]["learned"]["permutation_violation_count"] == 0  # type: ignore[index]
    assert report["modes"]["hybrid"]["permutation_violation_count"] == 0  # type: ignore[index]
    assert report["modes"]["learned"]["checked_stop_at_winner_count"] == 2  # type: ignore[index]
    assert report["modes"]["hybrid"]["checked_stop_at_winner_count"] == 2  # type: ignore[index]


def test_hybrid_mode_is_order_only_and_reports_no_invalid_accepts() -> None:
    report = benchmark_modes(
        batches=2,
        candidates_per_batch=12,
        seed=404,
        model=initial_hand_weight_model(),
        top_k=5,
    )

    assert report["learned_model_present"] is True
    assert report["modes"]["hybrid"]["invalid_accept_count"] == 0  # type: ignore[index]
    assert report["modes"]["hybrid"]["fallback_recovered_count"] == 2  # type: ignore[index]
    assert report["modes"]["hybrid"]["permutation_violation_count"] == 0  # type: ignore[index]
    assert report["modes"]["hybrid"]["checked_stop_at_winner_count"] == 2  # type: ignore[index]


def test_candidate_order_only_changes_order_not_best_result() -> None:
    batch = generate_synthetic_batch(rng=Random(402), batch_index=0, target_candidate_count=12)
    candidates = [item.candidate for item in batch.candidates]
    best_a = search_best_with_deterministic_fallback(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        scorer=lambda candidate: float(int(advisory_candidate_hash(candidate)[2:10], 16)),
    ).best
    best_b = search_best_with_deterministic_fallback(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        scorer=lambda candidate: -float(int(advisory_candidate_hash(candidate)[2:10], 16)),
    ).best

    assert best_a is not None
    assert best_b is not None
    assert best_a.certificate_hash == best_b.certificate_hash


def test_training_rows_are_marked_synthetic_only() -> None:
    rows = list(generate_dataset_rows(batches=2, candidates_per_batch=8, seed=403))

    assert rows
    assert {row["source"] for row in rows} == {"synthetic"}
