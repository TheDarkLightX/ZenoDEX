from __future__ import annotations

from src.energy.autotrader_energy import (
    AUTOTRADER_FEATURE_NAMES,
    evaluate_autotrader_rows,
    generate_rows,
    train_autotrader_linear_ranker,
)


def test_autotrader_synthetic_rows_are_reproducible() -> None:
    left = generate_rows(seed=20260518, contexts=8, candidates_per_context=6, profile="hard")
    right = generate_rows(seed=20260518, contexts=8, candidates_per_context=6, profile="hard")

    assert left == right
    assert tuple(left[0]["feature_names"]) == AUTOTRADER_FEATURE_NAMES
    assert all(sum(1 for row in left if row["batch_id"] == batch_id and row["label"]["is_winner"]) == 1 for batch_id in {str(row["batch_id"]) for row in left})


def test_autotrader_learned_energy_reduces_guard_calls_without_accepting_invalid() -> None:
    train_rows = generate_rows(seed=20260522, contexts=300, candidates_per_context=16, profile="hard")
    holdout_rows = generate_rows(seed=20260523, contexts=120, candidates_per_context=16, profile="hard")
    model = train_autotrader_linear_ranker(
        train_rows,
        epochs=4,
        learning_rate=0.001,
        margin=1.0,
        seed=20260522,
        init="hand",
    )

    hand = evaluate_autotrader_rows(holdout_rows, mode="hand", seed=20260523)
    learned = evaluate_autotrader_rows(holdout_rows, mode="learned", model=model, seed=20260523)

    assert learned["invalid_accept_count"] == 0
    assert learned["policy_guards_authoritative"] is True
    assert learned["scorer_authorizes_trade"] is False
    assert learned["mean_guard_calls"] < hand["mean_guard_calls"]
    assert learned["top_5_recall"] >= 0.95


def test_autotrader_model_output_is_advisory_under_bad_ordering() -> None:
    rows = generate_rows(seed=20260524, contexts=50, candidates_per_context=12, profile="hard")
    random_report = evaluate_autotrader_rows(rows, mode="random", seed=7)

    assert random_report["invalid_top_1_rate"] > 0.0
    assert random_report["invalid_accept_count"] == 0
    assert random_report["policy_guards_authoritative"] is True
