from __future__ import annotations

from src.energy.upba_v2_listwise_set_ranker import (
    LISTWISE_SET_FEATURE_DIM,
    LISTWISE_SET_FEATURE_NAMES,
    listwise_feature_rows,
    train_listwise_set_ranker,
)
from tools.compare_upba_energy_listwise_set_ranker import compare_listwise_set_ranker
from tools.generate_upba_energy_dataset import generate_dataset_rows


def test_listwise_feature_rows_are_fixed_width_and_label_free() -> None:
    rows = list(generate_dataset_rows(batches=1, candidates_per_batch=8, seed=801))
    featured = listwise_feature_rows(rows)

    assert featured
    assert len(LISTWISE_SET_FEATURE_NAMES) == LISTWISE_SET_FEATURE_DIM
    assert len(featured[0][1]) == LISTWISE_SET_FEATURE_DIM
    assert not any("verifier" in name or "is_winner" in name for name in LISTWISE_SET_FEATURE_NAMES)


def test_train_listwise_set_ranker_returns_energy_model() -> None:
    rows = list(generate_dataset_rows(batches=2, candidates_per_batch=8, seed=802))
    model = train_listwise_set_ranker(
        rows,
        epochs=1,
        learning_rate=0.02,
        seed=802,
    )

    assert model.feature_names == LISTWISE_SET_FEATURE_NAMES
    assert len(model.weights) == LISTWISE_SET_FEATURE_DIM


def test_listwise_set_comparison_reports_safety_and_deltas() -> None:
    report = compare_listwise_set_ranker(
        train_batches=2,
        holdout_batches=2,
        candidates_per_batch=8,
        train_seed=803,
        holdout_seed=804,
        pairwise_epochs=1,
        listwise_epochs=1,
        pairwise_learning_rate=0.01,
        listwise_learning_rate=0.02,
        l2=0.0,
    )

    assert report["schema"] == "zenodex/energy/upba_v2_listwise_set_ranker_comparison/v1"
    assert report["models"]["listwise_set"]["feature_dim"] == LISTWISE_SET_FEATURE_DIM
    assert set(report["modes"]) == {
        "random",
        "hand",
        "aggregate_pairwise",
        "set_aware_pairwise",
        "listwise_set",
    }
    assert report["modes"]["listwise_set"]["permutation_violation_count"] == 0
    assert report["interpretation"]["all_modes_invalid_accept_count"] == 0
    assert set(report["deltas"]) == {
        "listwise_vs_aggregate_pairwise",
        "listwise_vs_set_aware_pairwise",
    }
