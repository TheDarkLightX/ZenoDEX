from __future__ import annotations

from tools.compare_upba_energy_set_aware import compare_set_aware_rankers


def test_set_aware_comparison_reports_all_modes_without_invalid_accepts() -> None:
    report = compare_set_aware_rankers(
        train_batches=2,
        holdout_batches=2,
        candidates_per_batch=8,
        train_seed=701,
        holdout_seed=702,
        epochs=1,
        learning_rate=0.01,
        margin=1.0,
        winner_pair_weight=2.0,
        objective_gap_weight=4.0,
        same_volume_surplus_gap_weight=1.0,
        max_pair_weight=8.0,
    )

    assert report["schema"] == "zenodex/energy/upba_v2_set_aware_comparison/v1"
    assert report["models"]["aggregate"]["feature_dim"] == 96
    assert report["models"]["set_aware"]["feature_dim"] == 147
    assert set(report["modes"]) == {
        "random",
        "hand",
        "aggregate_learned",
        "aggregate_hybrid",
        "set_aware_learned",
        "set_aware_hybrid",
    }
    assert report["deltas"].keys() == {
        "set_aware_vs_aggregate_learned",
        "set_aware_hybrid_vs_aggregate_hybrid",
    }
    for stats in report["modes"].values():
        assert stats["invalid_accept_count"] == 0
