from __future__ import annotations

from tools.compare_upba_energy_compositional import compare_compositional_rankers


def test_compositional_energy_probe_reports_safety_and_deltas() -> None:
    report = compare_compositional_rankers(
        train_batches=2,
        holdout_batches=2,
        candidates_per_batch=8,
        train_seed=901,
        holdout_seed=902,
        epochs=1,
        learning_rate=0.01,
        margin=1.0,
        winner_pair_weight=2.0,
        objective_gap_weight=4.0,
        same_volume_surplus_gap_weight=1.0,
        max_pair_weight=8.0,
    )

    assert report["schema"] == "zenodex/energy/upba_v2_compositional_comparison/v1"
    assert set(report["modes"]) == {
        "random",
        "hand",
        "aggregate_pairwise",
        "set_aware_pairwise",
        "obligation_formula_sum",
        "obligation_formula_calibrated",
        "compositional_sum",
        "compositional_hybrid",
        "local_target_sum",
        "local_target_calibrated",
        "local_target_hybrid",
    }
    assert set(report["deltas"]) == {
        "compositional_vs_aggregate_pairwise",
        "compositional_vs_set_aware_pairwise",
        "compositional_hybrid_vs_compositional_sum",
        "obligation_formula_vs_aggregate_pairwise",
        "obligation_formula_calibrated_vs_aggregate_pairwise",
        "local_target_sum_vs_aggregate_pairwise",
        "local_target_calibrated_vs_aggregate_pairwise",
        "local_target_hybrid_vs_aggregate_pairwise",
    }
    assert report["models"]["compositional_sum"]["group_count"] == 5
    assert report["models"]["compositional_sum"]["active_parameter_count"] > 5
    assert report["models"]["local_target_sum"]["group_count"] == 5
    assert report["models"]["local_target_sum"]["calibrator_parameter_count"] == 5
    assert report["models"]["obligation_formula_calibrated"]["component_count"] == 5
    assert report["interpretation"]["all_modes_invalid_accept_count"] == 0
