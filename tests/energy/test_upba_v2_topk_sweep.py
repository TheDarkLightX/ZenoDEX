from __future__ import annotations

from src.energy.upba_v2_energy_model import initial_hand_weight_model
from tools.generate_upba_energy_dataset import generate_dataset_rows
from tools.sweep_upba_energy_topk import sweep_rows


def test_topk_sweep_reports_checked_stop_and_permutation_metrics() -> None:
    rows = list(generate_dataset_rows(batches=3, candidates_per_batch=12, seed=501))
    report = sweep_rows(
        rows,
        model=initial_hand_weight_model(),
        modes=("hand", "learned", "hybrid", "random"),
        top_ks=(1, 5, 10),
        seed=501,
    )

    assert report["schema"] == "zenodex/energy/upba_v2_topk_sweep/v1"
    assert report["top_ks"] == [1, 5, 10]
    for mode in ("hand", "learned", "hybrid", "random"):
        mode_report = report["modes"][mode]
        assert mode_report["batches"] > 0
        assert mode_report["permutation_violation_count"] == 0
        assert mode_report["checked_stop_at_winner_rate"] == 1.0
        for k in ("1", "5", "10"):
            metrics = mode_report["top_k"][k]
            assert 0.0 <= metrics["top_k_recall"] <= 1.0
            assert 0.0 <= metrics["checked_stop_top_k_rate"] <= 1.0
            assert metrics["false_exclusion_rate"] == 1.0 - metrics["top_k_recall"]
