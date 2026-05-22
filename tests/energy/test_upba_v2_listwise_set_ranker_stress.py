from __future__ import annotations

from tools.stress_upba_energy_listwise_set_ranker import stress_listwise_set_ranker


def test_listwise_set_ranker_cross_seed_stress_smoke() -> None:
    report = stress_listwise_set_ranker(
        train_batches=2,
        holdout_batches=2,
        candidates_per_batch=12,
        pairwise_epochs=1,
        listwise_epochs=1,
        pairwise_learning_rate=0.03,
        listwise_learning_rate=0.05,
        l2=0.0,
        seed_pairs=((921, 922), (923, 924)),
    )

    assert report["schema"] == "zenodex/energy/upba_v2_listwise_set_ranker_cross_seed/v1"
    assert report["run_count"] == 2
    assert report["safety"]["invalid_accept_count"] == 0
    assert report["safety"]["permutation_violation_count"] == 0
    assert report["aggregate"]["all_safety_passed"] is True
    assert "listwise_set" in report["aggregate"]["modes"]
