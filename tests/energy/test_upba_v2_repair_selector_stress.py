from __future__ import annotations

from tools.stress_upba_repair_selector import stress_repair_selector


def test_repair_selector_cross_seed_stress_smoke() -> None:
    report = stress_repair_selector(
        train_batches=2,
        holdout_batches=2,
        candidates_per_batch=12,
        candidate_budget=4,
        proposal_budget=2,
        repair_seed_count=2,
        max_proposals_per_seed=3,
        step_denominator=4,
        epochs=1,
        learning_rate=0.05,
        margin=1.0,
        seed_pairs=((821, 822), (823, 824)),
    )

    assert report["schema"] == "zenodex/energy/upba_v2_repair_selector_cross_seed/v1"
    assert report["run_count"] == 2
    assert report["safety"]["invalid_accept_count"] == 0
    assert report["safety"]["original_subset_violation_count"] == 0
    assert report["aggregate"]["all_safety_passed"] is True
    assert "learned_selected" in report["aggregate"]["modes"]
