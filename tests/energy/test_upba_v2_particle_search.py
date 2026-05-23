from __future__ import annotations

from tools.benchmark_upba_energy_particle_search import benchmark_particle_search


def test_particle_search_probe_is_advisory_and_reports_modes() -> None:
    report = benchmark_particle_search(
        batches=2,
        candidates_per_batch=12,
        candidate_budget=3,
        particle_count=2,
        iterations=2,
        max_proposals_per_particle=3,
        step_denominator=4,
        seed=911,
        score_mode="obligation",
    )

    assert report["schema"] == "zenodex/energy/upba_v2_particle_search_benchmark/v1"
    assert set(report["modes"]) == {
        "limited",
        "one_shot_neighborhood",
        "particle_resample",
    }
    assert report["safety"]["invalid_accept_count"] == 0
    assert report["safety"]["verifier_authoritative"] is True
    assert report["safety"]["model_authorizes_settlement"] is False
