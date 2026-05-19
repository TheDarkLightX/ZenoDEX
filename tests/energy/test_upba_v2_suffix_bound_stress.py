from __future__ import annotations

from pathlib import Path

from tools.stress_upba_v2_suffix_bound import stress_suffix_bound


def test_suffix_bound_cross_seed_stress_smoke() -> None:
    report = stress_suffix_bound(
        batches=2,
        seeds=(931, 932),
        candidate_counts=(12, 16),
        model_path=Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json"),
    )

    assert report["schema"] == "zenodex/energy/upba_v2_suffix_bound_cross_seed/v1"
    assert report["ok"] is True
    assert report["safety"]["invalid_accept_count_total"] == 0
    assert report["summary"]["learned"]["objective_equiv_accept_rate_min"] == 1.0
    assert report["summary"]["hybrid"]["objective_equiv_accept_rate_min"] == 1.0
