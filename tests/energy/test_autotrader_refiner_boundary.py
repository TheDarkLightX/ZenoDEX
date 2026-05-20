from __future__ import annotations

from pathlib import Path

from tools.check_autotrader_refiner_boundary import check_autotrader_refiner_boundary


ROOT = Path(__file__).resolve().parents[2]


def test_autotrader_refiner_is_policy_checked_before_selection() -> None:
    report = check_autotrader_refiner_boundary(
        seed=20260529,
        contexts=24,
        candidates_per_context=12,
        steps=12,
        learning_rate=0.04,
        noise_scale=0.0,
    )

    assert report["schema"] == "zenodex/energy/autotrader_refiner_boundary_receipt/v1"
    assert report["ok"] is True
    assert report["decision"] == "research_only_policy_checked_refinement"
    assert report["selected_invalid_count"] == 0
    assert report["policy_guards_authoritative"] is True
    assert report["model_authorizes_trade"] is False
    assert report["refined_proposal_authorizes_trade"] is False
    assert report["selected_vs_initial_objective_delta_mean"] > 0.0
    assert report["selected_vs_initial_energy_delta_mean"] < 0.0


def test_autotrader_refiner_receipt_records_synthetic_boundary() -> None:
    report = check_autotrader_refiner_boundary(
        seed=20260530,
        contexts=8,
        candidates_per_context=8,
        steps=4,
        learning_rate=0.02,
        noise_scale=0.0,
    )
    negative = " ".join(report["negative_knowledge"]).lower()

    assert "lower policy energy does not authorize" in negative
    assert "deterministic policy labels decide selection" in negative
    assert "does not replace real shadow replay" in negative
