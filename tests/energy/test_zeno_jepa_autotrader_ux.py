from __future__ import annotations

from src.energy import (
    apply_autotrader_control,
    autotrader_control_effect,
    autotrader_feature_map,
    build_autotrader_advisory_card,
    build_autotrader_batch_ux,
    default_autotrader_jepa_model,
    evaluate_autotrader_future_aware_rows,
    generate_rows,
    model_fingerprint,
    project_autotrader_future_stress,
    score_autotrader_future_tension,
    train_autotrader_linear_ranker,
)


def test_default_jepa_scores_fragile_action_above_balanced_action() -> None:
    balanced = autotrader_feature_map(
        {
            "expected_edge_norm": 0.85,
            "signal_strength_norm": 0.8,
            "liquidity_score_norm": 0.9,
            "hedge_coverage_norm": 0.8,
            "execution_urgency_norm": 0.35,
            "drawdown_risk_norm": 0.15,
            "slippage_bps_norm": 0.1,
            "fee_bps_norm": 0.2,
            "budget_used_norm": 0.2,
            "price_deviation_norm": 0.1,
            "position_pressure_norm": 0.1,
            "nonce_age_norm": 0.1,
        }
    )
    fragile = dict(balanced)
    fragile.update(
        {
            "liquidity_score_norm": 0.18,
            "drawdown_risk_norm": 0.82,
            "slippage_bps_norm": 0.78,
            "budget_used_norm": 0.88,
            "price_deviation_norm": 0.72,
            "position_pressure_norm": 0.81,
        }
    )

    model = default_autotrader_jepa_model()
    round_tripped = type(model).from_dict(model.to_dict())

    assert score_autotrader_future_tension(fragile, model=model) > score_autotrader_future_tension(
        balanced,
        model=model,
    )
    assert model_fingerprint(model) == model_fingerprint(round_tripped)
    assert model.to_dict()["model_authorizes_trade"] is False


def test_learned_future_aware_autotrader_ranking_keeps_guard_authority() -> None:
    train_rows = generate_rows(seed=20260522, contexts=500, candidates_per_context=16, profile="hard")
    rows = generate_rows(seed=20260531, contexts=64, candidates_per_context=12, profile="hard")
    ranker = train_autotrader_linear_ranker(
        train_rows,
        epochs=6,
        learning_rate=0.001,
        margin=1.0,
        seed=20260522,
        init="hand",
    )
    report = evaluate_autotrader_future_aware_rows(rows, base_model=ranker, future_weight=0.1)

    assert report["schema"] == "zenodex/energy/autotrader_future_aware_evaluation/v1"
    assert report["mode"] == "learned_future_aware"
    assert report["batches"] == 64
    assert report["invalid_accept_count"] == 0
    assert report["policy_guards_authoritative"] is True
    assert report["model_authorizes_trade"] is False
    assert report["future_tension_authorizes_trade"] is False
    assert report["top_5_recall"] >= 0.99
    assert report["mean_guard_calls"] <= 1.15


def test_autotrader_ux_card_explains_blocked_and_future_risk_without_authority() -> None:
    blocked = autotrader_feature_map(
        {
            "stale_signal_flag": 1.0,
            "route_violation_flag": 1.0,
            "expected_edge_norm": 0.75,
            "liquidity_score_norm": 0.2,
            "slippage_bps_norm": 0.85,
            "budget_used_norm": 0.8,
            "price_deviation_norm": 0.7,
        }
    )
    card = build_autotrader_advisory_card(blocked, candidate_id="blocked-case")

    assert card["schema"] == "zenodex/energy/autotrader_advisory_card/v1"
    assert card["status"] == "blocked_by_policy_guard"
    assert "stale signal or quote" in card["blocked_reasons"]
    assert "route or quote binding" in card["blocked_reasons"]
    assert card["authority"]["policy_guard_required"] is True
    assert card["authority"]["model_authorizes_trade"] is False
    assert card["authority"]["ux_card_authorizes_trade"] is False
    assert any("Refresh oracle" in item for item in card["suggested_controls"])


def test_autotrader_future_stress_tracks_later_policy_failures() -> None:
    balanced = autotrader_feature_map(
        {
            "expected_edge_norm": 0.85,
            "signal_strength_norm": 0.8,
            "liquidity_score_norm": 0.9,
            "hedge_coverage_norm": 0.8,
            "execution_urgency_norm": 0.35,
            "drawdown_risk_norm": 0.15,
            "slippage_bps_norm": 0.1,
            "fee_bps_norm": 0.2,
            "budget_used_norm": 0.2,
            "price_deviation_norm": 0.1,
            "position_pressure_norm": 0.1,
            "nonce_age_norm": 0.1,
        }
    )
    fragile = dict(balanced)
    fragile.update(
        {
            "liquidity_score_norm": 0.18,
            "drawdown_risk_norm": 0.82,
            "execution_urgency_norm": 0.88,
            "slippage_bps_norm": 0.78,
            "budget_used_norm": 0.88,
            "price_deviation_norm": 0.72,
            "position_pressure_norm": 0.81,
        }
    )

    balanced_stress = project_autotrader_future_stress(balanced)
    fragile_stress = project_autotrader_future_stress(fragile)

    assert balanced_stress["any_later_policy_failure"] is False
    assert fragile_stress["any_later_policy_failure"] is True
    assert fragile_stress["later_failure_count"] > balanced_stress["later_failure_count"]
    assert fragile_stress["slippage_stress"] > balanced_stress["slippage_stress"]
    assert fragile_stress["budget_stress"] > balanced_stress["budget_stress"]
    assert fragile_stress["drawdown_stress"] > balanced_stress["drawdown_stress"]
    assert fragile_stress["deterministic_projection_authorizes_trade"] is False


def test_safer_counterfactual_controls_lower_future_tension_without_authority() -> None:
    model = default_autotrader_jepa_model()
    fragile = autotrader_feature_map(
        {
            "expected_edge_norm": 0.86,
            "signal_strength_norm": 0.82,
            "liquidity_score_norm": 0.18,
            "hedge_coverage_norm": 0.8,
            "execution_urgency_norm": 0.88,
            "drawdown_risk_norm": 0.82,
            "slippage_bps_norm": 0.78,
            "fee_bps_norm": 0.2,
            "budget_used_norm": 0.88,
            "price_deviation_norm": 0.72,
            "position_pressure_norm": 0.81,
            "nonce_age_norm": 0.1,
        }
    )
    before = score_autotrader_future_tension(fragile, model=model)

    for control_id in ("improve_route", "reduce_notional", "slow_execution", "wait_budget_recovery"):
        adjusted = apply_autotrader_control(fragile, control_id)
        effect = autotrader_control_effect(fragile, control_id, model=model)

        assert score_autotrader_future_tension(adjusted, model=model) < before
        assert effect["future_tension_delta"] < 0.0
        assert effect["control_authorizes_trade"] is False


def test_autotrader_ux_suggested_controls_report_future_tension_reductions() -> None:
    fragile = autotrader_feature_map(
        {
            "expected_edge_norm": 0.86,
            "signal_strength_norm": 0.82,
            "liquidity_score_norm": 0.18,
            "hedge_coverage_norm": 0.8,
            "execution_urgency_norm": 0.88,
            "drawdown_risk_norm": 0.82,
            "slippage_bps_norm": 0.78,
            "fee_bps_norm": 0.2,
            "budget_used_norm": 0.88,
            "price_deviation_norm": 0.72,
            "position_pressure_norm": 0.81,
            "nonce_age_norm": 0.1,
        }
    )
    card = build_autotrader_advisory_card(fragile, candidate_id="fragile-controls")

    assert card["status"] == "needs_risk_review"
    assert card["authority"]["model_authorizes_trade"] is False
    assert card["authority"]["ux_card_authorizes_trade"] is False
    assert card["control_effects"]
    assert all(effect["control_authorizes_trade"] is False for effect in card["control_effects"])
    assert any(float(effect["future_tension_delta"]) < 0.0 for effect in card["control_effects"])


def test_autotrader_batch_ux_has_ranked_cards_and_authority_boundary() -> None:
    rows = generate_rows(seed=20260532, contexts=1, candidates_per_context=10, profile="hard")
    batch = build_autotrader_batch_ux(rows, max_cards=3)

    assert batch["schema"] == "zenodex/energy/autotrader_batch_ux/v1"
    assert batch["candidate_count"] == 10
    assert batch["valid_count"] >= 1
    assert len(batch["cards"]) == 3
    assert batch["authority"]["deterministic_policy_guards_authoritative"] is True
    assert batch["authority"]["model_authorizes_trade"] is False
