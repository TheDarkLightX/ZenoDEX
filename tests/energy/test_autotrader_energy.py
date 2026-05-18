from __future__ import annotations

from src.energy.autotrader_energy import (
    AUTOTRADER_FEATURE_NAMES,
    evaluate_autotrader_rows,
    generate_rows,
    group_counts,
    shadow_rows_from_observations,
    train_autotrader_linear_ranker,
)


def test_autotrader_synthetic_rows_are_reproducible() -> None:
    left = generate_rows(seed=20260518, contexts=8, candidates_per_context=6, profile="hard")
    right = generate_rows(seed=20260518, contexts=8, candidates_per_context=6, profile="hard")

    assert left == right
    assert tuple(left[0]["feature_names"]) == AUTOTRADER_FEATURE_NAMES
    assert all(sum(1 for row in left if row["batch_id"] == batch_id and row["label"]["is_winner"]) == 1 for batch_id in {str(row["batch_id"]) for row in left})


def test_autotrader_learned_energy_reduces_guard_calls_without_accepting_invalid() -> None:
    train_rows = generate_rows(seed=20260522, contexts=300, candidates_per_context=16, profile="hard")
    holdout_rows = generate_rows(seed=20260523, contexts=120, candidates_per_context=16, profile="hard")
    model = train_autotrader_linear_ranker(
        train_rows,
        epochs=4,
        learning_rate=0.001,
        margin=1.0,
        seed=20260522,
        init="hand",
    )

    hand = evaluate_autotrader_rows(holdout_rows, mode="hand", seed=20260523)
    learned = evaluate_autotrader_rows(holdout_rows, mode="learned", model=model, seed=20260523)

    assert learned["invalid_accept_count"] == 0
    assert learned["policy_guards_authoritative"] is True
    assert learned["scorer_authorizes_trade"] is False
    assert learned["mean_guard_calls"] < hand["mean_guard_calls"]
    assert learned["top_5_recall"] >= 0.95


def test_autotrader_model_output_is_advisory_under_bad_ordering() -> None:
    rows = generate_rows(seed=20260524, contexts=50, candidates_per_context=12, profile="hard")
    random_report = evaluate_autotrader_rows(rows, mode="random", seed=7)

    assert random_report["invalid_top_1_rate"] > 0.0
    assert random_report["invalid_accept_count"] == 0
    assert random_report["policy_guards_authoritative"] is True


def test_autotrader_shadow_rows_group_observations_by_family_occurrence() -> None:
    observations = [
        _shadow_observation("aligned_neutral", "neutral-0", "submit", 128.0),
        _shadow_observation("aligned_irrelevant", "irrelevant-0", "submit", 105.0),
        _shadow_observation("governance_block", "governance-0", "submit", 140.0, zenograph_block=True),
        _shadow_observation("oracle_stale_block", "stale-0", "skip", 118.0, stale=True),
        _shadow_observation("slippage_limit_block", "slippage-0", "reject", 125.0, slippage_block=True),
        _shadow_observation("aligned_neutral", "neutral-1", "submit", 126.0),
        _shadow_observation("aligned_irrelevant", "irrelevant-1", "submit", 104.0),
        _shadow_observation("governance_block", "governance-1", "submit", 139.0, zenograph_block=True),
        _shadow_observation("oracle_stale_block", "stale-1", "skip", 116.0, stale=True),
        _shadow_observation("slippage_limit_block", "slippage-1", "reject", 123.0, slippage_block=True),
    ]

    rows = shadow_rows_from_observations(observations, source_id="unit-shadow")
    report = evaluate_autotrader_rows(rows, mode="hand", seed=20260528)

    assert tuple(rows[0]["feature_names"]) == AUTOTRADER_FEATURE_NAMES
    assert sorted(group_counts(rows).values()) == [5, 5]
    assert sum(1 for row in rows if row["label"]["valid"]) == 6
    assert sum(1 for row in rows if row["label"]["is_winner"]) == 2
    assert report["candidate_count_mean"] == 5
    assert report["top_1_objective_recall"] >= report["top_1_recall"]
    assert report["top_5_recall"] == 1.0
    assert report["mean_guard_calls_to_objective_winner"] <= report["mean_guard_calls"]
    assert report["invalid_accept_count"] == 0
    assert report["policy_guards_authoritative"] is True
    assert report["scorer_authorizes_trade"] is False


def _shadow_observation(
    family: str,
    case_id: str,
    controller_tag: str,
    amount_out: float,
    *,
    zenograph_block: bool = False,
    stale: bool = False,
    slippage_block: bool = False,
) -> dict[str, object]:
    quote_epoch = 6 if stale else 10
    blocked_reasons = []
    if zenograph_block:
        blocked_reasons.append("governance_block")
    if stale:
        blocked_reasons.append("quote_receipt_stale")
    if slippage_block:
        blocked_reasons.append("slippage_limit_exceeded")
    reason = {
        "submit": "policy_guard_passed",
        "skip": "quote_receipt_stale:age=4,max=3",
        "reject": "slippage_limit_exceeded:60>50",
    }[controller_tag]
    return {
        "case_id": case_id,
        "strategy_id": "unit.dca.1",
        "family": family,
        "controller_tag": controller_tag,
        "controller_reason": reason,
        "controller_explain": [
            "receipt_amount_in=100",
            "max_oracle_staleness_epochs=3",
            f"quote_age_epochs={10 - quote_epoch}",
            "route_max_output_vs_reserve_bps=100",
            "route_max_price_impact_bps=25",
            "slippage_bps=60" if slippage_block else "slippage_bps=20",
            "fee_bps=30",
            "budget_spent_after=50",
            "lifetime_spent_after=200",
            "live_orders_after=1",
        ],
        "baseline_controller_slippage_bps": 60 if slippage_block else 20,
        "disagreement": {
            "disagreement": zenograph_block,
            "controller_submit_vs_zenograph_block": zenograph_block,
            "selected_template_mismatch": False,
            "current_template": "unit-template",
        },
        "zenograph_advisory": {
            "strategy_template": "unit-template",
            "selected_template_id": "unit-template",
            "tactic_evaluation": {
                "admissible": not blocked_reasons,
                "blocked_reasons": blocked_reasons,
                "positive_reasons": ["policy_guard_passed"] if controller_tag == "submit" else [],
            },
            "observation_packet": {
                "trusted_primary": True,
                "primary_signal": {
                    "amount_in": 100,
                    "amount_out": amount_out,
                    "current_epoch": 10,
                    "quote_epoch": quote_epoch,
                    "quote_receipt_present": True,
                    "quote_receipt_verified": True,
                    "source_available": True,
                    "auth_ok": True,
                    "binding_ok": True,
                },
                "wallet_capability": {
                    "enabled": True,
                    "notional_remaining": 1_000,
                },
            },
        },
    }
