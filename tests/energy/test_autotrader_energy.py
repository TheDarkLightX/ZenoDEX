from __future__ import annotations

from random import Random

from src.energy.autotrader_energy import (
    FEATURE_DIM,
    FEATURE_NAMES,
    AutoTraderCandidate,
    AutoTraderContext,
    candidate_hash,
    deterministic_best_candidate,
    extract_autotrader_feature_record,
    initial_autotrader_hand_model,
    rank_autotrader_candidates,
    verify_autotrader_candidate,
)
from tools.generate_autotrader_energy_dataset import generate_rows
from tools.train_autotrader_energy import train_autotrader_linear_ranker
from tools.evaluate_autotrader_energy import evaluate_autotrader_rows


def _context() -> AutoTraderContext:
    return AutoTraderContext(
        context_id="test-context",
        budget_remaining=500,
        window_budget=1_000,
        window_budget_used=100,
        lifetime_limit=10_000,
        lifetime_spent=200,
        live_orders=0,
        max_live_orders=3,
        max_quote_age_s=60,
        max_slippage_bps=100,
        volatility_bps=50,
        inventory_skew_bps=25,
        trust_bps=9_000,
        kill_switch_active=False,
        session_nonce_expected=7,
    )


def _candidate(**overrides: object) -> AutoTraderCandidate:
    values = {
        "candidate_id": "candidate",
        "kind": "submit",
        "requested": True,
        "admissible_hint": True,
        "wallet_capability_ok": True,
        "signal_provenance_ok": True,
        "route_sanity_ok": True,
        "oracle_freshness_ok": True,
        "execution_window_ok": True,
        "nonce": 7,
        "order_size": 100,
        "quote_age_s": 5,
        "slippage_bps": 20,
        "edge_bps": 260,
        "gas_bps": 10,
        "risk_bps": 15,
        "action_priority": 1,
    }
    values.update(overrides)
    return AutoTraderCandidate(**values)  # type: ignore[arg-type]


def test_autotrader_features_have_stable_schema() -> None:
    record = extract_autotrader_feature_record(_context(), _candidate())

    assert record.feature_names == FEATURE_NAMES
    assert len(record.values) == FEATURE_DIM
    assert record.raw["verifier_ok"] is True


def test_model_cannot_authorize_invalid_trade() -> None:
    context = _context()
    invalid = _candidate(candidate_id="invalid", wallet_capability_ok=False, edge_bps=2_000)
    model = initial_autotrader_hand_model()

    ranked = rank_autotrader_candidates(context, [invalid], model=model)
    assert candidate_hash(ranked[0]) == candidate_hash(invalid)
    assert verify_autotrader_candidate(context, ranked[0]).ok is False


def test_hand_ranker_preserves_candidate_permutation() -> None:
    context = _context()
    candidates = [_candidate(candidate_id="safe"), _candidate(candidate_id="bad", slippage_bps=500)]

    ranked = rank_autotrader_candidates(context, candidates)

    assert sorted(candidate_hash(candidate) for candidate in ranked) == sorted(
        candidate_hash(candidate) for candidate in candidates
    )


def test_tiny_training_improves_over_random_on_synthetic_rows() -> None:
    rows = list(generate_rows(contexts=40, candidates_per_context=8, seed=9001))
    train_rows = rows[:200]
    holdout_rows = rows[200:]
    model = train_autotrader_linear_ranker(
        train_rows,
        epochs=6,
        learning_rate=0.05,
        margin=1.0,
        seed=9001,
        init="zero",
    )
    report = evaluate_autotrader_rows(holdout_rows, model=model, seed=9002)

    assert report["schema"] == "zenodex/energy/autotrader_evaluation_report/v1"
    assert report["safety"]["invalid_accept_count"] == 0
    assert report["modes"]["learned"]["mean_guard_calls_until_winner"] <= report["modes"]["random"][
        "mean_guard_calls_until_winner"
    ]
