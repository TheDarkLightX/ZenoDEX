from __future__ import annotations

from src.core.perp_signed_surface_guard import (
    ACTION_INIT_MARKET_2P,
    ACTION_SET_POSITION_TRIPLET,
    REJECT_DISTINCT_ACCOUNTS_INVALID,
    REJECT_IDLE_LEG_INVALID,
    REJECT_INVALID_VERSION,
    evaluate_perp_signed_surface_guard,
    perp_signed_surface_guard_error,
)


def test_perp_signed_surface_guard_rejects_invalid_version_before_other_checks() -> None:
    outcome = evaluate_perp_signed_surface_guard(
        action_kind=ACTION_INIT_MARKET_2P,
        version_ok=False,
        unknown_fields_ok=False,
        distinct_accounts_ok=False,
        market_accounts_match_ok=True,
        net_zero_ok=True,
        idle_leg_ok=True,
        positive_price_ok=True,
    )

    assert outcome.signed_surface_ok is False
    assert outcome.reject_code == REJECT_INVALID_VERSION
    assert perp_signed_surface_guard_error(outcome, action="init_market_2p") == "init_market_2p requires perps.version=0.2 or 1.0"


def test_perp_signed_surface_guard_rejects_distinct_accounts_before_other_semantics() -> None:
    outcome = evaluate_perp_signed_surface_guard(
        action_kind=ACTION_INIT_MARKET_2P,
        version_ok=True,
        unknown_fields_ok=True,
        distinct_accounts_ok=False,
        market_accounts_match_ok=True,
        net_zero_ok=True,
        idle_leg_ok=True,
        positive_price_ok=True,
    )

    assert outcome.signed_surface_ok is False
    assert outcome.reject_code == REJECT_DISTINCT_ACCOUNTS_INVALID
    assert perp_signed_surface_guard_error(outcome, action="init_market_2p") == "accounts must be distinct"


def test_perp_signed_surface_guard_rejects_idle_leg_only_after_net_zero_passes() -> None:
    outcome = evaluate_perp_signed_surface_guard(
        action_kind=ACTION_SET_POSITION_TRIPLET,
        version_ok=True,
        unknown_fields_ok=True,
        distinct_accounts_ok=True,
        market_accounts_match_ok=True,
        net_zero_ok=True,
        idle_leg_ok=False,
        positive_price_ok=True,
    )

    assert outcome.signed_surface_ok is False
    assert outcome.reject_code == REJECT_IDLE_LEG_INVALID
    assert perp_signed_surface_guard_error(outcome, action="set_position_triplet") == "clearinghouse_3p requires at least one flat position"
