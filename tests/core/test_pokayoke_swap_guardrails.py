from __future__ import annotations

import pytest

from src.core.pokayoke_swap_guardrails import SwapGuardrailContext, decide_swap_guardrails


@pytest.mark.parametrize(
    "price_impact_bps,expected_action,reason",
    [
        (99, "allow", "just-below 1% impact boundary"),
        (100, "confirm", "exactly at 1% impact boundary (confirm)"),
        (101, "confirm", "just-above 1% impact boundary"),
        (499, "confirm", "just-below 5% impact boundary"),
        (500, "typed_confirm", "exactly at 5% impact boundary (typed confirm)"),
        (501, "typed_confirm", "just-above 5% impact boundary"),
    ],
    ids=lambda x: str(x),
)
def test_guardrails_bva_price_impact_tiers(price_impact_bps: int, expected_action: str, reason: str) -> None:
    _ = reason
    ctx = SwapGuardrailContext(
        price_impact_bps=int(price_impact_bps),
        slippage_advice_status="ok",
        required_slippage_bps=0,
        recommended_slippage_bps_revert_safe=50,
        recommended_slippage_bps_mev_safe=300,
        recommended_slippage_bps=50,
    )
    out = decide_swap_guardrails(ctx=ctx, user_slippage_bps=50)
    assert out.action == expected_action


@pytest.mark.parametrize(
    "status,expected_action,expected_reason,reason",
    [
        ("ok", "allow", None, "baseline ok"),
        ("inconclusive_mev", "confirm", "inconclusive_mev", "unknown is not treated as safe"),
        ("mev_conflict", "typed_confirm", "mev_conflict", "conflict => typed confirm"),
        ("no_revert_safe_option", "typed_confirm", "no_revert_safe_option", "likely revert => typed confirm"),
        ("weird_new_status", "confirm", "status_weird_new_status", "unknown status should be surfaced (fail-closed)"),
    ],
    ids=lambda x: str(x),
)
def test_guardrails_status_tiering(status: str, expected_action: str, expected_reason: str | None, reason: str) -> None:
    _ = reason
    ctx = SwapGuardrailContext(
        price_impact_bps=0,
        slippage_advice_status=str(status),
        required_slippage_bps=0,
        recommended_slippage_bps_revert_safe=50,
        recommended_slippage_bps_mev_safe=300,
        recommended_slippage_bps=50,
    )
    out = decide_swap_guardrails(ctx=ctx, user_slippage_bps=50)
    assert out.action == expected_action
    if expected_reason is not None:
        assert expected_reason in out.reasons


@pytest.mark.parametrize(
    "user_slip,rec_revert,expected_action,expected_reason,reason",
    [
        (49, 50, "typed_confirm", "slippage_below_revert_safe", "just-below revert-safe option"),
        (50, 50, "allow", None, "exactly at revert-safe option"),
        (51, 50, "allow", None, "just-above revert-safe option"),
    ],
    ids=lambda x: str(x),
)
def test_guardrails_bva_user_slippage_vs_revert_safe(
    user_slip: int, rec_revert: int, expected_action: str, expected_reason: str | None, reason: str
) -> None:
    _ = reason
    ctx = SwapGuardrailContext(
        price_impact_bps=0,
        slippage_advice_status="ok",
        required_slippage_bps=0,
        recommended_slippage_bps_revert_safe=int(rec_revert),
        recommended_slippage_bps_mev_safe=None,
        recommended_slippage_bps=int(rec_revert),
    )
    out = decide_swap_guardrails(ctx=ctx, user_slippage_bps=int(user_slip))
    assert out.action == expected_action
    if expected_reason is not None:
        assert expected_reason in out.reasons
    else:
        assert "slippage_below_revert_safe" not in out.reasons


@pytest.mark.parametrize(
    "user_slip,mev_safe,expected_action,expected_reason,reason",
    [
        (299, 300, "allow", None, "just-below MEV-safe ceiling"),
        (300, 300, "allow", None, "exactly at MEV-safe ceiling"),
        (301, 300, "confirm", "slippage_above_mev_safe", "just-above MEV-safe ceiling"),
    ],
    ids=lambda x: str(x),
)
def test_guardrails_bva_user_slippage_vs_mev_safe_ceiling(
    user_slip: int, mev_safe: int, expected_action: str, expected_reason: str | None, reason: str
) -> None:
    _ = reason
    ctx = SwapGuardrailContext(
        price_impact_bps=0,
        slippage_advice_status="ok",
        required_slippage_bps=0,
        recommended_slippage_bps_revert_safe=50,
        recommended_slippage_bps_mev_safe=int(mev_safe),
        recommended_slippage_bps=50,
    )
    out = decide_swap_guardrails(ctx=ctx, user_slippage_bps=int(user_slip))
    assert out.action == expected_action
    if expected_reason is not None:
        assert expected_reason in out.reasons


@pytest.mark.parametrize(
    "bad_bps,reason",
    [
        (-1, "just-below min (invalid)"),
        (10_001, "just-above max (invalid)"),
        (True, "bool is rejected explicitly"),
        ("50", "out-of-domain type: str"),
    ],
    ids=lambda x: str(x),
)
def test_guardrails_bva_user_slippage_input_validation(bad_bps, reason: str) -> None:
    _ = reason
    ctx = SwapGuardrailContext(
        price_impact_bps=0,
        slippage_advice_status="ok",
        required_slippage_bps=0,
        recommended_slippage_bps_revert_safe=None,
        recommended_slippage_bps_mev_safe=None,
        recommended_slippage_bps=None,
    )
    with pytest.raises((TypeError, ValueError)):
        decide_swap_guardrails(ctx=ctx, user_slippage_bps=bad_bps)  # type: ignore[arg-type]

