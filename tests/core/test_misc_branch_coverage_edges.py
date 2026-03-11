from __future__ import annotations

from types import SimpleNamespace

import pytest

import src.core.fees as fees_module
import src.core.slippage_advisor as slippage_module
from src.core.curve_revenue_tracker import CurveRevenueState
from src.core.dynamic_fee_policy import StressFeePolicy, fee_bps_from_stress_policy
from src.core.fees import (
    FeeAccumulatorState,
    FeeSplitParams,
    FeeSplitResult,
    split_fee_with_dust_carry,
)
from src.core.il_futures_math import compute_il_bps
from src.core.oracle import OracleState
from src.core.pokayoke_swap_guardrails import SwapGuardrailContext, decide_swap_guardrails
from src.core.sealed_bid_bonds import (
    BondedSealedBidCommit,
    SealedBidRevealRef,
    settle_sealed_bid_non_reveal_bonds,
)
from src.core.slippage_advisor import _ceil_div, slippage_advice_exact_in_cpmm


def test_oracle_state_rejects_negative_price_timestamp() -> None:
    with pytest.raises(ValueError, match="price_timestamp must be non-negative"):
        OracleState(price_timestamp=-1, max_staleness_seconds=300)


def test_il_bps_zero_after_reserves_fail_safe() -> None:
    assert compute_il_bps(1_000, 1_000, 0, 1_000) == 0
    assert compute_il_bps(1_000, 1_000, 1_000, 0) == 0


@pytest.mark.parametrize(
    ("required_slippage_bps", "expect_message"),
    [
        (0, False),
        (125, True),
    ],
)
def test_guardrails_surfaces_required_slippage_only_when_present(
    required_slippage_bps: int, expect_message: bool
) -> None:
    out = decide_swap_guardrails(
        ctx=SwapGuardrailContext(
            price_impact_bps=0,
            slippage_advice_status="ok",
            required_slippage_bps=required_slippage_bps,
            recommended_slippage_bps_revert_safe=None,
            recommended_slippage_bps_mev_safe=None,
            recommended_slippage_bps=None,
        ),
        user_slippage_bps=50,
    )
    assert (
        any("Required slippage at confidence (ceil)" in msg for msg in out.messages)
        is expect_message
    )


@pytest.mark.parametrize(
    ("commits", "reveals", "expected_error"),
    [
        ([BondedSealedBidCommit("", "c1", 5)], [], "bidder_id must be non-empty"),
        ([BondedSealedBidCommit("alice", "", 5)], [], "commitment must be non-empty"),
        (
            [BondedSealedBidCommit("alice", "c1", 5)],
            [SealedBidRevealRef("", "c1")],
            "reveal bidder_id must be non-empty",
        ),
        (
            [BondedSealedBidCommit("alice", "c1", 5)],
            [SealedBidRevealRef("alice", "")],
            "reveal commitment must be non-empty",
        ),
    ],
)
def test_sealed_bid_bonds_reject_empty_identifiers(
    commits: list[BondedSealedBidCommit],
    reveals: list[SealedBidRevealRef],
    expected_error: str,
) -> None:
    with pytest.raises(ValueError, match=expected_error):
        settle_sealed_bid_non_reveal_bonds(commits=commits, reveals=reveals)


def test_curve_revenue_state_rejects_bad_values_and_add_revenue_edges() -> None:
    with pytest.raises(TypeError, match="revenue_cpmm must be an int"):
        CurveRevenueState(revenue_cpmm=True)
    with pytest.raises(ValueError, match="revenue_cpmm must be non-negative"):
        CurveRevenueState(revenue_cpmm=-1)

    state = CurveRevenueState()
    with pytest.raises(ValueError, match="amount must be non-negative"):
        state.add_revenue(0, -1)
    with pytest.raises(ValueError, match="curve_id must be in"):
        state.add_revenue(5, 1)


def test_stress_fee_policy_validates_types_bounds_and_min_clamp() -> None:
    with pytest.raises(TypeError, match="base_fee_bps must be an int"):
        StressFeePolicy(base_fee_bps=True, slope_bps=0)
    with pytest.raises(ValueError, match="min_fee_bps must be in"):
        StressFeePolicy(base_fee_bps=0, slope_bps=0, min_fee_bps=-1)
    with pytest.raises(ValueError, match="max_fee_bps must be in"):
        StressFeePolicy(base_fee_bps=0, slope_bps=0, max_fee_bps=10_001)

    policy = StressFeePolicy(base_fee_bps=0, slope_bps=0, min_fee_bps=30, max_fee_bps=100)
    assert fee_bps_from_stress_policy(policy, reserve_in=100, amount_in=0) == 30


def test_fee_models_reject_invalid_structures_and_fail_closed_on_over_distribution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with pytest.raises(TypeError, match="buyback_bps must be an int"):
        FeeSplitParams(buyback_bps=True, treasury_bps=0, rewards_bps=10_000)
    with pytest.raises(ValueError, match="buyback_bps must be in"):
        FeeSplitParams(buyback_bps=-1, treasury_bps=0, rewards_bps=10_001)

    with pytest.raises(TypeError, match="buyback_amount must be an int"):
        FeeSplitResult(buyback_amount=True, treasury_amount=0, rewards_amount=0, dust_carried=0)
    with pytest.raises(ValueError, match="treasury_amount must be non-negative"):
        FeeSplitResult(buyback_amount=0, treasury_amount=-1, rewards_amount=0, dust_carried=0)

    with pytest.raises(TypeError, match="dust must be an int"):
        FeeAccumulatorState(dust=True)
    with pytest.raises(ValueError, match="dust must be non-negative"):
        FeeAccumulatorState(dust=-1)

    params = FeeSplitParams(buyback_bps=3333, treasury_bps=3333, rewards_bps=3334)
    monkeypatch.setattr(fees_module, "BPS_DENOM", 1)
    with pytest.raises(AssertionError, match="fee split over-distributed"):
        split_fee_with_dust_carry(1, params)


def test_slippage_advisor_internal_fail_closed_edges(monkeypatch: pytest.MonkeyPatch) -> None:
    with pytest.raises(ValueError, match="denominator must be positive"):
        _ceil_div(1, 0)

    monkeypatch.setattr(
        slippage_module,
        "price_impact_preview",
        lambda **_kwargs: SimpleNamespace(
            amount_out_best_case=0,
            amount_out_at_confidence=0,
            pending_volume_at_confidence=7,
            price_impact_bps=1234,
        ),
    )
    advice = slippage_advice_exact_in_cpmm(
        reserve_in=1_000,
        reserve_out=1_000,
        fee_bps=30,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=9_500,
        slippage_options_bps=[10, 50],
        max_attacker_amount_in=100,
    )
    assert advice.best_amount_out == 0
    assert advice.required_slippage_bps == 10_000
    assert advice.options == []
    assert advice.status == "no_revert_safe_option"


def test_slippage_advisor_preserves_ok_status_for_revert_safe_mev_safe_case(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        slippage_module,
        "price_impact_preview",
        lambda **_kwargs: SimpleNamespace(
            amount_out_best_case=100,
            amount_out_at_confidence=99,
            pending_volume_at_confidence=7,
            price_impact_bps=10,
        ),
    )
    monkeypatch.setattr(
        slippage_module,
        "max_sandwich_profit_exact_in_cpmm_bounded",
        lambda **_kwargs: SimpleNamespace(
            status="ok",
            max_profit=0,
            attacker_amount_in=0,
            victim_amount_out=99,
            scanned_max_attacker_amount_in=100,
        ),
    )

    advice = slippage_advice_exact_in_cpmm(
        reserve_in=1_000,
        reserve_out=1_000,
        fee_bps=30,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=9_500,
        slippage_options_bps=[100],
        max_attacker_amount_in=100,
    )

    assert advice.recommended_slippage_bps_revert_safe == 100
    assert advice.recommended_slippage_bps_mev_safe == 100
    assert advice.recommended_slippage_bps == 100
    assert advice.status == "ok"
