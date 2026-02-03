"""Tests for volatility tier controller (WS4)."""

from __future__ import annotations

import pytest

from src.state.volatility import TierState, TierEffects, tier_effects
from src.core.volatility_tier import (
    TierAction,
    TierActionParams,
    TierStepResult,
    effective_fee_bps,
    max_trade_amount,
    step,
)


# ---------------------------------------------------------------------------
# TierState validation
# ---------------------------------------------------------------------------

def test_tier_state_defaults() -> None:
    s = TierState()
    assert s.tier == 0
    assert s.t1_bps == 3000
    assert s.t2_bps == 6000
    assert s.t3_bps == 8000


def test_tier_state_rejects_bool() -> None:
    with pytest.raises(TypeError):
        TierState(tier=True)  # type: ignore[arg-type]


def test_tier_state_rejects_out_of_range() -> None:
    with pytest.raises(ValueError):
        TierState(tier=5)


def test_tier_state_rejects_unordered_thresholds() -> None:
    with pytest.raises(ValueError):
        TierState(t1_bps=5000, t2_bps=3000, t3_bps=8000)


# ---------------------------------------------------------------------------
# tier_effects lookup
# ---------------------------------------------------------------------------

def test_tier_effects_tier0() -> None:
    e = tier_effects(0)
    assert e.fee_mult_bps == 10000
    assert e.max_trade_bps == 10000
    assert e.halt is False


def test_tier_effects_tier1() -> None:
    e = tier_effects(1)
    assert e.fee_mult_bps == 20000
    assert e.max_trade_bps == 10000
    assert e.halt is False


def test_tier_effects_tier2() -> None:
    e = tier_effects(2)
    assert e.fee_mult_bps == 30000
    assert e.max_trade_bps == 1000
    assert e.halt is False


def test_tier_effects_tier3() -> None:
    e = tier_effects(3)
    assert e.fee_mult_bps == 0
    assert e.max_trade_bps == 0
    assert e.halt is True


# ---------------------------------------------------------------------------
# observe: tier escalation
# ---------------------------------------------------------------------------

def test_observe_calm_stays_tier0() -> None:
    s = TierState()
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=1000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 0


def test_observe_elevated() -> None:
    s = TierState()
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=4000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 1


def test_observe_high() -> None:
    s = TierState()
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=7000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 2


def test_observe_halt() -> None:
    s = TierState()
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=9000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 3
    assert r.effects is not None
    assert r.effects.halt is True


# ---------------------------------------------------------------------------
# observe: fail-closed
# ---------------------------------------------------------------------------

def test_observe_data_not_ok_halts() -> None:
    s = TierState()
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=0, data_ok=False))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 3


# ---------------------------------------------------------------------------
# observe: monotone within epoch
# ---------------------------------------------------------------------------

def test_observe_monotone_within_epoch() -> None:
    """Tier cannot decrease within the same epoch."""
    s = TierState(tier=2, last_epoch=5)
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=5, volatility_bps=1000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 2  # stays at 2, cannot decrease to 0


def test_observe_can_increase_within_epoch() -> None:
    s = TierState(tier=1, last_epoch=5)
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=5, volatility_bps=9000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 3


# ---------------------------------------------------------------------------
# observe: de-escalation on epoch advance
# ---------------------------------------------------------------------------

def test_observe_deescalation_on_new_epoch() -> None:
    s = TierState(tier=2, last_epoch=5)
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=6, volatility_bps=1000, data_ok=True))
    assert r.accepted
    assert r.state is not None
    assert r.state.tier == 0  # calm → tier 0


# ---------------------------------------------------------------------------
# observe: epoch cannot go backward
# ---------------------------------------------------------------------------

def test_observe_epoch_backward_rejected() -> None:
    s = TierState(tier=0, last_epoch=10)
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=5, volatility_bps=1000, data_ok=True))
    assert not r.accepted
    assert r.rejection == "guard"


# ---------------------------------------------------------------------------
# configure
# ---------------------------------------------------------------------------

def test_configure_updates_thresholds() -> None:
    s = TierState()
    r = step(s, TierActionParams(
        action=TierAction.CONFIGURE,
        caller_is_admin=True,
        new_t1_bps=2000,
        new_t2_bps=5000,
        new_t3_bps=7000,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.t1_bps == 2000
    assert r.state.t2_bps == 5000
    assert r.state.t3_bps == 7000


def test_configure_requires_admin() -> None:
    s = TierState()
    r = step(s, TierActionParams(
        action=TierAction.CONFIGURE,
        caller_is_admin=False,
        new_t1_bps=2000,
        new_t2_bps=5000,
        new_t3_bps=7000,
    ))
    assert not r.accepted


def test_configure_rejects_unordered() -> None:
    s = TierState()
    r = step(s, TierActionParams(
        action=TierAction.CONFIGURE,
        caller_is_admin=True,
        new_t1_bps=7000,
        new_t2_bps=5000,
        new_t3_bps=2000,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# effective_fee_bps
# ---------------------------------------------------------------------------

def test_effective_fee_tier0() -> None:
    s = TierState(tier=0)
    assert effective_fee_bps(30, s) == 30  # 30 * 10000 / 10000 = 30


def test_effective_fee_tier1() -> None:
    s = TierState(tier=1)
    assert effective_fee_bps(30, s) == 60  # 30 * 20000 / 10000 = 60


def test_effective_fee_tier2() -> None:
    s = TierState(tier=2)
    assert effective_fee_bps(30, s) == 90  # 30 * 30000 / 10000 = 90


def test_effective_fee_tier3_halts() -> None:
    s = TierState(tier=3)
    assert effective_fee_bps(30, s) == -1  # halt


# ---------------------------------------------------------------------------
# max_trade_amount
# ---------------------------------------------------------------------------

def test_max_trade_tier0() -> None:
    s = TierState(tier=0)
    assert max_trade_amount(1000000, s) == 1000000  # 100%


def test_max_trade_tier2() -> None:
    s = TierState(tier=2)
    assert max_trade_amount(1000000, s) == 100000  # 10%


def test_max_trade_tier3() -> None:
    s = TierState(tier=3)
    assert max_trade_amount(1000000, s) == 0  # halt


# ---------------------------------------------------------------------------
# Conservation: tier transition cannot lose protocol fees
# ---------------------------------------------------------------------------

def test_fee_multiplier_monotone_in_tier() -> None:
    """Fee multiplier is strictly monotone in tier for tiers 0-2."""
    fees = [tier_effects(t).fee_mult_bps for t in range(3)]
    assert fees[0] < fees[1] < fees[2]


# ---------------------------------------------------------------------------
# Full lifecycle integration
# ---------------------------------------------------------------------------

def test_lifecycle_calm_to_halt_and_back() -> None:
    """Full lifecycle: calm → halt → de-escalate on epoch advance."""
    s = TierState()

    # Epoch 1: calm
    r = step(s, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=500, data_ok=True))
    assert r.accepted and r.state is not None
    assert r.state.tier == 0

    # Epoch 1: spike (same epoch, escalation allowed)
    r = step(r.state, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=9000, data_ok=True))
    assert r.accepted and r.state is not None
    assert r.state.tier == 3

    # Epoch 1: data shows calm but monotone prevents de-escalation
    r = step(r.state, TierActionParams(action=TierAction.OBSERVE, epoch=1, volatility_bps=100, data_ok=True))
    assert r.accepted and r.state is not None
    assert r.state.tier == 3  # stuck at halt within same epoch

    # Epoch 2: calm data, epoch advances → de-escalation
    r = step(r.state, TierActionParams(action=TierAction.OBSERVE, epoch=2, volatility_bps=100, data_ok=True))
    assert r.accepted and r.state is not None
    assert r.state.tier == 0
    assert r.effects is not None
    assert r.effects.halt is False


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

def test_configure_out_of_range_rejected() -> None:
    """Out-of-range threshold values are rejected (not raised)."""
    s = TierState()
    r = step(s, TierActionParams(
        action=TierAction.CONFIGURE,
        caller_is_admin=True,
        new_t1_bps=-100,
        new_t2_bps=6000,
        new_t3_bps=8000,
    ))
    assert not r.accepted


def test_configure_above_max_rejected() -> None:
    """Threshold above BPS_DENOM=10000 is rejected."""
    s = TierState()
    r = step(s, TierActionParams(
        action=TierAction.CONFIGURE,
        caller_is_admin=True,
        new_t1_bps=3000,
        new_t2_bps=6000,
        new_t3_bps=15000,
    ))
    assert not r.accepted


def test_threshold_equality_boundary() -> None:
    """Equal thresholds are valid."""
    s = TierState()
    r = step(s, TierActionParams(
        action=TierAction.CONFIGURE,
        caller_is_admin=True,
        new_t1_bps=5000,
        new_t2_bps=5000,
        new_t3_bps=5000,
    ))
    assert r.accepted
    assert r.state.t1_bps == 5000


def test_effective_fee_negative_base_safe() -> None:
    """Non-positive base fee returns 0."""
    from src.core.volatility_tier import effective_fee_bps
    s = TierState()
    assert effective_fee_bps(-100, s) == 0
    assert effective_fee_bps(0, s) == 0


def test_max_trade_negative_reserve_safe() -> None:
    """Non-positive reserve returns 0."""
    from src.core.volatility_tier import max_trade_amount
    s = TierState()
    assert max_trade_amount(-1000, s) == 0
    assert max_trade_amount(0, s) == 0
