"""Tests for Curve Selection Prediction Market (WS2)."""

from __future__ import annotations

from src.core.curve_selection import (
    CSAction,
    CSActionParams,
    CSEvent,
    CSState,
    CSStepResult,
    BPS_DENOM,
    EARLY_EXIT_PENALTY_BPS,
    NUM_CURVES,
    step,
)
from src.core.curve_revenue_tracker import CurveRevenueState


# ---------------------------------------------------------------------------
# Revenue tracker
# ---------------------------------------------------------------------------

def test_revenue_tracker_initial() -> None:
    s = CurveRevenueState()
    assert s.get_winner() == 0  # tie goes to lowest id


def test_revenue_tracker_record() -> None:
    s = CurveRevenueState(revenue_sum_boost=500)
    assert s.get_revenue(2) == 500
    assert s.get_winner() == 2


def test_revenue_tracker_tiebreak() -> None:
    s = CurveRevenueState(revenue_cubic_sum=100, revenue_quartic_blend=100)
    # Tie in epoch revenue: lowest id wins
    assert s.get_winner() == 1


def test_revenue_tracker_roll_epoch() -> None:
    """roll_epoch snapshots current revenues and increments epoch."""
    s = CurveRevenueState(revenue_cpmm=100, revenue_cubic_sum=200)
    s2 = s.roll_epoch()
    assert s2.epoch == 1
    assert s2.epoch_start_revenue_cpmm == 100
    assert s2.epoch_start_revenue_cubic_sum == 200
    # Cumulative revenues unchanged
    assert s2.revenue_cpmm == 100
    assert s2.revenue_cubic_sum == 200
    # Epoch revenue is now zero (cumulative - epoch_start = 0)
    assert s2.get_epoch_revenue(0) == 0
    assert s2.get_epoch_revenue(1) == 0


def test_revenue_tracker_add_revenue() -> None:
    """add_revenue increments cumulative revenue for a curve."""
    s = CurveRevenueState()
    s = s.add_revenue(0, 500)
    s = s.add_revenue(2, 300)
    assert s.get_revenue(0) == 500
    assert s.get_revenue(2) == 300


def test_revenue_tracker_epoch_revenue_after_roll() -> None:
    """Epoch revenue tracks revenue added since last roll."""
    s = CurveRevenueState()
    s = s.add_revenue(0, 100)
    s = s.roll_epoch()
    s = s.add_revenue(0, 50)
    # Epoch revenue = cumulative (150) - epoch_start (100) = 50
    assert s.get_epoch_revenue(0) == 50


# ---------------------------------------------------------------------------
# State machine: staking
# ---------------------------------------------------------------------------

def test_stake_on_curve() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE,
        curve_id=2,
        amount=10000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.get_stake(2) == 10000
    assert r.state.total_staked == 10000
    assert r.effect is not None
    assert r.effect.event == CSEvent.STAKED


def test_stake_no_auth() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE,
        curve_id=0,
        amount=1000,
        auth_ok=False,
    ))
    assert not r.accepted


def test_stake_invalid_curve() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE,
        curve_id=5,  # out of range
        amount=1000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_stake_zero_amount() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE,
        curve_id=0,
        amount=0,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Unstaking
# ---------------------------------------------------------------------------

def test_unstake_with_penalty() -> None:
    s = CSState(stakes_1=10000, total_staked=10000)
    r = step(s, CSActionParams(
        action=CSAction.UNSTAKE,
        curve_id=1,
        amount=10000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.get_stake(1) == 0
    assert r.state.total_staked == 0
    # 5% penalty = 500
    expected_penalty = (10000 * EARLY_EXIT_PENALTY_BPS) // BPS_DENOM
    assert r.state.protocol_fee_pool == expected_penalty
    assert r.effect is not None
    assert r.effect.event == CSEvent.UNSTAKED


def test_unstake_insufficient() -> None:
    s = CSState(stakes_0=100, total_staked=100)
    r = step(s, CSActionParams(
        action=CSAction.UNSTAKE,
        curve_id=0,
        amount=200,
        auth_ok=True,
    ))
    assert not r.accepted


def test_unstake_no_auth() -> None:
    s = CSState(stakes_0=1000, total_staked=1000)
    r = step(s, CSActionParams(
        action=CSAction.UNSTAKE,
        curve_id=0,
        amount=500,
        auth_ok=False,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Epoch advancement
# ---------------------------------------------------------------------------

def test_advance_epoch() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.ADVANCE_EPOCH,
        revenue_deltas=(100, 200, 300, 150, 50),
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.epochs_since_start == 1
    assert r.state.get_revenue(0) == 100
    assert r.state.get_revenue(2) == 300
    assert r.effect is not None
    assert r.effect.event == CSEvent.EPOCH_ADVANCED


def test_advance_epoch_bad_deltas() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.ADVANCE_EPOCH,
        revenue_deltas=(100, 200),  # wrong length
    ))
    assert not r.accepted


def test_advance_cumulative() -> None:
    """Revenue accumulates across epochs."""
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.ADVANCE_EPOCH,
        revenue_deltas=(100, 0, 0, 0, 0),
    ))
    assert r.accepted
    s = r.state
    r = step(s, CSActionParams(
        action=CSAction.ADVANCE_EPOCH,
        revenue_deltas=(50, 0, 0, 0, 0),
    ))
    assert r.accepted
    assert r.state.get_revenue(0) == 150


# ---------------------------------------------------------------------------
# Settlement
# ---------------------------------------------------------------------------

def test_settle_prediction() -> None:
    """Settlement picks winner, distributes payoffs, resets."""
    s = CSState(
        stakes_0=5000,
        stakes_1=3000,
        stakes_2=2000,
        total_staked=10000,
        revenue_0=100,
        revenue_1=500,  # winner
        revenue_2=200,
        epochs_since_start=10,
        settlement_epoch_interval=10,
    )
    r = step(s, CSActionParams(action=CSAction.SETTLE_PREDICTION))
    assert r.accepted
    assert r.state is not None
    # Curve 1 has highest revenue → becomes active
    assert r.state.active_curve == 1
    assert r.state.prediction_epoch == 1
    assert r.state.epochs_since_start == 0
    # Revenues reset
    for cid in range(NUM_CURVES):
        assert r.state.get_revenue(cid) == 0
    # Losing stakes zeroed, winner stake preserved
    assert r.state.get_stake(1) == 3000  # winner kept
    assert r.state.get_stake(0) == 0     # loser zeroed
    assert r.state.get_stake(2) == 0     # loser zeroed
    assert r.state.total_staked == 3000  # only winner stake remains
    # Effect
    assert r.effect is not None
    assert r.effect.event == CSEvent.PREDICTION_SETTLED
    assert r.effect.winning_curve == 1


def test_settle_before_interval_rejected() -> None:
    s = CSState(epochs_since_start=5, settlement_epoch_interval=10)
    r = step(s, CSActionParams(action=CSAction.SETTLE_PREDICTION))
    assert not r.accepted


def test_settle_conservation() -> None:
    """Winner payout + protocol fee + winner stakes = pre-total staked."""
    s = CSState(
        stakes_0=8000,
        stakes_1=2000,
        total_staked=10000,
        revenue_0=1000,  # winner
        revenue_1=200,
        epochs_since_start=10,
        settlement_epoch_interval=10,
        protocol_fee_bps=200,
    )
    pre_total = s.total_staked
    pre_protocol = s.protocol_fee_pool

    r = step(s, CSActionParams(action=CSAction.SETTLE_PREDICTION))
    assert r.accepted
    ns = r.state

    # Losing stakes = total - winner_stake = 10000 - 8000 = 2000
    winner_stake = s.get_stake(0)
    losing = pre_total - winner_stake
    protocol_fee = (losing * s.protocol_fee_bps) // BPS_DENOM
    expected_payout = losing - protocol_fee

    assert ns.winner_payout_pool == expected_payout
    assert ns.protocol_fee_pool == pre_protocol + protocol_fee
    # Conservation: payout + fee = losing stakes
    assert ns.winner_payout_pool + protocol_fee == losing
    # Conservation: total_staked reduced to winner stake only
    assert ns.total_staked == winner_stake
    # Full conservation: winner_stake + payout + fee = pre_total
    assert ns.total_staked + ns.winner_payout_pool + protocol_fee == pre_total


# ---------------------------------------------------------------------------
# Admin
# ---------------------------------------------------------------------------

def test_admin_set_interval() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.ADMIN_SET_INTERVAL,
        new_interval=20,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.settlement_epoch_interval == 20


def test_admin_set_interval_no_auth() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.ADMIN_SET_INTERVAL,
        new_interval=20,
        auth_ok=False,
    ))
    assert not r.accepted


def test_admin_set_interval_zero() -> None:
    s = CSState()
    r = step(s, CSActionParams(
        action=CSAction.ADMIN_SET_INTERVAL,
        new_interval=0,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Full lifecycle
# ---------------------------------------------------------------------------

def test_full_lifecycle() -> None:
    """Stake → advance epochs → settle → verify curve switch."""
    s = CSState()

    # Stake on curves 0 and 2
    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE, curve_id=0, amount=5000, auth_ok=True,
    ))
    assert r.accepted
    s = r.state

    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE, curve_id=2, amount=3000, auth_ok=True,
    ))
    assert r.accepted
    s = r.state
    assert s.total_staked == 8000

    # Advance 10 epochs with curve 2 dominating revenue
    for _ in range(10):
        r = step(s, CSActionParams(
            action=CSAction.ADVANCE_EPOCH,
            revenue_deltas=(10, 0, 50, 0, 0),
        ))
        assert r.accepted
        s = r.state

    assert s.epochs_since_start == 10

    # Settle
    r = step(s, CSActionParams(action=CSAction.SETTLE_PREDICTION))
    assert r.accepted
    s = r.state

    # Curve 2 should be active (highest revenue)
    assert s.active_curve == 2
    assert s.prediction_epoch == 1
    assert s.epochs_since_start == 0

    # Payout pool should be non-zero (losers' stakes minus fee)
    assert s.winner_payout_pool > 0
    # Loser stakes zeroed, winner stake preserved
    assert s.get_stake(0) == 0     # curve 0 lost
    assert s.get_stake(2) == 3000  # curve 2 won
    assert s.total_staked == 3000


def test_settle_tiebreak_lowest_id() -> None:
    """When revenues are tied, lowest curve id wins."""
    s = CSState(
        stakes_0=1000,
        stakes_3=1000,
        total_staked=2000,
        revenue_0=500,
        revenue_3=500,  # tied with 0
        epochs_since_start=10,
        settlement_epoch_interval=10,
    )
    r = step(s, CSActionParams(action=CSAction.SETTLE_PREDICTION))
    assert r.accepted
    assert r.state.active_curve == 0  # lower id wins tie
    # Winner (0) stake preserved, loser (3) zeroed
    assert r.state.get_stake(0) == 1000
    assert r.state.get_stake(3) == 0
    assert r.state.total_staked == 1000


# ---------------------------------------------------------------------------
# Unstake effect reporting
# ---------------------------------------------------------------------------

def test_unstake_effect_reports_returned() -> None:
    """Unstake effect reports returned amount and penalty."""
    s = CSState(stakes_0=10000, total_staked=10000)
    r = step(s, CSActionParams(
        action=CSAction.UNSTAKE, curve_id=0, amount=10000, auth_ok=True,
    ))
    assert r.accepted
    assert r.effect.returned_amount == 9500  # 10000 - 5% penalty
    assert r.effect.penalty_amount == 500


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

def test_negative_revenue_delta_clamped() -> None:
    """Negative revenue deltas are clamped to zero."""
    s = CSState(revenue_0=100)
    r = step(s, CSActionParams(
        action=CSAction.ADVANCE_EPOCH,
        revenue_deltas=(-50, 0, 0, 0, 0),
    ))
    assert r.accepted
    # Negative delta clamped to 0 → revenue stays at 100
    assert r.state.get_revenue(0) == 100


def test_stake_max_amount_boundary() -> None:
    """Staking beyond MAX_AMOUNT is rejected."""
    from src.core.curve_selection import MAX_AMOUNT
    s = CSState(stakes_0=MAX_AMOUNT, total_staked=MAX_AMOUNT)
    r = step(s, CSActionParams(
        action=CSAction.STAKE_ON_CURVE, curve_id=0, amount=1, auth_ok=True,
    ))
    assert not r.accepted
