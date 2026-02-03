"""Tests for Endogenous Funding Rate Market (WS3)."""

from __future__ import annotations

from src.core.funding_rate_market import (
    FRMAction,
    FRMActionParams,
    FRMEvent,
    FRMState,
    BPS_DENOM,
    compute_implied_rate_bps,
    compute_basis_bps,
    step,
)


# ---------------------------------------------------------------------------
# Math helpers
# ---------------------------------------------------------------------------

def test_implied_rate_balanced() -> None:
    """Equal exposure → 0 rate."""
    assert compute_implied_rate_bps(1000, 1000, 100) == 0


def test_implied_rate_long_dominant() -> None:
    """Longs dominate → positive rate."""
    r = compute_implied_rate_bps(3000, 1000, 100)
    assert r > 0
    # (3000 - 1000) / (3000 + 1000) * 100 = 2000/4000 * 100 = 50
    assert r == 50


def test_implied_rate_short_dominant() -> None:
    """Shorts dominate → negative rate."""
    r = compute_implied_rate_bps(1000, 3000, 100)
    assert r < 0
    assert r == -50


def test_implied_rate_zero_exposure() -> None:
    """No exposure → 0 rate."""
    assert compute_implied_rate_bps(0, 0, 100) == 0


def test_implied_rate_clamped() -> None:
    """Rate clamped to ±funding_cap_bps."""
    # All long, no short → should be capped at funding_cap
    r = compute_implied_rate_bps(10000, 0, 100)
    assert r == 100
    # All short, no long → capped at -cap
    r = compute_implied_rate_bps(0, 10000, 100)
    assert r == -100


def test_basis_bps_positive() -> None:
    """Mark > index → positive basis."""
    # mark=101e8, index=100e8 → basis = (1e8/100e8)*10000 = 100 bps
    assert compute_basis_bps(10100000000, 10000000000) == 100


def test_basis_bps_negative() -> None:
    """Mark < index → negative basis."""
    assert compute_basis_bps(9900000000, 10000000000) == -100


def test_basis_bps_zero_index() -> None:
    """Zero index → 0 (fail-safe)."""
    assert compute_basis_bps(100, 0) == 0


# ---------------------------------------------------------------------------
# Open positions
# ---------------------------------------------------------------------------

def test_open_rate_long() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_LONG,
        amount=50000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.rate_long_exposure == 50000
    assert r.state.premium_pool == 50000
    assert r.effect is not None
    assert r.effect.event == FRMEvent.RATE_LONG_OPENED


def test_open_rate_short() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_SHORT,
        amount=100000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.rate_short_exposure == 100000
    assert r.state.premium_pool == 100000


def test_open_no_auth() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_LONG,
        amount=1000,
        auth_ok=False,
    ))
    assert not r.accepted


def test_open_when_frozen() -> None:
    s = FRMState(frozen=True)
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_LONG,
        amount=1000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_open_zero_amount() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_LONG,
        amount=0,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Implied rate tracking
# ---------------------------------------------------------------------------

def test_implied_rate_updates_on_open() -> None:
    """Opening positions updates implied rate."""
    s = FRMState(funding_cap_bps=100)

    # Open long → positive implied rate
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_LONG, amount=3000, auth_ok=True,
    ))
    assert r.accepted
    s = r.state
    assert s.implied_rate_bps == 100  # 3000/3000 * 100 = 100 (all long)

    # Open short → rate decreases
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_SHORT, amount=1000, auth_ok=True,
    ))
    assert r.accepted
    s = r.state
    # (3000 - 1000) / (3000 + 1000) * 100 = 50
    assert s.implied_rate_bps == 50


# ---------------------------------------------------------------------------
# Settlement
# ---------------------------------------------------------------------------

def test_settle_rate_epoch() -> None:
    s = FRMState(
        rate_long_exposure=50000,
        rate_short_exposure=50000,
        premium_pool=100000,
        funding_cap_bps=100,
        implied_rate_bps=0,
    )
    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=10100000000,  # 101
        index_price_e8=10000000000, # 100
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.settled_this_epoch is True
    assert r.state.settlement_epoch == 1
    assert r.state.realized_rate_bps == 100  # 1% basis
    # Premium pool should be distributed
    assert r.state.premium_pool == 0
    assert r.state.protocol_fee_pool > 0
    # Payouts are recorded
    assert r.state.long_payout + r.state.short_payout > 0
    assert r.effect.event == FRMEvent.RATE_EPOCH_SETTLED
    assert r.effect.payout_long == r.state.long_payout
    assert r.effect.payout_short == r.state.short_payout


def test_settle_no_exposure_rejected() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=100,
        index_price_e8=100,
    ))
    assert not r.accepted


def test_settle_already_settled_rejected() -> None:
    s = FRMState(
        rate_long_exposure=1000,
        rate_short_exposure=1000,
        premium_pool=2000,
        settled_this_epoch=True,
    )
    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=100,
        index_price_e8=100,
    ))
    assert not r.accepted


def test_settle_frozen_rejected() -> None:
    s = FRMState(
        rate_long_exposure=1000,
        rate_short_exposure=1000,
        premium_pool=2000,
        frozen=True,
    )
    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=100,
        index_price_e8=100,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Conservation
# ---------------------------------------------------------------------------

def test_conservation_settle() -> None:
    """Settlement conservation: premium_pool = long_payout + short_payout + protocol_fee."""
    s = FRMState(
        rate_long_exposure=50000,
        rate_short_exposure=50000,
        premium_pool=100000,
        protocol_fee_pool=5000,
        funding_cap_bps=100,
    )
    pre_premium = s.premium_pool
    pre_protocol = s.protocol_fee_pool

    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=10050000000,
        index_price_e8=10000000000,
    ))
    assert r.accepted
    ns = r.state
    # Premium pool is fully distributed
    assert ns.premium_pool == 0
    # Conservation: long_payout + short_payout + new_fee = pre_premium
    new_fee = ns.protocol_fee_pool - pre_protocol
    assert ns.long_payout + ns.short_payout + new_fee == pre_premium
    # Payouts are non-negative
    assert ns.long_payout >= 0
    assert ns.short_payout >= 0


# ---------------------------------------------------------------------------
# Epoch advance
# ---------------------------------------------------------------------------

def test_advance_rate_epoch() -> None:
    s = FRMState(
        rate_market_epoch=0,
        settled_this_epoch=True,
        rate_long_exposure=1000,
        rate_short_exposure=2000,
        implied_rate_bps=-30,
    )
    r = step(s, FRMActionParams(action=FRMAction.ADVANCE_RATE_EPOCH))
    assert r.accepted
    assert r.state is not None
    assert r.state.rate_market_epoch == 1
    assert r.state.settled_this_epoch is False
    assert r.state.rate_long_exposure == 0
    assert r.state.rate_short_exposure == 0
    assert r.state.implied_rate_bps == 0


def test_advance_before_settle_rejected() -> None:
    s = FRMState(settled_this_epoch=False)
    r = step(s, FRMActionParams(action=FRMAction.ADVANCE_RATE_EPOCH))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Emergency freeze
# ---------------------------------------------------------------------------

def test_emergency_freeze() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.EMERGENCY_FREEZE, auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.frozen is True
    assert r.effect.event == FRMEvent.MARKET_FROZEN


def test_freeze_no_auth() -> None:
    s = FRMState()
    r = step(s, FRMActionParams(
        action=FRMAction.EMERGENCY_FREEZE, auth_ok=False,
    ))
    assert not r.accepted


def test_double_freeze_rejected() -> None:
    s = FRMState(frozen=True)
    r = step(s, FRMActionParams(
        action=FRMAction.EMERGENCY_FREEZE, auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Full lifecycle
# ---------------------------------------------------------------------------

def test_full_lifecycle() -> None:
    """Open → settle → advance lifecycle."""
    s = FRMState(funding_cap_bps=100)

    # Open rate long
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_LONG, amount=60000, auth_ok=True,
    ))
    assert r.accepted
    s = r.state

    # Open rate short
    r = step(s, FRMActionParams(
        action=FRMAction.OPEN_RATE_SHORT, amount=40000, auth_ok=True,
    ))
    assert r.accepted
    s = r.state
    assert s.premium_pool == 100000

    # Implied rate should be positive (longs dominate)
    assert s.implied_rate_bps > 0

    # Settle with mark > index (longs were correct)
    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=10200000000,  # 102
        index_price_e8=10000000000, # 100
    ))
    assert r.accepted
    s = r.state
    assert s.settled_this_epoch is True
    assert s.settlement_epoch == 1

    # Advance
    r = step(s, FRMActionParams(action=FRMAction.ADVANCE_RATE_EPOCH))
    assert r.accepted
    assert r.state.rate_market_epoch == 1
    assert r.state.rate_long_exposure == 0


def test_rate_symmetric_by_construction() -> None:
    """Rate market is symmetric: long_payout + short_payout = distributable."""
    s = FRMState(
        rate_long_exposure=50000,
        rate_short_exposure=50000,
        premium_pool=100000,
        protocol_fee_bps=0,  # No fee for clean test
        funding_cap_bps=100,
        implied_rate_bps=0,
    )
    r = step(s, FRMActionParams(
        action=FRMAction.SETTLE_RATE_EPOCH,
        mark_price_e8=10100000000,
        index_price_e8=10000000000,
    ))
    assert r.accepted
    ns = r.state
    # With 0 fee: premium_pool should be fully distributed
    assert ns.premium_pool == 0
    assert ns.protocol_fee_pool == 0
    # All premium goes to payouts
    assert ns.long_payout + ns.short_payout == 100000
    # Longs were correct (realized ≥ implied=0), so longs get more
    assert ns.long_payout >= ns.short_payout
