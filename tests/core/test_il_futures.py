"""Tests for IL Futures Market (WS1)."""

from __future__ import annotations

import pytest

from src.core.il_futures import (
    ILF_TWAP_REFERENCE_SOURCE_KIND,
    ILFAction,
    ILFActionParams,
    ILFState,
    compute_twap_reference_commitment,
    step,
)
from src.core.il_futures_math import compute_il_bps, compute_payout


def _twap_commitment(
    *,
    reserve_x: int,
    reserve_y: int,
    elapsed: int = 1,
    window: int = 10,
    action: ILFAction = ILFAction.SETTLE_IL_EPOCH,
    epoch: int = 0,
) -> str:
    return compute_twap_reference_commitment(
        source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=window,
        reference_elapsed_blocks=elapsed,
        reserve_x=reserve_x,
        reserve_y=reserve_y,
        action_kind=action.value,
        epoch=epoch,
    )

# ---------------------------------------------------------------------------
# IL Math
# ---------------------------------------------------------------------------

def test_il_bps_no_change() -> None:
    """No price change → 0 IL."""
    assert compute_il_bps(1000, 1000, 1000, 1000) == 0


def test_il_bps_zero_reserves() -> None:
    """Zero reserves → 0 (fail-safe)."""
    assert compute_il_bps(0, 1000, 1000, 1000) == 0
    assert compute_il_bps(1000, 0, 1000, 1000) == 0


def test_il_bps_price_doubling() -> None:
    """Price doubling → ~5.7% IL (572 bps)."""
    # If x*y=k and price doubles: x' = x*sqrt(2), y' = y/sqrt(2)
    # IL = 1 - 2*sqrt(2)/(1+2) = 1 - 2*1.414/3 = 1 - 0.943 = 0.057
    # x_after ≈ 1414214, y_after ≈ 707107
    il = compute_il_bps(1000000, 1000000, 1414214, 707107)
    assert 400 <= il <= 700  # roughly 5.7% = 572 bps


def test_il_bps_symmetric() -> None:
    """IL should be similar for inverse price changes."""
    il_up = compute_il_bps(1000, 1000, 2000, 500)
    il_down = compute_il_bps(1000, 1000, 500, 2000)
    # Should be close (same price ratio magnitude)
    assert abs(il_up - il_down) < 100


def test_payout_basic() -> None:
    """Basic payout computation."""
    # 500 bps IL, 1M position, 80% coverage = 1M * 500 * 8000 / (10000^2) = 40000
    p = compute_payout(500, 1000000, 8000)
    assert p == 40000


def test_payout_zero_il() -> None:
    """Zero IL → zero payout."""
    assert compute_payout(0, 1000000, 8000) == 0


# ---------------------------------------------------------------------------
# State machine: open positions
# ---------------------------------------------------------------------------

def test_open_long() -> None:
    s = ILFState(short_exposure=100000, margin_pool=100000)
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=50000,
        premium_amount=1000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.long_exposure == 50000
    assert r.state.premium_pool == 1000


def test_open_long_no_auth() -> None:
    s = ILFState(short_exposure=100000, margin_pool=100000)
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=50000,
        premium_amount=1000,
        auth_ok=False,
    ))
    assert not r.accepted


def test_open_short() -> None:
    s = ILFState()
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_SHORT_IL,
        amount=100000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.short_exposure == 100000
    assert r.state.margin_pool == 100000


# ---------------------------------------------------------------------------
# Phase-gating: exposure frozen after snapshot
# ---------------------------------------------------------------------------

def test_open_long_during_snapshot_rejected() -> None:
    """Open long rejected when snapshot taken (exposure frozen)."""
    s = ILFState(
        snapshot_taken=True,
        short_exposure=100000,
        margin_pool=100000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=50000,
        premium_amount=1000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_open_short_during_snapshot_rejected() -> None:
    """Open short rejected when snapshot taken (exposure frozen)."""
    s = ILFState(snapshot_taken=True)
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_SHORT_IL,
        amount=100000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_close_during_snapshot_rejected() -> None:
    """Close position rejected between snapshot and settlement."""
    s = ILFState(
        snapshot_taken=True,
        settled_this_epoch=False,
        long_exposure=50000,
        short_exposure=100000,
        margin_pool=100000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.CLOSE_POSITION,
        amount=10000,
        close_long=True,
        auth_ok=True,
    ))
    assert not r.accepted


def test_open_long_after_settle_rejected() -> None:
    """Open long rejected after settlement (must advance epoch first)."""
    s = ILFState(
        snapshot_taken=True,
        settled_this_epoch=True,
        short_exposure=100000,
        margin_pool=100000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=50000,
        premium_amount=1000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_open_short_after_settle_rejected() -> None:
    """Open short rejected after settlement (must advance epoch first)."""
    s = ILFState(snapshot_taken=True, settled_this_epoch=True)
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_SHORT_IL,
        amount=100000,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Epoch lifecycle
# ---------------------------------------------------------------------------

def test_snapshot_epoch() -> None:
    s = ILFState()
    r = step(s, ILFActionParams(
        action=ILFAction.SNAPSHOT_EPOCH_START,
        reserve_x=1000000,
        reserve_y=1000000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.snapshot_taken is True
    assert r.state.pool_snapshot_reserve_x == 1000000


def test_snapshot_no_auth_rejected() -> None:
    """Snapshot requires auth_ok."""
    s = ILFState()
    r = step(s, ILFActionParams(
        action=ILFAction.SNAPSHOT_EPOCH_START,
        reserve_x=1000000,
        reserve_y=1000000,
        auth_ok=False,
    ))
    assert not r.accepted


def test_snapshot_requires_twap_reference_when_hardened_mode_enabled() -> None:
    commitment = _twap_commitment(
        reserve_x=1000000,
        reserve_y=1000000,
        action=ILFAction.SNAPSHOT_EPOCH_START,
    )
    s = ILFState(
        require_twap_reference=True,
        min_twap_window_blocks=10,
        accepted_twap_reference_commitments=frozenset({commitment}),
    )

    spot = step(s, ILFActionParams(
        action=ILFAction.SNAPSHOT_EPOCH_START,
        reserve_x=1000000,
        reserve_y=1000000,
        auth_ok=True,
        reference_source_kind="spot",
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
    ))
    unbound_twap = step(s, ILFActionParams(
        action=ILFAction.SNAPSHOT_EPOCH_START,
        reserve_x=1000000,
        reserve_y=1000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
    ))
    twap = step(s, ILFActionParams(
        action=ILFAction.SNAPSHOT_EPOCH_START,
        reserve_x=1000000,
        reserve_y=1000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
        reference_commitment=commitment,
    ))

    assert not spot.accepted
    assert not unbound_twap.accepted
    assert twap.accepted
    assert twap.state is not None
    assert twap.state.snapshot_taken is True


def test_snapshot_twice_rejected() -> None:
    s = ILFState(snapshot_taken=True)
    r = step(s, ILFActionParams(
        action=ILFAction.SNAPSHOT_EPOCH_START,
        reserve_x=1000000,
        reserve_y=1000000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_settle_epoch() -> None:
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        premium_pool=5000,
        margin_pool=200000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.settled_this_epoch is True
    assert r.state.realized_il_bps > 0


def test_settle_no_auth_rejected() -> None:
    """Settle requires auth_ok."""
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=False,
    ))
    assert not r.accepted


def test_settle_requires_elapsed_twap_reference_when_hardened_mode_enabled() -> None:
    commitment = _twap_commitment(reserve_x=500000, reserve_y=2000000)
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        premium_pool=5000,
        margin_pool=200000,
        require_twap_reference=True,
        min_twap_window_blocks=10,
        min_reference_elapsed_blocks=1,
        accepted_twap_reference_commitments=frozenset({commitment}),
    )

    same_block = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=0,
    ))
    unbound_elapsed = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
    ))
    elapsed = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
        reference_commitment=commitment,
    ))

    assert not same_block.accepted
    assert not unbound_elapsed.accepted
    assert elapsed.accepted
    assert elapsed.state is not None
    assert elapsed.state.realized_il_bps > 0


def test_settle_rejects_twap_commitment_bound_to_different_reserves() -> None:
    commitment = _twap_commitment(reserve_x=1000000, reserve_y=1000000)
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        premium_pool=5000,
        margin_pool=200000,
        require_twap_reference=True,
        min_twap_window_blocks=10,
        min_reference_elapsed_blocks=1,
        accepted_twap_reference_commitments=frozenset({commitment}),
    )

    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
        reference_commitment=commitment,
    ))

    assert not r.accepted


def test_settle_rejects_self_attested_unaccepted_twap_commitment() -> None:
    commitment = _twap_commitment(reserve_x=500000, reserve_y=2000000)
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        premium_pool=5000,
        margin_pool=200000,
        require_twap_reference=True,
        min_twap_window_blocks=10,
        min_reference_elapsed_blocks=1,
    )

    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
        reference_source_kind=ILF_TWAP_REFERENCE_SOURCE_KIND,
        twap_window_blocks=10,
        reference_elapsed_blocks=1,
        reference_commitment=commitment,
    ))

    assert not r.accepted


def test_twap_reference_commitment_changes_when_any_bound_field_changes() -> None:
    baseline = _twap_commitment(reserve_x=500000, reserve_y=2000000)

    variants = {
        _twap_commitment(reserve_x=500001, reserve_y=2000000),
        _twap_commitment(reserve_x=500000, reserve_y=2000001),
        _twap_commitment(reserve_x=500000, reserve_y=2000000, window=11),
        _twap_commitment(reserve_x=500000, reserve_y=2000000, elapsed=2),
        compute_twap_reference_commitment(
            source_kind="spot",
            twap_window_blocks=10,
            reference_elapsed_blocks=1,
            reserve_x=500000,
            reserve_y=2000000,
            action_kind=ILFAction.SETTLE_IL_EPOCH.value,
            epoch=0,
        ),
        _twap_commitment(
            reserve_x=500000,
            reserve_y=2000000,
            action=ILFAction.SNAPSHOT_EPOCH_START,
        ),
        _twap_commitment(reserve_x=500000, reserve_y=2000000, epoch=1),
    }

    assert baseline not in variants
    assert len(variants) == 7


def test_settle_before_snapshot_rejected() -> None:
    s = ILFState()
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert not r.accepted


def test_advance_epoch() -> None:
    s = ILFState(epoch=0, settled_this_epoch=True)
    r = step(s, ILFActionParams(action=ILFAction.ADVANCE_EPOCH))
    assert r.accepted
    assert r.state is not None
    assert r.state.epoch == 1
    assert r.state.settled_this_epoch is False
    assert r.state.snapshot_taken is False


def test_advance_before_settle_rejected() -> None:
    s = ILFState(epoch=0, settled_this_epoch=False)
    r = step(s, ILFActionParams(action=ILFAction.ADVANCE_EPOCH))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Conservation
# ---------------------------------------------------------------------------

def test_conservation_premium_plus_margin_ge_payoff() -> None:
    """Total payoffs never exceed total premiums + margin (conservation)."""
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        premium_pool=5000,
        margin_pool=200000,
    )
    pre_total = s.premium_pool + s.margin_pool + s.protocol_fee_pool

    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert r.accepted and r.state is not None
    post_total = r.state.premium_pool + r.state.margin_pool + r.state.protocol_fee_pool
    # Conservation: post_total <= pre_total (no value created)
    assert post_total <= pre_total


# ---------------------------------------------------------------------------
# Full lifecycle
# ---------------------------------------------------------------------------

def test_full_lifecycle() -> None:
    """Complete lifecycle: open → snapshot → settle → advance."""
    s = ILFState()

    # Open short position
    r = step(s, ILFActionParams(action=ILFAction.OPEN_SHORT_IL, amount=200000, auth_ok=True))
    assert r.accepted
    assert r.state is not None
    s = r.state

    # Open long position
    r = step(s, ILFActionParams(action=ILFAction.OPEN_LONG_IL, amount=50000, premium_amount=2000, auth_ok=True))
    assert r.accepted
    assert r.state is not None
    s = r.state

    # Snapshot
    r = step(s, ILFActionParams(action=ILFAction.SNAPSHOT_EPOCH_START, reserve_x=1000000, reserve_y=1000000, auth_ok=True))
    assert r.accepted
    assert r.state is not None
    s = r.state

    # Settle (price changed)
    r = step(s, ILFActionParams(action=ILFAction.SETTLE_IL_EPOCH, current_reserve_x=700000, current_reserve_y=1400000, auth_ok=True))
    assert r.accepted
    assert r.state is not None
    s = r.state
    assert s.settled_this_epoch is True

    # Advance
    r = step(s, ILFActionParams(action=ILFAction.ADVANCE_EPOCH))
    assert r.accepted
    assert r.state is not None
    assert r.state.epoch == 1


# ---------------------------------------------------------------------------
# Close position
# ---------------------------------------------------------------------------

def test_close_long_position() -> None:
    """Close long reduces long_exposure only."""
    s = ILFState(long_exposure=50000, short_exposure=100000, margin_pool=100000)
    r = step(s, ILFActionParams(
        action=ILFAction.CLOSE_POSITION,
        amount=20000,
        close_long=True,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.long_exposure == 30000
    assert r.state.short_exposure == 100000  # unchanged


def test_close_short_position() -> None:
    """Close short reduces short_exposure and margin_pool."""
    s = ILFState(short_exposure=100000, margin_pool=100000)
    r = step(s, ILFActionParams(
        action=ILFAction.CLOSE_POSITION,
        amount=30000,
        close_short=True,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.short_exposure == 70000
    assert r.state.margin_pool == 70000


def test_close_both_sides_rejected() -> None:
    """Cannot close both long and short simultaneously."""
    s = ILFState(long_exposure=1000, short_exposure=1000, margin_pool=1000)
    r = step(s, ILFActionParams(
        action=ILFAction.CLOSE_POSITION,
        amount=500,
        close_long=True,
        close_short=True,
        auth_ok=True,
    ))
    assert not r.accepted


def test_close_neither_side_rejected() -> None:
    """Must specify exactly one side."""
    s = ILFState(long_exposure=1000, short_exposure=1000, margin_pool=1000)
    r = step(s, ILFActionParams(
        action=ILFAction.CLOSE_POSITION,
        amount=500,
        auth_ok=True,
    ))
    assert not r.accepted


def test_close_exceeds_exposure_rejected() -> None:
    """Cannot close more than current exposure."""
    s = ILFState(long_exposure=1000, short_exposure=2000, margin_pool=2000)
    r = step(s, ILFActionParams(
        action=ILFAction.CLOSE_POSITION,
        amount=5000,
        close_long=True,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Leverage guard edge cases
# ---------------------------------------------------------------------------

def test_open_long_no_shorts_rejected() -> None:
    """Cannot open long when no shorts exist (leverage undefined)."""
    s = ILFState(short_exposure=0)
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=1000,
        premium_amount=100,
        auth_ok=True,
    ))
    assert not r.accepted


def test_open_long_at_leverage_boundary() -> None:
    """Open long exactly at max leverage (2x) should be accepted."""
    s = ILFState(short_exposure=50000, margin_pool=50000)
    # 2x leverage: long can be up to 50000 * 20000 / 10000 = 100000
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=100000,
        premium_amount=1000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.long_exposure == 100000


def test_open_long_over_leverage_rejected() -> None:
    """Open long over max leverage (2x) should be rejected."""
    s = ILFState(short_exposure=50000, margin_pool=50000)
    r = step(s, ILFActionParams(
        action=ILFAction.OPEN_LONG_IL,
        amount=100001,
        premium_amount=1000,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Double-settle rejection
# ---------------------------------------------------------------------------

def test_double_settle_rejected() -> None:
    """Cannot settle the same epoch twice."""
    s = ILFState(
        snapshot_taken=True,
        settled_this_epoch=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        margin_pool=200000,
        premium_pool=5000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert not r.accepted


# ---------------------------------------------------------------------------
# Settlement payout and fee accounting
# ---------------------------------------------------------------------------

def test_settle_payout_fee_accounting() -> None:
    """Settlement effect reports payout and fee correctly."""
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        margin_pool=200000,
        premium_pool=5000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.effect is not None
    ns = r.state
    eff = r.effect

    # Effect reports payout and fee
    assert eff.net_payout >= 0
    assert eff.protocol_fee >= 0
    # net_payout + protocol_fee = total deducted from pools
    pre_pools = 200000 + 5000  # margin + premium
    post_pools = ns.margin_pool + ns.premium_pool
    deducted = pre_pools - post_pools
    assert eff.net_payout + eff.protocol_fee == deducted
    # Protocol fee went to protocol_fee_pool
    assert ns.protocol_fee_pool == eff.protocol_fee


def test_settle_is_margin_capped_and_preserves_premium_pool() -> None:
    """Settlement payout is capped by short margin and does not consume premiums."""
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1_000_000,
        pool_snapshot_reserve_y=1_000_000,
        long_exposure=500_000,
        short_exposure=10_000,
        margin_pool=10_000,
        premium_pool=5_000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500_000,
        current_reserve_y=2_000_000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    # Margin is fully consumed up to the cap, premiums are left untouched.
    assert r.state.margin_pool == 0
    assert r.state.short_exposure == 0
    assert r.state.premium_pool == s.premium_pool
    assert (r.state.last_net_payout + r.state.last_protocol_fee) == s.margin_pool


def test_settle_margin_short_consistent() -> None:
    """After settlement, margin_pool == short_exposure."""
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        margin_pool=200000,
        premium_pool=5000,
    )
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    assert r.state.margin_pool == r.state.short_exposure


def test_close_short_after_settle() -> None:
    """Close short after settlement works because margin == short_exposure."""
    s = ILFState(
        snapshot_taken=True,
        pool_snapshot_reserve_x=1000000,
        pool_snapshot_reserve_y=1000000,
        long_exposure=100000,
        short_exposure=200000,
        margin_pool=200000,
        premium_pool=5000,
    )
    # Settle
    r = step(s, ILFActionParams(
        action=ILFAction.SETTLE_IL_EPOCH,
        current_reserve_x=500000,
        current_reserve_y=2000000,
        auth_ok=True,
    ))
    assert r.accepted
    assert r.state is not None
    s = r.state

    # Close part of short position
    close_amt = min(s.short_exposure, 50000)
    if close_amt > 0:
        r = step(s, ILFActionParams(
            action=ILFAction.CLOSE_POSITION,
            amount=close_amt,
            close_short=True,
            auth_ok=True,
        ))
        assert r.accepted
        assert r.state is not None
        assert r.state.short_exposure == s.short_exposure - close_amt
        assert r.state.margin_pool == s.margin_pool - close_amt


# ---------------------------------------------------------------------------
# Config validation
# ---------------------------------------------------------------------------

def test_protocol_fee_bps_over_10000_rejected() -> None:
    """protocol_fee_bps > 10000 rejected at construction."""
    with pytest.raises(ValueError, match="protocol_fee_bps"):
        ILFState(protocol_fee_bps=10001)


def test_coverage_ratio_bps_over_10000_rejected() -> None:
    """coverage_ratio_bps > 10000 rejected at construction."""
    with pytest.raises(ValueError, match="coverage_ratio_bps"):
        ILFState(coverage_ratio_bps=10001)


def test_max_leverage_bps_zero_rejected() -> None:
    """max_leverage_bps must be positive."""
    with pytest.raises(ValueError, match="max_leverage_bps"):
        ILFState(max_leverage_bps=0)


def test_protocol_fee_bps_negative_rejected() -> None:
    """Negative protocol_fee_bps rejected."""
    with pytest.raises(ValueError, match="protocol_fee_bps"):
        ILFState(protocol_fee_bps=-1)
