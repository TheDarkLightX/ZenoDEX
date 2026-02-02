"""Tests for src/core/perp_v2/engine.py — dispatch table + step function.

Tests cover known action sequences end-to-end through the engine.
"""

import pytest
from dataclasses import replace

from src.core.perp_v2 import (
    Action,
    ActionParams,
    Event,
    PerpGuardError,
    PerpInvariantError,
    PerpOverflowError,
    PerpState,
    StepResult,
    initial_state,
    step,
    step_or_raise,
)


def _make_state_with_oracle(
    price_e8: int = 100_000_000,
    collateral: int = 100_000,
    position: int = 0,
    **kwargs,
) -> PerpState:
    """Helper: state with oracle established and position setup."""
    return replace(
        initial_state(),
        oracle_seen=True,
        oracle_last_update_epoch=1,
        index_price_e8=price_e8,
        now_epoch=1,
        collateral_quote=collateral,
        position_base=position,
        entry_price_e8=price_e8 if position != 0 else 0,
        **kwargs,
    )


# ---------------------------------------------------------------------------
# advance_epoch
# ---------------------------------------------------------------------------

class TestAdvanceEpoch:
    def test_basic(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=1))
        assert r.accepted
        assert r.state is not None
        assert r.state.now_epoch == 1
        assert r.effect is not None
        assert r.effect.event == Event.EPOCH_ADVANCED

    def test_multi_delta(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=100))
        assert r.accepted
        assert r.state.now_epoch == 100

    def test_overflow_rejected(self):
        s = replace(initial_state(), now_epoch=999_999)
        r = step(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=10000))
        assert not r.accepted
        assert r.rejection == "guard"


# ---------------------------------------------------------------------------
# publish_clearing_price
# ---------------------------------------------------------------------------

class TestPublishClearingPrice:
    def test_basic(self):
        s = replace(initial_state(), now_epoch=1, clearing_price_epoch=0)
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000))
        assert r.accepted
        assert r.state.clearing_price_e8 == 100_000_000
        assert r.state.clearing_price_seen is True
        assert r.state.clearing_price_epoch == 1

    def test_duplicate_rejected(self):
        s = replace(initial_state(), now_epoch=1, clearing_price_epoch=1)
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000))
        assert not r.accepted


# ---------------------------------------------------------------------------
# settle_epoch
# ---------------------------------------------------------------------------

class TestSettleEpoch:
    def _ready_to_settle(self, price_e8=100_000_000, coll=100_000, pos=0):
        """Build a state ready to settle (clearing published, oracle lagging)."""
        s = replace(
            initial_state(),
            now_epoch=2,
            clearing_price_seen=True,
            clearing_price_epoch=2,
            clearing_price_e8=price_e8,
            oracle_seen=True,
            oracle_last_update_epoch=1,
            index_price_e8=100_000_000,
            collateral_quote=coll,
            position_base=pos,
            entry_price_e8=100_000_000 if pos != 0 else 0,
        )
        return s

    def test_flat_position(self):
        s = self._ready_to_settle()
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        assert r.state.oracle_seen is True
        assert r.state.oracle_last_update_epoch == 2
        assert r.effect.event == Event.EPOCH_SETTLED
        assert r.effect.oracle_fresh is True

    def test_profitable_long(self):
        # Long 100, price goes up 10% but clamped to 5% (max_oracle_move_bps=500)
        s = self._ready_to_settle(price_e8=110_000_000, coll=100_000, pos=100)
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        # Settle price clamped to 105_000_000; PnL = 100 * 5_000_000 / 1e8 = 5
        assert r.state.collateral_quote == 100_005
        assert r.state.index_price_e8 == 105_000_000  # clamped
        assert r.state.liquidated_this_step is False
        assert r.state.breaker_active is True  # move exceeded bound

    def test_losing_long_not_liquidated(self):
        # Long 100, price goes down 1%
        s = self._ready_to_settle(price_e8=99_000_000, coll=100_000, pos=100)
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        # PnL = -100 * 1_000_000 / 1e8 = -1
        assert r.state.collateral_quote == 99_999
        assert r.state.liquidated_this_step is False

    def test_liquidation(self):
        # Long 100, price drops 3% (within 5% max move → no clamping).
        # settle_price = 97_000_000. PnL = -(100 * 3_000_000 / 1e8) = -3.
        # collateral_after_pnl = 4 - 3 = 1.
        # notional at 97e6: 100 * 97e6 / 1e8 = 97.
        # maint_req = 97 * 600 / 10000 = 5. Since 1 < 5 → liquidated.
        s = replace(
            initial_state(),
            now_epoch=2,
            clearing_price_seen=True,
            clearing_price_epoch=2,
            clearing_price_e8=97_000_000,
            oracle_seen=True,
            oracle_last_update_epoch=1,
            index_price_e8=100_000_000,
            collateral_quote=4,
            position_base=100,
            entry_price_e8=100_000_000,
        )
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        assert r.state.liquidated_this_step is True
        assert r.state.position_base == 0
        assert r.state.entry_price_e8 == 0

    def test_guard_no_clearing(self):
        s = replace(initial_state(), now_epoch=2, clearing_price_seen=False)
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert not r.accepted

    def test_breaker_triggered_on_large_move(self):
        # price exceeds max_oracle_move_bps (500 = 5%)
        s = self._ready_to_settle(price_e8=110_000_000)  # 10% move > 5% bound
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        assert r.state.breaker_active is True
        assert r.state.breaker_last_trigger_epoch == 2
        # Price should be clamped
        assert r.state.index_price_e8 == 105_000_000


# ---------------------------------------------------------------------------
# deposit_collateral
# ---------------------------------------------------------------------------

class TestDepositCollateral:
    def test_basic(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=1000, auth_ok=True))
        assert r.accepted
        assert r.state.collateral_quote == 1000

    def test_auth_required(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=1000, auth_ok=False))
        assert not r.accepted


# ---------------------------------------------------------------------------
# withdraw_collateral
# ---------------------------------------------------------------------------

class TestWithdrawCollateral:
    def test_basic(self):
        s = replace(initial_state(), collateral_quote=1000)
        r = step(s, ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=500, auth_ok=True))
        assert r.accepted
        assert r.state.collateral_quote == 500

    def test_overdraw_rejected(self):
        s = replace(initial_state(), collateral_quote=100)
        r = step(s, ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=200, auth_ok=True))
        assert not r.accepted

    def test_margin_required_with_position(self):
        s = _make_state_with_oracle(collateral=100, position=100)
        # maint_req = 6; trying to withdraw 95 would leave 5 < 6
        r = step(s, ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=95, auth_ok=True))
        assert not r.accepted

    def test_margin_ok_after_withdrawal(self):
        s = _make_state_with_oracle(collateral=100, position=100)
        # maint_req = 6; withdrawing 90 leaves 10 >= 6
        r = step(s, ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=90, auth_ok=True))
        assert r.accepted


# ---------------------------------------------------------------------------
# set_position
# ---------------------------------------------------------------------------

class TestSetPosition:
    def test_open_long(self):
        s = _make_state_with_oracle(collateral=100_000)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=100, auth_ok=True))
        assert r.accepted
        assert r.state.position_base == 100
        assert r.state.entry_price_e8 == 100_000_000

    def test_close_to_flat(self):
        s = _make_state_with_oracle(collateral=100_000, position=100)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=0, auth_ok=True))
        assert r.accepted
        assert r.state.position_base == 0
        assert r.state.entry_price_e8 == 0

    def test_insufficient_margin_rejected(self):
        s = _make_state_with_oracle(collateral=5)
        # init_margin for 100 base @ 1e8 = 100 * 1000/10000 = 10
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=100, auth_ok=True))
        assert not r.accepted

    def test_oracle_not_seen_rejected(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=100, auth_ok=True))
        assert not r.accepted

    def test_breaker_reduce_only(self):
        s = _make_state_with_oracle(collateral=100_000, position=100, breaker_active=True)
        # Increasing is rejected
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=200, auth_ok=True))
        assert not r.accepted
        # Reducing is accepted
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=50, auth_ok=True))
        assert r.accepted

    def test_breaker_no_sign_flip(self):
        s = _make_state_with_oracle(collateral=100_000, position=100, breaker_active=True)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=-50, auth_ok=True))
        assert not r.accepted

    def test_breaker_close_to_zero(self):
        s = _make_state_with_oracle(collateral=100_000, position=100, breaker_active=True)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=0, auth_ok=True))
        assert r.accepted

    def test_exceeds_max_position(self):
        s = _make_state_with_oracle(collateral=1_000_000_000)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=1_000_001, auth_ok=True))
        assert not r.accepted

    def test_short_position(self):
        s = _make_state_with_oracle(collateral=100_000)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=-100, auth_ok=True))
        assert r.accepted
        assert r.state.position_base == -100


# ---------------------------------------------------------------------------
# clear_breaker
# ---------------------------------------------------------------------------

class TestClearBreaker:
    def test_basic(self):
        s = replace(
            initial_state(),
            breaker_active=True,
            breaker_last_trigger_epoch=5,
            now_epoch=10,
            position_base=0,
        )
        r = step(s, ActionParams(action=Action.CLEAR_BREAKER, auth_ok=True))
        assert r.accepted
        assert r.state.breaker_active is False
        assert r.state.breaker_last_trigger_epoch == 0

    def test_not_active_rejected(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.CLEAR_BREAKER, auth_ok=True))
        assert not r.accepted

    def test_position_open_rejected(self):
        s = replace(
            _make_state_with_oracle(position=100),
            breaker_active=True,
            breaker_last_trigger_epoch=1,
        )
        r = step(s, ActionParams(action=Action.CLEAR_BREAKER, auth_ok=True))
        assert not r.accepted


# ---------------------------------------------------------------------------
# apply_funding
# ---------------------------------------------------------------------------

class TestApplyFunding:
    def test_long_pays_positive_rate(self):
        s = _make_state_with_oracle(collateral=100_000, position=1000)
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=50, auth_ok=True))
        assert r.accepted
        # magnitude = 1000 * 50 / 10000 = 5
        assert r.state.collateral_quote == 99_995
        assert r.state.funding_paid_cumulative == 5
        assert r.state.funding_rate_bps == 50
        assert r.state.funding_last_applied_epoch == 1

    def test_short_receives_positive_rate(self):
        s = _make_state_with_oracle(collateral=100_000, position=-1000)
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=50, auth_ok=True))
        assert r.accepted
        assert r.state.collateral_quote == 100_005

    def test_rate_exceeds_cap_rejected(self):
        s = _make_state_with_oracle(collateral=100_000, position=1000)
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=200, auth_ok=True))
        assert not r.accepted

    def test_epoch_gate(self):
        s = _make_state_with_oracle(collateral=100_000, position=1000, funding_last_applied_epoch=1)
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=50, auth_ok=True))
        assert not r.accepted

    def test_flat_position_rejected(self):
        s = _make_state_with_oracle(collateral=100_000, position=0)
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=50, auth_ok=True))
        assert not r.accepted

    def test_margin_check(self):
        s = _make_state_with_oracle(collateral=7, position=100)
        # maint_req = 6, funding=5 would leave collateral=2 < 6
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True))
        # funding_payment = notional(100, 1e8) * 100 / 10000 = 100 * 100 / 10000 = 1
        # collateral = 7 - 1 = 6, maint_req = 6 → ok
        assert r.accepted


# ---------------------------------------------------------------------------
# deposit_insurance
# ---------------------------------------------------------------------------

class TestDepositInsurance:
    def test_basic(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.DEPOSIT_INSURANCE, amount=5000))
        assert r.accepted
        assert r.state.insurance_balance == 5000
        assert r.state.initial_insurance == 5000


# ---------------------------------------------------------------------------
# apply_insurance_claim
# ---------------------------------------------------------------------------

class TestApplyInsuranceClaim:
    def test_basic(self):
        s = replace(initial_state(), insurance_balance=5000, initial_insurance=5000)
        r = step(s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1000, auth_ok=True))
        assert r.accepted
        assert r.state.claims_paid == 1000
        assert r.state.insurance_balance == 4000

    def test_exceeds_balance_rejected(self):
        s = replace(initial_state(), insurance_balance=500, initial_insurance=500)
        r = step(s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=600, auth_ok=True))
        assert not r.accepted


# ---------------------------------------------------------------------------
# Full sequence test
# ---------------------------------------------------------------------------

class TestFullSequence:
    def test_deposit_trade_settle_withdraw(self):
        """Walk through a full lifecycle: deposit → open → settle → withdraw."""
        s = initial_state()

        # Epoch 1
        r = step(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=1))
        assert r.accepted
        s = r.state

        # Publish clearing price
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000))
        assert r.accepted
        s = r.state

        # Settle epoch (establishes oracle)
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        s = r.state
        assert s.oracle_seen is True
        assert s.index_price_e8 == 100_000_000

        # Deposit collateral
        r = step(s, ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=100_000, auth_ok=True))
        assert r.accepted
        s = r.state

        # Open position
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=500, auth_ok=True))
        assert r.accepted
        s = r.state
        assert s.position_base == 500

        # Epoch 2
        r = step(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=1))
        assert r.accepted
        s = r.state

        # Publish higher clearing price (profit)
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=110_000_000))
        assert r.accepted
        s = r.state

        # Settle epoch 2
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        s = r.state
        # PnL = 500 * (105_000_000 - 100_000_000) / 1e8 = 25 (clamped to 5% move)
        assert s.collateral_quote == 100_025
        assert s.index_price_e8 == 105_000_000  # clamped
        assert s.breaker_active is True  # 10% move > 5% threshold

        # Close position (breaker active, reduce-only)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=0, auth_ok=True))
        assert r.accepted
        s = r.state

        # Clear breaker
        r = step(s, ActionParams(action=Action.CLEAR_BREAKER, auth_ok=True))
        assert r.accepted
        s = r.state

        # Withdraw
        r = step(s, ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=100_025, auth_ok=True))
        assert r.accepted
        s = r.state
        assert s.collateral_quote == 0

    def test_invariants_always_hold_random_walk(self):
        """Execute a known sequence and verify no invariant is ever violated."""
        from src.core.perp_v2.invariants import check_all

        s = initial_state()
        actions = [
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000),
            ActionParams(action=Action.SETTLE_EPOCH),
            ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=1_000_000, auth_ok=True),
            ActionParams(action=Action.SET_POSITION, new_position_base=100, auth_ok=True),
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=102_000_000),
            ActionParams(action=Action.SETTLE_EPOCH),
            ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=50, auth_ok=True),
            ActionParams(action=Action.SET_POSITION, new_position_base=0, auth_ok=True),
            ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=100, auth_ok=True),
            ActionParams(action=Action.DEPOSIT_INSURANCE, amount=10_000),
            ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=100, auth_ok=True),
        ]

        for params in actions:
            r = step(s, params)
            if r.accepted:
                s = r.state
                violations = check_all(s)
                assert violations == [], f"Invariant violation after {params.action}: {violations}"


# ---------------------------------------------------------------------------
# Parameter domain validation
# ---------------------------------------------------------------------------

class TestParamDomainValidation:
    """YAML param bounds are enforced before guard dispatch."""

    def test_advance_epoch_delta_zero(self):
        r = step(initial_state(), ActionParams(action=Action.ADVANCE_EPOCH, delta=0))
        assert not r.accepted
        assert r.rejection == "param_domain:delta"

    def test_advance_epoch_delta_negative(self):
        r = step(initial_state(), ActionParams(action=Action.ADVANCE_EPOCH, delta=-1))
        assert not r.accepted
        assert r.rejection == "param_domain:delta"

    def test_advance_epoch_delta_exceeds_max(self):
        r = step(initial_state(), ActionParams(action=Action.ADVANCE_EPOCH, delta=10_001))
        assert not r.accepted
        assert r.rejection == "param_domain:delta"

    def test_advance_epoch_delta_at_max(self):
        r = step(initial_state(), ActionParams(action=Action.ADVANCE_EPOCH, delta=10_000))
        assert r.accepted

    def test_publish_clearing_price_zero(self):
        s = replace(initial_state(), now_epoch=1)
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=0))
        assert not r.accepted
        assert r.rejection == "param_domain:price_e8"

    def test_publish_clearing_price_negative(self):
        s = replace(initial_state(), now_epoch=1)
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=-100))
        assert not r.accepted
        assert r.rejection == "param_domain:price_e8"

    def test_publish_clearing_price_exceeds_max(self):
        s = replace(initial_state(), now_epoch=1)
        r = step(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=1_000_000_000_001))
        assert not r.accepted
        assert r.rejection == "param_domain:price_e8"

    def test_deposit_collateral_zero(self):
        r = step(initial_state(), ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=0, auth_ok=True))
        assert not r.accepted
        assert r.rejection == "param_domain:amount"

    def test_deposit_collateral_negative(self):
        r = step(initial_state(), ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=-1, auth_ok=True))
        assert not r.accepted
        assert r.rejection == "param_domain:amount"

    def test_withdraw_collateral_zero(self):
        s = replace(initial_state(), collateral_quote=1000)
        r = step(s, ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=0, auth_ok=True))
        assert not r.accepted
        assert r.rejection == "param_domain:amount"

    def test_deposit_insurance_zero(self):
        r = step(initial_state(), ActionParams(action=Action.DEPOSIT_INSURANCE, amount=0))
        assert not r.accepted
        assert r.rejection == "param_domain:amount"

    def test_insurance_claim_zero(self):
        s = replace(initial_state(), insurance_balance=5000, initial_insurance=5000)
        r = step(s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=0, auth_ok=True))
        assert not r.accepted
        assert r.rejection == "param_domain:claim_amount"

    def test_insurance_claim_exceeds_max(self):
        s = replace(initial_state(), insurance_balance=5000, initial_insurance=5000)
        r = step(s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1_000_000_000_001, auth_ok=True))
        assert not r.accepted
        assert r.rejection == "param_domain:claim_amount"

    def test_set_position_within_bounds(self):
        s = _make_state_with_oracle(collateral=100_000)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=1_000_000, auth_ok=True))
        assert r.accepted

    def test_set_position_exceeds_domain(self):
        s = _make_state_with_oracle(collateral=100_000_000)
        r = step(s, ActionParams(action=Action.SET_POSITION, new_position_base=1_000_001, auth_ok=True))
        assert not r.accepted
        assert r.rejection == "param_domain:new_position_base"


# ---------------------------------------------------------------------------
# Effect field assertions
# ---------------------------------------------------------------------------

class TestEffectFields:
    """Effects compute post-state observables correctly."""

    def test_advance_epoch_effects(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=1))
        assert r.effect.event == Event.EPOCH_ADVANCED
        assert r.effect.oracle_fresh is False  # oracle not seen yet
        assert r.effect.notional_quote == 0
        assert r.effect.margin_ok is True  # no position
        assert r.effect.liquidated is False
        assert r.effect.collateral_after == 0
        assert r.effect.fee_pool_after == 0
        assert r.effect.insurance_after == 0

    def test_deposit_collateral_effects(self):
        s = initial_state()
        r = step(s, ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=5000, auth_ok=True))
        assert r.effect.collateral_after == 5000
        assert r.effect.event == Event.COLLATERAL_DEPOSITED

    def test_settle_with_position_effects(self):
        """Verify effect fields when settling with open position."""
        s = replace(
            initial_state(),
            now_epoch=2,
            clearing_price_seen=True,
            clearing_price_epoch=2,
            clearing_price_e8=101_000_000,
            oracle_seen=True,
            oracle_last_update_epoch=1,
            index_price_e8=100_000_000,
            collateral_quote=100_000,
            position_base=100,
            entry_price_e8=100_000_000,
        )
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert r.accepted
        e = r.effect
        assert e.event == Event.EPOCH_SETTLED
        assert e.oracle_fresh is True  # settle_epoch forces oracle_fresh
        # Notional = |100| * 101e6 / 1e8 = 101
        assert e.notional_quote == 101
        # eff_maint = 500 + 100 = 600
        assert e.effective_maint_bps == 600
        # maint_req = 101 * 600 / 10000 = 6
        assert e.maint_req_quote == 6
        # init_req = 101 * 1000 / 10000 = 10
        assert e.init_req_quote == 10
        assert e.margin_ok is True
        assert e.liquidated is False
        assert e.collateral_after == 100_001  # +1 PnL
        assert e.fee_pool_after == 0
        assert e.insurance_after == 0

    def test_funding_effects(self):
        s = _make_state_with_oracle(collateral=100_000, position=1000)
        r = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=50, auth_ok=True))
        e = r.effect
        assert e.event == Event.FUNDING_APPLIED
        assert e.collateral_after == 99_995


# ---------------------------------------------------------------------------
# step_or_raise
# ---------------------------------------------------------------------------

class TestStepOrRaise:
    """Exception-raising entry point for strict callers."""

    def test_success_returns_result(self):
        s = initial_state()
        r = step_or_raise(s, ActionParams(action=Action.ADVANCE_EPOCH, delta=1))
        assert r.accepted
        assert r.state.now_epoch == 1

    def test_param_domain_raises_overflow_error(self):
        with pytest.raises(PerpOverflowError, match="param_domain:delta"):
            step_or_raise(initial_state(), ActionParams(action=Action.ADVANCE_EPOCH, delta=0))

    def test_guard_raises_guard_error(self):
        s = replace(initial_state(), now_epoch=1, clearing_price_epoch=1)
        with pytest.raises(PerpGuardError, match="guard"):
            step_or_raise(s, ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100))

    def test_invariant_raises_invariant_error(self):
        """Construct a scenario where invariant check catches a violation.

        We can't easily trigger this in practice (guards prevent it),
        so we test that the error class works correctly.
        """
        err = PerpInvariantError(["inv_foo", "inv_bar"])
        assert err.violations == ["inv_foo", "inv_bar"]
        assert "inv_foo" in str(err)


# ---------------------------------------------------------------------------
# Settle-epoch liquidation overflow boundary
# ---------------------------------------------------------------------------

class TestSettleLiqOverflowBoundary:
    """Test _settle_liq_overflow_ok logic at near-max boundaries."""

    def test_fee_pool_near_max(self):
        """Liquidation penalty would push fee_pool above MAX_COLLATERAL → rejected."""
        from src.core.perp_v2.math import MAX_COLLATERAL
        # pos=100M, clearing=97e6, index=100e6 → settle=97e6 (within 5% clamp).
        # pnl = -(100M * 3e6 / 1e8) = -3M. collateral_after_pnl = 4M - 3M = 1M.
        # notional = 100M * 97e6 / 1e8 = 97M. maint_req = 97M * 600 / 10000 = 5.82M.
        # 1M < 5.82M → liquidated. penalty = 97M * 50 / 10000 = 485K.
        # fee_pool(MAX) + 485K > MAX → guard rejects.
        s = replace(
            initial_state(),
            now_epoch=2,
            clearing_price_seen=True,
            clearing_price_epoch=2,
            clearing_price_e8=97_000_000,
            oracle_seen=True,
            oracle_last_update_epoch=1,
            index_price_e8=100_000_000,
            collateral_quote=4_000_000,
            position_base=100_000_000,
            entry_price_e8=100_000_000,
            fee_pool_quote=MAX_COLLATERAL,
            fee_income=MAX_COLLATERAL,
            min_notional_for_bounty=1,
        )
        r = step(s, ActionParams(action=Action.SETTLE_EPOCH))
        assert not r.accepted
        assert r.rejection == "guard"
