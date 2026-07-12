"""Tests for PARTIAL_LIQUIDATE action in perp_v2 engine (H-PP-011).

Validates that partial liquidation:
- Closes the minimum fraction to restore maintenance margin.
- Preserves all 18 invariants.
- Is rejected when preconditions are not met.
- Handles edge cases (flat, well-collateralized, deeply underwater).
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.perp_v2 import (
    Action,
    ActionParams,
    EpochPhase,
    Event,
    PerpGuardError,
    PerpOverflowError,
    PerpState,
    step,
    step_or_raise,
)
from src.core.perp_v2.invariants import check_all
from src.core.perp_v2.math import (
    BPS_SCALE,
    _is_partial_fraction_sufficient,
    compute_partial_close_fraction,
    is_liquidatable,
    maint_margin_req,
)


def _make_underwater_state(
    position_base: int = 100,
    collateral_quote: int = 300,
    index_price_e8: int = 100_00000000,
    now_epoch: int = 5,
    maintenance_margin_bps: int = 500,
    depeg_buffer_bps: int = 100,
    liquidation_penalty_bps: int = 50,
    initial_margin_bps: int = 1000,
    max_oracle_move_bps: int = 500,
    insurance_balance: int = 100000,
    initial_insurance: int = 100000,
    fee_income: int = 0,
    fee_pool_quote: int = 0,
    claims_paid: int = 0,
    min_notional_for_bounty: int = 100000000,
) -> PerpState:
    """Build a PerpState in OPEN phase with an underwater position.

    The default values create a long 100 at $100 index with only 300
    quote collateral, which is well below the maintenance margin of
    ~600 (6% of 10000 notional).
    """
    return PerpState(
        now_epoch=now_epoch,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=now_epoch,
        index_price_e8=index_price_e8,
        max_oracle_staleness_epochs=100,
        max_oracle_move_bps=max_oracle_move_bps,
        initial_margin_bps=initial_margin_bps,
        maintenance_margin_bps=maintenance_margin_bps,
        depeg_buffer_bps=depeg_buffer_bps,
        liquidation_penalty_bps=liquidation_penalty_bps,
        max_position_abs=1000000,
        position_base=position_base,
        entry_price_e8=index_price_e8 if position_base != 0 else 0,
        collateral_quote=collateral_quote,
        fee_pool_quote=fee_pool_quote,
        fee_income=fee_income,
        insurance_balance=insurance_balance,
        initial_insurance=initial_insurance,
        claims_paid=claims_paid,
        min_notional_for_bounty=min_notional_for_bounty,
    )


class TestPartialLiquidateBasic:
    """Basic acceptance and rejection of PARTIAL_LIQUIDATE."""

    def test_auto_fraction_accepted(self):
        """Auto-compute (fraction_bps=0) should succeed for underwater position."""
        state = _make_underwater_state()
        # Verify position is actually liquidatable.
        assert is_liquidatable(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        )

        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted, f"Expected accepted, got rejection: {result.rejection}"
        assert result.effect is not None
        assert result.effect.event == Event.PARTIAL_LIQUIDATION_APPLIED
        assert result.effect.liquidated is True

    def test_explicit_fraction_accepted(self):
        """Explicit fraction_bps should succeed if sufficient."""
        state = _make_underwater_state()
        # Auto-compute what fraction is needed.
        frac = compute_partial_close_fraction(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
            state.liquidation_penalty_bps, state.min_notional_for_bounty,
        )
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=frac,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted, f"Expected accepted, got rejection: {result.rejection}"

    def test_full_close_fraction_accepted(self):
        """fraction_bps=BPS_SCALE (full close) should be accepted."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=BPS_SCALE,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted, f"Expected accepted, got rejection: {result.rejection}"
        assert result.state is not None
        assert result.state.position_base == 0

    def test_rejected_when_not_liquidatable(self):
        """Well-collateralized position should be rejected."""
        state = _make_underwater_state(collateral_quote=500000)
        assert not is_liquidatable(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        )
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted
        assert result.rejection == "guard"

    def test_rejected_when_flat(self):
        """Flat position should be rejected."""
        state = _make_underwater_state(position_base=0, collateral_quote=10000)
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted

    def test_rejected_without_auth(self):
        """No authorization should be rejected."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=False,
        )
        result = step(state, params)
        assert not result.accepted

    def test_rejected_in_wrong_phase(self):
        """PARTIAL_LIQUIDATE only allowed in OPEN phase."""
        state = replace(
            _make_underwater_state(),
            epoch_phase=EpochPhase.PRICE_PUBLISHED,
            clearing_price_seen=True,
            clearing_price_epoch=5,
            clearing_price_e8=100_00000000,
        )
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted

    def test_rejected_with_stale_oracle(self):
        """Stale oracle should cause rejection."""
        state = replace(
            _make_underwater_state(now_epoch=200),
            oracle_last_update_epoch=1,  # 199 epochs stale (> max_oracle_staleness_epochs=100)
        )
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted


class TestPartialLiquidateInvariants:
    """Verify all 18 invariants are preserved after partial liquidation."""

    def test_invariants_preserved_auto_fraction(self):
        """Auto-computed fraction preserves all invariants."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        violations = check_all(result.state)
        assert violations == [], f"Invariants violated: {violations}"

    def test_invariants_preserved_full_close(self):
        """Full close preserves all invariants."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=BPS_SCALE,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        violations = check_all(result.state)
        assert violations == [], f"Invariants violated: {violations}"

    def test_invariants_preserved_short_position(self):
        """Short position partial liquidation preserves invariants."""
        state = _make_underwater_state(position_base=-100)
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        violations = check_all(result.state)
        assert violations == [], f"Invariants violated: {violations}"

    @pytest.mark.parametrize("position", [10, 50, 100, 500, 1000, -10, -50, -100, -500, -1000])
    def test_invariants_over_positions(self, position):
        """Various position sizes preserve invariants."""
        # Use zero collateral to guarantee underwater setup across all tested magnitudes.
        state = _make_underwater_state(position_base=position, collateral_quote=0)
        assert is_liquidatable(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        ), "test setup must produce a liquidatable position"

        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted, f"Rejected: {result.rejection}"
        violations = check_all(result.state)
        assert violations == [], f"Invariants violated: {violations}"


class TestPartialLiquidateMarginRestoration:
    """Verify remaining position is above maintenance margin after partial liq."""

    def test_margin_restored_long(self):
        """Long position: remaining position meets maintenance margin."""
        state = _make_underwater_state(position_base=1000, collateral_quote=3000)
        assert is_liquidatable(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        )

        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state

        if post.position_base != 0:
            mreq = maint_margin_req(
                post.position_base, post.index_price_e8,
                post.maintenance_margin_bps, post.depeg_buffer_bps,
            )
            assert post.collateral_quote >= mreq, (
                f"Margin not restored: collateral={post.collateral_quote} < mreq={mreq}"
            )

    def test_margin_restored_short(self):
        """Short position: remaining position meets maintenance margin."""
        state = _make_underwater_state(position_base=-1000, collateral_quote=3000)
        assert is_liquidatable(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        )

        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state

        if post.position_base != 0:
            mreq = maint_margin_req(
                post.position_base, post.index_price_e8,
                post.maintenance_margin_bps, post.depeg_buffer_bps,
            )
            assert post.collateral_quote >= mreq

    @pytest.mark.parametrize("collateral", [100, 200, 300, 400, 500])
    def test_margin_restored_varied_collateral(self, collateral):
        """Various collateral levels: margin always restored."""
        state = _make_underwater_state(position_base=1000, collateral_quote=collateral)
        if not is_liquidatable(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        ):
            pytest.skip("Not liquidatable")

        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state

        if post.position_base != 0:
            mreq = maint_margin_req(
                post.position_base, post.index_price_e8,
                post.maintenance_margin_bps, post.depeg_buffer_bps,
            )
            assert post.collateral_quote >= mreq

    def test_auto_fraction_is_minimal_across_nonmonotone_bounty_threshold(self):
        """The selector must not binary-search a nonmonotone health predicate."""
        args = {
            "position_base": 1_000,
            "collateral_after_pnl": 60,
            "settle_price_e8": 100_000_000,
            "maintenance_margin_bps": 1_000,
            "depeg_buffer_bps": 0,
            "liquidation_penalty_bps": 500,
            "min_notional_for_bounty": 500,
        }

        fraction = compute_partial_close_fraction(**args)

        assert fraction == 3_910
        assert _is_partial_fraction_sufficient(fraction_bps=fraction, **args)
        assert all(
            not _is_partial_fraction_sufficient(fraction_bps=earlier, **args)
            for earlier in range(1, fraction)
        )
        # Activating the bounty makes the predicate false again, which is the
        # exact shape that invalidated the previous binary search.
        assert _is_partial_fraction_sufficient(fraction_bps=4_999, **args)
        assert not _is_partial_fraction_sufficient(fraction_bps=5_000, **args)


class TestPartialLiquidateAccounting:
    """Verify accounting invariants: fee pool, insurance, entry price."""

    def test_fee_pool_equals_fee_income(self):
        """fee_pool_quote == fee_income after partial liq."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state
        assert post.fee_pool_quote == post.fee_income

    def test_insurance_conservation(self):
        """insurance_balance == initial_insurance + fee_income - claims_paid."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state
        assert post.insurance_balance == post.initial_insurance + post.fee_income - post.claims_paid

    def test_entry_zero_when_fully_closed(self):
        """Entry price is 0 when position fully closed."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=BPS_SCALE,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state
        assert post.position_base == 0
        assert post.entry_price_e8 == 0

    def test_entry_matches_index_when_partially_closed(self):
        """Entry price matches index price when position remains."""
        state = _make_underwater_state(position_base=10000, collateral_quote=3000)
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state
        if post.position_base != 0:
            assert post.entry_price_e8 == post.index_price_e8

    def test_penalty_increases_fee_pool(self):
        """Partial liq penalty should increase fee pool (when above min notional)."""
        state = _make_underwater_state(
            position_base=10000,
            collateral_quote=3000,
            min_notional_for_bounty=0,  # Disable anti-bounty-farming for this test
        )
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step(state, params)
        assert result.accepted
        post = result.state
        assert post.fee_pool_quote >= state.fee_pool_quote

    def test_partial_preserves_position_direction(self):
        """Partial close doesn't flip position direction."""
        for pos in [1000, -1000]:
            state = _make_underwater_state(position_base=pos, collateral_quote=3000)
            if not is_liquidatable(
                state.position_base, state.collateral_quote, state.index_price_e8,
                state.maintenance_margin_bps, state.depeg_buffer_bps,
            ):
                continue
            params = ActionParams(
                action=Action.PARTIAL_LIQUIDATE,
                fraction_bps=0,
                auth_ok=True,
            )
            result = step(state, params)
            assert result.accepted
            post = result.state
            if post.position_base != 0:
                assert (post.position_base > 0) == (pos > 0), (
                    f"Direction flipped: {pos} -> {post.position_base}"
                )


class TestPartialLiquidateParamDomain:
    """Verify parameter domain validation for PARTIAL_LIQUIDATE."""

    def test_fraction_bps_negative_rejected(self):
        """Negative fraction_bps rejected by param domain check."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=-1,
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted
        assert "param_domain" in (result.rejection or "")

    def test_fraction_bps_too_large_rejected(self):
        """fraction_bps > 10000 rejected by param domain check."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=10001,
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted
        assert "param_domain" in (result.rejection or "")

    def test_fraction_bps_bool_rejected(self):
        """Boolean fraction_bps rejected (Python: isinstance(True, int) is True)."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=True,  # type: ignore[arg-type]
            auth_ok=True,
        )
        result = step(state, params)
        assert not result.accepted


class TestPartialLiquidateStepOrRaise:
    """Verify step_or_raise behavior for PARTIAL_LIQUIDATE."""

    def test_step_or_raise_succeeds(self):
        """step_or_raise returns result for valid partial liquidation."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        result = step_or_raise(state, params)
        assert result.accepted

    def test_step_or_raise_guard_error(self):
        """step_or_raise raises PerpGuardError when guard fails."""
        state = _make_underwater_state(collateral_quote=500000)  # Well-collateralized
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        )
        with pytest.raises(PerpGuardError):
            step_or_raise(state, params)

    def test_step_or_raise_overflow_error(self):
        """step_or_raise raises PerpOverflowError for invalid params."""
        state = _make_underwater_state()
        params = ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=-1,
            auth_ok=True,
        )
        with pytest.raises(PerpOverflowError):
            step_or_raise(state, params)
