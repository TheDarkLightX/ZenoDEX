"""Wave 3 perp timing and keeper-game evidence.

These tests cover the perps obligations in
`docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md` that can be bound to the inspected
single-account `perp_v2` core.

Model conventions:

- Arithmetic is exact integer arithmetic through the runtime helpers.
- Phase-reachability tests use the real `perp_v2.engine.step` dispatcher.
- O-PT-04 remains queued because the inspected core has no multi-account
  price-impact surface; it needs a separate cascade model.

They are research evidence only. They do not change production behavior.
"""

from __future__ import annotations

from dataclasses import replace

from src.core.perp_funding_apply_gate import evaluate_perp_funding_apply_gate
from src.core.perp_v2.engine import step
from src.core.perp_v2.guards import guard_set_position
from src.core.perp_v2.math import (
    BPS_SCALE,
    compute_partial_close_fraction,
    funding_payment,
    maint_margin_req,
    notional_quote,
    partial_liq_penalty_capped,
)
from src.core.perp_v2.types import Action, ActionParams, EpochPhase, PerpState

PRICE_E8 = 100_000_000


def _state(
    *,
    now_epoch: int = 1,
    phase: EpochPhase = EpochPhase.OPEN,
    position_base: int = 100,
    collateral_quote: int = 20_000,
    oracle_last_update_epoch: int | None = None,
    funding_last_applied_epoch: int = 0,
) -> PerpState:
    if oracle_last_update_epoch is None:
        oracle_last_update_epoch = now_epoch
    return PerpState(
        now_epoch=now_epoch,
        epoch_phase=phase,
        oracle_seen=True,
        oracle_last_update_epoch=oracle_last_update_epoch,
        index_price_e8=PRICE_E8,
        position_base=position_base,
        entry_price_e8=0 if position_base == 0 else PRICE_E8,
        collateral_quote=collateral_quote,
        funding_cap_bps=100,
        funding_last_applied_epoch=funding_last_applied_epoch,
        maintenance_margin_bps=500,
        depeg_buffer_bps=100,
        initial_margin_bps=1000,
        liquidation_penalty_bps=50,
        min_notional_for_bounty=0,
        max_position_abs=1_000_000,
    )


def _apply_funding_params(rate_bps: int) -> ActionParams:
    return ActionParams(
        action=Action.APPLY_FUNDING,
        new_rate_bps=rate_bps,
        auth_ok=True,
    )


# ---------------------------------------------------------------------------
# H-MD-PT-001 / O-PT-01: funding timing residual is exactly bounded.
# ---------------------------------------------------------------------------


def test_h_md_pt_001_funding_timing_residual_is_cap_bounded() -> None:
    """Immediate funding exposure is zero when the account is flat."""

    rate_bps = 100
    exposed = _state(position_base=10_000, collateral_quote=20_000)
    flat = replace(exposed, position_base=0, entry_price_e8=0)

    exposed_result = step(exposed, _apply_funding_params(rate_bps))
    assert exposed_result.accepted
    assert exposed_result.state is not None

    expected_payment = funding_payment(
        exposed.position_base, exposed.index_price_e8, rate_bps
    )
    assert expected_payment == 100
    assert (
        exposed_result.state.collateral_quote
        == exposed.collateral_quote - expected_payment
    )

    flat_outcome = evaluate_perp_funding_apply_gate(
        now_epoch=flat.now_epoch,
        epoch_phase=flat.epoch_phase,
        auth_ok=True,
        index_price_e8=flat.index_price_e8,
        oracle_last_update_epoch=flat.oracle_last_update_epoch,
        max_oracle_staleness_epochs=flat.max_oracle_staleness_epochs,
        oracle_seen=flat.oracle_seen,
        funding_last_applied_epoch=flat.funding_last_applied_epoch,
        funding_cap_bps=flat.funding_cap_bps,
        new_rate_bps=rate_bps,
        position_base=flat.position_base,
        collateral_quote=flat.collateral_quote,
        maintenance_margin_bps=flat.maintenance_margin_bps,
        depeg_buffer_bps=flat.depeg_buffer_bps,
        funding_paid_cumulative=flat.funding_paid_cumulative,
    )
    assert flat_outcome.funding_payment_quote == 0
    assert not flat_outcome.position_open_ok
    assert not flat_outcome.funding_apply_allowed

    notional = notional_quote(exposed.position_base, exposed.index_price_e8)
    cap_bound = (notional * exposed.funding_cap_bps) // BPS_SCALE
    assert expected_payment == cap_bound


# ---------------------------------------------------------------------------
# H-MD-PT-005 / O-PT-01: entry can condition on already-applied funding.
# ---------------------------------------------------------------------------


def test_h_md_pt_005_set_position_ignores_funding_last_applied_epoch() -> None:
    """OPEN-phase `set_position` remains legal after funding is marked applied."""

    before_funding = _state(position_base=0, funding_last_applied_epoch=0)
    after_funding = replace(
        before_funding,
        funding_last_applied_epoch=before_funding.now_epoch,
    )
    params = ActionParams(
        action=Action.SET_POSITION,
        new_position_base=100,
        auth_ok=True,
    )

    assert guard_set_position(before_funding, params)
    assert guard_set_position(after_funding, params)

    result = step(after_funding, params)
    assert result.accepted
    assert result.state is not None
    assert result.state.position_base == 100
    assert result.state.funding_last_applied_epoch == after_funding.now_epoch


# ---------------------------------------------------------------------------
# H-MD-PT-002 / O-PT-02: price-published phase blocks voluntary position edits.
# ---------------------------------------------------------------------------


def test_h_md_pt_002_price_published_phase_blocks_free_look_position_changes() -> None:
    """After price publication, set_position rejects and allowed steps keep size."""

    open_state = _state(
        now_epoch=3,
        oracle_last_update_epoch=2,
        position_base=100,
        collateral_quote=50_000,
        funding_last_applied_epoch=2,
    )
    published = step(
        open_state,
        ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=PRICE_E8),
    )
    assert published.accepted
    assert published.state is not None
    assert published.state.epoch_phase is EpochPhase.PRICE_PUBLISHED

    attempted_reposition = step(
        published.state,
        ActionParams(
            action=Action.SET_POSITION,
            new_position_base=-100,
            auth_ok=True,
        ),
    )
    assert not attempted_reposition.accepted
    assert attempted_reposition.rejection == "guard"

    funded = step(published.state, _apply_funding_params(0))
    assert funded.accepted
    assert funded.state is not None
    assert funded.state.position_base == published.state.position_base

    settled = step(funded.state, ActionParams(action=Action.SETTLE_EPOCH))
    assert settled.accepted
    assert settled.state is not None
    assert settled.state.position_base == published.state.position_base
    assert settled.state.epoch_phase is EpochPhase.SETTLED


# ---------------------------------------------------------------------------
# H-MD-PT-003 / O-PT-03: keeper-race cost surface.
# ---------------------------------------------------------------------------


def test_h_md_pt_003_keeper_race_all_pay_trace_can_dissipate_reward() -> None:
    """A priority-gas all-pay trace can burn almost the entire reward."""

    deterministic_execution_cost = 1
    for reward in range(2, 129):
        deterministic_total_effort = deterministic_execution_cost
        all_pay_winning_bid = reward - 1
        all_pay_runner_up_bid = max(0, reward - 2)

        assert reward - all_pay_winning_bid == 1
        assert all_pay_winning_bid >= deterministic_total_effort
        assert (
            all_pay_winning_bid + all_pay_runner_up_bid
            >= deterministic_total_effort
        )


# ---------------------------------------------------------------------------
# H-MD-PT-006 / O-PT-05: fraction_bps is a value-transfer lever.
# ---------------------------------------------------------------------------


def test_h_md_pt_006_fraction_bps_can_over_liquidate_relative_to_minimum() -> None:
    """Full liquidation can be guard-legal while the auto minimum is cheaper."""

    state = _state(
        position_base=100_000,
        collateral_quote=5_900,
        funding_last_applied_epoch=0,
    )
    maint_req = maint_margin_req(
        state.position_base,
        state.index_price_e8,
        state.maintenance_margin_bps,
        state.depeg_buffer_bps,
    )
    assert maint_req == 6_000
    assert state.collateral_quote < maint_req

    auto_fraction = compute_partial_close_fraction(
        state.position_base,
        state.collateral_quote,
        state.index_price_e8,
        state.maintenance_margin_bps,
        state.depeg_buffer_bps,
        state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )
    assert 1 <= auto_fraction < BPS_SCALE
    assert auto_fraction == 181

    auto_penalty = partial_liq_penalty_capped(
        state.collateral_quote,
        state.position_base,
        auto_fraction,
        state.index_price_e8,
        state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )
    full_penalty = partial_liq_penalty_capped(
        state.collateral_quote,
        state.position_base,
        BPS_SCALE,
        state.index_price_e8,
        state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )
    assert auto_penalty == 9
    assert full_penalty == 500
    assert auto_penalty < full_penalty

    auto = step(
        state,
        ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=0,
            auth_ok=True,
        ),
    )
    full = step(
        state,
        ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=BPS_SCALE,
            auth_ok=True,
        ),
    )
    assert auto.accepted
    assert full.accepted
    assert auto.state is not None
    assert full.state is not None
    assert auto.state.position_base == 98_190
    assert full.state.position_base == 0
    assert state.collateral_quote - auto.state.collateral_quote == auto_penalty
    assert state.collateral_quote - full.state.collateral_quote == full_penalty
