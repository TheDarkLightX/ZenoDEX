"""Deterministic boundary-value tests for perp_v2 engine guards and updates.

These are lightweight, fast regressions intended to catch off-by-one errors
around key safety boundaries (caps, strict inequalities, clamp thresholds).
"""

from __future__ import annotations

from dataclasses import replace

from src.core.perp_v2 import Action, ActionParams, EpochPhase, initial_state, step


def _open_state_with_fresh_oracle(**kwargs):
    base = replace(
        initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        index_price_e8=100_000_000,
        collateral_quote=1_000_000,
        position_base=1_000,
        entry_price_e8=100_000_000,
    )
    return replace(base, **kwargs) if kwargs else base


def _price_published_state_for_settle(**kwargs):
    base = replace(
        initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=5,
        clearing_price_e8=100_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        index_price_e8=100_000_000,
        collateral_quote=100_000,
        position_base=0,
        entry_price_e8=0,
    )
    return replace(base, **kwargs) if kwargs else base


def test_apply_funding_rate_cap_boundary_exact_vs_outside():
    s = _open_state_with_fresh_oracle(funding_cap_bps=100)

    r_pos_eq = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True))
    assert r_pos_eq.accepted

    r_neg_eq = step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=-100, auth_ok=True))
    assert r_neg_eq.accepted

    r_pos_outside = step(
        s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=101, auth_ok=True)
    )
    assert not r_pos_outside.accepted
    assert r_pos_outside.rejection == "guard"

    r_neg_outside = step(
        s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=-101, auth_ok=True)
    )
    assert not r_neg_outside.accepted
    assert r_neg_outside.rejection == "guard"


def test_apply_insurance_claim_amount_boundary_exact_balance_vs_plus_one():
    s = replace(
        initial_state(),
        insurance_balance=1_000,
        initial_insurance=1_000,
        fee_income=0,
        claims_paid=0,
    )

    r_min = step(s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1, auth_ok=True))
    assert r_min.accepted
    assert r_min.state is not None
    assert r_min.state.insurance_balance == 999

    r_eq = step(
        s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1_000, auth_ok=True)
    )
    assert r_eq.accepted
    assert r_eq.state is not None
    assert r_eq.state.insurance_balance == 0

    r_plus_one = step(
        s, ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1_001, auth_ok=True)
    )
    assert not r_plus_one.accepted
    assert r_plus_one.rejection == "guard"


def test_settle_epoch_oracle_last_update_boundary_prev_epoch_vs_same_epoch():
    # Spec guard requires: oracle_last_update_epoch < now_epoch.
    s_prev = _price_published_state_for_settle(oracle_last_update_epoch=4)
    r_prev = step(s_prev, ActionParams(action=Action.SETTLE_EPOCH))
    assert r_prev.accepted

    s_same = replace(s_prev, oracle_last_update_epoch=s_prev.now_epoch)
    r_same = step(s_same, ActionParams(action=Action.SETTLE_EPOCH))
    assert not r_same.accepted
    assert r_same.rejection == "pre_invariant:inv_phase_published_has_settlement_path"


def test_publish_price_requires_immediately_settleable_oracle_boundaries():
    command = ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000, auth_ok=True)

    exact = _open_state_with_fresh_oracle(
        oracle_last_update_epoch=3,
        max_oracle_staleness_epochs=2,
    )
    exact_result = step(exact, command)
    assert exact_result.accepted

    stale_by_one = replace(exact, oracle_last_update_epoch=2)
    same_epoch = replace(exact, oracle_last_update_epoch=exact.now_epoch)
    unseen = replace(
        initial_state(),
        now_epoch=1,
        clearing_price_epoch=0,
    )

    for rejected_state in (stale_by_one, same_epoch, unseen):
        result = step(
            rejected_state,
            command,
        )
        assert result.accepted is False
        assert result.state is None
        assert result.effect is None
        assert result.rejection == "guard"


def test_publish_price_requires_authenticated_publication_authority():
    state = _open_state_with_fresh_oracle(
        oracle_last_update_epoch=3,
        max_oracle_staleness_epochs=2,
    )
    result = step(
        state,
        ActionParams(
            action=Action.PUBLISH_CLEARING_PRICE,
            price_e8=100_000_000,
            auth_ok=False,
        ),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "guard"


def test_settle_epoch_oracle_move_boundary_exact_vs_one_tick_past():
    s = _price_published_state_for_settle(max_oracle_move_bps=500)

    r_exact = step(
        replace(s, clearing_price_e8=105_000_000), ActionParams(action=Action.SETTLE_EPOCH)
    )
    assert r_exact.accepted
    assert r_exact.state is not None
    assert r_exact.state.breaker_active is False
    assert r_exact.state.index_price_e8 == 105_000_000

    r_past = step(
        replace(s, clearing_price_e8=105_000_001), ActionParams(action=Action.SETTLE_EPOCH)
    )
    assert r_past.accepted
    assert r_past.state is not None
    assert r_past.state.breaker_active is True
    assert r_past.state.breaker_last_trigger_epoch == s.now_epoch
    assert r_past.state.index_price_e8 == 105_000_000
