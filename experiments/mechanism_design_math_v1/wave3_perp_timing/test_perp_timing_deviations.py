# [TESTER] v1
"""
Wave-3 perp-timing deviations (charter docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md
section 10, O-PT). Integer witnesses through the REAL perp_v2 funding reducer
(apply_funding, src/core/perp_v2/updates.py) and funding math.

O-PT-01 (funding-straddle residual / H-MD-PT-001): a trader holding a position
through the once-per-epoch apply_funding has collateral debited by the funding
payment, while a straddler (no position during the funding event) is debited
nothing. So funding is NOT timing-neutral: the intra-epoch round-trip strictly
avoids a positive funding payment. The avoided amount equals funding_magnitude
and is bounded by floor(notional * cap / 10_000) per epoch, tight at the cap.

Verdict polarity (charter): hypotheses are phrased "deviation exists", so a
PASSING test == SUPPORTED — the timing deviation is demonstrated.
Research evidence only; no production change, no remedy claim.
"""

from __future__ import annotations

from dataclasses import replace

from src.core.perp_funding_apply_gate import (
    evaluate_perp_funding_apply_gate,
    perp_funding_apply_gate_error,
)
from src.core.perp_v2.engine import step
from src.core.perp_v2.funding_rule import compute_funding_rate_bps
from src.core.perp_v2.math import BPS_SCALE, funding_magnitude, notional_quote
from src.core.perp_v2.state import initial_state
from src.core.perp_v2.types import Action, ActionParams, EpochPhase
from src.core.perp_v2.updates import apply_funding


def _capped_long_rate(index_price_e8: int, cap_bps: int) -> int:
    """A mark deviating above index by more than the cap, so compute_funding_rate_bps
    saturates at +cap (longs pay). Exercises the real rate rule."""
    mark = index_price_e8 * (BPS_SCALE + 2 * cap_bps) // BPS_SCALE
    rate = compute_funding_rate_bps(
        index_price_e8=index_price_e8, mark_price_e8=mark, funding_cap_bps=cap_bps
    )
    assert rate == cap_bps  # deviation exceeds the cap -> saturated
    return rate


def test_h_md_pt_001_funding_straddle_avoids_real_collateral_debit() -> None:
    """Through the REAL reducer apply_funding: holder is debited funding_magnitude,
    straddler is debited nothing; avoided amount is tight at floor(notional*cap/1e4)."""
    q = 100
    index = 50_000 * 10**8
    cap = 100
    rate = _capped_long_rate(index, cap)
    collateral = 10**14

    base = replace(initial_state(), index_price_e8=index, collateral_quote=collateral)
    holder_after = apply_funding(replace(base, position_base=q), ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate))
    straddler_after = apply_funding(replace(base, position_base=0), ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate))

    paid = collateral - holder_after.collateral_quote
    avoided = paid - (collateral - straddler_after.collateral_quote)

    assert straddler_after.collateral_quote == collateral  # straddler pays 0
    assert paid > 0                                        # holder pays
    assert avoided == paid == funding_magnitude(q, index, rate)

    bound = (notional_quote(q, index) * cap) // BPS_SCALE  # O-PT-01 bound
    assert avoided <= bound
    assert avoided == bound  # tight at the cap


def test_h_md_pt_005_straddle_residual_bound_holds_over_witness_family() -> None:
    """O-PT-01 bound (H-MD-PT-005): across positions and caps, the avoided amount
    equals funding_magnitude, stays within floor(notional*cap/1e4), and is
    strictly positive whenever notional*cap >= 1e4 (tight at the cap)."""
    index = 30_000 * 10**8
    collateral = 10**16
    for q in (1, 7, 100, 9_999):
        for cap in (1, 25, 100, 500):
            rate = _capped_long_rate(index, cap)
            base = replace(initial_state(), index_price_e8=index, collateral_quote=collateral)
            holder_after = apply_funding(replace(base, position_base=q), ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate))
            straddler_after = apply_funding(replace(base, position_base=0), ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate))
            avoided = (
                (collateral - holder_after.collateral_quote)
                - (collateral - straddler_after.collateral_quote)
            )
            bound = (notional_quote(q, index) * cap) // BPS_SCALE
            assert avoided == funding_magnitude(q, index, rate)
            assert avoided <= bound
            assert avoided == bound  # tight at the cap
            if notional_quote(q, index) * cap >= BPS_SCALE:
                assert avoided > 0


def test_h_md_pt_001_payee_holds_payer_straddles_asymmetry() -> None:
    """The straddle is a one-sided deviation: the PAYER (same-sign as rate)
    avoids a loss by straddling, while the PAYEE (opposite sign) would only give
    up a gain. A short under a +cap (longs-pay) rate is the payee -> negative
    funding_payment (credit), so it does NOT want to straddle. This pins the
    deviation to the payer side."""
    index = 40_000 * 10**8
    cap = 100
    rate = _capped_long_rate(index, cap)  # +cap, longs pay
    collateral = 10**14
    base = replace(initial_state(), index_price_e8=index, collateral_quote=collateral)

    long_after = apply_funding(replace(base, position_base=100), ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate))
    short_after = apply_funding(replace(base, position_base=-100), ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate))

    assert long_after.collateral_quote < collateral   # long pays (payer) -> would straddle
    assert short_after.collateral_quote > collateral  # short receives (payee) -> would NOT


def _open_market(*, collateral: int, index: int, cap: int):
    """A valid OPEN-phase market (oracle seen, ample collateral) where both
    set_position and apply_funding are guard-legal."""
    return replace(
        initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=5,
        max_oracle_staleness_epochs=100,
        index_price_e8=index,
        max_position_abs=10**9,
        funding_cap_bps=cap,
        collateral_quote=collateral,
        position_base=0,
        entry_price_e8=0,
    )


def test_h_md_pt_001_funding_charges_holders_not_the_flat_straddler_at_guard() -> None:
    """Through the real GUARDED engine.step: the once-per-epoch apply_funding is
    accepted (and debits collateral by funding_magnitude) for a position-holder
    reached via the guarded set_position action, but is REJECTED for a flat
    account. So in this single-account model funding is conditioned on holding
    exposure at the funding moment — a trader who is flat then is never charged,
    which is exactly the timing lever the straddle exploits. (apply_funding-while-
    flat is not even a legal action here, so the deviation lives at the
    holds-or-not boundary, demonstrated through the real guards rather than a
    hand-built state.)"""
    q = 100
    index = 50_000 * 10**8
    cap = 100
    collateral = 10**12
    rate = cap  # within the cap; longs pay
    flat = _open_market(collateral=collateral, index=index, cap=cap)

    # A holder reached by the real guarded set_position action.
    opened = step(flat, ActionParams(action=Action.SET_POSITION, new_position_base=q, auth_ok=True))
    assert opened.accepted, opened.rejection
    holder = opened.state

    def _apply(s):
        return step(s, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=rate, auth_ok=True))

    holder_funded = _apply(holder)
    flat_funded = _apply(flat)

    assert holder_funded.accepted, holder_funded.rejection           # holder: funding applies
    assert holder_funded.state.collateral_quote == collateral - funding_magnitude(q, index, rate)
    assert not flat_funded.accepted                                  # flat straddler: never charged
    assert flat_funded.rejection == "guard"

    # Pin the rejection REASON to the position-open condition (not phase / oracle /
    # rate / margin) so the deviation is precisely "funding is gated on holding".
    flat_gate = evaluate_perp_funding_apply_gate(
        now_epoch=flat.now_epoch,
        epoch_phase=flat.epoch_phase,
        auth_ok=True,
        index_price_e8=flat.index_price_e8,
        oracle_last_update_epoch=flat.oracle_last_update_epoch,
        max_oracle_staleness_epochs=flat.max_oracle_staleness_epochs,
        oracle_seen=flat.oracle_seen,
        funding_last_applied_epoch=flat.funding_last_applied_epoch,
        funding_cap_bps=flat.funding_cap_bps,
        new_rate_bps=rate,
        position_base=flat.position_base,
        collateral_quote=flat.collateral_quote,
        maintenance_margin_bps=flat.maintenance_margin_bps,
        depeg_buffer_bps=flat.depeg_buffer_bps,
        funding_paid_cumulative=flat.funding_paid_cumulative,
    )
    assert not flat_gate.position_open_ok                  # the ONLY failing condition
    assert flat_gate.phase_allows_funding and flat_gate.oracle_fresh and flat_gate.rate_within_cap
    assert perp_funding_apply_gate_error(flat_gate) == "apply_funding requires non-zero position"
