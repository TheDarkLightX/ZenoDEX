# [TESTER] v1
"""
Wave-3 perp liquidation-size lever (charter docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md
section 10, O-PT-05 / H-MD-PT-006). Integer witnesses through the REAL perp_v2
partial-liquidation guard + reducer (src/core/perp_v2/guards.py
guard_partial_liquidate, src/core/perp_v2/updates.py apply_partial_liquidate)
and the eligibility gate (src/core/perp_liquidation_eligibility_gate.py).

O-PT-05: liquidation-size choice is NOT neutral. For an underwater position the
guard requires post-penalty collateral to stay non-negative AND, when the residual
position is non-flat, to restore maintenance margin (guard_partial_liquidate lines
307-314) — but it does NOT require the chosen fraction to be the MINIMAL sufficient
one. So the legal fraction set is [f_min, BPS_SCALE], every member of which flattens
or restores margin, and a liquidator may pick the FULL close (max penalty) over the
minimal f_min. The penalty scales with the closed notional and is transferred from
the liquidatee's collateral into the fee_pool / insurance (conservation: collateral
loss == fee_pool gain). Hence an oversized (but still legal) liquidation extracts
strictly more penalty than the minimal sufficient one. NB: a fraction below f_min
that leaves collateral non-negative is still guard-REJECTED for failing residual
margin — the lever is "oversize above the minimum", not "any fraction".

Verdict polarity (charter): hypotheses are phrased "deviation exists", so a
PASSING test == SUPPORTED — the size-choice deviation is demonstrated.
Research evidence only; no production change, no remedy claim (e.g. "the guard
should force the minimal fraction" is an UNTESTED candidate, not asserted here).
"""

from __future__ import annotations

from dataclasses import replace

from src.core.perp_v2.engine import step
from src.core.perp_v2.guards import guard_partial_liquidate
from src.core.perp_v2.math import (
    BPS_SCALE,
    compute_partial_close_fraction,
    is_liquidatable,
    maint_margin_req,
    partial_liq_penalty_capped,
    remaining_position_signed,
)
from src.core.perp_v2.state import initial_state
from src.core.perp_v2.types import Action, ActionParams, EpochPhase

# A slightly-underwater long: collateral (45_000) sits below the maintenance
# requirement (50_000) but above the full-close penalty (20_000), so BOTH a
# small partial close and a full close are guard-legal. index = 1.0 (e8) makes
# notional == |position| for transparent arithmetic.
_Q = 1_000_000
_INDEX = 1 * 10**8
_MAINT_BPS = 500          # 5% maintenance
_DEPEG_BPS = 0
_PEN_BPS = 200            # 2% liquidation penalty
_MIN_NOTIONAL = 0         # bounty threshold off -> penalty always applies
_COLLATERAL = 45_000


def _liquidatable_market(collateral: int = _COLLATERAL):
    return replace(
        initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=5,
        max_oracle_staleness_epochs=100,
        index_price_e8=_INDEX,
        position_base=_Q,
        entry_price_e8=_INDEX,       # PnL == 0, so collateral_after_pnl == collateral
        collateral_quote=collateral,
        maintenance_margin_bps=_MAINT_BPS,
        depeg_buffer_bps=_DEPEG_BPS,
        liquidation_penalty_bps=_PEN_BPS,
        min_notional_for_bounty=_MIN_NOTIONAL,
        max_position_abs=10**12,
    )


def _liq(state, fraction_bps):
    return step(state, ActionParams(
        action=Action.PARTIAL_LIQUIDATE, fraction_bps=fraction_bps, auth_ok=True))


def _auto_min(state) -> int:
    return compute_partial_close_fraction(
        state.position_base, state.collateral_quote, state.index_price_e8,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
        state.liquidation_penalty_bps, state.min_notional_for_bounty,
    )


def test_h_md_pt_006_oversized_liquidation_extracts_strictly_more_penalty() -> None:
    """Through the REAL guard + reducer: a liquidatable long can be closed at the
    auto-MINIMUM fraction (which restores margin) OR at the FULL fraction; both
    are guard-legal, but full-close transfers strictly more penalty. The extra is
    extracted from the liquidatee's collateral and credited to fee_pool/insurance
    (conservation). Liquidation size is a lever, not a neutral choice."""
    base = _liquidatable_market()
    assert is_liquidatable(_Q, base.collateral_quote, _INDEX, _MAINT_BPS, _DEPEG_BPS)

    f_min = _auto_min(base)
    assert 1 <= f_min < BPS_SCALE          # a strictly partial fraction suffices

    # Both fractions are guard-legal at the SAME liquidatable state.
    assert guard_partial_liquidate(base, ActionParams(
        action=Action.PARTIAL_LIQUIDATE, fraction_bps=f_min, auth_ok=True))
    assert guard_partial_liquidate(base, ActionParams(
        action=Action.PARTIAL_LIQUIDATE, fraction_bps=BPS_SCALE, auth_ok=True))

    r_min = _liq(base, f_min)
    r_full = _liq(base, BPS_SCALE)
    assert r_min.accepted, r_min.rejection
    assert r_full.accepted, r_full.rejection

    pen_min = base.collateral_quote - r_min.state.collateral_quote
    pen_full = base.collateral_quote - r_full.state.collateral_quote

    # Minimal close leaves a (margin-compliant) residual position; full close flattens.
    assert r_min.state.position_base != 0
    assert r_full.state.position_base == 0

    # The deviation: full-close penalty strictly exceeds the minimal-close penalty.
    assert pen_full > pen_min
    assert (pen_min, pen_full) == (3334, 20000)          # exact integer witness
    assert pen_full - pen_min == 16666                    # extra extracted by oversizing

    # Conservation: every quote the liquidatee loses is gained by fee_pool/income.
    for base_s, res, pen in ((base, r_min, pen_min), (base, r_full, pen_full)):
        assert res.state.fee_pool_quote - base_s.fee_pool_quote == pen
        assert res.state.fee_income - base_s.fee_income == pen


def test_h_md_pt_006_guard_requires_residual_margin_not_just_nonneg_collateral() -> None:
    """Precise guard scope (corrects an overbroad reading): the guard does NOT
    accept every fraction with non-negative post-penalty collateral. One bps below
    the minimum, fraction f_min-1 leaves collateral non-negative yet is GUARD-
    REJECTED because the residual position still fails maintenance margin
    (guard_partial_liquidate lines 307-314). So the legal set is [f_min, BPS_SCALE]
    — fractions that flatten or restore margin — and the lever is "oversize above
    the minimum sufficient fraction", not "any fraction at all"."""
    base = _liquidatable_market()
    f_min = _auto_min(base)
    assert f_min >= 2
    below = f_min - 1

    # Below-min fraction: post-penalty collateral stays non-negative ...
    pen_below = partial_liq_penalty_capped(
        base.collateral_quote, _Q, below, _INDEX, _PEN_BPS, _MIN_NOTIONAL)
    assert base.collateral_quote - pen_below >= 0
    # ... but the residual position still FAILS maintenance margin ...
    rem_below = remaining_position_signed(_Q, below)
    assert rem_below != 0
    assert base.collateral_quote - pen_below < maint_margin_req(
        rem_below, _INDEX, _MAINT_BPS, _DEPEG_BPS)
    # ... so the REAL guard rejects it, while the minimal fraction is accepted.
    assert not guard_partial_liquidate(base, ActionParams(
        action=Action.PARTIAL_LIQUIDATE, fraction_bps=below, auth_ok=True))
    assert not _liq(base, below).accepted
    assert guard_partial_liquidate(base, ActionParams(
        action=Action.PARTIAL_LIQUIDATE, fraction_bps=f_min, auth_ok=True))


def test_h_md_pt_006_auto_min_fraction_is_tight_and_restores_margin() -> None:
    """Non-vacuity for "minimal restores margin": the auto-computed fraction
    restores maintenance margin on the residual (collateral_after >= maint_req),
    and exactly one bps LESS does not — so the minimal sufficient fraction is
    tight, and the cheaper alternative to full-close genuinely exists."""
    base = _liquidatable_market()
    f_min = _auto_min(base)

    def _restores(frac: int) -> bool:
        rem = remaining_position_signed(_Q, frac)
        pen = partial_liq_penalty_capped(
            base.collateral_quote, _Q, frac, _INDEX, _PEN_BPS, _MIN_NOTIONAL)
        coll_after = base.collateral_quote - pen
        if rem == 0:
            return True
        return coll_after >= maint_margin_req(rem, _INDEX, _MAINT_BPS, _DEPEG_BPS)

    assert _restores(f_min)                # minimal fraction restores margin
    assert f_min >= 2 and not _restores(f_min - 1)   # ... and is tight (one bps less fails)

    # The reducer at f_min indeed lands margin-compliant (engine post-state).
    r_min = _liq(base, f_min)
    assert r_min.accepted, r_min.rejection
    rem = r_min.state.position_base
    assert rem != 0
    assert r_min.state.collateral_quote >= maint_margin_req(
        rem, _INDEX, _MAINT_BPS, _DEPEG_BPS)


def test_h_md_pt_006_penalty_transfer_monotonic_nondecreasing_in_fraction() -> None:
    """The lever's magnitude is monotone in the liquidator's choice: across the
    guard-legal fraction range [f_min, BPS_SCALE], penalty is non-decreasing in
    fraction_bps, equals the fee_pool transfer exactly (conservation), and the
    liquidatee's collateral is non-increasing. So a larger chosen fraction never
    reduces — and generically increases — the value transferred away."""
    base = _liquidatable_market()
    f_min = _auto_min(base)

    prev_pen: int | None = None
    prev_coll: int | None = None
    saw_strict_increase = False
    saw_endpoint = False
    for frac in range(f_min, BPS_SCALE + 1):          # EXHAUSTIVE over the legal range
        r = _liq(base, frac)
        assert r.accepted, (frac, r.rejection)        # all of [f_min, BPS_SCALE] is legal
        pen = base.collateral_quote - r.state.collateral_quote
        transfer = r.state.fee_pool_quote - base.fee_pool_quote
        assert pen == transfer                        # conservation at every fraction
        if prev_pen is not None:
            assert pen >= prev_pen                     # penalty non-decreasing
            assert r.state.collateral_quote <= prev_coll  # collateral non-increasing
            if pen > prev_pen:                         # strict increase between REAL adjacent samples
                saw_strict_increase = True
        prev_pen = pen
        prev_coll = r.state.collateral_quote
        if frac == BPS_SCALE:
            saw_endpoint = True

    assert saw_endpoint                               # endpoint BPS_SCALE included
    assert saw_strict_increase                        # the lever genuinely moves value
    assert prev_pen == 20000                          # full-close penalty at the endpoint
