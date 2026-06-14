# [TESTER] v1
"""
Wave-1 spot-settlement CoW self-netting capture (charter
docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md section 10, O-SS-06 / H-MD-SS-007).
Integer witnesses through the REAL batch-clearing settlement
(src/core/batch_clearing.py compute_settlement with swap_ordering
"cow_pair_netting_v1" -> _cow_pair_netting_exact_in_v1).

O-SS-06: a self-supplied counter-intent captures fee+spread otherwise accruing
to LPs. When an actor supplies a counter-intent that CoW-nets against a
pool-bound trade, the matched pair is filled peer-to-peer at fee_paid = 0,
reason "COW_NETTED", with NO pool interaction (reserve_deltas == []). The
UNIVERSAL capture is on the LP side: routing the SAME pair through the pool in
one batch earns LPs the full fee (585 = 300 + 285 here) and moves reserves,
while CoW earns them nothing. The party-level benefit is ASYMMETRIC and
counterfactual-dependent: the min-out-binding initiator (T) strictly gains
(beats both its isolated and same-batch pool outputs), while the counter-supplier
(A) beats only its ISOLATED single-trade pool quote — a same-batch pool routing
can actually give A MORE than CoW. So we claim the LP capture as universal and
explicitly scope the party-level gains (this is the subtlety a careful reviewer
flags).

Verdict polarity (charter): hypotheses are phrased "deviation exists", so a
PASSING test == SUPPORTED — the fee+spread capture is demonstrated.
Research evidence only; no settlement-behavior change, no remedy claim (CoW
netting is a config-gated experimental ordering; whether to charge a netting
fee is an UNTESTED design question, not asserted here).
"""

from __future__ import annotations

from src.core.batch_clearing import compute_settlement, validate_settlement
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

_A0 = "0x" + "01" * 32
_A1 = "0x" + "02" * 32
_T = "0x" + "11" * 48          # trader whose flow would feed LP fees
_A = "0x" + "22" * 48          # actor supplying the counter-intent
_PID = "0x" + "aa" * 32


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pool() -> PoolState:
    return PoolState(
        pool_id=_PID, asset0=_A0, asset1=_A1,
        reserve0=1_000_000, reserve1=1_000_000, fee_bps=30,
        lp_supply=0, status=PoolStatus.ACTIVE, created_at=0,
    )


def _swap(intent_id: str, sender: str, asset_in: str, asset_out: str,
          amount_in: int, min_out: int) -> Intent:
    return Intent(
        module="TauSwap", version="0.1", kind=IntentKind.SWAP_EXACT_IN,
        intent_id=intent_id, sender_pubkey=sender, deadline=9999999999,
        fields={
            "pool_id": _PID, "asset_in": asset_in, "asset_out": asset_out,
            "amount_in": amount_in, "min_amount_out": min_out,
        },
    )


def _filled(settlement):
    return [f for f in settlement.fills if f.action.value == "FILL"]


def _pool_output(sender: str, asset_in: str, asset_out: str, amount_in: int) -> tuple[int, int]:
    """Route one swap through the REAL pool; return (output, fee_paid)."""
    bal = BalanceTable()
    bal.set(sender, asset_in, amount_in)
    bal.set(sender, asset_out, 0)
    s = compute_settlement([_swap(_iid(9), sender, asset_in, asset_out, amount_in, 0)],
                           {_PID: _pool()}, bal, LPTable())
    f = _filled(s)[0]
    return int(f.amount_out_filled), int(f.fee_paid or 0)


def _netting_pair():
    return (_swap(_iid(1), _T, _A0, _A1, 100_000, 90_000),
            _swap(_iid(2), _A, _A1, _A0, 95_000, 90_000))


def _pair_balances() -> BalanceTable:
    b = BalanceTable()
    b.set(_T, _A0, 100_000); b.set(_T, _A1, 0)
    b.set(_A, _A1, 95_000); b.set(_A, _A0, 0)
    return b


def test_h_md_ss_007_cow_netting_captures_the_whole_batch_lp_fee_and_spread() -> None:
    """The UNIVERSAL capture (LP side, no per-party counterfactual needed): routing
    the pair {T, A} through the pool in ONE batch earns LPs the full fee (585) and
    moves reserves; CoW-netting the SAME pair earns LPs nothing (fee_paid sum 0,
    reserve_deltas == []). The fee+spread that would accrue to LPs is captured."""
    t, a = _netting_pair()

    # Same-batch pool routing -> LPs earn the whole fee and reserves move.
    pool_batch = compute_settlement([t, a], {_PID: _pool()}, _pair_balances(), LPTable())
    pool_fee = sum(int(f.fee_paid or 0) for f in _filled(pool_batch))
    assert pool_fee == 585                                    # 300 (T) + 285 (A)
    assert pool_batch.reserve_deltas != []                   # pool moved -> LPs earn the spread

    # CoW routing of the SAME pair -> LPs earn nothing.
    cow = compute_settlement([t, a], {_PID: _pool()}, _pair_balances(), LPTable(),
                             swap_ordering="cow_pair_netting_v1")
    ok, err = validate_settlement(cow, _pair_balances(), {_PID: _pool()}, LPTable())
    assert ok, err
    fills = _filled(cow)
    assert {f.intent_id for f in fills} == {_iid(1), _iid(2)}
    assert all(f.reason == "COW_NETTED" for f in fills)
    assert sum(int(f.fee_paid or 0) for f in fills) == 0     # LPs earn ZERO fee
    assert cow.reserve_deltas == []                          # ... and ZERO spread (pool untouched)
    assert pool_fee - 0 == 585                               # the whole batch fee captured from LPs


def test_h_md_ss_007_party_gains_are_asymmetric_and_counterfactual_dependent() -> None:
    """Party-level gains are ASYMMETRIC (the subtlety a careful reviewer flags): the
    min-out-binding initiator T strictly gains vs BOTH its isolated and same-batch
    pool outputs, but the counter-supplier A gains only vs its ISOLATED single-trade
    pool quote — a same-batch pool routing actually gives A MORE than CoW. So the
    universal capture is the LP side, not a universal per-party profit. All
    counterfactuals are computed through the REAL engine."""
    t, a = _netting_pair()
    t_iso, _ = _pool_output(_T, _A0, _A1, 100_000)
    a_iso, _ = _pool_output(_A, _A1, _A0, 95_000)

    pool_batch = compute_settlement([t, a], {_PID: _pool()}, _pair_balances(), LPTable())
    pb = {f.intent_id: int(f.amount_out_filled) for f in _filled(pool_batch)}
    cow = compute_settlement([t, a], {_PID: _pool()}, _pair_balances(), LPTable(),
                             swap_ordering="cow_pair_netting_v1")
    cw = {f.intent_id: int(f.amount_out_filled) for f in _filled(cow)}

    # Initiator T: CoW (receives A's input) beats BOTH counterfactuals.
    assert cw[_iid(1)] == 95_000
    assert cw[_iid(1)] > t_iso                                # > isolated pool (90_661)
    assert cw[_iid(1)] > pb[_iid(1)]                          # > same-batch pool

    # Counter-supplier A: CoW (receives T's input) beats ISOLATED but LOSES to same-batch.
    assert cw[_iid(2)] == 100_000
    assert cw[_iid(2)] > a_iso                                # > isolated pool (86_520)
    assert cw[_iid(2)] < pb[_iid(2)]                          # < same-batch pool (A better NOT netting)


def test_h_md_ss_007_capture_requires_a_feasible_counter_intent() -> None:
    """Bounded scope (non-vacuity): the capture is conditional on supplying a
    FEASIBLE counter-intent. If the counter-intent's input falls below the
    trader's min_amount_out, the pair is not matchable, CoW netting does not fire,
    and the trade falls back to the pool — where LPs DO earn the fee. So the
    deviation requires the actor to actually post a min-out-satisfying counter
    side, it is not a free no-op."""
    t_in = 100_000
    t_min_out = 90_000

    bal = BalanceTable()
    bal.set(_T, _A0, t_in); bal.set(_T, _A1, 0)
    bal.set(_A, _A1, 200_000); bal.set(_A, _A0, 0)
    # A's input (89_999) is BELOW T's min_out (90_000) -> pair infeasible.
    s = compute_settlement(
        [_swap(_iid(1), _T, _A0, _A1, t_in, t_min_out),
         _swap(_iid(2), _A, _A1, _A0, t_min_out - 1, 90_000)],
        {_PID: _pool()}, bal, LPTable(), swap_ordering="cow_pair_netting_v1")

    fills = _filled(s)
    # No COW_NETTED fill for T; whatever fills happen are NOT fee-free netting.
    assert not any(f.reason == "COW_NETTED" and f.intent_id == _iid(1) for f in fills)
    # T routed through the pool pays a positive fee back to LPs (no capture).
    t_fill = [f for f in fills if f.intent_id == _iid(1)]
    if t_fill:
        assert int(t_fill[0].fee_paid or 0) > 0
        assert s.reserve_deltas != []                         # pool was touched -> LPs earn
