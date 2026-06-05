"""PR-gated binding: the LIVE coupled DEX transition (dex.step / step_with_candidate_settlement)
ATOMICALLY couples the per-sender nonce advance to settlement success — the running_impl evidence
for the nonces surface.

The nonce GATE (src/state/nonces.py::validate_and_apply_intent_nonce_batch) only STAGES `next_nonces`.
The live AUTHORITY fact, which the existing gate-only bindings do not exercise, is in
src/core/dex.py: on ANY reject — a nonce-policy reject (step:231) OR a settlement-VALIDATION failure
(_validate_and_apply_settlement:132) — `step` returns `DexStepResult(ok=False, state=None)`, so the
staged nonce advance is DISCARDED and the caller's prior `state.nonces` stays authoritative. Only on
accept does `state.nonces` advance (to next_nonces) AND the settlement apply.

This drives the COUPLED transition over real scenarios and asserts, against an INDEPENDENT Python
oracle (expected_next_last recomputed here, never the gate re-imported):
  * accept  => ok=True, per-sender nonce advanced to last+count, settlement applied (state mutated);
  * settlement-reject (valid nonces, invalid settlement) => ok=False, state is None, nonces UNCHANGED;
  * nonce-reject (gap/stale) => ok=False, state is None, nonces UNCHANGED.

Teeth: monkeypatch dex._validate_and_apply_settlement to LEAK `next_nonces` on a settlement reject;
the reject-atomicity assertions (ok=False AND nonces unchanged) must then FAIL — proving the binding
observes the coupled-transition atomicity, not just the gate's internal return.
"""

from __future__ import annotations

import dataclasses

import pytest

import src.core.dex as dex
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexConfig, DexState, step, step_with_candidate_settlement
from src.core.liquidity import create_pool
from src.core.settlement import BalanceDelta
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind

A0 = "0x" + "01" * 32
A1 = "0x" + "02" * 32
SENDER = "0x" + "11" * 48
SENDER_B = "0x" + "33" * 48
LP_LOCK = "0x" + "00" * 48


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _state_with_pool() -> tuple[DexState, str]:
    pool_id, pool, lp_minted = create_pool(
        asset0=A0, asset1=A1, amount0=2_000_000, amount1=2_000_000, fee_bps=30, creator_pubkey=SENDER
    )
    balances = BalanceTable()
    for pk in (SENDER, SENDER_B):
        balances.set(pk, A0, 10_000_000)
        balances.set(pk, A1, 10_000_000)
    lp = LPTable()
    lp.set(SENDER, pool_id, lp_minted)
    lp.set(LP_LOCK, pool_id, pool.lp_supply - lp_minted)
    # DexState.nonces defaults to an empty NonceTable (last=0 for every sender).
    return DexState(balances=balances, pools={pool_id: pool}, lp_balances=lp), pool_id


def _swap_intent(sender: str, nonce: int, iid: int, pool_id: str, amount_in: int = 50_000) -> Intent:
    return Intent(
        module="TauSwap", version="0.1", kind=IntentKind.SWAP_EXACT_IN, intent_id=_iid(iid),
        sender_pubkey=sender, deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": A0, "asset_out": A1,
                "amount_in": amount_in, "min_amount_out": 1, "nonce": nonce},
    )


# --- INDEPENDENT oracle (transcribed, not re-imported) ---
def _expected_next_last(last: int, nonces_for_sender: list[int]) -> int | None:
    """Accept iff the sorted nonces are exactly last+1..last+k; then next_last = last+k. Else None
    (reject => no advance). A few lines of arithmetic, NOT a call into the live gate."""
    s = sorted(nonces_for_sender)
    if s != list(range(last + 1, last + 1 + len(s))):
        return None
    return last + len(s)


def _assert_reject_discards_nonce_state(
    result: dex.DexStepResult,
    state: DexState,
    sender: str,
    before_last: int,
) -> None:
    # REVIEW [B+ -> A-]: Claude's first teeth check manually asserted the leak
    # inside the mutation test. Reuse one helper for all reject cases so the
    # mutation proves the same release-load-bearing atomicity contract: reject
    # results must not return a staged state, and the caller's committed nonce
    # table remains unchanged.
    assert not result.ok
    assert result.state is None, "reject must not leak an advanced-nonce state"
    assert state.nonces.get_last(sender) == before_last, "caller nonce table must remain authoritative"


def test_accept_advances_nonce_and_applies_settlement() -> None:
    state, pool_id = _state_with_pool()
    pre_last = state.nonces.get_last(SENDER)
    pre_a1 = state.balances.get(SENDER, A1)
    intents = [_swap_intent(SENDER, nonce=pre_last + 1, iid=10, pool_id=pool_id)]

    result = step(DexConfig(), state, intents)

    assert result.ok, result.error
    assert result.state is not None
    exp = _expected_next_last(pre_last, [pre_last + 1])
    assert exp is not None and result.state.nonces.get_last(SENDER) == exp
    # settlement actually applied (received some A1)
    assert result.state.balances.get(SENDER, A1) > pre_a1


def test_multi_sender_contiguous_batch_advances_each() -> None:
    state, pool_id = _state_with_pool()
    intents = [
        _swap_intent(SENDER, nonce=1, iid=20, pool_id=pool_id),
        _swap_intent(SENDER_B, nonce=1, iid=21, pool_id=pool_id),
    ]
    result = step(DexConfig(), state, intents)
    assert result.ok, result.error
    assert result.state.nonces.get_last(SENDER) == _expected_next_last(0, [1])
    assert result.state.nonces.get_last(SENDER_B) == _expected_next_last(0, [1])


def test_settlement_reject_does_not_advance_nonce() -> None:
    # valid nonce, but an INVALID (non-conserving) candidate settlement -> nonce accepts, settlement
    # rejects -> ok=False, state None, nonce UNCHANGED (the coupled atomicity).
    state, pool_id = _state_with_pool()
    intents = [_swap_intent(SENDER, nonce=1, iid=30, pool_id=pool_id)]
    good = compute_settlement(intents=intents, pools=state.pools, balances=state.balances,
                              lp_balances=state.lp_balances)
    tampered = dataclasses.replace(
        good,
        balance_deltas=tuple(good.balance_deltas)
        + (BalanceDelta(pubkey=SENDER_B, asset=A1, delta_add=1_000_000, delta_sub=0),),
    )
    before_last = state.nonces.get_last(SENDER)
    result = step_with_candidate_settlement(DexConfig(), state, intents, candidate_settlement=tampered)
    _assert_reject_discards_nonce_state(result, state, SENDER, before_last)


def test_nonce_gap_reject_does_not_advance() -> None:
    state, pool_id = _state_with_pool()
    intents = [_swap_intent(SENDER, nonce=5, iid=40, pool_id=pool_id)]  # gap from last=0
    assert _expected_next_last(0, [5]) is None  # oracle: reject
    before_last = state.nonces.get_last(SENDER)
    result = step(DexConfig(), state, intents)
    _assert_reject_discards_nonce_state(result, state, SENDER, before_last)


def test_teeth_leaked_nonce_on_settlement_reject_is_caught(monkeypatch) -> None:
    # Monkeypatch the live coupled apply to LEAK next_nonces on a settlement reject, then prove the
    # reject-atomicity check catches it (a gate-only binding would not — the gate returns no state).
    state, pool_id = _state_with_pool()
    intents = [_swap_intent(SENDER, nonce=1, iid=50, pool_id=pool_id)]
    good = compute_settlement(intents=intents, pools=state.pools, balances=state.balances,
                              lp_balances=state.lp_balances)
    tampered = dataclasses.replace(
        good,
        balance_deltas=tuple(good.balance_deltas)
        + (BalanceDelta(pubkey=SENDER_B, asset=A1, delta_add=1_000_000, delta_sub=0),),
    )

    real = dex._validate_and_apply_settlement

    def leaky(config, st, ins, settlement, next_nonces):
        res = real(config, st, ins, settlement, next_nonces)
        if not res.ok:
            # LEAK: persist the gate-advanced nonce despite the settlement reject
            return dex.DexStepResult(ok=False, error=res.error,
                                     state=dataclasses.replace(st, nonces=next_nonces))
        return res

    monkeypatch.setattr(dex, "_validate_and_apply_settlement", leaky)
    before_last = state.nonces.get_last(SENDER)
    result = step_with_candidate_settlement(DexConfig(), state, intents, candidate_settlement=tampered)
    # the leak: state is now present with an advanced nonce. The atomicity assertions must catch it.
    leaked = result.state is not None and result.state.nonces.get_last(SENDER) == 1
    assert leaked, "teeth setup: the mutation must produce the leak the real code forbids"
    with pytest.raises(AssertionError, match="advanced-nonce state"):
        _assert_reject_discards_nonce_state(result, state, SENDER, before_last)
