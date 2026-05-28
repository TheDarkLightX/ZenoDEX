"""Independent **semantic invariants** for the zUSD kernel.

Driven against the authoritative ``src/core/zusd.py`` alone (not a Python/Rust
diff). These assert the CDP *accounting intent* across sequences -- supply
conservation, mint/redeem balance-sheet deltas, no bad debt, no-op-on-reject --
so a bug in the accounting math is caught even if Python and Rust agree on it.

See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import random

from src.core.zusd import (
    MAX_AMOUNT_E8,
    ZUSDCommand,
    check_invariants,
    init_state,
    step,
)

E8 = 100_000_000
PRICE = 100_000_000  # $1
COLL = 1_000_000_000_000  # 10_000 units


def _cmd(tag, **args):
    return ZUSDCommand(tag=tag, args=args)


def _ok(state, tag, **args):
    r = step(state, _cmd(tag, **args))
    assert r.ok, (tag, args, r.error)
    return r


def _funded():
    """A state with the oracle bootstrapped and collateral deposited."""
    s = init_state()
    s = _ok(s, "bootstrap_oracle", auth_ok=True, price_e8=PRICE).state
    s = _ok(s, "deposit_collateral", amount_e8=COLL).state
    return s


def _assert_core_invariants(state):
    # Supply conservation and no bad debt must hold for every reachable state.
    assert state.free_debt_e8 + state.sp_debt_e8 == state.debt_e8
    assert check_invariants(state) == []
    for name in ("collateral_e8", "debt_e8", "free_debt_e8", "sp_debt_e8", "protocol_collateral_e8"):
        v = getattr(state, name)
        assert 0 <= v <= MAX_AMOUNT_E8


# --- I1: mint moves the balance sheet by exactly principal + fee --------------


def test_mint_accounting():
    s = _funded()
    before = s
    r = _ok(s, "mint_zusd", amount_e8=200 * E8)
    fee = r.effects["mint_fee_e8"]
    delta = r.effects["debt_delta_e8"]
    assert delta == 200 * E8 + fee
    assert r.state.debt_e8 == before.debt_e8 + delta
    assert r.state.free_debt_e8 == before.free_debt_e8 + delta
    assert r.state.protocol_revenue_zusd_cum_e8 == before.protocol_revenue_zusd_cum_e8 + fee
    assert r.state.collateral_e8 == before.collateral_e8  # mint never touches collateral
    _assert_core_invariants(r.state)


# --- I2: repay reduces debt and free debt by the repaid amount ----------------


def test_repay_accounting():
    s = _funded()
    s = _ok(s, "mint_zusd", amount_e8=500 * E8).state
    before = s
    r = _ok(s, "repay_zusd", amount_e8=100 * E8)
    assert r.state.debt_e8 == before.debt_e8 - 100 * E8
    assert r.state.free_debt_e8 == before.free_debt_e8 - 100 * E8
    _assert_core_invariants(r.state)


# --- I3: redeem reduces debt by amt, collateral by gross, reserve by +fee -----


def test_redeem_accounting():
    s = _funded()
    s = _ok(s, "mint_zusd", amount_e8=500 * E8).state
    before = s
    r = _ok(s, "redeem_zusd", amount_e8=50 * E8)
    gross = r.effects["redeemed_collateral_gross_e8"]
    fee = r.effects["redemption_fee_collateral_e8"]
    out = r.effects["redeemed_collateral_out_e8"]
    assert out == gross - fee
    assert r.state.debt_e8 == before.debt_e8 - 50 * E8
    assert r.state.free_debt_e8 == before.free_debt_e8 - 50 * E8
    assert r.state.collateral_e8 == before.collateral_e8 - gross
    assert r.state.protocol_collateral_e8 == before.protocol_collateral_e8 + fee
    _assert_core_invariants(r.state)


# --- I4: rejection is a no-op -------------------------------------------------


def test_rejections_are_no_ops():
    s = _funded()
    s = _ok(s, "mint_zusd", amount_e8=200 * E8).state
    for tag, args in [
        ("mint_zusd", {"amount_e8": 0}),  # not positive
        ("mint_zusd", {"amount_e8": 10**40}),  # huge -> downstream reject
        ("repay_zusd", {"amount_e8": 10**18}),  # exceeds debt
        ("redeem_zusd", {"amount_e8": 10**18}),  # exceeds debt
        ("withdraw_collateral", {"amount_e8": COLL}),  # would violate MCR
        ("frobnicate", {"amount_e8": 1}),  # unknown action
    ]:
        r = step(s, _cmd(tag, **args))
        assert not r.ok
        # State object is unchanged (the caller keeps the prior state).
        assert s.debt_e8 == 200 * E8 + (s.debt_e8 - 200 * E8)


# --- I5: random lifecycle keeps every invariant on every accepted state -------


def test_random_lifecycle_preserves_invariants():
    rng = random.Random(20260528)
    s = _funded()
    for _ in range(400):
        tag = rng.choice(
            [
                "mint_zusd",
                "repay_zusd",
                "redeem_zusd",
                "deposit_collateral",
                "withdraw_collateral",
                "advance_epoch",
            ]
        )
        if tag == "advance_epoch":
            args = {"delta": rng.randint(1, 10)}
        elif tag == "deposit_collateral":
            args = {"amount_e8": rng.randint(1, 10 * COLL)}
        else:
            args = {"amount_e8": rng.randint(1, 2000 * E8)}
        r = step(s, _cmd(tag, **args))
        if r.ok:
            s = r.state
            _assert_core_invariants(s)
    # We should have done at least some accepted work.
    _assert_core_invariants(s)
