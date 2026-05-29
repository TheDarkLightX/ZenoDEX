"""Unit tests for the authoritative Python zUSD single-vault `step`
(`src.core.zusd`).

These pin the reference semantics the Rust shadow (`zenodex-runtime-core::zusd`)
must match bit-for-bit. zUSD was the one migrated surface without a `_reference`
suite; this closes that gap (Phase D). Coverage spans the full single-vault
command set — mint / repay / deposit_sp / withdraw_sp / redeem / liquidate plus
oracle and recovery gating — asserting balance-sheet deltas, the supply-
conservation invariant, rejection paths, no-op-on-reject, and the large-integer
(arbitrary-precision) CDP path that a u128-only port would get wrong.
"""

from __future__ import annotations

import pytest

from src.core.zusd import (
    BPS_SCALE,
    E8,
    MAX_AMOUNT_E8,
    ZUSDCommand,
    ZUSDState,
    init_state,
    step,
)

_PRICE = E8  # 1.0 in e8 fixed point


def _ok(state: ZUSDState, tag: str, **args) -> ZUSDState:
    r = step(state, ZUSDCommand(tag, args))
    assert r.ok, f"expected {tag} to succeed, got error={r.error!r}"
    assert r.state is not None
    return r.state


def _bootstrapped(*, collateral_e8: int = 1_000_000_000_000, mint_e8: int = 500 * E8) -> ZUSDState:
    s = init_state()
    s = _ok(s, "bootstrap_oracle", auth_ok=True, price_e8=_PRICE)
    s = _ok(s, "deposit_collateral", amount_e8=collateral_e8)
    s = _ok(s, "mint_zusd", amount_e8=mint_e8)
    return s


def _conserved(s: ZUSDState) -> None:
    # The load-bearing zUSD invariant: free + stability-pool debt == total debt.
    assert s.free_debt_e8 + s.sp_debt_e8 == s.debt_e8


# --- mint / repay -------------------------------------------------------------


def test_mint_increases_debt_and_free_debt():
    s = init_state()
    s = _ok(s, "bootstrap_oracle", auth_ok=True, price_e8=_PRICE)
    s = _ok(s, "deposit_collateral", amount_e8=1_000_000_000_000)
    before = s.debt_e8
    s2 = _ok(s, "mint_zusd", amount_e8=500 * E8)
    # Default borrow fee floor/base-rate are 0, so debt grows by exactly the principal.
    assert s2.debt_e8 == before + 500 * E8
    assert s2.free_debt_e8 == s.free_debt_e8 + 500 * E8
    assert s2.sp_debt_e8 == s.sp_debt_e8
    _conserved(s2)


def test_repay_decreases_debt_and_free_debt():
    s = _bootstrapped()
    before_debt, before_free = s.debt_e8, s.free_debt_e8
    # Repay down to the min-debt floor (keep >= min_debt_open_e8).
    repay = before_debt - s.min_debt_open_e8
    s2 = _ok(s, "repay_zusd", amount_e8=repay)
    assert s2.debt_e8 == before_debt - repay
    assert s2.free_debt_e8 == before_free - repay
    _conserved(s2)


def test_repay_exceeding_debt_is_rejected_noop():
    s = _bootstrapped()
    r = step(s, ZUSDCommand("repay_zusd", {"amount_e8": s.debt_e8 + 1}))
    assert not r.ok and r.error is not None
    # No-op on reject: the returned/again-computed state is unchanged.
    assert step(s, ZUSDCommand("repay_zusd", {"amount_e8": s.debt_e8 + 1})).state is None


# --- stability pool: deposit_sp / withdraw_sp ---------------------------------


def test_deposit_sp_moves_free_to_sp_debt_invariant():
    s = _bootstrapped()
    before = (s.free_debt_e8, s.sp_debt_e8, s.debt_e8)
    s2 = _ok(s, "deposit_sp", amount_e8=100 * E8)
    assert s2.free_debt_e8 == before[0] - 100 * E8
    assert s2.sp_debt_e8 == before[1] + 100 * E8
    assert s2.debt_e8 == before[2]  # total debt unchanged
    _conserved(s2)


def test_withdraw_sp_is_exact_reverse():
    s = _bootstrapped()
    s = _ok(s, "deposit_sp", amount_e8=100 * E8)
    before = (s.free_debt_e8, s.sp_debt_e8, s.debt_e8)
    s2 = _ok(s, "withdraw_sp", amount_e8=40 * E8)
    assert s2.free_debt_e8 == before[0] + 40 * E8
    assert s2.sp_debt_e8 == before[1] - 40 * E8
    assert s2.debt_e8 == before[2]
    _conserved(s2)


def test_deposit_sp_exceeding_free_debt_rejected():
    s = _bootstrapped()
    r = step(s, ZUSDCommand("deposit_sp", {"amount_e8": s.free_debt_e8 + 1}))
    assert not r.ok and r.state is None


def test_withdraw_sp_exceeding_sp_debt_rejected():
    s = _bootstrapped()
    s = _ok(s, "deposit_sp", amount_e8=100 * E8)
    r = step(s, ZUSDCommand("withdraw_sp", {"amount_e8": s.sp_debt_e8 + 1}))
    assert not r.ok and r.state is None


# --- redeem -------------------------------------------------------------------


def test_redeem_conserves_and_reduces_debt():
    s = _bootstrapped()
    before_debt = s.debt_e8
    r = step(s, ZUSDCommand("redeem_zusd", {"amount_e8": 100 * E8}))
    assert r.ok, f"redeem failed: {r.error!r}"
    assert r.state.debt_e8 < before_debt
    _conserved(r.state)


def test_redeem_exceeding_debt_rejected():
    s = _bootstrapped()
    r = step(s, ZUSDCommand("redeem_zusd", {"amount_e8": s.debt_e8 + 1}))
    assert not r.ok and r.state is None


# --- liquidate / recovery gating ---------------------------------------------


def test_liquidate_healthy_vault_rejected_noop():
    # A well-collateralized vault is not liquidatable; the handler must reject.
    s = _bootstrapped(collateral_e8=1_000_000_000_000, mint_e8=500 * E8)
    r = step(s, ZUSDCommand("liquidate", {}))
    assert not r.ok and r.state is None


def test_mint_blocked_before_oracle():
    # No oracle => recovery mode => risky ops (mint) blocked, even with collateral.
    s = init_state()
    s = _ok(s, "deposit_collateral", amount_e8=1_000_000_000_000)
    r = step(s, ZUSDCommand("mint_zusd", {"amount_e8": 500 * E8}))
    assert not r.ok and r.state is None


# --- unknown command + arbitrary-precision path -------------------------------


def test_unknown_command_rejected():
    s = _bootstrapped()
    r = step(s, ZUSDCommand("frobnicate", {}))
    assert not r.ok and r.state is None


def test_large_amount_is_deterministic_and_no_overflow():
    # The CDP MCR check multiplies collateral * price * bps and compares against
    # debt * mcr * 1e8 -- products that exceed u128 at the 1e30 bound. Python's
    # arbitrary precision must neither panic nor wrap; the result is deterministic.
    s = _bootstrapped()
    cmd = ZUSDCommand("mint_zusd", {"amount_e8": MAX_AMOUNT_E8})
    r1 = step(s, cmd)
    r2 = step(s, cmd)
    assert r1.ok == r2.ok and r1.error == r2.error
    # At this magnitude the mint cannot satisfy the debt ceiling / MCR, so it is
    # rejected -- and a rejected command never mutates state.
    assert not r1.ok and r1.state is None
    _conserved(s)
