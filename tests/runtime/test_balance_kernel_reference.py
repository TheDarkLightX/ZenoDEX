"""Unit tests for the authoritative Python balance-accounting kernel."""

from __future__ import annotations

import pytest

import src.core.balance_kernel as balance_kernel
from src.core.balance_kernel import (
    MAX_BALANCE,
    BalanceAccepted,
    BalanceState,
    credit,
    transfer,
)


def pk(tag: int) -> str:
    return "0x" + f"{tag:02x}" * 48


def asset(tag: int) -> str:
    return "0x" + f"{tag:02x}" * 32


A, B, C = pk(0x11), pk(0x22), pk(0x33)
X, Y = asset(0xAA), asset(0xBB)


def _credit(state, recipient, a, amount):
    return credit(state=state, recipient=recipient, asset=a, amount=amount)


def _xfer(state, sender, recipient, a, amount):
    return transfer(state=state, sender=sender, recipient=recipient, asset=a, amount=amount)


def _fund(state, who, a, amount):
    res = _credit(state, who, a, amount)
    assert isinstance(res, BalanceAccepted)
    return res.state


# --- credit -------------------------------------------------------------------


def test_credit_funds_account():
    res = _credit(BalanceState(), A, X, 100)
    assert isinstance(res, BalanceAccepted)
    assert res.state.balance_of(A, X) == 100
    assert len(res.state.entries) == 1


def test_raw_and_upper_hex_match_runtime_canonicalization():
    raw_a = A[2:]
    upper_x = "0X" + X[2:].upper()
    spaced_b = f"  {B[2:].upper()}  "
    control_wrapped_c = f"\x1c{C}\x1f"
    prefixed = _credit(BalanceState(), A, X, 100)
    raw = _credit(BalanceState(), raw_a, upper_x, 100)
    spaced = _credit(BalanceState(), spaced_b, X, 100)
    control_wrapped = _credit(BalanceState(), control_wrapped_c, X, 100)
    assert isinstance(prefixed, BalanceAccepted)
    assert isinstance(raw, BalanceAccepted)
    assert isinstance(spaced, BalanceAccepted)
    assert isinstance(control_wrapped, BalanceAccepted)
    assert raw.receipt.recipient == A
    assert raw.receipt.asset == X
    assert spaced.receipt.recipient == B
    assert control_wrapped.receipt.recipient == C
    assert raw.receipt.receipt_hash() == prefixed.receipt.receipt_hash()
    assert raw.state.state_root() == prefixed.state.state_root()


def test_credit_rejections():
    assert _credit(BalanceState(), "0x11", X, 100).reason == "invalid_recipient"
    assert _credit(BalanceState(), A, "0x" + "aa" * 48, 100).reason == "invalid_asset"
    for bad in (0, -1, MAX_BALANCE + 1, True, 1.5):
        assert _credit(BalanceState(), A, X, bad).reason == "invalid_amount"


def test_canonical_pubkey_internal_fault_is_not_masked(monkeypatch):
    def broken_canonicalizer(*args, **kwargs):  # noqa: ANN002, ANN003, ARG001
        raise RuntimeError("injected pubkey canonicalizer fault")

    monkeypatch.setattr(balance_kernel, "canonical_hex_fixed_allow_0x", broken_canonicalizer)

    with pytest.raises(RuntimeError, match="injected pubkey canonicalizer fault"):
        _credit(BalanceState(), A, X, 100)


def test_canonical_asset_internal_fault_is_not_masked(monkeypatch):
    original_canonicalizer = balance_kernel.canonical_hex_fixed_allow_0x

    def broken_asset_canonicalizer(*args, **kwargs):  # noqa: ANN002, ANN003
        if kwargs.get("name") == "asset":
            raise RuntimeError("injected asset canonicalizer fault")
        return original_canonicalizer(*args, **kwargs)

    monkeypatch.setattr(balance_kernel, "canonical_hex_fixed_allow_0x", broken_asset_canonicalizer)

    with pytest.raises(RuntimeError, match="injected asset canonicalizer fault"):
        _credit(BalanceState(), A, X, 100)


def test_credit_overflow():
    state = _fund(BalanceState(), A, X, MAX_BALANCE)
    assert _credit(state, A, X, 1).reason == "balance_overflow"


# --- transfer -----------------------------------------------------------------


def test_transfer_moves_value_and_conserves_supply():
    state = _fund(BalanceState(), A, X, 100)
    res = _xfer(state, A, B, X, 30)
    assert isinstance(res, BalanceAccepted)
    assert res.state.balance_of(A, X) == 70
    assert res.state.balance_of(B, X) == 30
    # Supply of X is conserved.
    assert res.state.balance_of(A, X) + res.state.balance_of(B, X) == 100


def test_transfer_entire_balance_makes_sender_sparse():
    state = _fund(BalanceState(), A, X, 50)
    res = _xfer(state, A, B, X, 50)
    assert isinstance(res, BalanceAccepted)
    assert res.state.balance_of(A, X) == 0
    # Zero balance is not stored.
    assert all(e.pubkey != A for e in res.state.entries)
    assert res.state.balance_of(B, X) == 50


def test_transfer_insufficient_balance():
    state = _fund(BalanceState(), A, X, 70)
    assert _xfer(state, A, B, X, 100).reason == "insufficient_balance"


def test_transfer_self_rejected():
    state = _fund(BalanceState(), A, X, 100)
    assert _xfer(state, A, A, X, 10).reason == "self_transfer"


def test_transfer_validation_order_and_rejections():
    state = _fund(BalanceState(), A, X, 100)
    assert _xfer(state, "0x11", B, X, 10).reason == "invalid_sender"
    assert _xfer(state, A, "0x22", X, 10).reason == "invalid_recipient"
    assert _xfer(state, A, B, "0xbb", 10).reason == "invalid_asset"
    assert _xfer(state, A, B, X, 0).reason == "invalid_amount"
    # Bad sender wins over a bad nonce-equivalent (amount) — order check.
    assert _xfer(state, "0x11", B, X, 0).reason == "invalid_sender"


def test_transfer_overflow_on_recipient():
    state = _fund(BalanceState(), A, X, 10)
    state = _fund(state, B, X, MAX_BALANCE)
    assert _xfer(state, A, B, X, 5).reason == "balance_overflow"


def test_per_asset_isolation():
    state = _fund(BalanceState(), A, X, 100)
    state = _fund(state, A, Y, 100)
    res = _xfer(state, A, B, X, 40)
    assert isinstance(res, BalanceAccepted)
    # Asset Y balances are untouched by an asset-X transfer.
    assert res.state.balance_of(A, Y) == 100
    assert res.state.balance_of(B, Y) == 0


# --- hashing ------------------------------------------------------------------


def test_state_root_deterministic_and_sensitive():
    empty = BalanceState().state_root()
    assert empty == BalanceState().state_root()
    s = _fund(BalanceState(), A, X, 100)
    assert s.state_root() != empty
    assert s.state_root().startswith("0x")
    # Different amount -> different root.
    assert _fund(BalanceState(), A, X, 101).state_root() != s.state_root()
    # Same balances regardless of construction order -> same root.
    s1 = _fund(_fund(BalanceState(), A, X, 10), B, X, 20)
    s2 = _fund(_fund(BalanceState(), B, X, 20), A, X, 10)
    assert s1.state_root() == s2.state_root()


def test_receipt_hash_distinguishes_credit_and_transfer():
    state = _fund(BalanceState(), A, X, 100)
    cr = _credit(state, B, X, 10)
    tr = _xfer(state, A, B, X, 10)
    assert isinstance(cr, BalanceAccepted) and isinstance(tr, BalanceAccepted)
    # Same recipient/asset/amount, but credit != transfer.
    assert cr.receipt.receipt_hash() != tr.receipt.receipt_hash()
    assert tr.receipt.receipt_hash().startswith("0x")
    # Transfer hash is sensitive to sender.
    state2 = _fund(state, C, X, 100)
    tr2 = _xfer(state2, C, B, X, 10)
    assert tr.receipt.receipt_hash() != tr2.receipt.receipt_hash()
