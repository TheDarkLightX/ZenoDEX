"""Unit tests for the authoritative Python replay/idempotency guard."""

from __future__ import annotations

import pytest

import src.core.replay_guard as replay_guard
from src.core.replay_guard import (
    U32_MAX,
    AdmitAccepted,
    AdmitRejected,
    ReplayGuardState,
    admit,
)


def sender(tag: int) -> str:
    """A valid 48-byte (96 hex char) sender pubkey for tests."""
    return "0x" + f"{tag:02x}" * 48


A = sender(0x11)
B = sender(0x22)


def _admit(state, s, n):
    return admit(state=state, sender=s, nonce=n)


# --- Happy path ---------------------------------------------------------------


def test_sequential_nonces_accepted_and_state_advances():
    state = ReplayGuardState()
    for n in (1, 2, 3, 4):
        result = _admit(state, A, n)
        assert isinstance(result, AdmitAccepted), (n, result)
        assert result.receipt.nonce == n
        assert result.receipt.prev_nonce == n - 1
        state = result.state
        assert state.last_for(A) == n


def test_receipt_hash_deterministic_and_sensitive():
    s0 = ReplayGuardState()
    r1 = _admit(s0, A, 1)
    r2 = _admit(s0, A, 1)
    assert isinstance(r1, AdmitAccepted) and isinstance(r2, AdmitAccepted)
    assert r1.receipt.receipt_hash() == r2.receipt.receipt_hash()
    assert r1.receipt.receipt_hash().startswith("0x")
    # Different sender or nonce must change the hash.
    assert r1.receipt.receipt_hash() != _admit(s0, B, 1).receipt.receipt_hash()
    after1 = r1.state
    assert r1.receipt.receipt_hash() != _admit(after1, A, 2).receipt.receipt_hash()


def test_raw_hex_sender_matches_nonce_table_canonicalization():
    raw = A[2:]
    upper_prefix = "0X" + A[2:]
    spaced = f"  {upper_prefix}  "
    info_sep_wrapped = f"\u001c{upper_prefix}\u001f"
    prefixed = _admit(ReplayGuardState(), A, 1)
    raw_result = _admit(ReplayGuardState(), raw, 1)
    upper_result = _admit(ReplayGuardState(), upper_prefix, 1)
    spaced_result = _admit(ReplayGuardState(), spaced, 1)
    info_sep_result = _admit(ReplayGuardState(), info_sep_wrapped, 1)
    assert isinstance(prefixed, AdmitAccepted)
    assert isinstance(raw_result, AdmitAccepted)
    assert isinstance(upper_result, AdmitAccepted)
    assert isinstance(spaced_result, AdmitAccepted)
    assert isinstance(info_sep_result, AdmitAccepted)
    assert raw_result.receipt.sender == A
    assert upper_result.receipt.sender == A
    assert spaced_result.receipt.sender == A
    assert info_sep_result.receipt.sender == A
    assert raw_result.receipt.receipt_hash() == prefixed.receipt.receipt_hash()
    assert upper_result.receipt.receipt_hash() == prefixed.receipt.receipt_hash()
    assert spaced_result.receipt.receipt_hash() == prefixed.receipt.receipt_hash()
    assert info_sep_result.receipt.receipt_hash() == prefixed.receipt.receipt_hash()
    assert raw_result.state.state_root() == prefixed.state.state_root()
    assert upper_result.state.state_root() == prefixed.state.state_root()
    assert spaced_result.state.state_root() == prefixed.state.state_root()
    assert info_sep_result.state.state_root() == prefixed.state.state_root()


def test_state_root_deterministic_and_sensitive():
    empty = ReplayGuardState().state_root()
    assert empty == ReplayGuardState().state_root()
    s = _admit(ReplayGuardState(), A, 1).state
    assert s.state_root() != empty
    assert s.state_root().startswith("0x")


# --- Anti-replay / idempotency ------------------------------------------------


def test_duplicate_nonce_rejected_and_state_unchanged():
    state = _admit(ReplayGuardState(), A, 1).state
    root_before = state.state_root()
    result = _admit(state, A, 1)  # re-submit the just-accepted nonce
    assert isinstance(result, AdmitRejected)
    assert result.reason == "duplicate_nonce"
    # The caller keeps the prior state; nothing changed.
    assert state.state_root() == root_before


def test_stale_nonce_rejected():
    state = ReplayGuardState()
    for n in (1, 2, 3):
        state = _admit(state, A, n).state
    result = _admit(state, A, 2)  # replay of an older tx
    assert isinstance(result, AdmitRejected)
    assert result.reason == "stale_nonce"


def test_nonce_gap_rejected():
    # First nonce must be 1; jumping to 2 is a gap.
    result = _admit(ReplayGuardState(), A, 2)
    assert isinstance(result, AdmitRejected)
    assert result.reason == "nonce_gap"
    # A later gap too.
    state = _admit(ReplayGuardState(), A, 1).state
    assert isinstance(_admit(state, A, 3), AdmitRejected)
    assert _admit(state, A, 3).reason == "nonce_gap"


# --- Invalid input ------------------------------------------------------------


@pytest.mark.parametrize(
    "bad_sender",
    ["", "0x", "0xzz", "11" * 47, "11" * 49, "0x" + "11" * 47, "0x" + "11" * 49, 123],
)
def test_invalid_sender_rejected(bad_sender):
    result = admit(state=ReplayGuardState(), sender=bad_sender, nonce=1)
    assert isinstance(result, AdmitRejected)
    assert result.reason == "invalid_sender"


def test_canonical_sender_internal_fault_is_not_masked(monkeypatch):
    def broken_canonicalizer(*args, **kwargs):  # noqa: ANN002, ANN003, ARG001
        raise RuntimeError("injected canonicalizer fault")

    monkeypatch.setattr(replay_guard, "canonical_hex_fixed_allow_0x", broken_canonicalizer)

    with pytest.raises(RuntimeError, match="injected canonicalizer fault"):
        admit(state=ReplayGuardState(), sender=A, nonce=1)


@pytest.mark.parametrize("bad_nonce", [0, -1, U32_MAX + 1, True, 1.0, "1"])
def test_invalid_nonce_rejected(bad_nonce):
    result = admit(state=ReplayGuardState(), sender=A, nonce=bad_nonce)
    assert isinstance(result, AdmitRejected)
    assert result.reason == "invalid_nonce"


def test_max_u32_nonce_is_admissible_in_sequence():
    # Reaching U32_MAX is valid; it just requires the full sequence (we jump-start
    # via state construction to avoid 4 billion calls).
    state = ReplayGuardState().with_last(A, U32_MAX - 1)
    result = _admit(state, A, U32_MAX)
    assert isinstance(result, AdmitAccepted)
    assert _admit(result.state, A, U32_MAX).reason == "duplicate_nonce"


# --- Cross-sender independence (intent-level) ---------------------------------


def test_senders_are_independent():
    state = ReplayGuardState()
    state = _admit(state, A, 1).state
    state = _admit(state, A, 2).state
    # B has never been seen; B's first nonce must still be 1 (not 3).
    assert _admit(state, B, 1).__class__ is AdmitAccepted
    assert _admit(state, B, 3).reason == "nonce_gap"
    # A is unaffected by B activity.
    state = _admit(state, B, 1).state
    assert _admit(state, A, 3).__class__ is AdmitAccepted
