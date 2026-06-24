from __future__ import annotations

import pytest

import src.core.replay_guard as replay_guard_module
from src.core.replay_guard import AdmitRejected, ReplayGuardState, admit


SENDER = "0x" + "11" * 48


def test_replay_guard_rejects_malformed_sender_without_mutating_state() -> None:
    state = ReplayGuardState()

    result = admit(state=state, sender="not-hex", nonce=1)

    assert isinstance(result, AdmitRejected)
    assert result.reason == "invalid_sender"
    assert state.entries == ()


def test_replay_guard_propagates_unexpected_canonicalizer_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def _programmer_error(*_args: object, **_kwargs: object) -> str:
        raise RuntimeError("canonicalizer bug")

    monkeypatch.setattr(replay_guard_module, "canonical_hex_fixed_allow_0x", _programmer_error)

    with pytest.raises(RuntimeError, match="canonicalizer bug"):
        admit(state=ReplayGuardState(), sender=SENDER, nonce=1)
