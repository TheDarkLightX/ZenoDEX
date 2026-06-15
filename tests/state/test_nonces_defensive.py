from __future__ import annotations

import pytest

from src.state import nonces as nonces_module
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch

PK_48B = "0x" + "11" * 48


def _intent(*, sender: str = PK_48B, nonce: object = 1) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "33" * 32,
        sender_pubkey=sender,
        deadline=1,
        fields={
            "pool_id": "0x" + "aa" * 32,
            "asset_in": "0x" + "01" * 32,
            "asset_out": "0x" + "02" * 32,
            "amount_in": 1,
            "min_amount_out": 0,
            "nonce": nonce,
        },
    )


def test_nonce_parse_value_error_still_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_nonce(_value: object, *, name: str) -> int:
        assert name == "nonce"
        raise ValueError("bad nonce")

    monkeypatch.setattr(nonces_module, "_require_int_u32_pos", reject_nonce)

    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[_intent()],
        require_all_nonces=True,
    )

    assert ok is False
    assert err == "Missing/invalid nonce"
    assert updated is None


def test_nonce_parse_helper_bugs_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_nonce(_value: object, *, name: str) -> int:
        assert name == "nonce"
        raise RuntimeError("nonce helper bug")

    monkeypatch.setattr(nonces_module, "_require_int_u32_pos", broken_nonce)

    with pytest.raises(RuntimeError, match="nonce helper bug"):
        validate_and_apply_intent_nonce_batch(
            nonces=NonceTable(),
            intents=[_intent()],
            require_all_nonces=True,
        )


def test_sender_canonical_value_error_still_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_sender(hex_str: str, *, nbytes: int, name: str) -> str:
        assert hex_str == PK_48B
        assert nbytes == 48
        assert name == "sender_pubkey"
        raise ValueError("bad sender")

    monkeypatch.setattr(nonces_module, "canonical_hex_fixed_allow_0x", reject_sender)

    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[_intent()],
        require_all_nonces=True,
    )

    assert ok is False
    assert err is not None
    assert "invalid sender_pubkey for nonce accounting" in err
    assert updated is None


def test_sender_canonical_helper_bugs_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_sender(_hex_str: str, *, nbytes: int, name: str) -> str:
        assert nbytes == 48
        assert name == "sender_pubkey"
        raise RuntimeError("sender canonicalizer bug")

    monkeypatch.setattr(nonces_module, "canonical_hex_fixed_allow_0x", broken_sender)

    with pytest.raises(RuntimeError, match="sender canonicalizer bug"):
        validate_and_apply_intent_nonce_batch(
            nonces=NonceTable(),
            intents=[_intent()],
            require_all_nonces=True,
        )
