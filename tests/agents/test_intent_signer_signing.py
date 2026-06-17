from __future__ import annotations

import hashlib

import pytest

import src.agents.intent_signer as intent_signer
from src.agents.intent_signer import (
    _create_canonical_message,
    _generate_intent_id,
    create_swap_intent,
    sign_intent,
    verify_intent_signature,
)
from src.integration.dex_engine import _verify_intent_signature_bytes
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_dex_intent_for_engine
from src.state.canonical import canonical_json_bytes


def _intent(*, sender_pubkey: str) -> object:
    return create_swap_intent(
        pool_id="p_ab",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=50,
        deadline=99,
        sender_pubkey=sender_pubkey,
        nonce=1,
    )


def test_sign_intent_matches_engine_signature_and_verifies() -> None:
    sender_pubkey = "0x" + bls_pubkey_hex_from_privkey(25)
    signed = sign_intent(_intent(sender_pubkey=sender_pubkey), 25, chain_id="tau-local")
    transport = {
        "module": signed.intent.module,
        "version": signed.intent.version,
        "kind": signed.intent.kind.value,
        "intent_id": signed.intent.intent_id,
        "sender_pubkey": signed.intent.sender_pubkey,
        "deadline": signed.intent.deadline,
        **dict(signed.intent.fields),
    }
    expected = sign_dex_intent_for_engine(transport, privkey=25, chain_id="tau-local")

    assert signed.signature == expected
    assert verify_intent_signature(signed, chain_id="tau-local") is True
    ok, err = _verify_intent_signature_bytes(
        sender_pubkey_hex=signed.intent.sender_pubkey,
        signature_hex=signed.signature,
        signing_payload_bytes=_create_canonical_message(signed.intent),
        chain_id="tau-local",
    )
    assert ok, err


def test_sign_intent_importerror_and_verify_invalid_signature(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(intent_signer, "G2Basic", None)
    with pytest.raises(ImportError):
        sign_intent(_intent(sender_pubkey="0x" + bls_pubkey_hex_from_privkey(26)), 26)
    with pytest.raises(ImportError):
        verify_intent_signature(object())  # type: ignore[arg-type]

    monkeypatch.undo()
    signed = sign_intent(_intent(sender_pubkey="0x" + bls_pubkey_hex_from_privkey(26)), 26)
    bad = type(signed)(intent=signed.intent, signature="0x" + "12" * 96)
    assert verify_intent_signature(bad) is False


def test_verify_intent_signature_rejects_bad_sender_hex() -> None:
    signed = sign_intent(_intent(sender_pubkey="0x" + bls_pubkey_hex_from_privkey(27)), 27)
    bad = type(signed)(
        intent=create_swap_intent(
            pool_id="p_ab",
            asset_in="A",
            asset_out="B",
            amount_in=100,
            min_amount_out=50,
            deadline=99,
            sender_pubkey="bad",
            nonce=1,
        ),
        signature=signed.signature,
    )
    assert verify_intent_signature(bad) is False


def test_verify_intent_signature_propagates_unexpected_bls_backend_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class ExplodingBLS:
        @staticmethod
        def Verify(*_args: object) -> bool:
            raise RuntimeError("backend invariant failure")

    signed = sign_intent(_intent(sender_pubkey="0x" + bls_pubkey_hex_from_privkey(28)), 28)
    monkeypatch.setattr(intent_signer, "G2Basic", ExplodingBLS)

    with pytest.raises(RuntimeError, match="backend invariant failure"):
        verify_intent_signature(signed)


def test_generate_intent_id_uses_shared_canonical_json_encoder() -> None:
    fields = {
        "pool_id": "p_ab",
        "asset_in": "A",
        "asset_out": "B",
        "limits": {"b": 2, "a": 1},
    }
    got = _generate_intent_id(
        sender="0x" + "12" * 48,
        deadline=99,
        kind="SWAP_EXACT_IN",
        fields=fields,
        salt="nonce-7",
    )
    payload = (
        ("0x" + "12" * 48).encode("utf-8")
        + b"99"
        + b"SWAP_EXACT_IN"
        + canonical_json_bytes(fields)
        + b"nonce-7"
    )
    want = "0x" + hashlib.sha256(payload).hexdigest()
    assert got == want


def test_generate_intent_id_rejects_non_canonical_float_fields() -> None:
    with pytest.raises(TypeError, match="floats are not allowed"):
        _generate_intent_id(
            sender="0x" + "34" * 48,
            deadline=99,
            kind="SWAP_EXACT_IN",
            fields={"amount_in": 1.5},
            salt=None,
        )
