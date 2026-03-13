from __future__ import annotations

import hashlib

import pytest

from src.core.dex_intent_auth_message import (
    build_dex_intent_auth_message_v1,
    build_dex_intent_signing_dict_v1,
    hash_dex_intent_auth_message_v1,
)
from src.state.intents import Intent, IntentKind


def _sample_intent(*, amount_in: int = 123, min_amount_out: int = 100) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "ab" * 32,
        sender_pubkey="0x" + "11" * 48,
        deadline=1700000000,
        salt="salt-1",
        fields={
            "pool_id": "pool-a",
            "asset_in": "TAU",
            "asset_out": "zUSD",
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
            "recipient": "0x" + "11" * 48,
        },
    )


def test_build_dex_intent_signing_dict_v1_for_intent() -> None:
    intent = _sample_intent()
    signing_dict = build_dex_intent_signing_dict_v1(intent)
    assert signing_dict["module"] == "TauSwap"
    assert signing_dict["version"] == "0.1"
    assert signing_dict["kind"] == "swap_exact_in"
    assert signing_dict["salt"] == "salt-1"
    assert signing_dict["fields"]["amount_in"] == 123


def test_build_dex_intent_signing_dict_v1_mapping_ignores_signature_and_flattens_fields() -> None:
    mapping = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "swap_exact_in",
        "intent_id": "0x" + "cd" * 32,
        "sender_pubkey": "0x" + "22" * 48,
        "deadline": 1700000100,
        "signature": "0xdeadbeef",
        "pool_id": "pool-b",
        "asset_in": "TAU",
        "asset_out": "zUSD",
        "amount_in": 55,
        "min_amount_out": 44,
    }
    signing_dict = build_dex_intent_signing_dict_v1(mapping)
    assert "signature" not in signing_dict
    assert signing_dict["fields"]["pool_id"] == "pool-b"
    assert signing_dict["fields"]["amount_in"] == 55


def test_hash_dex_intent_auth_message_v1_matches_message_hash() -> None:
    intent = _sample_intent()
    msg = build_dex_intent_auth_message_v1(intent, chain_id="tau-local")
    assert hash_dex_intent_auth_message_v1(intent, chain_id="tau-local") == hashlib.sha256(msg).digest()


def test_build_dex_intent_auth_message_requires_chain_id() -> None:
    with pytest.raises(ValueError, match="chain_id must be a non-empty string"):
        build_dex_intent_auth_message_v1(_sample_intent(), chain_id="")
