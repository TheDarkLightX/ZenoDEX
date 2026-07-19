from __future__ import annotations

import hashlib

import pytest

from src.core.dex_intent_auth_message import (
    build_dex_intent_auth_message_v1,
    build_dex_intent_signing_dict_v1,
    hash_dex_intent_auth_message_v1,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes
from src.state.intents import Intent, IntentKind


def test_build_dex_intent_signing_dict_v1_matches_transport_mapping() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id="0x" + "aa" * 32,
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        salt="salt-1",
        fields={
            "asset0": "0x" + "22" * 32,
            "asset1": "0x" + "33" * 32,
            "fee_bps": 30,
            "amount0": 1000,
            "amount1": 2000,
        },
    )
    transport = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": "0x" + "11" * 48,
        "deadline": 9999999999,
        "salt": "salt-1",
        "asset0": "0x" + "22" * 32,
        "asset1": "0x" + "33" * 32,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "signature": "0x" + "44" * 96,
    }

    assert build_dex_intent_signing_dict_v1(intent) == build_dex_intent_signing_dict_v1(transport)


def test_hash_dex_intent_auth_message_v1_matches_manual_contract() -> None:
    transport = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": "0x" + "55" * 48,
        "deadline": 123456789,
        "pool_id": "pool-1",
        "asset_in": "0x" + "66" * 32,
        "asset_out": "0x" + "77" * 32,
        "amount_in": 500,
        "min_amount_out": 490,
        "recipient": "0x" + "88" * 48,
    }

    signing_dict = build_dex_intent_signing_dict_v1(transport)
    manual_message = domain_sep_bytes("dex_intent_sig:tau-test", version=1) + canonical_json_bytes(signing_dict)

    assert build_dex_intent_auth_message_v1(transport, chain_id="tau-test") == manual_message
    assert hash_dex_intent_auth_message_v1(transport, chain_id="tau-test") == hashlib.sha256(manual_message).digest()


def test_build_dex_intent_signing_dict_v1_prefers_explicit_fields_mapping() -> None:
    transport = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "cc" * 32,
        "sender_pubkey": "0x" + "44" * 48,
        "deadline": 123,
        "salt": "salt-2",
        "fields": {
            "pool_id": "pool-explicit",
            "amount_in": 7,
        },
        "pool_id": "pool-top-level",
        "amount_in": 99,
        "signature": "0x" + "55" * 96,
    }

    assert build_dex_intent_signing_dict_v1(transport) == {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "cc" * 32,
        "sender_pubkey": "0x" + "44" * 48,
        "deadline": 123,
        "salt": "salt-2",
        "fields": {
            "pool_id": "pool-explicit",
            "amount_in": 7,
        },
    }


def test_build_dex_intent_signing_dict_v1_rejects_transport_non_mapping_explicit_fields() -> None:
    transport = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "dd" * 32,
        "sender_pubkey": "0x" + "66" * 48,
        "deadline": 5,
        "fields": ["not", "a", "mapping"],
    }

    with pytest.raises(TypeError, match="intent.fields must be a mapping when present"):
        build_dex_intent_signing_dict_v1(transport)


def test_intent_seal_rejects_non_mapping_fields() -> None:
    with pytest.raises(TypeError, match="fields must be a mapping when present"):
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id="0x" + "ee" * 32,
            sender_pubkey="0x" + "77" * 48,
            deadline=1,
            fields=[],
        )
