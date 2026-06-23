from __future__ import annotations

import hashlib

import pytest

from src.core.perp_submission_auth_message import (
    build_perp_op_auth_message_v1,
    build_perp_op_auth_signing_dict_v1,
    hash_perp_op_auth_message_v1,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes


def test_build_perp_op_auth_signing_dict_v1_selects_only_signed_fields() -> None:
    op = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": "perp:ch2p:btc-usd",
        "action": "set_position_pair",
        "account_a_pubkey": "aa" * 48,
        "account_b_pubkey": "bb" * 48,
        "new_position_base_a": 15,
        "new_position_base_b": -15,
        "deadline": 12345,
        "nonce_a": 7,
        "nonce_b": 9,
        "sig_a": "0x" + "11" * 96,
        "sig_b": "0x" + "22" * 96,
    }

    signing_dict = build_perp_op_auth_signing_dict_v1(op, signer_pubkey="aa" * 48, nonce=7)

    assert signing_dict == {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": "perp:ch2p:btc-usd",
        "action": "set_position_pair",
        "signer_pubkey": "aa" * 48,
        "nonce": 7,
        "fields": {
            "account_a_pubkey": "aa" * 48,
            "account_b_pubkey": "bb" * 48,
            "new_position_base_a": 15,
            "new_position_base_b": -15,
            "deadline": 12345,
        },
    }


def test_hash_perp_op_auth_message_v1_matches_manual_contract() -> None:
    op = {
        "module": "TauPerp",
        "version": "1.1",
        "market_id": "perp:ch3p:eth-usd",
        "action": "publish_clearing_price",
        "price_e8": 250_000_000_000,
        "deadline": 555,
        "oracle_nonce": 3,
        "oracle_sig": "0x" + "33" * 96,
    }

    signing_dict = build_perp_op_auth_signing_dict_v1(op, signer_pubkey="cc" * 48, nonce=3)
    message = build_perp_op_auth_message_v1(op, chain_id="tau-test", signer_pubkey="cc" * 48, nonce=3)
    manual_message = domain_sep_bytes("perp_op_sig:tau-test", version=1) + canonical_json_bytes(signing_dict)

    assert message == manual_message
    assert hash_perp_op_auth_message_v1(op, chain_id="tau-test", signer_pubkey="cc" * 48, nonce=3) == hashlib.sha256(
        manual_message
    ).digest()


def test_build_perp_op_auth_message_v1_rejects_missing_required_field() -> None:
    op = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": "perp:ch2p:btc-usd",
        "action": "init_market_2p",
        "quote_asset": "0x" + "44" * 32,
        "account_a_pubkey": "aa" * 48,
        # missing account_b_pubkey
        "deadline": 1000,
    }

    with pytest.raises(ValueError, match="signing dict missing field: account_b_pubkey"):
        build_perp_op_auth_message_v1(op, chain_id="tau-test", signer_pubkey="aa" * 48, nonce=1)
