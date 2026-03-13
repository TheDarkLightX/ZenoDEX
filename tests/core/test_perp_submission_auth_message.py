from __future__ import annotations

import hashlib

import pytest

from src.core.perp_submission_auth_message import (
    build_perp_op_auth_message_v1,
    build_perp_op_auth_signing_dict_v1,
    hash_perp_op_auth_message_v1,
)


def test_build_perp_op_auth_signing_dict_v1_for_init_market_2p() -> None:
    op = {
        "module": "perps",
        "version": "v1",
        "market_id": "BTC-zUSD",
        "action": "init_market_2p",
        "quote_asset": "zUSD",
        "account_a_pubkey": "0x" + "11" * 48,
        "account_b_pubkey": "0x" + "22" * 48,
        "deadline": 100,
    }
    signing_dict = build_perp_op_auth_signing_dict_v1(op, signer_pubkey="0x" + "33" * 48, nonce=7)
    assert signing_dict["action"] == "init_market_2p"
    assert signing_dict["signer_pubkey"] == "0x" + "33" * 48
    assert signing_dict["nonce"] == 7
    assert signing_dict["fields"]["quote_asset"] == "zUSD"


def test_build_perp_op_auth_signing_dict_v1_requires_supported_action_and_fields() -> None:
    with pytest.raises(ValueError, match="unsupported signed action"):
        build_perp_op_auth_signing_dict_v1(
            {
                "module": "perps",
                "version": "v1",
                "market_id": "BTC-zUSD",
                "action": "unknown",
            },
            signer_pubkey="pk",
            nonce=1,
        )

    with pytest.raises(ValueError, match="signing dict missing field: deadline"):
        build_perp_op_auth_signing_dict_v1(
            {
                "module": "perps",
                "version": "v1",
                "market_id": "BTC-zUSD",
                "action": "publish_clearing_price",
                "price_e8": 123,
            },
            signer_pubkey="pk",
            nonce=1,
        )


def test_hash_perp_op_auth_message_v1_matches_message_hash() -> None:
    op = {
        "module": "perps",
        "version": "v1",
        "market_id": "BTC-zUSD",
        "action": "publish_clearing_price",
        "price_e8": 123_00000000,
        "deadline": 77,
    }
    msg = build_perp_op_auth_message_v1(op, chain_id="tau-local", signer_pubkey="0x" + "44" * 48, nonce=9)
    assert (
        hash_perp_op_auth_message_v1(op, chain_id="tau-local", signer_pubkey="0x" + "44" * 48, nonce=9)
        == hashlib.sha256(msg).digest()
    )


def test_build_perp_op_auth_message_requires_chain_id() -> None:
    op = {
        "module": "perps",
        "version": "v1",
        "market_id": "BTC-zUSD",
        "action": "publish_clearing_price",
        "price_e8": 123_00000000,
        "deadline": 77,
    }
    with pytest.raises(ValueError, match="chain_id must be a non-empty string"):
        build_perp_op_auth_message_v1(op, chain_id="", signer_pubkey="pk", nonce=1)
