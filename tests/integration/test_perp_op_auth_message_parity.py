from __future__ import annotations

import pytest

pytest.importorskip("py_ecc.bls", reason="py_ecc not installed (install py-ecc to run signing tests)")
from py_ecc.bls import G2Basic  # type: ignore  # noqa: E402

from src.core.perp_submission_auth_message import (
    build_perp_op_auth_signing_dict_v1,
    hash_perp_op_auth_message_v1,
)
from src.integration.perp_engine import _perp_op_signing_dict
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine


def test_perp_engine_wrapper_matches_shared_auth_signing_contract() -> None:
    op = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": "perp:ch2p:btc-usd",
        "action": "init_market_2p",
        "quote_asset": "0x" + "55" * 32,
        "account_a_pubkey": "aa" * 48,
        "account_b_pubkey": "bb" * 48,
        "deadline": 999,
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": "0x" + "11" * 96,
        "sig_b": "0x" + "22" * 96,
    }

    assert _perp_op_signing_dict(op, signer_pubkey="aa" * 48, nonce=1) == build_perp_op_auth_signing_dict_v1(
        op,
        signer_pubkey="aa" * 48,
        nonce=1,
    )


def test_sign_perp_op_for_engine_uses_shared_auth_message_hash() -> None:
    chain_id = "tau-auth-message"
    signer_privkey = 7
    signer_pubkey = bls_pubkey_hex_from_privkey(signer_privkey)
    op = {
        "module": "TauPerp",
        "version": "1.1",
        "market_id": "perp:ch3p:eth-usd",
        "action": "set_position_triplet",
        "account_a_pubkey": signer_pubkey,
        "account_b_pubkey": "bb" * 48,
        "account_c_pubkey": "cc" * 48,
        "new_position_base_a": 10,
        "new_position_base_b": -6,
        "new_position_base_c": -4,
        "deadline": 1000,
        "nonce_a": 5,
        "nonce_b": 3,
        "nonce_c": 8,
        "sig_a": "0x" + "aa" * 96,
    }

    sig_hex = sign_perp_op_for_engine(
        op,
        privkey=signer_privkey,
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        nonce=5,
    )

    assert G2Basic.Verify(
        bytes.fromhex(signer_pubkey),
        hash_perp_op_auth_message_v1(
            op,
            chain_id=chain_id,
            signer_pubkey=signer_pubkey,
            nonce=5,
        ),
        bytes.fromhex(sig_hex.removeprefix("0x")),
    )
