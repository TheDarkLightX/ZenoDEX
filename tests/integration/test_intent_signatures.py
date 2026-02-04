# [TESTER] v1

from __future__ import annotations

import hashlib

import pytest

from src.integration.dex_engine import _verify_intent_signature_bytes
from src.state.canonical import canonical_json_bytes, domain_sep_bytes


def _signing_dict(*, intent_id: str, sender_pubkey: str) -> dict:
    # Matches src/integration/dex_engine.py::_intent_signing_dict for CREATE_POOL.
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "fields": {
            "asset0": "0x" + "11" * 32,
            "asset1": "0x" + "22" * 32,
            "fee_bps": 30,
            "amount0": 1000,
            "amount1": 2000,
            "created_at": 1,
        },
    }


def test_intent_signature_roundtrip_bls_g2basic() -> None:
    pytest.importorskip("py_ecc")
    from py_ecc.bls import G2Basic

    # Deterministic keypair from fixed seed.
    sk = G2Basic.KeyGen(b"\x01" * 32)
    pk = G2Basic.SkToPk(sk)
    sender_pubkey_hex = "0x" + pk.hex()
    chain_id = "tau-net-alpha"

    intent_id = "0x" + "aa" * 32
    payload = canonical_json_bytes(_signing_dict(intent_id=intent_id, sender_pubkey=sender_pubkey_hex))

    # Signing spec: sign SHA256( domain_sep(f"dex_intent_sig:{chain_id}", v1) || canonical_json_bytes(intent_signing_dict) ).
    msg_hash = hashlib.sha256(domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + payload).digest()
    sig = G2Basic.Sign(sk, msg_hash)
    signature_hex = "0x" + sig.hex()

    ok, err = _verify_intent_signature_bytes(
        sender_pubkey_hex=sender_pubkey_hex,
        signature_hex=signature_hex,
        signing_payload_bytes=payload,
        chain_id=chain_id,
    )
    assert ok, err


def test_intent_signature_rejects_payload_mismatch() -> None:
    pytest.importorskip("py_ecc")
    from py_ecc.bls import G2Basic

    sk = G2Basic.KeyGen(b"\x02" * 32)
    pk = G2Basic.SkToPk(sk)
    sender_pubkey_hex = "0x" + pk.hex()
    chain_id = "tau-net-alpha"

    intent_id = "0x" + "bb" * 32
    payload = canonical_json_bytes(_signing_dict(intent_id=intent_id, sender_pubkey=sender_pubkey_hex))
    msg_hash = hashlib.sha256(domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + payload).digest()
    sig = G2Basic.Sign(sk, msg_hash)

    # Mutate the payload; signature must no longer verify.
    bad_payload = payload.replace(b'"deadline":9999999999', b'"deadline":9999999998')
    ok, err = _verify_intent_signature_bytes(
        sender_pubkey_hex=sender_pubkey_hex,
        signature_hex="0x" + sig.hex(),
        signing_payload_bytes=bad_payload,
        chain_id=chain_id,
    )
    assert not ok
    assert err is not None
