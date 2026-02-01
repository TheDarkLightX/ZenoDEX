import hashlib
import json
import time

import pytest


pytest.importorskip("py_ecc.bls", reason="py_ecc not installed (install py-ecc to run signing tests)")
from py_ecc.bls import G2Basic  # type: ignore  # noqa: E402


def _now() -> int:
    return int(time.time())


def test_tau_tx_signature_verifies():
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction

    privkey = 1
    payload = build_signed_tau_transaction(
        privkey=privkey,
        sequence_number=0,
        expiration_time=_now() + 3600,
        operations={},
        fee_limit="0",
    )
    assert payload["sender_pubkey"] == bls_pubkey_hex_from_privkey(privkey)

    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "operations": payload["operations"],
        "fee_limit": payload["fee_limit"],
    }
    msg_bytes = json.dumps(signing_dict, sort_keys=True, separators=(",", ":")).encode("utf-8")
    msg_hash = hashlib.sha256(msg_bytes).digest()

    pubkey_bytes = bytes.fromhex(payload["sender_pubkey"])
    sig_bytes = bytes.fromhex(payload["signature"])
    assert G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes) is True


def test_dex_intent_signature_required_for_third_party_submitter(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_dex_intent_for_engine

    user_sk = 2
    agg_sk = 3
    user_pub = bls_pubkey_hex_from_privkey(user_sk)
    agg_pub = bls_pubkey_hex_from_privkey(agg_sk)

    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    chain_id = "tau-local"

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "1")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)

    create_pool_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": user_pub,
        "deadline": _now() + 3600,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    # Missing signature: should fail when tx_sender != intent.sender.
    ok, _json0, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={user_pub: 123, agg_pub: 0},
        operations={"4": {"mint": [[user_pub, asset0, 10_000], [user_pub, asset1, 10_000]]}, "2": [create_pool_intent]},
        tx_sender_pubkey=agg_pub,
        block_timestamp=123,
    )
    assert ok is False
    assert isinstance(err0, str) and "missing intent signature" in err0

    # Signed: should succeed.
    sig0 = sign_dex_intent_for_engine(create_pool_intent, privkey=user_sk, chain_id=chain_id)
    ok1, app_state_json, _hash1, _patch1, err1 = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={user_pub: 123, agg_pub: 0},
        operations={"4": {"mint": [[user_pub, asset0, 10_000], [user_pub, asset1, 10_000]]}, "2": [[create_pool_intent, sig0]]},
        tx_sender_pubkey=agg_pub,
        block_timestamp=123,
    )
    assert ok1 is True
    assert err1 is None

    parsed = json.loads(app_state_json)
    pools = parsed.get("pools") or []
    assert isinstance(pools, list) and pools
    pool_id = pools[0].get("pool_id")
    assert isinstance(pool_id, str) and pool_id

    balances_before = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed.get("balances") or [])
        if isinstance(b, dict)
    }
    before_in = balances_before.get((user_pub, asset0), 0)
    before_out = balances_before.get((user_pub, asset1), 0)

    swap_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": user_pub,
        "deadline": _now() + 3600,
        "nonce": 2,
        "pool_id": pool_id,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 100,
        "min_amount_out": 1,
        "recipient": user_pub,
    }
    sig1 = sign_dex_intent_for_engine(swap_intent, privkey=user_sk, chain_id=chain_id)
    ok2, app_state_json2, _hash2, _patch2, err2 = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={user_pub: 123, agg_pub: 0},
        operations={"2": [[swap_intent, sig1]]},
        tx_sender_pubkey=agg_pub,
        block_timestamp=124,
    )
    assert ok2 is True
    assert err2 is None

    parsed2 = json.loads(app_state_json2)
    balances_after = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed2.get("balances") or [])
        if isinstance(b, dict)
    }
    after_in = balances_after.get((user_pub, asset0), 0)
    after_out = balances_after.get((user_pub, asset1), 0)
    assert isinstance(before_in, int) and isinstance(after_in, int)
    assert isinstance(before_out, int) and isinstance(after_out, int)
    assert after_in < before_in
    assert after_out > before_out
