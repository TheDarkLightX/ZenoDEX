from __future__ import annotations

import json

from src.core.zusd import E8
from src.integration import tau_testnet_dex_plugin as plugin
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id


CHAIN_ID = "tau-test-perps-stream8-resilience"
DEADLINE = 999_999_999
ALICE_PRIVKEY = 91
BOB_PRIVKEY = 92
OPERATOR_PRIVKEY = 93
ORACLE_PRIVKEY = 94
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
BOB = "0x" + bls_pubkey_hex_from_privkey(BOB_PRIVKEY)
OPERATOR = "0x" + bls_pubkey_hex_from_privkey(OPERATOR_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(ORACLE_PRIVKEY)


def _signed_init_market(*, market_id: str, quote_asset: str, nonce_a: int, nonce_b: int, deadline: int = DEADLINE):
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "deadline": int(deadline),
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _signed_set_position(*, market_id: str, new_a: int, new_b: int, nonce_a: int, nonce_b: int):
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "set_position_pair",
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "new_position_base_a": int(new_a),
        "new_position_base_b": int(new_b),
        "deadline": DEADLINE,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _signed_publish_price(*, market_id: str, price_e8: int, oracle_nonce: int):
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": DEADLINE,
        "oracle_nonce": int(oracle_nonce),
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=oracle_nonce,
    )
    return op


def _apply(app_state_json: str, *, operations, sender: str, block_timestamp: int, chain_balances=None):
    return plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={} if chain_balances is None else dict(chain_balances),
        operations=operations,
        tx_sender_pubkey=sender,
        block_timestamp=block_timestamp,
    )


def test_stream8_app_bridge_rejects_nonce_replay_without_side_effect(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", CHAIN_ID)
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)

    ok1, app_state_json1, _hash1, _patch1, err1 = _apply(
        "",
        operations={"8": [_signed_init_market(market_id="perp:ch2p:replay-a", quote_asset=quote_asset, nonce_a=1, nonce_b=1)]},
        sender=OPERATOR,
        block_timestamp=1,
    )
    assert ok1 is True, err1

    ok2, app_state_json2, _hash2, _patch2, err2 = _apply(
        app_state_json1,
        operations={"8": [_signed_init_market(market_id="perp:ch2p:replay-b", quote_asset=quote_asset, nonce_a=1, nonce_b=1)]},
        sender=OPERATOR,
        block_timestamp=2,
    )
    assert ok2 is False
    assert err2 == "account_a signature invalid: nonce invalid"
    assert app_state_json2 == app_state_json1


def test_stream8_app_bridge_rejects_expired_signature_without_materializing_market(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", CHAIN_ID)
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)

    ok, app_state_json, _hash, _patch, err = _apply(
        "",
        operations={"8": [_signed_init_market(market_id="perp:ch2p:expired", quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=1)]},
        sender=OPERATOR,
        block_timestamp=2,
    )
    assert ok is False
    assert err == "account_a signature invalid: signature expired (deadline)"
    assert app_state_json == ""


def test_cross_stream_zusd_then_bad_perps_is_atomic(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)

    ok, app_state_json, _hash, _patch, err = _apply(
        "",
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                    "deadline": DEADLINE,
                }
            ],
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": "perp:ch2p:missing",
                    "action": "deposit_collateral",
                    "account_pubkey": ORACLE,
                    "amount": 1,
                }
            ],
        },
        sender=ORACLE,
        block_timestamp=1,
    )
    assert ok is False
    assert err == "unknown market_id"
    assert app_state_json == ""


def test_stream8_settle_epoch_requires_oracle_adapter_when_configured(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_PERP_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    market_id = "perp:ch2p:oracle-adapter-required"

    ok1, app_state_json1, _hash1, _patch1, err1 = _apply(
        "",
        operations={"8": [_signed_init_market(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1)]},
        sender=OPERATOR,
        block_timestamp=1,
    )
    assert ok1 is True, err1

    ok2, app_state_json2, _hash2, _patch2, err2 = _apply(
        app_state_json1,
        operations={"8": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "settle_epoch"}]},
        sender=OPERATOR,
        block_timestamp=2,
    )
    assert ok2 is False
    assert err2 == "settle_epoch requires oracle_adapter_bridge"
    assert app_state_json2 == app_state_json1


def test_stream8_app_bridge_accepts_signed_position_pair_after_zusd_collateral_deposits(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_PERP_ORACLE_PUBKEY", ORACLE)
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    market_id = "perp:ch2p:position"

    ok0, app_state_json0, _hash0, _patch0, err0 = _apply(
        "",
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "mint",
                    "asset": quote_asset,
                    "to_pubkey": ALICE,
                    "amount": 1_000,
                    "nonce": 1,
                    "deadline": DEADLINE,
                    "operator_pubkey": OPERATOR,
                },
                {
                    "module": "TauToken",
                    "action": "mint",
                    "asset": quote_asset,
                    "to_pubkey": BOB,
                    "amount": 1_000,
                    "nonce": 2,
                    "deadline": DEADLINE,
                    "operator_pubkey": OPERATOR,
                },
            ]
        },
        sender=OPERATOR,
        block_timestamp=1,
    )
    assert ok0 is True, err0

    ok1, app_state_json1, _hash1, _patch1, err1 = _apply(
        app_state_json0,
        operations={"8": [_signed_init_market(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1)]},
        sender=OPERATOR,
        block_timestamp=2,
    )
    assert ok1 is True, err1

    for op, timestamp in (
        ({"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "advance_epoch", "delta": 1}, 3),
        (_signed_publish_price(market_id=market_id, price_e8=100_000_000, oracle_nonce=1), 4),
        ({"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "settle_epoch"}, 5),
    ):
        ok_epoch, app_state_json1, _hash_epoch, _patch_epoch, err_epoch = _apply(
            app_state_json1,
            operations={"8": [op]},
            sender=OPERATOR,
            block_timestamp=timestamp,
        )
        assert ok_epoch is True, err_epoch

    for sender, amount, timestamp in ((ALICE, 250, 6), (BOB, 250, 7)):
        ok_deposit, app_state_json1, _hash, _patch, err_deposit = _apply(
            app_state_json1,
            operations={
                "8": [
                    {
                        "module": "TauPerp",
                        "version": "1.0",
                        "market_id": market_id,
                        "action": "deposit_collateral",
                        "account_pubkey": sender,
                        "amount": amount,
                    }
                ]
            },
            sender=sender,
            block_timestamp=timestamp,
        )
        assert ok_deposit is True, err_deposit

    ok2, app_state_json2, _hash2, _patch2, err2 = _apply(
        app_state_json1,
        operations={"8": [_signed_set_position(market_id=market_id, new_a=1, new_b=-1, nonce_a=2, nonce_b=2)]},
        sender=OPERATOR,
        block_timestamp=8,
    )
    assert ok2 is True, err2
    parsed = json.loads(app_state_json2)
    state_view = parsed.get("dex_state", parsed)
    market = next(entry for entry in state_view["perps"]["markets"] if entry["market_id"] == market_id)
    assert market["state"]["position_base_a"] == 1
    assert market["state"]["position_base_b"] == -1
