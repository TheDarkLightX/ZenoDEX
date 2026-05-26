from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping

import pytest


pytest.importorskip("py_ecc.bls")


def _priv(value: int) -> str:
    return "0x" + int(value).to_bytes(32, "big").hex()


def _pub(privkey: str) -> str:
    from py_ecc.bls import G2Basic

    return "0x" + G2Basic.SkToPk(int(privkey, 16)).hex()


def _sign(body: Mapping[str, Any], *, privkey: str) -> str:
    from py_ecc.bls import G2Basic
    from src.integration.tau_testnet_dex_plugin import (
        confidential_sealed_bid_asset_authorization_message_v1,
    )

    digest = hashlib.sha256(confidential_sealed_bid_asset_authorization_message_v1(body)).digest()
    return "0x" + G2Basic.Sign(int(privkey, 16), digest).hex()


def _balances(app_state_json: str) -> dict[tuple[str, str], int]:
    obj = json.loads(app_state_json)
    dex_state = obj["dex_state"] if obj.get("schema") == "zenodex/tau_app_state/v1" else obj
    return {
        (str(row["pubkey"]), str(row["asset"])): int(row["amount"])
        for row in dex_state.get("balances", [])
    }


def _settlement_op(
    *,
    bad_buyer_signature: bool = False,
    version: str = "1",
) -> tuple[dict[str, Any], dict[str, str]]:
    from src.integration import tau_testnet_dex_plugin as plugin

    seller_priv = _priv(1)
    buyer_priv = _priv(2)
    wrong_priv = _priv(3)
    seller = _pub(seller_priv)
    buyer = _pub(buyer_priv)
    payment_asset = "0x" + "44" * 32
    inventory_asset = "0x" + "55" * 32
    commitment = "0x" + "66" * 32
    fill = {
        "bidder_id": "alice",
        "bidder_pubkey": buyer,
        "commitment": commitment,
        "filled_quantity": 4,
        "paid_price": 105,
    }
    fills_hash = plugin._confidential_sealed_bid_fills_hash([dict(fill, buyer_payment_signature="")])
    seller_body = plugin._confidential_sealed_bid_asset_authorization_body_v1(
        chain_id="tau-local",
        settlement_id="settlement-1",
        batch_id="batch-1",
        role="seller_inventory",
        pubkey=seller,
        payment_asset=payment_asset,
        inventory_asset=inventory_asset,
        clearing_price=105,
        quantity=4,
        amount=0,
        fills_hash=fills_hash,
    )
    buyer_body = plugin._confidential_sealed_bid_asset_authorization_body_v1(
        chain_id="tau-local",
        settlement_id="settlement-1",
        batch_id="batch-1",
        role="buyer_payment",
        pubkey=buyer,
        payment_asset=payment_asset,
        inventory_asset=inventory_asset,
        clearing_price=105,
        quantity=4,
        amount=420,
        fills_hash=fills_hash,
        commitment=commitment,
    )
    fill["buyer_payment_signature"] = _sign(
        buyer_body,
        privkey=wrong_priv if bad_buyer_signature else buyer_priv,
    )
    op = {
        "module": "ZenoConfidentialSealedBid",
        "version": version,
        "action": "settle_assets",
        "settlement_id": "settlement-1",
        "batch_id": "batch-1",
        "seller_pubkey": seller,
        "payment_asset": payment_asset,
        "inventory_asset": inventory_asset,
        "units_for_sale": 10,
        "clearing_price": 105,
        "nonce": 1,
        "seller_inventory_signature": _sign(seller_body, privkey=seller_priv),
        "fills": [fill],
    }
    return op, {
        "seller": seller,
        "buyer": buyer,
        "payment_asset": payment_asset,
        "inventory_asset": inventory_asset,
    }


def test_confidential_sealed_bid_asset_settlement_moves_assets_atomically(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    op, ids = _settlement_op()

    ok, app_state_json, _app_hash, _patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "7": {
                "mint": [
                    [ids["buyer"], ids["payment_asset"], 1_000],
                    [ids["seller"], ids["inventory_asset"], 10],
                ]
            },
            "13": [op],
        },
        tx_sender_pubkey=ids["buyer"],
        block_timestamp=100,
    )
    assert ok is True
    assert err is None
    balances = _balances(app_state_json)
    assert balances[(ids["buyer"], ids["payment_asset"])] == 580
    assert balances[(ids["seller"], ids["payment_asset"])] == 420
    assert balances[(ids["buyer"], ids["inventory_asset"])] == 4
    assert balances[(ids["seller"], ids["inventory_asset"])] == 6

    replay_ok, replay_state, _hash2, _patch2, replay_err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={"13": [op]},
        tx_sender_pubkey=ids["buyer"],
        block_timestamp=101,
    )
    assert replay_ok is False
    assert replay_state == app_state_json
    assert replay_err == "confidential settlement op[0] nonce invalid (expected 2, got 1)"


def test_confidential_sealed_bid_asset_settlement_rejects_bad_buyer_signature(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    op, ids = _settlement_op(bad_buyer_signature=True)

    ok, app_state_json, _app_hash, _patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "7": {
                "mint": [
                    [ids["buyer"], ids["payment_asset"], 1_000],
                    [ids["seller"], ids["inventory_asset"], 10],
                ]
            },
            "13": [op],
        },
        tx_sender_pubkey=ids["buyer"],
        block_timestamp=100,
    )
    assert ok is False
    assert app_state_json == ""
    assert isinstance(err, str)
    assert "buyer authorization rejected:invalid_signature" in err


def test_confidential_sealed_bid_asset_settlement_rejects_unknown_version(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    op, ids = _settlement_op(version="2")

    ok, app_state_json, _app_hash, _patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "7": {
                "mint": [
                    [ids["buyer"], ids["payment_asset"], 1_000],
                    [ids["seller"], ids["inventory_asset"], 10],
                ]
            },
            "13": [op],
        },
        tx_sender_pubkey=ids["buyer"],
        block_timestamp=100,
    )
    assert ok is False
    assert app_state_json == ""
    assert err == "confidential settlement op[0] version unsupported: '2'"


def test_confidential_sealed_bid_tau_guard_rejects_overfill(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_runner import find_tau_bin

    if not find_tau_bin():
        pytest.skip("tau not found")

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CONFIDENTIAL_SEALED_BID_TAU_GUARD", "1")
    op, ids = _settlement_op()
    op["units_for_sale"] = 3

    ok, app_state_json, _app_hash, _patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "7": {
                "mint": [
                    [ids["buyer"], ids["payment_asset"], 1_000],
                    [ids["seller"], ids["inventory_asset"], 10],
                ]
            },
            "13": [op],
        },
        tx_sender_pubkey=ids["buyer"],
        block_timestamp=100,
    )
    assert ok is False
    assert app_state_json == ""
    assert err == "confidential settlement op[0] Tau seller totals guard rejected"
