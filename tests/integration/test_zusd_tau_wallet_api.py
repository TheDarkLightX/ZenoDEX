from __future__ import annotations

import json

import src.integration.zusd_tau_wallet_api as wallet_api
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    init_monetary_state,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id, token_sender_nonce_key

SENDER = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48
OPERATOR = "0x" + "33" * 48


def _monetary_policy_state(*, chain_id: str, asset_id: str | None = None) -> dict:
    return zusd_monetary_state_to_obj(
        init_monetary_state(
            ZUSDMonetaryConfig(
                chain_id=chain_id,
                asset_id=asset_id,
            )
        )
    )


class _FakeClient:
    def __init__(self, _cfg=None) -> None:
        self.sent: list[dict[str, object]] = []

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
        payload = {
            "app_hash": "sha256:" + "ab" * 32,
            "app_state": {
                "zusd_monetary": _monetary_policy_state(chain_id="tau-test-wallet"),
                "balances": [
                    {"pubkey": SENDER, "asset": asset_id, "amount": 400},
                    {"pubkey": RECIPIENT, "asset": asset_id, "amount": 50},
                ],
                "nonces": [
                    {"pubkey": token_sender_nonce_key(SENDER), "last_nonce": 4},
                    {"pubkey": token_sender_nonce_key(OPERATOR), "last_nonce": 2},
                ],
            },
        }
        return json.dumps(payload, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == SENDER[2:]:
            return 7
        if sender_pubkey_hex == OPERATOR[2:]:
            return 9
        return 0

    def sendtx(self, payload):
        self.sent.append(dict(payload))
        return "SUCCESS tx accepted"

    def createblock(self) -> str:
        return "BLOCK created"


def test_status_reports_tau_node_bridge(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET", "/api/zusd/wallet/status", None
    )

    assert status_code == 200
    assert payload["ok"] is True
    status = payload["status"]
    assert status["node_reachable"] is True
    assert status["chain_id"] == "tau-test-wallet"
    assert status["app_bridge_available"] is True
    assert status["holder_count"] == 2


def test_status_and_prepare_use_committed_asset_when_environment_drifts(
    monkeypatch,
) -> None:
    chain_id = "tau-test-wallet"
    committed_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    configured_asset = "0x" + "ab" * 32
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", configured_asset)
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, status_payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET", "/api/zusd/wallet/status", None
    )
    prepare_code, prepare_payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": "burn",
                "asset_id": committed_asset,
                "sender_pubkey": SENDER,
                "amount": 1,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 200
    status = status_payload["status"]
    assert status["asset_id"] == committed_asset
    assert status["configured_asset_id"] == configured_asset
    assert status["policy_binding_ok"] is False
    assert prepare_code == 400
    assert prepare_payload == {
        "ok": False,
        "error": (
            "generic zUSD token operation rejected: canonical_zusd_burn_requires_monetary_authority"
        ),
    }


def test_custom_canonical_asset_is_shared_by_status_and_default_prepare(
    monkeypatch,
) -> None:
    custom_asset = "0x" + "a7" * 32

    class _CustomAssetClient(_FakeClient):
        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            payload = {
                "app_hash": "sha256:" + "cd" * 32,
                "app_state": {
                    "zusd_monetary": _monetary_policy_state(
                        chain_id="tau-test-wallet",
                        asset_id=custom_asset,
                    ),
                    "balances": [
                        {
                            "pubkey": SENDER,
                            "asset": custom_asset,
                            "amount": 400,
                        },
                        {
                            "pubkey": RECIPIENT,
                            "asset": custom_asset,
                            "amount": 50,
                        },
                    ],
                    "nonces": [
                        {
                            "pubkey": token_sender_nonce_key(SENDER),
                            "last_nonce": 4,
                        }
                    ],
                },
            }
            return json.dumps(payload, sort_keys=True)

    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", custom_asset)
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _CustomAssetClient)

    status_code, status_payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET",
        "/api/zusd/wallet/status",
        None,
    )
    prepare_code, prepare_payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": "transfer",
                "sender_pubkey": SENDER,
                "recipient_pubkey": RECIPIENT,
                "amount": 100,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 200
    assert status_payload["status"]["asset_id"] == custom_asset
    assert status_payload["status"]["holder_count"] == 2
    assert prepare_code == 200
    assert prepare_payload["transport"]["asset_id"] == custom_asset
    assert prepare_payload["report"]["asset_id"] == custom_asset


def test_prepare_transfer_uses_tau_app_state_balances_and_nonce(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "transfer",
        "sender_pubkey": SENDER,
        "recipient_pubkey": RECIPIENT,
        "amount": 100,
        "deadline": 123456789,
    }
    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    transport = payload["transport"]
    report = payload["report"]
    assert transport["sender_balance_before"] == 400
    assert transport["recipient_balance_before"] == 50
    assert transport["total_supply_before"] == 450
    assert transport["last_used_nonce"] == 4
    assert transport["tx_sequence_number"] == 7
    assert report["nonce_before"] == 4
    assert report["nonce_after"] == 5
    assert report["sender_balance_after"] == 300
    assert report["recipient_balance_after"] == 150
    assert report["supply_after"] == 450
    assert report["tau_tx_payload"] is None


def test_prepare_burn_rejects_generic_canonical_zusd_supply_authority(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "burn",
        "sender_pubkey": SENDER,
        "amount": 100,
        "deadline": 123456789,
    }
    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {
        "ok": False,
        "error": (
            "generic zUSD token operation rejected: canonical_zusd_burn_requires_monetary_authority"
        ),
    }


def test_submit_requires_explicit_local_signing_and_returns_sendtx(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    class _Report:
        action = "transfer"
        asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
        nonce_key = token_sender_nonce_key(SENDER)
        nonce_before = 4
        nonce_after = 5
        operation = {"action": "transfer"}
        operations = {"9": [{"action": "transfer"}]}
        sender_balance_after = 300
        recipient_balance_after = 150
        supply_after = 450
        tau_receipts = ()
        tau_tx_payload = {"sender_pubkey": SENDER[2:], "sequence_number": 7}

    monkeypatch.setattr(wallet_api, "prepare_zusd_tau_token_operation", lambda **kwargs: _Report())

    body = {
        "action": "transfer",
        "sender_pubkey": SENDER,
        "recipient_pubkey": RECIPIENT,
        "amount": 100,
        "deadline": 123456789,
        "signer_privkey": "1",
    }
    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
