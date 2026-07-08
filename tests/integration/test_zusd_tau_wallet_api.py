from __future__ import annotations

import json

from src.integration.zusd_tau_token import derive_zusd_tau_asset_id, token_sender_nonce_key
import src.integration.zusd_tau_wallet_api as wallet_api


SENDER = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48
OPERATOR = "0x" + "33" * 48


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

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request("GET", "/api/zusd/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    status = payload["status"]
    assert status["node_reachable"] is True
    assert status["chain_id"] == "tau-test-wallet"
    assert status["app_bridge_available"] is True
    assert status["holder_count"] == 2


def test_status_is_account_aware_for_funded_holder(monkeypatch) -> None:
    # Community bug: a funded account's balance must surface on the zUSD token
    # wallet surface (it previously only resolved on the LP Pool surface).
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET",
        f"/api/zusd/wallet/status?account={SENDER}",
        None,
    )

    assert status_code == 200
    assert payload["ok"] is True
    status = payload["status"]
    assert status["node_reachable"] is True
    assert status["account"] == SENDER
    assert status["account_view"]["account"] == SENDER
    assert status["account_view"]["balance"] == 400


def test_status_account_aware_zero_for_unknown_account(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    unknown = "0x" + "ee" * 48
    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET",
        f"/api/zusd/wallet/status?account={unknown}",
        None,
    )

    assert status_code == 200
    assert payload["status"]["account_view"]["balance"] == 0


def test_status_without_account_omits_account_view(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET",
        "/api/zusd/wallet/status",
        None,
    )

    assert status_code == 200
    assert "account" not in payload["status"]
    assert "account_view" not in payload["status"]


def test_status_fails_closed_on_malformed_account(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET",
        "/api/zusd/wallet/status?account=not-a-pubkey",
        None,
    )

    assert status_code == 400
    assert payload["ok"] is False


def test_status_rejects_malformed_tau_port(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setenv("ZUSD_TAU_WALLET_TAU_PORT", "70000")

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request("GET", "/api/zusd/wallet/status", None)

    assert status_code == 400
    assert payload["ok"] is False
    assert "ZUSD_TAU_WALLET_TAU_PORT" in str(payload["error"])


def test_prepare_rejects_malformed_tau_verify_flag(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setenv("ZUSD_TAU_WALLET_TAU_VERIFY", "maybe")
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

    assert status_code == 400
    assert payload["ok"] is False
    assert "ZUSD_TAU_WALLET_TAU_VERIFY" in str(payload["error"])


def test_prepare_rejects_nonfinite_tau_verify_timeout(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setenv("ZUSD_TAU_WALLET_TAU_VERIFY_TIMEOUT_S", "nan")
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

    assert status_code == 400
    assert payload["ok"] is False
    assert "ZUSD_TAU_WALLET_TAU_VERIFY_TIMEOUT_S" in str(payload["error"])


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


def test_prepare_burn_uses_tau_app_state_balances_and_nonce(monkeypatch) -> None:
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

    assert status_code == 200
    assert payload["ok"] is True
    transport = payload["transport"]
    report = payload["report"]
    assert transport["sender_balance_before"] == 400
    assert transport["recipient_balance_before"] == 0
    assert transport["total_supply_before"] == 450
    assert transport["last_used_nonce"] == 4
    assert transport["tx_sequence_number"] == 7
    assert report["nonce_before"] == 4
    assert report["nonce_after"] == 5
    assert report["sender_balance_after"] == 300
    assert report["recipient_balance_after"] == 0
    assert report["supply_after"] == 350
    assert report["tau_tx_payload"] is None


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
        operations = {"23": [{"action": "transfer"}]}
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


def test_submit_rejects_malformed_signed_payload_echo_flag(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", "maybe")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    class _Report:
        action = "transfer"
        asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
        nonce_key = token_sender_nonce_key(SENDER)
        nonce_before = 4
        nonce_after = 5
        operation = {"action": "transfer"}
        operations = {"23": [{"action": "transfer"}]}
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

    assert status_code == 400
    assert payload["ok"] is False
    assert "ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD" in str(payload["error"])
