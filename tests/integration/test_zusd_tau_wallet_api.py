from __future__ import annotations

import json

import pytest

import src.integration.zusd_tau_wallet_api as wallet_api
from src.integration.http_authority_ingress_v1 import (
    HttpAuthorityIngressAcceptedV1,
    inspect_http_authority_ingress_v1,
)
from src.integration.tau_net_client import (
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id, token_sender_nonce_key

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
    assert status["external_signed_payload_supported"] is True
    assert status["preferred_signing_mode"] == "external_signed_payload"


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


def _external_submit_fixture(monkeypatch, *, tx_fee_limit: int = 0):
    signer_privkey = 5
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(signer_privkey)
    operations = {"9": [{"action": "transfer", "amount": 100}]}
    client = _FakeClient()

    class _Report:
        action = "transfer"
        asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
        nonce_key = token_sender_nonce_key(signer_pubkey)
        nonce_before = 4
        nonce_after = 5
        operation = {"action": "transfer", "amount": 100}
        operations = {"9": [{"action": "transfer", "amount": 100}]}
        sender_balance_after = 300
        recipient_balance_after = 150
        supply_after = 450
        tau_receipts = ()
        tau_tx_payload = None

    report = _Report()
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.delenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(wallet_api, "_tau_client", lambda: client)
    monkeypatch.setattr(
        wallet_api,
        "_transport_context",
        lambda **_kwargs: {
            "app_hash": "sha256:" + "ab" * 32,
            "asset_id": report.asset_id,
            "actor_pubkey": signer_pubkey,
            "sender_balance_before": 400,
            "recipient_balance_before": 50,
            "total_supply_before": 450,
            "last_used_nonce": 4,
            "tx_sequence_number": 7,
        },
    )
    monkeypatch.setattr(
        wallet_api,
        "prepare_zusd_tau_token_operation",
        lambda **_kwargs: report,
    )
    signed_payload = build_signed_tau_transaction(
        privkey=signer_privkey,
        sequence_number=7,
        expiration_time=123456789,
        operations=operations,
        fee_limit=tx_fee_limit,
    )
    body = {
        "action": "transfer",
        "sender_pubkey": signer_pubkey,
        "recipient_pubkey": RECIPIENT,
        "amount": 100,
        "deadline": 123456789,
        "tx_fee_limit": tx_fee_limit,
        "signed_tau_tx_payload": signed_payload,
    }
    return client, body, signed_payload


def test_submit_accepts_exact_external_signed_payload_without_server_key(monkeypatch) -> None:
    client, body, signed_payload = _external_submit_fixture(monkeypatch)
    raw_body = json.dumps(body).encode("utf-8")

    assert inspect_http_authority_ingress_v1(raw_body) == HttpAuthorityIngressAcceptedV1()

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        raw_body,
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["signing_mode"] == "external_signed_payload"
    assert payload["report"]["tau_tx_payload"] == signed_payload
    assert client.sent == [signed_payload]


def test_prepare_sign_submit_roundtrip_uses_real_token_operation_projection(monkeypatch) -> None:
    signer_privkey = 5
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(signer_privkey)
    asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")

    class _SignerClient(_FakeClient):
        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            return json.dumps(
                {
                    "app_hash": "sha256:" + "ab" * 32,
                    "app_state": {
                        "balances": [
                            {"pubkey": signer_pubkey, "asset": asset_id, "amount": 400},
                            {"pubkey": RECIPIENT, "asset": asset_id, "amount": 50},
                        ],
                        "nonces": [
                            {
                                "pubkey": token_sender_nonce_key(signer_pubkey),
                                "last_nonce": 4,
                            }
                        ],
                    },
                },
                sort_keys=True,
            )

        def get_sequence(self, sender_pubkey_hex: str) -> int:
            assert sender_pubkey_hex == signer_pubkey[2:]
            return 7

    client = _SignerClient()
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.delenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(wallet_api, "_tau_client", lambda: client)
    body = {
        "action": "transfer",
        "sender_pubkey": signer_pubkey,
        "recipient_pubkey": RECIPIENT,
        "amount": 100,
        "deadline": 123456789,
        "tx_fee_limit": 17,
    }

    prepare_status, prepared = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert prepare_status == 200
    assert prepared["report"]["tau_tx_payload"] is None
    signed_payload = build_signed_tau_transaction(
        privkey=signer_privkey,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=body["deadline"],
        operations=prepared["report"]["operations"],
        fee_limit=body["tx_fee_limit"],
    )

    submit_status, submitted = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps({**body, "signed_tau_tx_payload": signed_payload}).encode("utf-8"),
    )

    assert submit_status == 200
    assert submitted["transport"]["signing_mode"] == "external_signed_payload"
    assert submitted["report"]["operations"] == prepared["report"]["operations"]
    assert client.sent == [signed_payload]


def test_submit_binds_nonzero_external_fee_limit(monkeypatch) -> None:
    client, body, signed_payload = _external_submit_fixture(
        monkeypatch,
        tx_fee_limit=17,
    )

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["transport"]["tx_fee_limit"] == "17"
    assert client.sent == [signed_payload]


def test_submit_accepts_external_payload_as_json_string(monkeypatch) -> None:
    client, body, signed_payload = _external_submit_fixture(monkeypatch)
    body["signed_tau_tx_payload"] = json.dumps(signed_payload, sort_keys=True)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["transport"]["signing_mode"] == "external_signed_payload"
    assert client.sent == [signed_payload]


def test_submit_never_reports_rejected_sendtx_as_success(monkeypatch) -> None:
    client, body, signed_payload = _external_submit_fixture(monkeypatch)

    def reject_sendtx(payload):
        client.sent.append(dict(payload))
        return "ERROR transaction rejected"

    client.sendtx = reject_sendtx

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 502
    assert payload == {
        "ok": False,
        "error": "tau_rpc_error",
        "detail": "sendtx rejected",
    }
    assert client.sent == [signed_payload]


@pytest.mark.parametrize(
    ("mutation", "expected_error"),
    (
        (lambda payload: payload.update(sequence_number=True), "signed_tau_tx_payload bad sequence_number"),
        (lambda payload: payload.update(sequence_number=6), "signed_tau_tx_payload sequence mismatch"),
        (lambda payload: payload.update(sequence_number=8), "signed_tau_tx_payload sequence mismatch"),
        (lambda payload: payload.update(expiration_time=123456788), "signed_tau_tx_payload expiration mismatch"),
        (lambda payload: payload.update(expiration_time=123456790), "signed_tau_tx_payload expiration mismatch"),
        (lambda payload: payload.update(fee_limit="1"), "signed_tau_tx_payload fee_limit mismatch"),
        (lambda payload: payload.update(operations={"9": "[]"}), "signed_tau_tx_payload operations mismatch"),
        (lambda payload: payload.update(sender_pubkey="22" * 48), "signed_tau_tx_payload sender mismatch"),
        (lambda payload: payload.update(signature="00" * 96), "signed_tau_tx_payload signature invalid"),
        (lambda payload: payload.update(unexpected="field"), "signed_tau_tx_payload fields mismatch"),
    ),
)
def test_external_signed_payload_binding_mutations_reject_without_send(
    monkeypatch,
    mutation,
    expected_error: str,
) -> None:
    client, body, signed_payload = _external_submit_fixture(monkeypatch)
    mutation(signed_payload)
    body["signed_tau_tx_payload"] = signed_payload

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": expected_error}
    assert client.sent == []


def test_submit_rejects_ambiguous_local_and_external_signing_authority(monkeypatch) -> None:
    client, body, _signed_payload = _external_submit_fixture(monkeypatch)
    body["signer_privkey"] = "5"

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "ambiguous_signing_authority"}
    assert client.sent == []


def test_submit_rejects_ambiguous_external_payload_aliases(monkeypatch) -> None:
    client, body, signed_payload = _external_submit_fixture(monkeypatch)
    body["tau_tx_payload"] = signed_payload

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "ambiguous_signed_tau_tx_payload"}
    assert client.sent == []


def test_prepare_rejects_signed_payload_in_wrong_phase(monkeypatch) -> None:
    client, body, _signed_payload = _external_submit_fixture(monkeypatch)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload_submit_only"}
    assert client.sent == []
