from __future__ import annotations

import json

from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, init_state, step
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryState,
    zusd_monetary_sender_nonce_key,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
import src.integration.zusd_monetary_wallet_api as monetary_api


ALICE_PRIVKEY = 82
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(81)


def _ok(core, tag: str, **kwargs):
    res = step(core, ZUSDCommand(tag=tag, args=kwargs))
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _wrapped_app_state() -> dict[str, object]:
    core = init_state()
    core = _ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _ok(core, "deposit_collateral", amount_e8=20 * E8)
    dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(
            ZUSDMonetaryState(
                core=core,
                vault_owner_pubkey=ALICE,
                sp_deposits_e8={},
                sp_collateral_claims_e8={},
            )
        ),
    }


class _FakeClient:
    def __init__(self, _cfg=None) -> None:
        self.sent: list[dict[str, object]] = []

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        payload = {
            "app_hash": "sha256:" + "ab" * 32,
            "app_state": _wrapped_app_state(),
        }
        return json.dumps(payload, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == ALICE[2:]:
            return 7
        return 0

    def get_balance(self, address_hex: str) -> int:
        if address_hex == ALICE[2:]:
            return 0
        return 0

    def sendtx(self, payload):
        self.sent.append(dict(payload))
        return "SUCCESS tx accepted"

    def createblock(self) -> str:
        return "BLOCK created"


def test_status_reports_zusd_monetary_state_from_wrapped_app_state(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "GET",
        "/api/zusd/monetary/status",
        None,
    )

    assert status_code == 200
    assert payload["ok"] is True
    status = payload["status"]
    assert status["node_reachable"] is True
    assert status["monetary_state_present"] is True
    assert status["core"]["collateral_e8"] == 20 * E8
    assert status["vault_owner_pubkey"] == ALICE


def test_prepare_mint_uses_monetary_nonce_and_preflights_stream_11(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["actor_pubkey"] == ALICE
    assert payload["transport"]["tx_sequence_number"] == 7
    report = payload["report"]
    assert report["nonce_key"] == zusd_monetary_sender_nonce_key(ALICE)
    assert report["nonce_before"] == 0
    assert report["nonce_after"] == 1
    assert report["operation"]["action"] == "mint_zusd"
    assert report["operation"]["amount_e8"] == 1000 * E8
    assert "11" in report["operations"]
    assert report["preflight"]["ok"] is True
    assert report["fee_limit"]["tx_fee_limit"] == "2"
    assert report["fee_limit"]["native_balance_covers_fee_limit"] is False
    assert report["fee_limit"]["warning"] == "native balance is below requested Tau fee limit"
    assert report["preflight"]["effects"][0]["effects"]["principal_e8"] == 1000 * E8
    assert payload["transport"]["tx_fee_limit"] == "2"
    assert payload["transport"]["fee_limit_native_balance_ok"] is False
    assert payload["transport"]["asset_id"] == derive_zusd_tau_asset_id(chain_id=chain_id)


def test_submit_mint_requires_local_signing_and_returns_sendtx(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "signer_privkey": str(ALICE_PRIVKEY),
        "tx_fee_limit": "2",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]
    assert payload["report"]["tau_tx_payload"]["fee_limit"] == "2"


def test_prepare_rejects_bad_tx_fee_limit(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "1.5",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_tx_fee_limit"}
