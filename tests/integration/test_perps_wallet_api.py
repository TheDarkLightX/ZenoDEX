from __future__ import annotations

import json

import pytest

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
import src.integration.perps_wallet_api as perps_wallet_api


CHAIN_ID = "tau-test-perps-wallet"
ALICE_PRIVKEY = 83
BOB_PRIVKEY = 84
ORACLE_PRIVKEY = 85
OPERATOR_PRIVKEY = 86
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
BOB = "0x" + bls_pubkey_hex_from_privkey(BOB_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(ORACLE_PRIVKEY)
OPERATOR = "0x" + bls_pubkey_hex_from_privkey(OPERATOR_PRIVKEY)
MARKET_ID = "perp:ch2p:test"


def _wrapped_app_state(state: DexState) -> dict[str, object]:
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }


def _signed_init_op(*, quote_asset: str, nonce_a: int = 1, nonce_b: int = 1) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "deadline": 123456789,
        "nonce_a": nonce_a,
        "nonce_b": nonce_b,
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _state_with_market_and_balance(*, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID),
        state=state,
        operations={"5": [_signed_init_op(quote_asset=quote_asset)]},
        tx_sender_pubkey=ALICE,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    res.state.balances.set(ALICE, quote_asset, 5_000)
    return res.state


def _apply_perps(state: DexState, ops: list[dict[str, object]], *, sender: str = OPERATOR) -> DexState:
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID, oracle_pubkey=ORACLE),
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _state_with_advanced_market(*, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply_perps(state, [_signed_init_op(quote_asset=quote_asset)])
    return _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )


def _state_with_posted_collateral(*, quote_asset: str) -> DexState:
    state = _state_with_market_and_balance(quote_asset=quote_asset)
    return _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": ALICE,
                "amount": 1_000,
            }
        ],
        sender=ALICE,
    )


class _FakeClient:
    app_state: dict[str, object] = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    sent: list[dict[str, object]] = []
    native_balances: dict[str, int] = {}

    def __init__(self, _cfg=None) -> None:
        pass

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        return json.dumps({"app_hash": "sha256:" + "cd" * 32, "app_state": self.app_state}, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == ALICE[2:]:
            return 9
        if sender_pubkey_hex == BOB[2:]:
            return 11
        if sender_pubkey_hex == ORACLE[2:]:
            return 13
        if sender_pubkey_hex == OPERATOR[2:]:
            return 15
        return 0

    def get_balance(self, address_hex: str) -> int:
        return int(self.native_balances.get(address_hex, 0))

    def sendtx(self, payload):
        self.sent.append(dict(payload))
        return "SUCCESS tx accepted"

    def createblock(self) -> str:
        return "BLOCK created"


@pytest.fixture(autouse=True)
def _reset_fake_client_balances() -> None:
    _FakeClient.native_balances = {}
    yield
    _FakeClient.native_balances = {}


def test_prepare_init_market_2p_builds_signed_stream_8_and_preflights(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 0}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["stream_key"] == "8"
    assert payload["transport"]["tx_sender_pubkey"] == ALICE
    assert payload["transport"]["tx_sequence_number"] == 9
    assert payload["transport"]["tx_fee_limit"] == "0"
    assert payload["transport"]["fee_limit_native_balance_ok"] is True
    assert payload["report"]["operations"]["8"][0]["action"] == "init_market_2p"
    assert payload["report"]["preflight"]["ok"] is True


def test_prepare_reports_tau_fee_limit_native_balance_posture(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 1}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["tx_fee_limit"] == "2"
    assert payload["transport"]["native_balance_e8"] == 1
    assert payload["transport"]["fee_limit_native_balance_ok"] is False
    assert payload["transport"]["fee_limit_warning"] == "native balance is below requested Tau fee limit"
    assert payload["report"]["fee_limit"]["native_balance_covers_fee_limit"] is False


def test_prepare_rejects_bad_tx_fee_limit(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "tx_fee_limit": "1.5",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_tx_fee_limit"}


def test_prepare_rejects_bad_counterparty_signature_in_preflight(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    good = _signed_init_op(quote_asset=quote_asset)
    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": good["sig_a"],
        "sig_b": "0x" + "00" * 96,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is False
    assert "account_b signature invalid" in payload["report"]["preflight"]["error"]


def test_submit_deposit_collateral_uses_sender_bound_account_and_stream_8(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["account_pubkey"] == ALICE
    assert payload["transport"]["fee_limit_native_balance_ok"] is True
    assert payload["report"]["tau_tx_payload"]["fee_limit"] == "2"
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]
    assert json.loads(payload["report"]["tau_tx_payload"]["operations"]["8"])[0]["action"] == "deposit_collateral"


def test_submit_withdraw_collateral_uses_sender_bound_account_and_stream_8(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_posted_collateral(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "withdraw_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 100,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["action"] == "withdraw_collateral"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]


def test_prepare_publish_price_signs_oracle_op(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_advanced_market(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_PERP_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "publish_clearing_price",
        "market_id": MARKET_ID,
        "oracle_privkey": str(ORACLE_PRIVKEY),
        "price_e8": 100_000_000,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["tx_sender_pubkey"] == ORACLE
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_nonce"] == 1
    assert payload["report"]["operation"]["oracle_sig"].startswith("0x")


def test_submit_advance_epoch_uses_operator_signer(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "advance_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "delta": 1,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["action"] == "advance_epoch"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == OPERATOR[2:]


def test_prepare_settle_epoch_can_fail_closed_on_missing_oracle_bridge(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_advanced_market(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is False
    assert payload["report"]["preflight"]["error"] == "settle_epoch requires oracle_adapter_bridge"


def test_submit_rejects_preflight_failure_before_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": "0x" + "00" * 96,
        "sig_b": "0x" + "00" * 96,
        "deadline": 123456789,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"].startswith("preflight_failed:")
    assert _FakeClient.sent == []
