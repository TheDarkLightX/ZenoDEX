from __future__ import annotations

import copy
import json
from dataclasses import replace
from typing import Any

import src.integration.perps_wallet_api as perps_wallet_api
import src.integration.zusd_monetary_wallet_api as monetary_api
from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, step
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.integration.tau_net_client import (
    TauNetRpcError,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    sign_perp_op_for_engine,
)
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    init_monetary_state,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable

CHAIN_ID = "tau-test-live-surface-network-chaos"
ALICE_PRIVKEY = 82
BOB_PRIVKEY = 83
ORACLE_PRIVKEY = 84
OPERATOR_PRIVKEY = 85
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
BOB = "0x" + bls_pubkey_hex_from_privkey(BOB_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(ORACLE_PRIVKEY)
OPERATOR = "0x" + bls_pubkey_hex_from_privkey(OPERATOR_PRIVKEY)
MARKET_ID = "perp:ch2p:network-chaos"


def _zusd_ok(core: Any, tag: str, **kwargs: object) -> Any:
    result = step(core, ZUSDCommand(tag=tag, args=kwargs))
    assert result.ok, result.error
    assert result.state is not None
    return result.state


def _zusd_app_state() -> dict[str, object]:
    monetary = init_monetary_state(ZUSDMonetaryConfig(chain_id=CHAIN_ID, oracle_pubkey=ORACLE))
    core = monetary.core
    core = _zusd_ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _zusd_ok(core, "deposit_collateral", amount_e8=20 * E8)
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(
            DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
        ).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(
            replace(
                monetary,
                core=core,
                vault_owner_pubkey=ALICE,
            )
        ),
    }


def _signed_init_perps_op(*, quote_asset: str) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "deadline": 123456789,
        "nonce_a": 1,
        "nonce_b": 1,
    }
    op["sig_a"] = sign_perp_op_for_engine(
        op,
        privkey=ALICE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ALICE,
        nonce=1,
    )
    op["sig_b"] = sign_perp_op_for_engine(
        op,
        privkey=BOB_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=BOB,
        nonce=1,
    )
    return op


def _perps_app_state() -> dict[str, object]:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    init_result = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID),
        state=state,
        operations={"5": [_signed_init_perps_op(quote_asset=quote_asset)]},
        tx_sender_pubkey=OPERATOR,
        block_timestamp=1,
    )
    assert init_result.ok, init_result.error
    assert init_result.state is not None
    init_result.state.balances.set(ALICE, quote_asset, 5_000)
    return _wrapped_perps_state(init_result.state)


def _wrapped_perps_state(state: DexState) -> dict[str, object]:
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }


class _PacketLossMonetaryClient:
    app_state: dict[str, object] = {}
    attempts: int = 0
    accepted: list[dict[str, object]] = []

    def __init__(self, _cfg: object = None) -> None:
        pass

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        return json.dumps(
            {"app_hash": "sha256:" + "11" * 32, "app_state": self.app_state}, sort_keys=True
        )

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        return 7 if sender_pubkey_hex == ALICE[2:] else 0

    def get_balance(self, _address_hex: str) -> int:
        return 5

    def sendtx(self, _payload: object) -> str:
        type(self).attempts += 1
        raise TauNetRpcError("packet_loss_before_commit")

    def createblock(self) -> str:
        raise AssertionError("createblock must not run after failed sendtx")


class _JitterPerpsClient:
    app_state: dict[str, object] = {}
    attempts: int = 0
    accepted: list[dict[str, object]] = []

    def __init__(self, _cfg: object = None) -> None:
        pass

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        return json.dumps(
            {"app_hash": "sha256:" + "22" * 32, "app_state": self.app_state}, sort_keys=True
        )

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        return 9 if sender_pubkey_hex == ALICE[2:] else 0

    def get_balance(self, _address_hex: str) -> int:
        return 5

    def sendtx(self, _payload: object) -> str:
        type(self).attempts += 1
        raise TauNetRpcError("rpc timed out after 0.2s waiting for response")

    def createblock(self) -> str:
        raise AssertionError("createblock must not run after failed sendtx")


def _assert_redacted_error(payload: dict[str, object], *forbidden: str) -> None:
    detail = str(payload.get("detail", ""))
    for text in forbidden:
        assert text not in detail


def test_live_zusd_and_perps_submit_fail_closed_under_packet_loss_and_jitter(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", "false")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_AUTO_MINE", "true")
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "false")
    monkeypatch.setenv("PERPS_WALLET_AUTO_MINE", "true")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("TAU_DEX_PERP_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)

    _PacketLossMonetaryClient.app_state = _zusd_app_state()
    _PacketLossMonetaryClient.attempts = 0
    _PacketLossMonetaryClient.accepted = []
    monetary_before = copy.deepcopy(_PacketLossMonetaryClient.app_state)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _PacketLossMonetaryClient)

    zusd_body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared_zusd = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(zusd_body).encode("utf-8"),
    )
    assert status_code == 200
    zusd_tx = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared_zusd["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared_zusd["report"]["operations"],
        fee_limit=2,
    )
    status_code, failed_zusd = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps({**zusd_body, "signed_tau_tx_payload": zusd_tx}).encode("utf-8"),
    )
    assert status_code == 502
    assert failed_zusd["error"] == "tau_rpc_error"
    assert _PacketLossMonetaryClient.attempts == 1
    assert _PacketLossMonetaryClient.accepted == []
    assert _PacketLossMonetaryClient.app_state == monetary_before
    _assert_redacted_error(failed_zusd, "mint_zusd", "sender_pubkey", "signature")

    _JitterPerpsClient.app_state = _perps_app_state()
    _JitterPerpsClient.attempts = 0
    _JitterPerpsClient.accepted = []
    perps_before = copy.deepcopy(_JitterPerpsClient.app_state)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _JitterPerpsClient)

    perps_body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared_perps = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(perps_body).encode("utf-8"),
    )
    assert status_code == 200
    perps_tx = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared_perps["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared_perps["report"]["operations"],
        fee_limit=2,
    )
    status_code, failed_perps = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps({**perps_body, "signed_tau_tx_payload": perps_tx}).encode("utf-8"),
    )
    assert status_code == 502
    assert failed_perps["error"] == "tau_rpc_error"
    assert _JitterPerpsClient.attempts == 1
    assert _JitterPerpsClient.accepted == []
    assert _JitterPerpsClient.app_state == perps_before
    _assert_redacted_error(failed_perps, "deposit_collateral", "sender_pubkey", "signature")
