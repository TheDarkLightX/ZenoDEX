from __future__ import annotations

import json

import pytest

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perp_engine import PerpEngineConfig, _kernel_initial_global_state, apply_perp_ops
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
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
ISOLATED_MARKET_ID = "perp:isolated:test"


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


def _state_ready_to_settle(*, quote_asset: str) -> DexState:
    state = _state_with_advanced_market(quote_asset=quote_asset)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "publish_clearing_price",
        "price_e8": 100_000_000,
        "deadline": 123456789,
        "oracle_nonce": 1,
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=1,
    )
    return _apply_perps(state, [op], sender=ORACLE)


def _signed_set_position_pair(*, new_a: int, new_b: int, nonce_a: int, nonce_b: int) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "set_position_pair",
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "new_position_base_a": int(new_a),
        "new_position_base_b": int(new_b),
        "deadline": 123456789,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _signed_publish_price(*, price_e8: int, oracle_nonce: int) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": 123456789,
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


def _state_after_pair_liquidation(*, quote_asset: str) -> DexState:
    state = _state_ready_to_settle(quote_asset=quote_asset)
    state = _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
    )
    state.balances.set(ALICE, quote_asset, 1000)
    state.balances.set(BOB, quote_asset, 1000)
    state = _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": ALICE,
                "amount": 100,
            }
        ],
        sender=ALICE,
    )
    state = _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": BOB,
                "amount": 100,
            }
        ],
        sender=BOB,
    )
    state = _apply_perps(state, [_signed_set_position_pair(new_a=1000, new_b=-1000, nonce_a=2, nonce_b=2)])
    state = _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )
    state = _apply_perps(state, [_signed_publish_price(price_e8=105_000_000, oracle_nonce=2)], sender=ORACLE)
    return _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
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


def _state_with_isolated_liquidatable_account(*, quote_asset: str) -> DexState:
    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 5,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 10_000_000_000,
            "max_oracle_staleness_epochs": 100,
            "max_oracle_move_bps": 500,
            "initial_margin_bps": 1000,
            "maintenance_margin_bps": 500,
            "depeg_buffer_bps": 100,
            "liquidation_penalty_bps": 50,
            "max_position_abs": 1_000_000,
            "fee_pool_quote": 0,
            "fee_income": 0,
            "initial_insurance": 100_000,
            "insurance_balance": 100_000,
            "claims_paid": 0,
            "min_notional_for_bounty": 100_000_000,
        }
    )
    market = PerpMarketState(
        quote_asset=quote_asset,
        global_state=global_state,
        accounts={
            ALICE: PerpAccountState(
                position_base=100,
                entry_price_e8=10_000_000_000,
                collateral_quote=300,
                funding_paid_cumulative=0,
                funding_last_applied_epoch=0,
                liquidated_this_step=False,
            )
        },
    )
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={ISOLATED_MARKET_ID: market}),
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
    assert payload["transport"]["quote_balance"] == 5_000
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


def test_oracle_bridge_template_preflights_required_settle_epoch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )

    assert status_code == 200
    assert bridge_payload["ok"] is True
    assert bridge_payload["fixture_kind"] == "local_o3_aggregate_adapter"
    assert bridge_payload["production_authority"] is False
    assert bridge_payload["verify_result"]["status"] == "accepted"
    assert bridge_payload["target"]["consumer_module"] == "zenodex.perps"
    assert bridge_payload["target"]["action_kind"] == "settle_epoch"

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
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
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_adapter_bridge"]["bridge_id"] == bridge_payload["bridge"]["bridge_id"]


def test_status_exposes_clearinghouse_liquidation_summary_fields(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    markets = payload["status"]["markets"]
    assert len(markets) == 1
    market = markets[0]
    assert market["market_id"] == MARKET_ID
    assert market["liquidated_this_step"] is True
    assert market["account_a_quote_balance"] == 900
    assert market["account_b_quote_balance"] == 900
    assert market["fee_pool_e8"] == 525_000_000
    assert market["position_base_a"] == 0
    assert market["position_base_b"] == 0
    assert market["net_deposited_e8"] == 20_000_000_000


def test_prepare_partial_liquidate_is_opt_in_for_isolated_markets(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("TAU_DEX_ALLOW_ISOLATED_PERPS", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 2500,
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
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["preflight"]["ok"] is False
    assert "isolated perps disabled" in payload["report"]["preflight"]["error"]


def test_prepare_partial_liquidate_accepts_auto_fraction_zero(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 0,
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
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["operation"]["fraction_bps"] == 0


def test_oracle_bridge_template_preflights_required_partial_liquidate(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, bridge_payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps(
            {
                "action": "partial_liquidate",
                "market_id": ISOLATED_MARKET_ID,
                "account_pubkey": ALICE,
                "fraction_bps": 0,
            }
        ).encode("utf-8"),
    )

    assert status_code == 200
    assert bridge_payload["ok"] is True
    assert bridge_payload["action"] == "partial_liquidate"
    assert bridge_payload["target"]["action_kind"] == "liquidate_account"
    assert bridge_payload["target"]["wallet_action"] == "partial_liquidate"
    assert bridge_payload["verify_result"]["status"] == "accepted"

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 0,
        "oracle_adapter_bridge": bridge_payload["bridge"],
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
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_adapter_bridge"]["bridge_id"] == bridge_payload["bridge"]["bridge_id"]


def test_submit_partial_liquidate_builds_account_bound_stream_8_tx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "fraction_bps": 5000,
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
    assert payload["transport"]["stream_key"] == "8"
    assert payload["transport"]["tx_sender_pubkey"] == ALICE
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["operation"]["fraction_bps"] == 5000
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]
    wire_ops = json.loads(payload["report"]["tau_tx_payload"]["operations"]["8"])
    assert wire_ops[0]["action"] == "partial_liquidate"
    assert wire_ops[0]["account_pubkey"] == ALICE
    assert wire_ops[0]["fraction_bps"] == 5000
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"


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
