from __future__ import annotations

import json
from dataclasses import replace

import pytest

import src.integration.zusd_tau_wallet_api as wallet_api
from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, step
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    init_monetary_state,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id, token_sender_nonce_key
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus

SENDER = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48
OPERATOR = "0x" + "33" * 48
OTHER_OPERATOR = "0x" + "44" * 48
GENERIC_ASSET = "0x" + "77" * 32


def _monetary_policy_state(
    *,
    chain_id: str,
    asset_id: str | None = None,
    supply_units: int = 450,
) -> dict:
    monetary_state = init_monetary_state(
        ZUSDMonetaryConfig(
            chain_id=chain_id,
            asset_id=asset_id,
        )
    )
    core = monetary_state.core
    for command in (
        ZUSDCommand(
            tag="bootstrap_oracle",
            args={"price_e8": 100 * E8, "auth_ok": True},
        ),
        ZUSDCommand(tag="deposit_collateral", args={"amount_e8": 10 * E8}),
        ZUSDCommand(tag="mint_zusd", args={"amount_e8": supply_units * E8}),
    ):
        result = step(core, command)
        assert result.ok is True and result.state is not None
        core = result.state
    return zusd_monetary_state_to_obj(
        replace(
            monetary_state,
            core=core,
            vault_owner_pubkey=SENDER,
        )
    )


def _app_state_payload(
    *,
    asset_id: str,
    chain_id: str = "tau-test-wallet",
    pool_zusd_units: int = 0,
) -> dict:
    assert 0 <= pool_zusd_units <= 50
    balances = BalanceTable()
    balances.set(SENDER, asset_id, 400)
    balances.set(RECIPIENT, asset_id, 50 - pool_zusd_units)
    nonces = NonceTable()
    nonces.set_last(token_sender_nonce_key(SENDER), 4)
    nonces.set_last(token_sender_nonce_key(OPERATOR), 2)
    pools = {}
    if pool_zusd_units:
        pools["pool-zusd-native"] = PoolState(
            pool_id="pool-zusd-native",
            asset0="0x" + "00" * 32,
            asset1=asset_id,
            reserve0=1,
            reserve1=pool_zusd_units,
            fee_bps=30,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=1,
        )
    dex_state = DexState(
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        nonces=nonces,
    )
    return {
        "schema": "zenodex/tau_app_state/v2",
        "version": 2,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": _monetary_policy_state(
            chain_id=chain_id,
            asset_id=asset_id,
        ),
        "generic_token_authority": {
            "schema": "zenodex/generic_token_authority/v1",
            "version": 1,
            "assets": [],
        },
    }


class _FakeClient:
    def __init__(self, _cfg=None) -> None:
        pass

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
        payload = {
            "app_hash": "sha256:" + "ab" * 32,
            "app_state": _app_state_payload(asset_id=asset_id),
        }
        return json.dumps(payload, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == SENDER[2:]:
            return 7
        if sender_pubkey_hex == OPERATOR[2:]:
            return 9
        return 0

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
    assert status["generic_mint_authorities"] == []
    assert "token_operator_pubkey" not in status
    assert "allow_local_signing" not in status
    assert "auto_mine" not in status


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
                "app_state": _app_state_payload(asset_id=custom_asset),
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


@pytest.mark.parametrize("action", [1, True, " TRANSFER", "Transfer"])
def test_prepare_rejects_noncanonical_action_syntax(monkeypatch, action) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": action,
                "sender_pubkey": SENDER,
                "recipient_pubkey": RECIPIENT,
                "amount": 1,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "unsupported_action"}


@pytest.mark.parametrize(
    ("extra_field", "extra_value"),
    [
        ("unexpected", "ignored-before-fix"),
        ("operator_pubkey", OPERATOR),
    ],
)
def test_prepare_rejects_fields_outside_exact_transfer_grammar(
    monkeypatch,
    extra_field: str,
    extra_value: str,
) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "transfer",
        "sender_pubkey": SENDER,
        "recipient_pubkey": RECIPIENT,
        "amount": 1,
        "deadline": 123456789,
        extra_field: extra_value,
    }
    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "unexpected_request_fields"}


@pytest.mark.parametrize("asset_id", [None, 1, "", " 0x" + "11" * 32])
def test_prepare_rejects_explicit_malformed_asset_id(monkeypatch, asset_id) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": "transfer",
                "asset_id": asset_id,
                "sender_pubkey": SENDER,
                "recipient_pubkey": RECIPIENT,
                "amount": 1,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_asset_id"}


@pytest.mark.parametrize("chain_id", [None, 1, True, " tau-test-wallet"])
def test_prepare_rejects_explicit_malformed_chain_id(monkeypatch, chain_id) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": "transfer",
                "chain_id": chain_id,
                "sender_pubkey": SENDER,
                "recipient_pubkey": RECIPIENT,
                "amount": 1,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 400
    expected_error = (
        "bad_chain_id"
        if chain_id in (None, 1, True)
        else "chain_id does not match committed zUSD policy"
    )
    assert payload == {"ok": False, "error": expected_error}


def test_prepare_supply_includes_pool_balance_location(monkeypatch) -> None:
    class _PoolBalanceClient(_FakeClient):
        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
            return json.dumps(
                {
                    "app_hash": "sha256:" + "ef" * 32,
                    "app_state": _app_state_payload(
                        asset_id=asset_id,
                        pool_zusd_units=50,
                    ),
                },
                sort_keys=True,
            )

    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _PoolBalanceClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
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
    assert payload["transport"]["sender_balance_before"] == 400
    assert payload["transport"]["recipient_balance_before"] == 0
    assert payload["transport"]["total_supply_before"] == 450


def test_prepare_rejects_legacy_state_without_committed_token_authority(
    monkeypatch,
) -> None:
    class _LegacyStateClient(_FakeClient):
        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
            app_state = _app_state_payload(asset_id=asset_id)
            app_state["schema"] = "zenodex/tau_app_state/v1"
            app_state["version"] = 1
            app_state.pop("generic_token_authority")
            return json.dumps(
                {
                    "app_hash": "sha256:" + "aa" * 32,
                    "app_state": app_state,
                },
                sort_keys=True,
            )

    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _LegacyStateClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": "transfer",
                "sender_pubkey": SENDER,
                "recipient_pubkey": RECIPIENT,
                "amount": 1,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 502
    assert payload == {
        "ok": False,
        "error": "tau_rpc_error",
        "detail": "authoritative app state must use schema v2",
    }


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


def test_prepare_generic_mint_requires_committed_asset_authority(monkeypatch) -> None:
    class _GenericAssetClient(_FakeClient):
        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            zusd_asset = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")
            app_state = _app_state_payload(asset_id=zusd_asset)
            app_state["dex_state"]["balances"].append(
                {
                    "pubkey": RECIPIENT,
                    "asset": GENERIC_ASSET,
                    "amount": 5,
                }
            )
            app_state["generic_token_authority"]["assets"] = [
                {
                    "asset_id": GENERIC_ASSET,
                    "total_supply_units": 5,
                    "mint_authority_pubkey": OPERATOR,
                }
            ]
            return json.dumps(
                {
                    "app_hash": "sha256:" + "be" * 32,
                    "app_state": app_state,
                },
                sort_keys=True,
            )

    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _GenericAssetClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(
            {
                "action": "mint",
                "asset_id": GENERIC_ASSET,
                "operator_pubkey": OTHER_OPERATOR,
                "recipient_pubkey": RECIPIENT,
                "amount": 1,
                "deadline": 123456789,
            }
        ).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {
        "ok": False,
        "error": "generic token authority rejected: unauthorized_mint",
    }


@pytest.mark.parametrize(
    ("secret_fields", "expected_path"),
    [
        ({"signer_privkey": "1"}, "signer_privkey"),
        ({"metadata": {"private_key": "1"}}, "metadata.private_key"),
        ({"metadata": [{"seed_phrase": "do not accept"}]}, "metadata[0].seed_phrase"),
    ],
)
def test_prepare_recursively_rejects_raw_signing_material(
    monkeypatch,
    secret_fields: dict[str, object],
    expected_path: str,
) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "transfer",
        "sender_pubkey": SENDER,
        "recipient_pubkey": RECIPIENT,
        "amount": 100,
        "deadline": 123456789,
        **secret_fields,
    }
    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {
        "ok": False,
        "error": f"raw_signing_material_forbidden:{expected_path}",
    }


def test_submit_endpoint_is_absent(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", "tau-test-wallet")
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "POST",
        "/api/zusd/wallet/submit",
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

    assert status_code == 404
    assert payload == {"ok": False, "error": "not_found"}
