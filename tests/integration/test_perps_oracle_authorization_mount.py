from __future__ import annotations

import pytest

from src.integration import perps_wallet_api, tau_testnet_dex_plugin

_OPERATOR = "11" * 48
_RECEIPT_GRAPH_ROOT = "sha256:" + "22" * 32


def _set_perps_authorization_env(monkeypatch) -> None:
    monkeypatch.setenv(
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH",
        "1",
    )
    monkeypatch.setenv(
        "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE",
        "1",
    )
    monkeypatch.setenv(
        "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
        "1",
    )
    monkeypatch.setenv(
        "TAU_DEX_PERP_ORACLE_AUTHORIZATION_RECEIPT_GRAPH_ROOT",
        _RECEIPT_GRAPH_ROOT,
    )


def test_wallet_settle_operation_passes_owned_oracle_authorization() -> None:
    # Arrange: the wallet receives a typed authorization object with a settle
    # request. The adapter must copy it into the engine operation.
    authorization = {
        "schema": "zenodex.oracle.authorization.envelope.v1",
        "authorization": {"receipt_graph_root": _RECEIPT_GRAPH_ROOT},
    }
    body = {
        "market_id": "perp:ch2p:oracle-authorization-mount",
        "operator_pubkey": _OPERATOR,
        "oracle_authorization": authorization,
    }

    # Act.
    operation, sender, _meta = perps_wallet_api._build_operation_and_sender(
        body,
        action="settle_epoch",
        app_state={},
        chain_id="tau-local",
        deadline=1,
    )

    # Assert: the engine receives an exact owned dictionary, independent from
    # subsequent caller mutation.
    assert sender == "0x" + _OPERATOR
    assert operation["oracle_authorization"] == authorization
    assert operation["oracle_authorization"] is not authorization
    authorization["authorization"]["receipt_graph_root"] = "sha256:" + "ff" * 32
    assert (
        operation["oracle_authorization"]["authorization"]["receipt_graph_root"]
        == _RECEIPT_GRAPH_ROOT
    )


def test_wallet_settle_operation_rejects_mapping_subclass_authorization() -> None:
    # Arrange: caller-defined mapping behavior must not cross the API boundary.
    class AuthorizationDict(dict):
        pass

    body = {
        "market_id": "perp:ch2p:oracle-authorization-subclass",
        "operator_pubkey": _OPERATOR,
        "oracle_authorization": AuthorizationDict({"schema": "hostile"}),
    }

    # Act and assert.
    with pytest.raises(ValueError, match="^bad_oracle_authorization$"):
        perps_wallet_api._build_operation_and_sender(
            body,
            action="settle_epoch",
            app_state={},
            chain_id="tau-local",
            deadline=1,
        )


def test_wallet_perps_config_binds_authorization_controls(monkeypatch) -> None:
    # Arrange.
    _set_perps_authorization_env(monkeypatch)

    # Act.
    config = perps_wallet_api._build_perp_config(chain_id="tau-local")

    # Assert.
    assert config.require_oracle_adapter_for_isolated_settle_epoch is True
    assert config.require_oracle_authorization_for_isolated_settle is True
    assert config.require_oracle_authorization_for_clearinghouse_settle_epoch is True
    assert config.oracle_authorization_receipt_graph_root == _RECEIPT_GRAPH_ROOT


def test_tau_testnet_perps_config_binds_authorization_controls(monkeypatch) -> None:
    # Arrange.
    _set_perps_authorization_env(monkeypatch)

    # Act.
    config = tau_testnet_dex_plugin._build_perp_engine_config(chain_id="tau-local")

    # Assert.
    assert config.require_oracle_adapter_for_isolated_settle_epoch is True
    assert config.require_oracle_authorization_for_isolated_settle is True
    assert config.require_oracle_authorization_for_clearinghouse_settle_epoch is True
    assert config.oracle_authorization_receipt_graph_root == _RECEIPT_GRAPH_ROOT
