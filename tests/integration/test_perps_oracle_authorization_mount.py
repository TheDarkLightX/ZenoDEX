from __future__ import annotations

import pytest

from src.integration import perps_wallet_api, tau_testnet_dex_plugin

_OPERATOR = "11" * 48
_RECEIPT_GRAPH_ROOT = "sha256:" + "22" * 32
_CURRENT_DISPUTE_STATUS_ROOT = "sha256:" + "33" * 32


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
    monkeypatch.setenv(
        "TAU_DEX_REQUIRE_ORACLE_CURRENT_DISPUTE_STATUS_FOR_ISOLATED_SETTLE",
        "1",
    )
    monkeypatch.setenv(
        "TAU_DEX_REQUIRE_ORACLE_CURRENT_DISPUTE_STATUS_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
        "1",
    )
    monkeypatch.setenv(
        "TAU_DEX_PERP_ORACLE_CURRENT_DISPUTE_STATUS_ROOT",
        _CURRENT_DISPUTE_STATUS_ROOT,
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


def test_wallet_settle_operation_passes_owned_current_dispute_status() -> None:
    status = {
        "schema": "zenodex.oracle.current_dispute_status.v1",
        "current_dispute_status_root": _CURRENT_DISPUTE_STATUS_ROOT,
    }
    body = {
        "market_id": "perp:ch2p:current-dispute-status-mount",
        "operator_pubkey": _OPERATOR,
        "oracle_current_dispute_status": status,
    }

    operation, _sender, _meta = perps_wallet_api._build_operation_and_sender(
        body,
        action="settle_epoch",
        app_state={},
        chain_id="tau-local",
        deadline=1,
    )

    assert operation["oracle_current_dispute_status"] == status
    assert operation["oracle_current_dispute_status"] is not status
    status["current_dispute_status_root"] = "sha256:" + "ff" * 32
    assert (
        operation["oracle_current_dispute_status"]["current_dispute_status_root"]
        == _CURRENT_DISPUTE_STATUS_ROOT
    )


def test_wallet_proof_intent_hash_binds_current_dispute_status() -> None:
    base_operation = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": "perp:ch2p:status-hash-binding",
        "action": "settle_epoch",
        "oracle_current_dispute_status": {
            "schema": "zenodex.oracle.current_dispute_status.v1",
            "current_dispute_status_root": _CURRENT_DISPUTE_STATUS_ROOT,
        },
    }

    def receipt_for(operation: dict[str, object]) -> dict[str, object]:
        return perps_wallet_api._perps_proof_intent_receipt(
            chain_id="tau-local",
            action="settle_epoch",
            operation=operation,
            operations={"5": [operation]},
            app_hash_before="0x" + "11" * 32,
            app_hash_after="0x" + "22" * 32,
            preflight={"ok": True},
            tx_sender_pubkey="0x" + _OPERATOR,
            tx_sequence_number=7,
            tx_fee_limit=1,
            signing_mode="test",
            tau_tx_payload=None,
        )

    original = receipt_for(base_operation)
    mutated_operation = {
        **base_operation,
        "oracle_current_dispute_status": {
            **base_operation["oracle_current_dispute_status"],
            "current_dispute_status_root": "sha256:" + "ff" * 32,
        },
    }
    mutated = receipt_for(mutated_operation)

    assert original["body"]["operation_hash"] != mutated["body"]["operation_hash"]
    assert original["body"]["operations_hash"] != mutated["body"]["operations_hash"]
    assert original["receipt_hash"] != mutated["receipt_hash"]


def test_current_dispute_status_requirement_also_requires_authorization(
    monkeypatch,
) -> None:
    monkeypatch.setenv(
        "TAU_DEX_REQUIRE_ORACLE_CURRENT_DISPUTE_STATUS_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
        "1",
    )
    monkeypatch.delenv(
        "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
        raising=False,
    )

    exercise = perps_wallet_api._oracle_authority_exercise_for_action(
        action="settle_epoch",
        chain_id="tau-local",
        operation={
            "market_id": "perp:ch2p:current-status-implies-authorization",
            "oracle_adapter_bridge": {},
        },
    )

    assert exercise is not None
    assert exercise["oracle_authorization_required"] is True
    assert exercise["oracle_current_dispute_status_required"] is True
    assert "typed oracle authorization is missing from operation" in exercise[
        "readiness_gaps"
    ]
    assert "current oracle dispute status is missing from operation" in exercise[
        "readiness_gaps"
    ]


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
    assert config.require_oracle_current_dispute_status_for_isolated_settle is True
    assert (
        config.require_oracle_current_dispute_status_for_clearinghouse_settle_epoch
        is True
    )
    assert config.oracle_current_dispute_status_root == _CURRENT_DISPUTE_STATUS_ROOT


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
    assert config.require_oracle_current_dispute_status_for_isolated_settle is True
    assert (
        config.require_oracle_current_dispute_status_for_clearinghouse_settle_epoch
        is True
    )
    assert config.oracle_current_dispute_status_root == _CURRENT_DISPUTE_STATUS_ROOT
