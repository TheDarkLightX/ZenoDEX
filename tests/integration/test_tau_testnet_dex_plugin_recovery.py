from __future__ import annotations

import json

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _empty_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _wrapped_state(*, schema: str = "zenodex/tau_app_state/v1", version: int = 1) -> str:
    return json.dumps(
        {
            "schema": schema,
            "version": version,
            "dex_state": snapshot_from_state(_empty_state()).data,
            "proof_mining": None,
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def test_apply_app_tx_rejects_truncated_app_state_json_and_preserves_previous_blob(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    bad_state = '{"schema":"zenodex/tau_app_state/v1","version":1'
    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=bad_state,
        chain_balances={},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=1,
    )
    assert ok is False
    assert app_state_json == bad_state
    assert app_hash_hex == ""
    assert balances_patch is None
    assert isinstance(err, str) and "invalid app_state_json" in err


def test_apply_app_tx_rejects_wrapper_schema_drift_and_preserves_previous_blob(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    bad_state = _wrapped_state(schema="zenodex/tau_app_state/v2")
    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=bad_state,
        chain_balances={},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=1,
    )
    assert ok is False
    assert app_state_json == bad_state
    assert app_hash_hex == ""
    assert balances_patch is None
    assert err == (
        "invalid app_state snapshot: app_state schema/version mismatch: "
        "expected 'zenodex/tau_app_state/v1' for version 1"
    )


def test_apply_app_tx_rejects_wrapper_version_drift_and_preserves_previous_blob(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    bad_state = _wrapped_state(version=2)
    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=bad_state,
        chain_balances={},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=1,
    )
    assert ok is False
    assert app_state_json == bad_state
    assert app_hash_hex == ""
    assert balances_patch is None
    assert err == (
        "invalid app_state snapshot: app_state schema/version mismatch: "
        "expected 'zenodex/tau_app_state/v2' for version 2"
    )


def test_apply_app_tx_rejects_wrapper_like_payload_missing_schema(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    bad_state = json.dumps(
        {
            "version": 1,
            "dex_state": snapshot_from_state(_empty_state()).data,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=bad_state,
        chain_balances={},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=1,
    )
    assert ok is False
    assert app_state_json == bad_state
    assert app_hash_hex == ""
    assert balances_patch is None
    assert err == (
        "invalid app_state snapshot: app_state schema/version mismatch: "
        "expected 'zenodex/tau_app_state/v1' for version 1"
    )


def test_apply_app_tx_rejects_oversized_app_state_json_before_parse(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setattr(plugin, "_MAX_APP_STATE_JSON_BYTES", 32)
    bad_state = json.dumps({"schema": "zenodex/tau_app_state/v1", "version": 1, "junk": "x" * 64})
    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=bad_state,
        chain_balances={},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=1,
    )
    assert ok is False
    assert app_state_json == bad_state
    assert app_hash_hex == ""
    assert balances_patch is None
    assert err == "app_state_json too large"
