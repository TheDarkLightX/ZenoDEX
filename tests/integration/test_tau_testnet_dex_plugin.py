import copy
import hashlib
import json
import sys

import pytest


@pytest.fixture(autouse=True)
def _explicit_test_deployment_profile(monkeypatch):
    monkeypatch.setenv("TAU_DEX_DEPLOYMENT_PROFILE", "test")


def test_missing_settlement_policy_defaults_to_reject(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.delenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", raising=False)
    assert plugin._allow_missing_settlement_from_env() is False


def test_missing_settlement_policy_rejects_malformed_boolean(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "truthy")
    with pytest.raises(ValueError, match="strict boolean"):
        plugin._allow_missing_settlement_from_env()
    result = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=0,
    )
    assert result[0] is False
    assert result[4] == "TAU_DEX_ALLOW_MISSING_SETTLEMENT must be a strict boolean"


def test_missing_settlement_policy_rejects_non_test_profile(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "true")
    monkeypatch.setenv("TAU_DEX_DEPLOYMENT_PROFILE", "production")
    with pytest.raises(ValueError, match="restricted"):
        plugin._allow_missing_settlement_from_env()


def _policy_bound_empty_state(plugin) -> str:
    chain_id = plugin.os.environ.get("TAU_DEX_CHAIN_ID", "").strip() or "tau-local"
    config = plugin._build_zusd_monetary_config(chain_id=chain_id)
    app_state_json, _app_hash = plugin.build_zusd_policy_bound_genesis_app_state(config=config)
    return app_state_json


def _policy_bound_generic_state(
    plugin,
    *,
    assets: tuple[str, ...],
    mint_authority_pubkey: str,
) -> str:
    from src.core.generic_token_authority import (
        GenericTokenAssetAuthority,
        GenericTokenAuthorityState,
    )

    chain_id = plugin.os.environ.get("TAU_DEX_CHAIN_ID", "").strip() or "tau-local"
    config = plugin._build_zusd_monetary_config(chain_id=chain_id)
    registrations = tuple(
        sorted(
            (
                GenericTokenAssetAuthority(
                    asset_id=asset,
                    total_supply_units=0,
                    mint_authority_pubkey=mint_authority_pubkey,
                )
                for asset in assets
            ),
            key=lambda registration: registration.asset_id,
        )
    )
    app_state_json, _app_hash = plugin.build_zusd_policy_bound_genesis_app_state(
        config=config,
        generic_token_authority=GenericTokenAuthorityState(
            assets=registrations
        ),
    )
    return app_state_json


def _dex_snapshot_from_app_state_json(app_state_json: str) -> dict:
    payload = json.loads(app_state_json)
    nested = payload.get("dex_state")
    return nested if isinstance(nested, dict) else payload


def _intent_signing_dict_from_tx_intent(intent_dict: dict) -> dict:
    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    return {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": intent.deadline,
        "fields": intent.fields or {},
        **({"salt": intent.salt} if intent.salt is not None else {}),
    }


def _parse_single_intent(intent_dict: dict):
    from src.integration.operations import parse_intents

    return parse_intents({"2": [intent_dict]})[0]


def _settlement_commitment_dict_from_settlement(settlement_obj: dict) -> dict:
    out = {k: v for k, v in settlement_obj.items() if k not in ("batch_ref", "events", "proof")}
    fills = out.get("fills") or []
    out["fills"] = [
        {k: v for k, v in fill.items() if v is not None and k != "reason"}
        for fill in fills
        if isinstance(fill, dict)
    ]
    return out


def _batch_commitment(*, signing_dicts: list[dict], settlement_obj: dict) -> str:
    from src.state.canonical import (
        CANONICAL_ENCODING_VERSION,
        canonical_json_bytes,
        domain_sep_bytes,
        sha256_hex,
    )

    payload = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": signing_dicts,
        "settlement": _settlement_commitment_dict_from_settlement(settlement_obj),
    }
    return sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload))


def test_apply_app_tx_sync_only(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.dex_snapshot import DEX_SNAPSHOT_VERSION

    monkeypatch.delenv("TAU_DEX_FAUCET", raising=False)
    monkeypatch.delenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", raising=False)
    monkeypatch.delenv("TAU_DEX_REQUIRE_INTENT_SIGS", raising=False)
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={"00" * 48: 123},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=123,
    )
    assert ok is True
    assert err is None
    assert isinstance(app_state_json, str) and app_state_json
    assert isinstance(app_hash_hex, str) and len(app_hash_hex) == 64
    assert balances_patch is None

    parsed = _dex_snapshot_from_app_state_json(app_state_json)
    assert isinstance(parsed, dict)
    assert parsed.get("version") == DEX_SNAPSHOT_VERSION


def test_apply_app_tx_rejects_policy_sensitive_ops_before_policy_bound_genesis(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "01" * 48
    token = "0x" + "02" * 32
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-unbound-policy")

    ok, returned_state, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "burn",
                    "asset": token,
                    "amount": 1,
                    "nonce": 1,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert returned_state == ""
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "zUSD monetary policy is absent from authoritative state; "
        "install a policy-bound genesis or governed migration first"
    )


def test_apply_app_tx_rejects_zusd_transition_from_v1_app_state(
    monkeypatch,
) -> None:
    from src.core.dex import DexState
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state import BalanceTable, LPTable

    chain_id = "tau-v1-zusd-reject"
    oracle = "0x" + "03" * 48
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", oracle)
    config = plugin._build_zusd_monetary_config(chain_id=chain_id)
    legacy_json, _legacy_hash = plugin._canonical_state_and_hash(
        DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
        zusd_monetary_state=plugin.init_monetary_state(config),
    )
    assert json.loads(legacy_json)["version"] == 1

    ok, returned_state, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=legacy_json,
        chain_balances={},
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                }
            ]
        },
        tx_sender_pubkey=oracle,
        block_timestamp=1,
    )

    assert ok is False
    assert returned_state == legacy_json
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "generic token authority is absent from app state; "
        "install a v2 genesis or governed migration first"
    )


def test_apply_app_tx_replay_uses_committed_economics_across_environment_drift(
    monkeypatch,
) -> None:
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin

    chain_id = "tau-policy-replay"
    actor = "0x" + "03" * 48
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", actor)
    monkeypatch.setenv("TAU_DEX_ZUSD_BORROW_FEE_FLOOR_BPS", "0")
    genesis = _policy_bound_empty_state(plugin)
    operations = {
        "11": [
            {
                "module": "ZUSDFinance",
                "action": "bootstrap_oracle",
                "price_e8": 100 * E8,
                "nonce": 1,
            },
            {
                "module": "ZUSDFinance",
                "action": "deposit_collateral",
                "owner_pubkey": actor,
                "amount_e8": 2 * E8,
                "nonce": 2,
            },
            {
                "module": "ZUSDFinance",
                "action": "mint_zusd",
                "owner_pubkey": actor,
                "amount_e8": 100 * E8,
                "nonce": 3,
            },
        ]
    }

    first = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={actor: 2 * E8},
        operations=operations,
        tx_sender_pubkey=actor,
        block_timestamp=1,
    )
    monkeypatch.setenv("TAU_DEX_ZUSD_BORROW_FEE_FLOOR_BPS", "100")
    second = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={actor: 2 * E8},
        operations=operations,
        tx_sender_pubkey=actor,
        block_timestamp=1,
    )

    assert first == second
    assert first[0] is True
    payload = json.loads(first[1])
    assert payload["zusd_monetary"]["core"]["debt_e8"] == 100 * E8
    assert payload["zusd_monetary"]["protocol_zusd_fee_reserve_e8"] == 0


def test_apply_app_tx_create_pool_unsigned_intent(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    sender_pubkey = "00" * 48
    canonical_sender_pubkey = "0x" + sender_pubkey
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(asset0, asset1),
            mint_authority_pubkey=canonical_sender_pubkey,
        ),
        chain_balances={sender_pubkey: 123},
        operations={
            "7": {
                "mint": [
                    [canonical_sender_pubkey, asset0, 10_000],
                    [canonical_sender_pubkey, asset1, 10_000],
                ]
            },
            "5": [intent],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )

    assert ok is True
    assert err is None
    assert isinstance(app_state_json, str) and app_state_json
    assert isinstance(app_hash_hex, str) and len(app_hash_hex) == 64
    assert balances_patch in (None, {})

    parsed = _dex_snapshot_from_app_state_json(app_state_json)
    assert isinstance(parsed, dict)
    pools = parsed.get("pools")
    assert isinstance(pools, list) and pools


def test_apply_app_tx_swap_exact_in(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    sender_pubkey = "00" * 48
    canonical_sender_pubkey = "0x" + sender_pubkey
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    create_pool_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    ok, app_state_json, app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(asset0, asset1),
            mint_authority_pubkey=canonical_sender_pubkey,
        ),
        chain_balances={sender_pubkey: 123},
        operations={
            "7": {
                "mint": [
                    [canonical_sender_pubkey, asset0, 10_000],
                    [canonical_sender_pubkey, asset1, 10_000],
                ]
            },
            "5": [create_pool_intent],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )
    assert ok is True
    assert err is None
    assert isinstance(app_hash_hex, str) and len(app_hash_hex) == 64

    parsed = _dex_snapshot_from_app_state_json(app_state_json)
    pools = parsed.get("pools")
    assert isinstance(pools, list) and pools
    pool_id = pools[0]["pool_id"]

    balances_before = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed.get("balances") or [])
        if isinstance(b, dict)
    }
    before_in = int(balances_before.get((canonical_sender_pubkey, asset0), 0))
    before_out = int(balances_before.get((canonical_sender_pubkey, asset1), 0))

    swap_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 2,
        "pool_id": pool_id,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 100,
        "min_amount_out": 1,
        "recipient": sender_pubkey,
    }
    ok, app_state_json2, _app_hash_hex2, _balances_patch2, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={sender_pubkey: 123},
        operations={"5": [swap_intent]},
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=124,
    )
    assert ok is True
    assert err is None

    parsed2 = _dex_snapshot_from_app_state_json(app_state_json2)
    balances_after = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed2.get("balances") or [])
        if isinstance(b, dict)
    }
    after_in = int(balances_after.get((canonical_sender_pubkey, asset0), 0))
    after_out = int(balances_after.get((canonical_sender_pubkey, asset1), 0))

    assert after_in < before_in
    assert after_out > before_out


def test_apply_app_tx_zero_output_swap_is_atomic_reject_noop(monkeypatch) -> None:
    """CPMM-IN-003: a computed rejection cannot consume nonce or move value."""
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.dex_engine import DexEngineConfig, apply_ops

    sender_pubkey = "00" * 48
    canonical_sender_pubkey = "0x" + sender_pubkey
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    create_pool_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 50,
        "amount0": 1000,
        "amount1": 2000,
    }
    created, app_state_json, app_hash, setup_patch, setup_error = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(asset0, asset1),
            mint_authority_pubkey=canonical_sender_pubkey,
        ),
        chain_balances={sender_pubkey: 123},
        operations={
            "7": {
                "mint": [
                    [canonical_sender_pubkey, asset0, 10_000],
                    [canonical_sender_pubkey, asset1, 10_000],
                ]
            },
            "5": [create_pool_intent],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )
    assert created is True
    assert setup_error is None
    assert setup_patch in (None, {})
    assert hashlib.sha256(app_state_json.encode("utf-8")).hexdigest() == app_hash

    pool_id = _dex_snapshot_from_app_state_json(app_state_json)["pools"][0]["pool_id"]
    swap_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 2,
        "pool_id": pool_id,
        "asset_in": asset1,
        "asset_out": asset0,
        "amount_in": 2,
        "min_amount_out": 1,
        "recipient": sender_pubkey,
    }
    operations = {"5": [swap_intent]}
    chain_balances = {sender_pubkey: 123}
    operations_before = copy.deepcopy(operations)
    chain_balances_before = copy.deepcopy(chain_balances)
    dex_state, _proof_mining, _zusd, _token_authority = plugin._load_state(
        app_state_json
    )
    engine_result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            chain_id="tau-local",
            canonicalize_authenticated_bls_principals=True,
            proof_config=plugin._build_proof_verifier_config(),
        ),
        state=dex_state,
        operations={"2": [swap_intent]},
        block_timestamp=124,
        tx_sender_pubkey=canonical_sender_pubkey,
    )
    expected_error = (
        "settlement contains rejected intent at public DEX boundary: "
        + swap_intent["intent_id"]
    )
    assert engine_result.ok is False
    assert engine_result.state is None
    assert engine_result.settlement is None
    assert engine_result.error == expected_error
    assert dex_state.nonces.get_last(canonical_sender_pubkey) == 1

    committed, committed_state, committed_hash, balances_patch, error = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances=chain_balances,
        operations=operations,
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=124,
    )

    assert committed is False
    assert error == expected_error
    assert committed_state == app_state_json
    assert committed_hash == ""
    assert balances_patch is None
    assert operations == operations_before
    assert chain_balances == chain_balances_before

    replay_ok, replay_state, replay_hash, replay_patch, replay_error = plugin.apply_app_tx(
        app_state_json=committed_state,
        chain_balances=chain_balances,
        operations=operations,
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=125,
    )
    assert replay_ok is False
    assert replay_state == committed_state
    assert replay_hash == ""
    assert replay_patch is None
    assert replay_error == expected_error
    assert operations == operations_before
    assert chain_balances == chain_balances_before


def test_apply_app_tx_create_pool_with_native_asset_updates_chain_balance(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state.balances import NATIVE_ASSET

    sender_pubkey = "00" * 48
    canonical_sender_pubkey = "0x" + sender_pubkey
    token = "0x" + "11" * 32

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": NATIVE_ASSET,
        "asset1": token,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, app_state_json, _app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(token,),
            mint_authority_pubkey=canonical_sender_pubkey,
        ),
        chain_balances={sender_pubkey: 10_000},
        operations={
            "7": {"mint": [[canonical_sender_pubkey, token, 10_000]]},
            "5": [intent],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )
    assert ok is True
    assert err is None
    assert balances_patch == {sender_pubkey: 9000}

    ok2, synced_json, _synced_hash, synced_patch, err2 = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances=balances_patch,
        operations={},
        tx_sender_pubkey="",
        block_timestamp=124,
    )
    assert ok2 is True
    assert err2 is None
    assert synced_patch is None

    parsed = _dex_snapshot_from_app_state_json(synced_json)
    balances = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed.get("balances") or [])
        if isinstance(b, dict)
    }
    assert balances.get((canonical_sender_pubkey, NATIVE_ASSET)) == 9000


def test_apply_app_tx_native_output_uses_raw_tau_key_for_absent_recipient(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state.balances import NATIVE_ASSET

    sender_pubkey = "00" * 48
    canonical_sender = "0x" + sender_pubkey
    recipient_pubkey = "11" * 48
    canonical_recipient = "0x" + recipient_pubkey
    token = "0x" + "12" * 32

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    create_pool = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "a1" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": NATIVE_ASSET,
        "asset1": token,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    created, app_state_json, _app_hash, create_patch, create_error = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(token,),
            mint_authority_pubkey=canonical_sender,
        ),
        chain_balances={sender_pubkey: 10_000},
        operations={
            "7": {"mint": [[canonical_sender, token, 10_000]]},
            "5": [create_pool],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )
    assert created is True, create_error
    assert create_patch == {sender_pubkey: 9000}
    pool_id = _dex_snapshot_from_app_state_json(app_state_json)["pools"][0]["pool_id"]

    swap = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "a2" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
        "nonce": 2,
        "pool_id": pool_id,
        "asset_in": token,
        "asset_out": NATIVE_ASSET,
        "amount_in": 100,
        "min_amount_out": 1,
        "recipient": recipient_pubkey,
    }
    accepted, _next_json, _next_hash, patch, error = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances=create_patch,
        operations={"5": [swap]},
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=124,
    )

    assert accepted is True, error
    assert patch is not None
    assert patch[recipient_pubkey] > 0
    assert canonical_recipient not in patch


def test_apply_app_tx_routes_upstream_streams_to_internal_engines(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    captured = {"dex_ops": None, "perp_ops": None}

    class _Res:
        def __init__(self, ok, state, error=None):
            self.ok = ok
            self.state = state
            self.error = error

    def _fake_apply_ops(*, config, state, operations, block_timestamp, tx_sender_pubkey):
        captured["dex_ops"] = operations
        return _Res(True, state)

    def _fake_apply_perp_ops(*, config, state, operations, tx_sender_pubkey, block_timestamp):
        captured["perp_ops"] = operations
        return _Res(True, state)

    monkeypatch.setattr(plugin, "apply_ops", _fake_apply_ops)
    monkeypatch.setattr(plugin, "apply_perp_ops", _fake_apply_perp_ops)

    ok, _app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={
            "5": [{"module": "TauSwap", "kind": "CREATE_POOL"}],
            "6": {"swaps": []},
            "8": [{"module": "TauPerp", "action": "apply_funding_auto"}],
        },
        tx_sender_pubkey="",
        block_timestamp=123,
    )

    assert ok is True
    assert err is None
    assert captured["dex_ops"] == {
        "2": [{"module": "TauSwap", "kind": "CREATE_POOL"}],
        "3": {"swaps": []},
    }
    assert captured["perp_ops"] == {
        "5": [{"module": "TauPerp", "action": "apply_funding_auto"}],
    }


def test_apply_app_tx_legacy_stream_5_perps_fallback(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    captured = {"perp_ops": None}

    class _Res:
        def __init__(self, ok, state, error=None):
            self.ok = ok
            self.state = state
            self.error = error

    def _fake_apply_ops(*, config, state, operations, block_timestamp, tx_sender_pubkey):
        raise AssertionError("DEX engine should not run for legacy-perp stream fallback")

    def _fake_apply_perp_ops(*, config, state, operations, tx_sender_pubkey, block_timestamp):
        captured["perp_ops"] = operations
        return _Res(True, state)

    monkeypatch.setattr(plugin, "apply_ops", _fake_apply_ops)
    monkeypatch.setattr(plugin, "apply_perp_ops", _fake_apply_perp_ops)

    ok, _app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={"5": [{"action": "apply_funding_auto"}]},
        tx_sender_pubkey="",
        block_timestamp=123,
    )

    assert ok is True
    assert err is None
    assert captured["perp_ops"] == {"5": [{"action": "apply_funding_auto"}]}


def test_apply_app_tx_rejects_non_object_operations(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    ok, _app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations=[],  # type: ignore[arg-type]
        tx_sender_pubkey="",
        block_timestamp=1,
    )
    assert ok is False
    assert app_hash_hex == ""
    assert balances_patch is None
    assert err == "operations must be an object"


def test_apply_app_tx_token_transfer_updates_balances_and_nonce(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "11" * 48
    recipient = "0x" + "22" * 48
    token = "0x" + "33" * 32

    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.delenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", raising=False)

    ok, app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(token,),
            mint_authority_pubkey=sender,
        ),
        chain_balances={},
        operations={
            "7": {"mint": [[sender, token, 1000]]},
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": token,
                    "sender_pubkey": sender,
                    "to_pubkey": recipient,
                    "amount": 250,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ],
        },
        tx_sender_pubkey=sender,
        block_timestamp=100,
    )
    assert ok is True
    assert err is None

    parsed = _dex_snapshot_from_app_state_json(app_state_json)
    balances = {(b["pubkey"], b["asset"]): int(b["amount"]) for b in parsed.get("balances", [])}
    assert balances.get((sender, token)) == 750
    assert balances.get((recipient, token)) == 250

    ok2, _app_state2, _app_hash2, _balances2, err2 = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": token,
                    "sender_pubkey": sender,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=101,
    )
    assert ok2 is False
    assert isinstance(err2, str) and "nonce invalid" in err2


def test_apply_app_tx_token_self_transfer_rejects_atomically(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "12" * 48
    token = "0x" + "34" * 32
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-token-self-transfer")

    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=sender,
    )
    ok, app_state_json, _app_hash, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={
            "7": {"mint": [[sender, token, 100]]},
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": token,
                    "sender_pubkey": sender,
                    "to_pubkey": sender,
                    "amount": 40,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ],
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == genesis
    assert err == "token op[0] authority transition rejected: self_transfer"


def test_apply_app_tx_token_unhashable_action_rejects_atomically(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "12" * 48
    token = "0x" + "35" * 32
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-token-malformed-action")

    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=sender,
    )
    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={"9": [{"action": []}]},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == genesis
    assert app_hash == ""
    assert balances_patch is None
    assert err == "token op[0] action unsupported: []"


def test_apply_app_tx_faucet_extra_field_rejects_atomically(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "13" * 48
    token = "0x" + "36" * 32
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-faucet-extra-field")

    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=sender,
    )
    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={"7": {"mint": [[sender, token, 1]], "extra": 1}},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == genesis
    assert app_hash == ""
    assert balances_patch is None
    assert err == "faucet op fields must match exactly"


def test_apply_app_tx_faucet_only_postcheck_rejects_atomically(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "13" * 48
    token = "0x" + "37" * 32
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-faucet-postcheck")
    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=sender,
    )
    accounting_checks = 0

    def forced_second_accounting_failure(**_kwargs: object) -> str | None:
        nonlocal accounting_checks
        accounting_checks += 1
        return None if accounting_checks == 1 else "forced_postcheck_failure"

    monkeypatch.setattr(
        plugin,
        "generic_token_accounting_error",
        forced_second_accounting_failure,
    )

    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={"7": {"mint": [[sender, token, 1]]}},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert accounting_checks == 2
    assert ok is False
    assert app_state_json == genesis
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "generic token accounting postcheck failed: forced_postcheck_failure"
    )


def test_apply_app_tx_token_recipient_overflow_rejects_atomically(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "13" * 48
    recipient = "0x" + "23" * 48
    token = "0x" + "35" * 32
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-token-overflow")

    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=sender,
    )
    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={
            "7": {
                "mint": [
                    [sender, token, 1],
                    [recipient, token, 0xFFFFFFFF],
                ]
            },
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": token,
                    "sender_pubkey": sender,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ],
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == genesis
    assert app_hash == ""
    assert balances_patch is None
    assert err == "faucet.mint[1] authority transition rejected: supply_overflow"


def test_apply_app_tx_token_mint_recipient_overflow_rejects_atomically(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    operator = "0x" + "14" * 48
    recipient = "0x" + "24" * 48
    token = "0x" + "36" * 32
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-token-mint-overflow")
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    setup_ok, app_state_json, _setup_hash, _setup_patch, setup_error = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(token,),
            mint_authority_pubkey=operator,
        ),
        chain_balances={},
        operations={"7": {"mint": [[recipient, token, 0xFFFFFFFF]]}},
        tx_sender_pubkey=operator,
        block_timestamp=1,
    )
    assert setup_ok is True, setup_error

    ok, rejected_state, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": token,
                    "operator_pubkey": operator,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=2,
    )

    assert ok is False
    assert rejected_state == app_state_json
    assert app_hash == ""
    assert balances_patch is None
    assert err == "token op[0] authority transition rejected: supply_overflow"


def test_apply_app_tx_faucet_recipient_overflow_rejects_atomically(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    recipient = "0x" + "25" * 48
    token = "0x" + "37" * 32
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-faucet-overflow")

    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=recipient,
    )
    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={
            "7": {
                "mint": [
                    [recipient, token, 0xFFFFFFFF],
                    [recipient, token, 1],
                ]
            }
        },
        tx_sender_pubkey=recipient,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == genesis
    assert app_hash == ""
    assert balances_patch is None
    assert err == "faucet.mint[1] authority transition rejected: supply_overflow"


def test_apply_app_tx_token_mint_requires_committed_signer(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    operator = "0x" + "aa" * 48
    non_operator = "0x" + "bb" * 48
    recipient = "0x" + "cc" * 48
    token = "0x" + "44" * 32

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    ok, _app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(token,),
            mint_authority_pubkey=operator,
        ),
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": token,
                    "operator_pubkey": non_operator,
                    "to_pubkey": recipient,
                    "amount": 100,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=non_operator,
        block_timestamp=123,
    )
    assert ok is False
    assert err == "token op[0] authority transition rejected: unauthorized_mint"


def test_apply_app_tx_later_token_failure_rolls_back_supply_balance_and_nonce(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    operator = "0x" + "ad" * 48
    recipient = "0x" + "ce" * 48
    token = "0x" + "56" * 32
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-token-multi-op-rollback")
    genesis = _policy_bound_generic_state(
        plugin,
        assets=(token,),
        mint_authority_pubkey=operator,
    )

    ok, rejected_state, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": token,
                    "operator_pubkey": operator,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                },
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": token,
                    "operator_pubkey": operator,
                    "to_pubkey": recipient,
                    "amount": 0xFFFFFFFF,
                    "nonce": 2,
                    "deadline": 1_000,
                },
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=1,
    )

    assert ok is False
    assert rejected_state == genesis
    assert app_hash == ""
    assert balances_patch is None
    assert err == "token op[1] authority transition rejected: supply_overflow"


def test_apply_app_tx_token_mint_and_burn(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    operator = "0x" + "ab" * 48
    user = "0x" + "cd" * 48
    token = "0x" + "55" * 32

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    ok, app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(token,),
            mint_authority_pubkey=operator,
        ),
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": token,
                    "operator_pubkey": operator,
                    "to_pubkey": user,
                    "amount": 500,
                    "nonce": 1,
                    "deadline": 1_000,
                },
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": token,
                    "operator_pubkey": operator,
                    "to_pubkey": user,
                    "amount": 100,
                    "nonce": 2,
                    "deadline": 1_000,
                },
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=10,
    )
    assert ok is True
    assert err is None

    ok2, app_state_json2, _app_hash_hex2, _balances_patch2, err2 = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "burn",
                    "asset": token,
                    "sender_pubkey": user,
                    "amount": 150,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=user,
        block_timestamp=11,
    )
    assert ok2 is True
    assert err2 is None

    parsed = _dex_snapshot_from_app_state_json(app_state_json2)
    balances = {(b["pubkey"], b["asset"]): int(b["amount"]) for b in parsed.get("balances", [])}
    assert balances.get((user, token)) == 450


def _mint_one_canonical_zusd_app_state(
    monkeypatch,
    *,
    chain_id: str,
    owner: str,
    collateral_e8: int | None = None,
    mint_e8: int | None = None,
    generic_assets: tuple[str, ...] = (),
) -> str:
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin

    collateral_e8 = 2 * E8 if collateral_e8 is None else collateral_e8
    mint_e8 = 100 * E8 if mint_e8 is None else mint_e8

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", owner)
    genesis = (
        _policy_bound_empty_state(plugin)
        if not generic_assets
        else _policy_bound_generic_state(
            plugin,
            assets=generic_assets,
            mint_authority_pubkey=owner,
        )
    )
    ok, app_state_json, _app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=genesis,
        chain_balances={owner: collateral_e8},
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                },
                {
                    "module": "ZUSDFinance",
                    "action": "deposit_collateral",
                    "owner_pubkey": owner,
                    "amount_e8": collateral_e8,
                    "nonce": 2,
                },
                {
                    "module": "ZUSDFinance",
                    "action": "mint_zusd",
                    "owner_pubkey": owner,
                    "amount_e8": mint_e8,
                    "nonce": 3,
                },
            ]
        },
        tx_sender_pubkey=owner,
        block_timestamp=1,
    )
    assert ok is True, err
    assert balances_patch == {owner: 0}
    return app_state_json


def test_apply_app_tx_uses_committed_canonical_asset_when_environment_drifts(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    chain_id = "tau-zusd-asset-rebind"
    owner = "0x" + "58" * 48
    asset_a = "0x" + "a1" * 32
    asset_b = "0x" + "b1" * 32
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", asset_a)
    app_state_json = _mint_one_canonical_zusd_app_state(
        monkeypatch,
        chain_id=chain_id,
        owner=owner,
    )

    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", asset_b)
    ok, replayed_state, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={},
        tx_sender_pubkey=owner,
        block_timestamp=2,
    )

    assert ok is True
    assert replayed_state == app_state_json
    assert len(app_hash) == 64
    assert balances_patch is None
    assert err is None


def test_apply_app_tx_uses_committed_fee_stake_asset_when_environment_drifts(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    chain_id = "tau-zusd-stake-rebind"
    owner = "0x" + "59" * 48
    stake_a = "0x" + "a2" * 32
    stake_b = "0x" + "b2" * 32
    monkeypatch.setenv("TAU_DEX_ZUSD_FEE_STAKE_ASSET_ID", stake_a)
    app_state_json = _mint_one_canonical_zusd_app_state(
        monkeypatch,
        chain_id=chain_id,
        owner=owner,
    )

    monkeypatch.setenv("TAU_DEX_ZUSD_FEE_STAKE_ASSET_ID", stake_b)
    ok, replayed_state, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={},
        tx_sender_pubkey=owner,
        block_timestamp=2,
    )

    assert ok is True
    assert replayed_state == app_state_json
    assert len(app_hash) == 64
    assert balances_patch is None
    assert err is None


def test_apply_app_tx_zusd_pool_balance_remains_live_for_later_repay(
    monkeypatch,
) -> None:
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-zusd-pool-balance-live"
    owner = "0x" + "5a" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    other_asset = "0x" + "f1" * 32
    app_state_json = _mint_one_canonical_zusd_app_state(
        monkeypatch,
        chain_id=chain_id,
        owner=owner,
        collateral_e8=3 * E8,
        mint_e8=200 * E8,
        generic_assets=(other_asset,),
    )
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")

    asset0, asset1 = sorted((zusd_asset, other_asset))
    amount0 = 50 if asset0 == zusd_asset else 100_000
    amount1 = 50 if asset1 == zusd_asset else 100_000
    created, pooled_state, _pool_hash, _pool_patch, pool_error = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={
            "7": {"mint": [[owner, other_asset, 100_000]]},
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "CREATE_POOL",
                    "intent_id": "0x" + "c1" * 32,
                    "sender_pubkey": owner,
                    "deadline": 100,
                    "nonce": 1,
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": 30,
                    "amount0": amount0,
                    "amount1": amount1,
                }
            ],
        },
        tx_sender_pubkey=owner,
        block_timestamp=2,
    )
    assert created is True, pool_error

    repaid, repaid_state, _repay_hash, _repay_patch, repay_error = plugin.apply_app_tx(
        app_state_json=pooled_state,
        chain_balances={},
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "repay_zusd",
                    "owner_pubkey": owner,
                    "amount_e8": 100 * E8,
                    "nonce": 4,
                    "deadline": 100,
                }
            ]
        },
        tx_sender_pubkey=owner,
        block_timestamp=3,
    )

    assert repaid is True, repay_error
    parsed = json.loads(repaid_state)
    monetary = parsed["zusd_monetary"]
    assert monetary["core"]["free_debt_e8"] == 100 * E8
    pools = parsed["dex_state"]["pools"]
    assert len(pools) == 1
    pool = pools[0]
    zusd_reserve = pool["reserve0"] if pool["asset0"] == zusd_asset else pool["reserve1"]
    assert zusd_reserve == 50


def test_apply_app_tx_rejects_generic_canonical_zusd_mint_without_state_change(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-canonical-zusd-mint-authority"
    operator = "0x" + "61" * 48
    recipient = "0x" + "62" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": zusd_asset,
                    "operator_pubkey": operator,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == _policy_bound_empty_state(plugin)
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "token op[0] rejected by zUSD authority policy: "
        "canonical_zusd_mint_requires_monetary_authority"
    )


def test_apply_app_tx_binds_custom_canonical_zusd_asset_to_generic_writer_policy(
    monkeypatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    chain_id = "tau-custom-zusd-asset-authority"
    operator = "0x" + "66" * 48
    recipient = "0x" + "67" * 48
    custom_zusd_asset = "0x" + "a6" * 32

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", custom_zusd_asset)
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": custom_zusd_asset,
                    "operator_pubkey": operator,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == _policy_bound_empty_state(plugin)
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "token op[0] rejected by zUSD authority policy: "
        "canonical_zusd_mint_requires_monetary_authority"
    )


def test_apply_app_tx_rejects_generic_zusd_transfer_to_protocol_address_without_state_change(
    monkeypatch,
):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.zusd_monetary_bridge import stability_pool_pubkey
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-canonical-zusd-sp-address"
    sender = "0x" + "63" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    sp_pubkey = stability_pool_pubkey(chain_id=chain_id)
    app_state_json = _mint_one_canonical_zusd_app_state(
        monkeypatch, chain_id=chain_id, owner=sender
    )

    ok, rejected_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": zusd_asset,
                    "sender_pubkey": sender,
                    "to_pubkey": sp_pubkey,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert rejected_state_json == app_state_json
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "token op[0] rejected by zUSD authority policy: "
        "canonical_zusd_reserved_protocol_address_requires_monetary_authority"
    )


def test_apply_app_tx_rejects_generic_canonical_zusd_burn_without_state_change(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-canonical-zusd-burn-authority"
    sender = "0x" + "64" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    app_state_json = _mint_one_canonical_zusd_app_state(
        monkeypatch, chain_id=chain_id, owner=sender
    )

    ok, rejected_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "burn",
                    "asset": zusd_asset,
                    "sender_pubkey": sender,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )

    assert ok is False
    assert rejected_state_json == app_state_json
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "token op[0] rejected by zUSD authority policy: "
        "canonical_zusd_burn_requires_monetary_authority"
    )


def test_apply_app_tx_rejects_faucet_canonical_zusd_mint_without_state_change(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-canonical-zusd-faucet-authority"
    recipient = "0x" + "65" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")

    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={"7": {"mint": [[recipient, zusd_asset, 1]]}},
        tx_sender_pubkey=recipient,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == _policy_bound_empty_state(plugin)
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "faucet.mint[0] rejected by zUSD authority policy: "
        "canonical_zusd_mint_requires_monetary_authority"
    )


def test_select_perp_ops_prefers_upstream_stream_8() -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    upstream_ops = [{"module": "TauPerp", "action": "advance_epoch"}]
    legacy_ops = [{"module": "TauPerp", "action": "set_position"}]

    selected = plugin._select_perp_ops(  # type: ignore[attr-defined]
        {
            "8": upstream_ops,
            "5": legacy_ops,
            "2": [{"kind": "swap"}],
        }
    )

    assert selected == {"5": upstream_ops}


def test_select_perp_ops_accepts_legacy_fallback_only_for_perp_like_payload() -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    legacy_ops = [{"module": "TauPerp", "action": "advance_epoch"}]

    selected = plugin._select_perp_ops({"5": legacy_ops})  # type: ignore[attr-defined]

    assert selected == {"5": legacy_ops}


def test_select_perp_ops_rejects_legacy_fallback_when_legacy_dex_stream_present() -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    legacy_ops = [{"module": "TauPerp", "action": "advance_epoch"}]

    selected = plugin._select_perp_ops(  # type: ignore[attr-defined]
        {
            "5": legacy_ops,
            "2": [{"kind": "swap"}],
        }
    )

    assert selected == {}


def test_select_perp_ops_rejects_legacy_candidate_that_looks_like_dex_intents() -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    dex_like_payload = [{"kind": "swap", "sender_pubkey": "aa" * 48}]

    selected = plugin._select_perp_ops({"5": dex_like_payload})  # type: ignore[attr-defined]

    assert selected == {}


def test_select_perp_ops_rejects_legacy_candidate_that_is_not_perp_like() -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    selected = plugin._select_perp_ops({"5": [{"module": "TauToken"}]})  # type: ignore[attr-defined]

    assert selected == {}


def test_apply_app_tx_token_ops_reject_native_and_expired(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state.balances import NATIVE_ASSET

    sender = "0x" + "11" * 48
    recipient = "0x" + "22" * 48

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    ok, _app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={sender: 1000},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": NATIVE_ASSET,
                    "sender_pubkey": sender,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=50,
    )
    assert ok is False
    assert err == "token stream does not support native asset"

    token = "0x" + "66" * 32
    ok2, _state2, _hash2, _patch2, err2 = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": token,
                    "sender_pubkey": sender,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                    "deadline": 10,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=11,
    )
    assert ok2 is False
    assert err2 == "token op[0].deadline expired"


def test_apply_app_tx_perps_rejects_generic_zusd_quote_collateral_issuance(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-local-perps-zusd-authority"
    operator = "0x" + "71" * 48
    alice = "0x" + "72" * 48
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "mint",
                    "asset": zusd_asset,
                    "to_pubkey": alice,
                    "amount": 1_000,
                    "nonce": 1,
                    "operator_pubkey": operator,
                    "deadline": 1_000,
                }
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == _policy_bound_empty_state(plugin)
    assert app_hash == ""
    assert balances_patch is None
    assert err == (
        "token op[0] rejected by zUSD authority policy: "
        "canonical_zusd_mint_requires_monetary_authority"
    )


def test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral(monkeypatch):
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
    from src.integration.zusd_monetary_bridge import stability_pool_pubkey
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-local-zusd-monetary-perps"
    oracle_privkey = 81
    alice_privkey = 82
    bob_privkey = 83
    oracle = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    alice = "0x" + bls_pubkey_hex_from_privkey(alice_privkey)
    bob = "0x" + bls_pubkey_hex_from_privkey(bob_privkey)
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:zusd-monetary"
    deadline = 999_999_999
    chain_balances = {alice: 20 * E8}

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", oracle)

    ok0, app_state_json0, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=oracle,
        block_timestamp=1,
    )
    assert ok0 is True, err0

    ok1, app_state_json1, _hash1, patch1, err1 = plugin.apply_app_tx(
        app_state_json=app_state_json0,
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "deposit_collateral",
                    "owner_pubkey": alice,
                    "amount_e8": 20 * E8,
                    "nonce": 1,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=alice,
        block_timestamp=2,
    )
    assert ok1 is True, err1
    assert patch1 == {alice: 0}
    chain_balances = {alice: 0}

    ok2, app_state_json2, _hash2, _patch2, err2 = plugin.apply_app_tx(
        app_state_json=app_state_json1,
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "mint_zusd",
                    "owner_pubkey": alice,
                    "amount_e8": 1_000 * E8,
                    "nonce": 2,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=alice,
        block_timestamp=3,
    )
    assert ok2 is True, err2

    ok3, app_state_json3, _hash3, _patch3, err3 = plugin.apply_app_tx(
        app_state_json=app_state_json2,
        chain_balances=chain_balances,
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": zusd_asset,
                    "sender_pubkey": alice,
                    "to_pubkey": bob,
                    "amount": 400,
                    "nonce": 1,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=alice,
        block_timestamp=4,
    )
    assert ok3 is True, err3

    init_market = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "init_market_2p",
        "quote_asset": zusd_asset,
        "account_a_pubkey": alice,
        "account_b_pubkey": bob,
        "deadline": deadline,
        "nonce_a": 1,
        "nonce_b": 1,
    }
    init_market["sig_a"] = sign_perp_op_for_engine(
        init_market,
        privkey=alice_privkey,
        chain_id=chain_id,
        signer_pubkey=alice,
        nonce=1,
    )
    init_market["sig_b"] = sign_perp_op_for_engine(
        init_market,
        privkey=bob_privkey,
        chain_id=chain_id,
        signer_pubkey=bob,
        nonce=1,
    )

    ok4, app_state_json4, _hash4, _patch4, err4 = plugin.apply_app_tx(
        app_state_json=app_state_json3,
        chain_balances=chain_balances,
        operations={"8": [init_market]},
        tx_sender_pubkey=alice,
        block_timestamp=5,
    )
    assert ok4 is True, err4

    ok5, app_state_json5, _hash5, _patch5, err5 = plugin.apply_app_tx(
        app_state_json=app_state_json4,
        chain_balances=chain_balances,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": alice,
                    "amount": 250,
                }
            ]
        },
        tx_sender_pubkey=alice,
        block_timestamp=6,
    )
    assert ok5 is True, err5

    ok6, app_state_json6, _hash6, _patch6, err6 = plugin.apply_app_tx(
        app_state_json=app_state_json5,
        chain_balances=chain_balances,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": bob,
                    "amount": 300,
                }
            ]
        },
        tx_sender_pubkey=bob,
        block_timestamp=7,
    )
    assert ok6 is True, err6

    parsed = json.loads(app_state_json6)
    assert parsed["schema"] == "zenodex/tau_app_state/v2"
    assert parsed["version"] == 2
    assert "generic_token_authority" in parsed
    balances = {
        (b["pubkey"], b["asset"]): int(b["amount"]) for b in parsed["dex_state"].get("balances", [])
    }
    assert balances[(alice, zusd_asset)] == 350
    assert balances[(bob, zusd_asset)] == 100
    assert balances.get((stability_pool_pubkey(chain_id=chain_id), zusd_asset), 0) == 0
    assert parsed["zusd_monetary"]["core"]["debt_e8"] == 1_000 * E8
    market = next(
        entry
        for entry in parsed["dex_state"]["perps"]["markets"]
        if entry["market_id"] == market_id
    )
    assert market["state"]["collateral_e8_a"] == 250 * E8
    assert market["state"]["collateral_e8_b"] == 300 * E8


def test_apply_app_tx_zusd_monetary_accepts_tau_raw_sender_native_balance(monkeypatch):
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

    chain_id = "tau-local-zusd-raw-native"
    alice = "0x" + bls_pubkey_hex_from_privkey(82)
    alice_raw = alice[2:]
    deadline = 999_999_999

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", alice)

    ok, app_state_json, _hash, patch, err = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances={alice_raw: 1000},
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 20_000_000 * E8,
                    "nonce": 1,
                    "deadline": deadline,
                },
                {
                    "module": "ZUSDFinance",
                    "action": "deposit_collateral",
                    "owner_pubkey": alice,
                    "amount_e8": 1000,
                    "nonce": 2,
                    "deadline": deadline,
                },
            ]
        },
        tx_sender_pubkey=alice_raw,
        block_timestamp=1,
    )

    assert ok is True, err
    assert patch == {alice_raw: 0}
    parsed = json.loads(app_state_json)
    assert parsed["zusd_monetary"]["vault_owner_pubkey"] == alice
    assert parsed["zusd_monetary"]["core"]["collateral_e8"] == 1000


def test_apply_app_tx_zusd_monetary_stability_pool_liquidation_and_claim(monkeypatch):
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
    from src.integration.zusd_monetary_bridge import stability_pool_pubkey
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

    chain_id = "tau-local-zusd-monetary-sp"
    oracle_privkey = 91
    alice_privkey = 92
    keeper_privkey = 93
    oracle = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    alice = "0x" + bls_pubkey_hex_from_privkey(alice_privkey)
    keeper = "0x" + bls_pubkey_hex_from_privkey(keeper_privkey)
    zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    sp_account = stability_pool_pubkey(chain_id=chain_id)
    deadline = 999_999_999
    chain_balances = {alice: 2 * E8}

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", oracle)

    ok0, app_state_json, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json=_policy_bound_empty_state(plugin),
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=oracle,
        block_timestamp=1,
    )
    assert ok0 is True, err0

    for block_timestamp, nonce, action, amount_e8 in (
        (2, 1, "deposit_collateral", 2 * E8),
        (3, 2, "mint_zusd", 150 * E8),
        (4, 3, "deposit_sp", 150 * E8),
    ):
        body = {
            "module": "ZUSDFinance",
            "action": action,
            "amount_e8": amount_e8,
            "nonce": nonce,
            "deadline": deadline,
        }
        if action in {"deposit_collateral", "mint_zusd"}:
            body["owner_pubkey"] = alice
        else:
            body["account_pubkey"] = alice
        ok, next_json, _hash, patch, err = plugin.apply_app_tx(
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            operations={"11": [body]},
            tx_sender_pubkey=alice,
            block_timestamp=block_timestamp,
        )
        assert ok is True, err
        app_state_json = next_json
        if patch:
            chain_balances = {alice: int(patch.get(alice, chain_balances.get(alice, 0)))}

    parsed_after_sp = json.loads(app_state_json)
    balances_after_sp = {
        (b["pubkey"], b["asset"]): int(b["amount"])
        for b in parsed_after_sp["dex_state"].get("balances", [])
    }
    assert balances_after_sp.get((alice, zusd_asset), 0) == 0
    assert balances_after_sp[(sp_account, zusd_asset)] == 150
    assert parsed_after_sp["zusd_monetary"]["core"]["sp_debt_e8"] == 150 * E8

    ok4, app_state_json4, _hash4, _patch4, err4 = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "oracle_report",
                    "price_e8": 70 * E8,
                    "nonce": 2,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=oracle,
        block_timestamp=5,
    )
    assert ok4 is True, err4

    ok5, app_state_json5, _hash5, _patch5, err5 = plugin.apply_app_tx(
        app_state_json=app_state_json4,
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "liquidate",
                    "nonce": 1,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=keeper,
        block_timestamp=6,
    )
    assert ok5 is True, err5
    parsed_after_liq = json.loads(app_state_json5)
    balances_after_liq = {
        (b["pubkey"], b["asset"]): int(b["amount"])
        for b in parsed_after_liq["dex_state"].get("balances", [])
    }
    assert balances_after_liq.get((sp_account, zusd_asset), 0) == 0
    assert parsed_after_liq["zusd_monetary"]["core"]["debt_e8"] == 0
    assert parsed_after_liq["zusd_monetary"]["core"]["sp_debt_e8"] == 0
    assert parsed_after_liq["zusd_monetary"]["sp_collateral_claims"] == [
        {"amount_e8": 2 * E8, "pubkey": alice}
    ]

    ok6, app_state_json6, _hash6, patch6, err6 = plugin.apply_app_tx(
        app_state_json=app_state_json5,
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "claim_sp_collateral",
                    "account_pubkey": alice,
                    "amount_e8": 2 * E8,
                    "nonce": 4,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=alice,
        block_timestamp=7,
    )
    assert ok6 is True, err6
    assert patch6 == {alice: 2 * E8}
    parsed_after_claim = json.loads(app_state_json6)
    assert parsed_after_claim["zusd_monetary"]["core"]["sp_coll_e8"] == 0
    assert parsed_after_claim["zusd_monetary"]["sp_collateral_claims"] == []


def test_zusd_monetary_liquidation_fee_comp_env_aliases_prefer_fee_names(monkeypatch):
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8", str(E8))
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS", "10")
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_FIXED_COLLATERAL_E8", str(E8 // 4))
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS", "25")

    config = plugin._build_zusd_monetary_config(chain_id="tau-local-zusd-fee-alias")

    assert config.liquidation_gas_comp_fixed_collateral_e8 == E8 // 4
    assert config.liquidation_gas_comp_bps == 25


def test_zusd_monetary_liquidation_fee_comp_env_aliases_accept_legacy_gas_names(monkeypatch):
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8", str(E8 // 5))
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS", "15")

    config = plugin._build_zusd_monetary_config(chain_id="tau-local-zusd-fee-alias")

    assert config.liquidation_gas_comp_fixed_collateral_e8 == E8 // 5
    assert config.liquidation_gas_comp_bps == 15


def test_apply_app_tx_zusd_monetary_liquidation_compensation_pays_keeper(monkeypatch):
    from src.core.zusd import E8
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

    chain_id = "tau-local-zusd-monetary-liq-comp"
    oracle = "0x" + bls_pubkey_hex_from_privkey(101)
    alice = "0x" + bls_pubkey_hex_from_privkey(102)
    keeper = "0x" + bls_pubkey_hex_from_privkey(103)
    fixed_comp = E8 // 10
    deadline = 999_999_999
    chain_balances = {alice: 2 * E8, keeper: 0}

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", oracle)
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8", str(fixed_comp))
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS", "0")

    app_state_json = _policy_bound_empty_state(plugin)
    for block_timestamp, sender, body in (
        (
            1,
            oracle,
            {
                "module": "ZUSDFinance",
                "action": "bootstrap_oracle",
                "price_e8": 100 * E8,
                "nonce": 1,
                "deadline": deadline,
            },
        ),
        (
            2,
            alice,
            {
                "module": "ZUSDFinance",
                "action": "deposit_collateral",
                "owner_pubkey": alice,
                "amount_e8": 2 * E8,
                "nonce": 1,
                "deadline": deadline,
            },
        ),
        (
            3,
            alice,
            {
                "module": "ZUSDFinance",
                "action": "mint_zusd",
                "owner_pubkey": alice,
                "amount_e8": 150 * E8,
                "nonce": 2,
                "deadline": deadline,
            },
        ),
        (
            4,
            alice,
            {
                "module": "ZUSDFinance",
                "action": "deposit_sp",
                "account_pubkey": alice,
                "amount_e8": 150 * E8,
                "nonce": 3,
                "deadline": deadline,
            },
        ),
        (
            5,
            oracle,
            {
                "module": "ZUSDFinance",
                "action": "oracle_report",
                "price_e8": 70 * E8,
                "nonce": 2,
                "deadline": deadline,
            },
        ),
    ):
        ok, next_json, _hash, patch, err = plugin.apply_app_tx(
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            operations={"11": [body]},
            tx_sender_pubkey=sender,
            block_timestamp=block_timestamp,
        )
        assert ok is True, err
        app_state_json = next_json
        for pk, amount in (patch or {}).items():
            chain_balances[pk] = int(amount)

    ok, app_state_json, _hash, patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances=chain_balances,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "liquidate",
                    "nonce": 1,
                    "deadline": deadline,
                }
            ]
        },
        tx_sender_pubkey=keeper,
        block_timestamp=6,
    )

    assert ok is True, err
    assert patch == {keeper: fixed_comp}
    parsed = json.loads(app_state_json)
    assert (
        parsed["zusd_monetary"]["core"]["liquidator_compensation_collateral_cum_e8"] == fixed_comp
    )
    assert parsed["zusd_monetary"]["core"]["sp_coll_e8"] == 2 * E8 - fixed_comp
    assert parsed["zusd_monetary"]["sp_collateral_claims"] == [
        {"amount_e8": 2 * E8 - fixed_comp, "pubkey": alice}
    ]


def test_apply_app_tx_proof_mining_claim_updates_reward_pool_and_wrapper_state(monkeypatch):
    from src.core.batch_clearing import compute_settlement
    from src.core.proof_mining_claims import build_proof_mining_claim
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.dex_engine import DexEngineConfig, apply_ops
    from src.integration.dex_snapshot import state_from_snapshot
    from src.integration.operations import (
        canonicalize_authenticated_intent_for_execution,
        create_settlement_operation,
    )
    from src.integration.proof_verifier import ProofVerifierConfig
    from src.state.lp import LPTable
    from src.state.state_root import compute_state_root

    sender = "11" * 48
    canonical_sender = "0x" + sender
    reward_pool = "99" * 48
    canonical_reward_pool = "0x" + reward_pool
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    verifier_cmd = [
        sys.executable,
        "-c",
        "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')",
    ]
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "0")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_ALLOW_EXTERNAL_TOOLS", "1")
    monkeypatch.setenv("TAU_DEX_CONSENSUS_MODE", "0")
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(verifier_cmd))
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)

    ok0, app_state_json0, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(asset0, asset1),
            mint_authority_pubkey=canonical_sender,
        ),
        chain_balances={sender: 123, reward_pool: 20},
        operations={
            "7": {
                "mint": [
                    [canonical_sender, asset0, 10_000],
                    [canonical_sender, asset1, 10_000],
                ]
            }
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert ok0 is True
    assert err0 is None

    state0 = state_from_snapshot(_dex_snapshot_from_app_state_json(app_state_json0))
    intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "ab" * 32,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    parsed_intent = _parse_single_intent(intent)
    execution_intent = canonicalize_authenticated_intent_for_execution(parsed_intent)
    settlement = compute_settlement(
        intents=[execution_intent],
        pools=state0.pools,
        balances=state0.balances,
        lp_balances=state0.lp_balances,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    pre_state_commitment = compute_state_root(
        balances=state0.balances,
        pools=state0.pools,
        lp_balances=state0.lp_balances or LPTable(),
        nonces=state0.nonces,
    )
    batch_commitment = _batch_commitment(
        signing_dicts=[_intent_signing_dict_from_tx_intent(intent)],
        settlement_obj=settlement_op,
    )
    settlement_op["proof"] = {
        "pre_state_commitment": pre_state_commitment,
        "batch_commitment": batch_commitment,
        "scheme": "dummy",
    }

    preview = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            canonicalize_authenticated_bls_principals=True,
            allow_external_tools=True,
            consensus_mode=False,
            chain_id="tau-local",
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=verifier_cmd),
        ),
        state=state0,
        operations={"2": [intent], "3": settlement_op},
        block_timestamp=2,
        tx_sender_pubkey=sender,
    )
    assert preview.ok is True
    assert preview.proof_mining_context is not None
    ctx = preview.proof_mining_context
    claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "job-proof-1",
            "winner": {
                "miner_id": sender,
                "witness_sha256": ctx.witness_hash,
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="round-proof-1",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id=ctx.chain_id,
        prev_state_hash=ctx.prev_state_hash,
        batch_hash=ctx.batch_hash,
        dex_hash_after=ctx.dex_hash_after,
    )

    ok1, app_state_json1, _hash1, balances_patch1, err1 = plugin.apply_app_tx(
        app_state_json=app_state_json0,
        chain_balances={sender: 123, reward_pool: 20},
        operations={
            "5": [intent],
            "6": settlement_op,
            "10": {"module": "ZenoProofMining", "action": "submit_proof", "claim": claim},
        },
        tx_sender_pubkey=sender,
        block_timestamp=2,
    )
    assert ok1 is True
    assert err1 is None
    assert balances_patch1 == {reward_pool: 16, sender: 127}

    parsed = json.loads(app_state_json1)
    assert parsed["schema"] == "zenodex/tau_app_state/v2"
    assert parsed["version"] == 2
    assert "generic_token_authority" in parsed
    assert parsed["proof_mining"]["schema"] == "zenodex/proof_mining_runtime_state/v1"
    assert parsed["proof_mining"]["reward_pool_pubkey"] == canonical_reward_pool
    assert parsed["proof_mining"]["reward_pool_balance"] == 16
    assert parsed["proof_mining"]["total_paid"] == 4
    claimed_slots = parsed["proof_mining"]["claimed_slots"]
    assert isinstance(claimed_slots, list) and len(claimed_slots) == 1
    assert claimed_slots[0]["proposal_hash"] == ctx.proposal_hash

    ok2, synced_json, _hash2, synced_patch, err2 = plugin.apply_app_tx(
        app_state_json=app_state_json1,
        chain_balances=balances_patch1,
        operations={},
        tx_sender_pubkey="",
        block_timestamp=3,
    )
    assert ok2 is True
    assert err2 is None
    assert synced_patch is None
    synced = json.loads(synced_json)
    assert synced["schema"] == "zenodex/tau_app_state/v2"
    assert synced["version"] == 2
    assert synced["generic_token_authority"] == parsed["generic_token_authority"]

    ok3, synced_drift_json, _hash3, drift_patch, err3 = plugin.apply_app_tx(
        app_state_json=app_state_json1,
        chain_balances={reward_pool: 15, sender: 127},
        operations={},
        tx_sender_pubkey="",
        block_timestamp=4,
    )
    assert ok3 is True
    assert err3 is None
    assert drift_patch is None
    drifted = json.loads(synced_drift_json)
    assert drifted["proof_mining"]["reward_pool_balance"] == 15
    assert drifted["proof_mining"]["initial_pool"] == 19
    assert drifted["proof_mining"]["total_paid"] == 4


def test_apply_proof_mining_op_rejects_malformed_claim_shapes_without_crashing(monkeypatch):
    from src.core.dex import DexState
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state import BalanceTable, LPTable

    sender = "0x" + "11" * 48
    reward_pool = "0x" + "99" * 48
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    for claim, expected_err in (
        ({"body": "not-a-mapping"}, "proof mining claim.body must be an object"),
        ({"body": {"winner": "not-a-mapping"}}, "proof mining claim.body.winner must be an object"),
    ):
        ok, _state, _pm_state, err = plugin._apply_proof_mining_op(
            state=state,
            proof_mining_state=None,
            proof_mining_op={"module": "ZenoProofMining", "action": "submit_proof", "claim": claim},
            proof_mining_context=object(),
            tx_sender_pubkey=sender,
            native_balances=plugin.TauNativeBalanceSnapshot.from_chain_balances({reward_pool: 10}),
        )
        assert ok is False
        assert err == expected_err


def test_native_principal_binding_preserves_raw_key_and_rejects_duplicate_spellings() -> None:
    from src.integration.tau_native_identity import TauNativeBalanceSnapshot

    raw_pubkey = "11" * 48
    canonical_pubkey = "0x" + raw_pubkey
    snapshot = TauNativeBalanceSnapshot.from_chain_balances({raw_pubkey: 20})
    binding = snapshot.binding_for(
        canonical_pubkey,
        preferred_chain_key=canonical_pubkey,
        name="test principal",
    )

    assert binding.canonical_pubkey == canonical_pubkey
    assert binding.chain_key == raw_pubkey
    assert binding.balance == 20
    with pytest.raises(ValueError, match="ambiguous identity spellings"):
        TauNativeBalanceSnapshot.from_chain_balances({raw_pubkey: 20, canonical_pubkey: 20})


def test_native_balance_patch_preserves_exact_tau_keys() -> None:
    from src.core.dex import DexState
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.tau_native_identity import TauNativeBalanceSnapshot
    from src.state import BalanceTable, LPTable
    from src.state.balances import NATIVE_ASSET

    raw_recipient = "11" * 48
    canonical_recipient = "0x" + raw_recipient
    raw_pool = "99" * 48
    canonical_pool = "0x" + raw_pool
    before = TauNativeBalanceSnapshot.from_chain_balances({raw_pool: 20})
    balances = BalanceTable()
    balances.set(canonical_recipient, NATIVE_ASSET, 4)
    balances.set(canonical_pool, NATIVE_ASSET, 16)
    after = DexState(balances=balances, pools={}, lp_balances=LPTable())

    patch = plugin._balances_patch_for_native(
        before=before,
        after_state=after,
    )

    assert patch == {raw_recipient: 4, raw_pool: 16}


def test_apply_app_tx_rejects_duplicate_tau_spellings_before_state_load(monkeypatch) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    raw_pubkey = "11" * 48
    canonical_pubkey = "0x" + raw_pubkey

    def fail_if_manager_called(**_kwargs):
        raise AssertionError("ambiguous Tau identities must reject before manager application")

    monkeypatch.setattr(plugin, "apply_proof_mining_claim", fail_if_manager_called)
    ok, app_state_json, app_hash, balances_patch, err = plugin.apply_app_tx(
        app_state_json="opaque-prestate",
        chain_balances={raw_pubkey: 20, canonical_pubkey: 20},
        operations={},
        tx_sender_pubkey=raw_pubkey,
        block_timestamp=1,
    )

    assert ok is False
    assert app_state_json == "opaque-prestate"
    assert app_hash == ""
    assert balances_patch is None
    assert err is not None
    assert "ambiguous identity spellings" in err


def test_apply_proof_mining_op_rejects_reward_pool_self_payment_without_mutation(monkeypatch):
    """Given the pool is also the winner, payout rejects without changing either state."""
    from src.core.dex import DexState
    from src.core.proof_mining_claims import build_proof_mining_claim
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.proof_mining_context import ProofMiningContext
    from src.state import BalanceTable, LPTable
    from src.state.balances import NATIVE_ASSET

    reward_pool = "0x" + "99" * 48
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "job-self-payment",
            "winner": {
                "miner_id": reward_pool,
                "witness_sha256": "witness-self-payment",
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="round-self-payment",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id="tau-local",
        prev_state_hash="sha256:prev-self-payment",
        batch_hash="sha256:batch-self-payment",
        dex_hash_after="sha256:after-self-payment",
    )
    binding = claim["body"]["proposal_binding"]
    context = ProofMiningContext(
        chain_id=str(binding["chain_id"]),
        prev_state_hash=str(binding["prev_state_hash"]),
        batch_hash=str(binding["batch_hash"]),
        witness_hash=str(binding["witness_hash"]),
        dex_hash_after=str(binding["dex_hash_after"]),
        proposal_hash=str(claim["body"]["proposal_hash"]),
        proof_scheme="dummy",
    )
    balances = BalanceTable()
    balances.set(reward_pool, NATIVE_ASSET, 20)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    def fail_if_manager_called(**_kwargs):
        raise AssertionError("self-payment must reject before proof-mining manager application")

    monkeypatch.setattr(plugin, "apply_proof_mining_claim", fail_if_manager_called)

    ok, next_state, next_proof_mining_state, err = plugin._apply_proof_mining_op(
        state=state,
        proof_mining_state=None,
        proof_mining_op={
            "module": "ZenoProofMining",
            "action": "submit_proof",
            "claim": claim,
        },
        proof_mining_context=context,
        tx_sender_pubkey=reward_pool,
        native_balances=plugin.TauNativeBalanceSnapshot.from_chain_balances({reward_pool: 20}),
    )

    assert ok is False
    assert err == "proof mining reward recipient must differ from reward pool"
    assert next_state is state
    assert next_proof_mining_state is None
    assert state.balances.get(reward_pool, NATIVE_ASSET) == 20


def test_apply_app_tx_proof_mining_rejects_claim_context_mismatch(monkeypatch):
    from src.core.batch_clearing import compute_settlement
    from src.core.proof_mining_claims import build_proof_mining_claim
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.dex_engine import DexEngineConfig, apply_ops
    from src.integration.dex_snapshot import state_from_snapshot
    from src.integration.operations import create_settlement_operation
    from src.integration.proof_verifier import ProofVerifierConfig
    from src.state.state_root import compute_state_root

    sender = "0x" + "22" * 48
    reward_pool = "0x" + "88" * 48
    asset0 = "0x" + "33" * 32
    asset1 = "0x" + "44" * 32

    verifier_cmd = [
        sys.executable,
        "-c",
        "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')",
    ]
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "0")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_ALLOW_EXTERNAL_TOOLS", "1")
    monkeypatch.setenv("TAU_DEX_CONSENSUS_MODE", "0")
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(verifier_cmd))
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)

    ok0, app_state_json0, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json=_policy_bound_generic_state(
            plugin,
            assets=(asset0, asset1),
            mint_authority_pubkey=sender,
        ),
        chain_balances={sender: 50, reward_pool: 20},
        operations={
            "7": {
                "mint": [
                    [sender, asset0, 10_000],
                    [sender, asset1, 10_000],
                ]
            }
        },
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert ok0 is True
    assert err0 is None

    state0 = state_from_snapshot(_dex_snapshot_from_app_state_json(app_state_json0))
    intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "cd" * 32,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    parsed_intent = _parse_single_intent(intent)
    settlement = compute_settlement(
        intents=[parsed_intent],
        pools=state0.pools,
        balances=state0.balances,
        lp_balances=state0.lp_balances,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["proof"] = {
        "pre_state_commitment": compute_state_root(
            balances=state0.balances,
            pools=state0.pools,
            lp_balances=state0.lp_balances,
            nonces=state0.nonces,
        ),
        "batch_commitment": _batch_commitment(
            signing_dicts=[_intent_signing_dict_from_tx_intent(intent)],
            settlement_obj=settlement_op,
        ),
        "scheme": "dummy",
    }
    preview = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            canonicalize_authenticated_bls_principals=True,
            allow_external_tools=True,
            consensus_mode=False,
            chain_id="tau-local",
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=verifier_cmd),
        ),
        state=state0,
        operations={"2": [intent], "3": settlement_op},
        block_timestamp=2,
        tx_sender_pubkey=sender,
    )
    assert preview.ok is True
    assert preview.proof_mining_context is not None
    ctx = preview.proof_mining_context
    claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "job-proof-2",
            "winner": {
                "miner_id": sender,
                "witness_sha256": ctx.witness_hash,
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="round-proof-2",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id=ctx.chain_id,
        prev_state_hash=ctx.prev_state_hash,
        batch_hash=ctx.batch_hash,
        dex_hash_after="sha256:wrong",
    )

    ok1, _state1, _hash1, _patch1, err1 = plugin.apply_app_tx(
        app_state_json=app_state_json0,
        chain_balances={sender: 50, reward_pool: 20},
        operations={
            "5": [intent],
            "6": settlement_op,
            "10": {"module": "ZenoProofMining", "action": "submit_proof", "claim": claim},
        },
        tx_sender_pubkey=sender,
        block_timestamp=2,
    )
    assert ok1 is False
    assert err1 == "proof mining claim proposal_hash mismatch"
