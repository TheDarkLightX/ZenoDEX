import json


def test_apply_app_tx_sync_only(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    monkeypatch.delenv("TAU_DEX_FAUCET", raising=False)
    monkeypatch.delenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", raising=False)
    monkeypatch.delenv("TAU_DEX_REQUIRE_INTENT_SIGS", raising=False)
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
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

    parsed = json.loads(app_state_json)
    assert isinstance(parsed, dict)
    assert parsed.get("version") == 1


def test_apply_app_tx_create_pool_unsigned_intent(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    sender_pubkey = "00" * 48
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
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, app_state_json, app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender_pubkey: 123},
        operations={
            "4": {"mint": [[sender_pubkey, asset0, 10_000], [sender_pubkey, asset1, 10_000]]},
            "2": [intent],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )

    assert ok is True
    assert err is None
    assert isinstance(app_state_json, str) and app_state_json
    assert isinstance(app_hash_hex, str) and len(app_hash_hex) == 64
    assert balances_patch in (None, {})

    parsed = json.loads(app_state_json)
    assert isinstance(parsed, dict)
    pools = parsed.get("pools")
    assert isinstance(pools, list) and pools


def test_apply_app_tx_swap_exact_in(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    sender_pubkey = "00" * 48
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
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    ok, app_state_json, app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender_pubkey: 123},
        operations={
            "4": {"mint": [[sender_pubkey, asset0, 10_000], [sender_pubkey, asset1, 10_000]]},
            "2": [create_pool_intent],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=123,
    )
    assert ok is True
    assert err is None
    assert isinstance(app_hash_hex, str) and len(app_hash_hex) == 64

    parsed = json.loads(app_state_json)
    pools = parsed.get("pools")
    assert isinstance(pools, list) and pools
    pool_id = pools[0]["pool_id"]

    balances_before = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed.get("balances") or [])
        if isinstance(b, dict)
    }
    before_in = int(balances_before.get((sender_pubkey, asset0), 0))
    before_out = int(balances_before.get((sender_pubkey, asset1), 0))

    swap_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 9999999999,
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
        operations={"2": [swap_intent]},
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=124,
    )
    assert ok is True
    assert err is None

    parsed2 = json.loads(app_state_json2)
    balances_after = {
        (b.get("pubkey"), b.get("asset")): b.get("amount")
        for b in (parsed2.get("balances") or [])
        if isinstance(b, dict)
    }
    after_in = int(balances_after.get((sender_pubkey, asset0), 0))
    after_out = int(balances_after.get((sender_pubkey, asset1), 0))

    assert after_in < before_in
    assert after_out > before_out


def test_apply_app_tx_create_pool_with_native_asset_updates_chain_balance(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state.balances import NATIVE_ASSET

    sender_pubkey = "00" * 48
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
        "asset0": NATIVE_ASSET,
        "asset1": token,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, app_state_json, _app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender_pubkey: 10_000},
        operations={"4": {"mint": [[sender_pubkey, token, 10_000]]}, "2": [intent]},
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

    parsed = json.loads(synced_json)
    balances = {(b.get("pubkey"), b.get("asset")): b.get("amount") for b in (parsed.get("balances") or []) if isinstance(b, dict)}
    assert balances.get((sender_pubkey, NATIVE_ASSET)) == 9000
