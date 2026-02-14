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
    assert parsed.get("version") == 2


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
        "nonce": 1,
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
            "7": {"mint": [[sender_pubkey, asset0, 10_000], [sender_pubkey, asset1, 10_000]]},
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
        "nonce": 1,
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
            "7": {"mint": [[sender_pubkey, asset0, 10_000], [sender_pubkey, asset1, 10_000]]},
            "5": [create_pool_intent],
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
        "nonce": 1,
        "asset0": NATIVE_ASSET,
        "asset1": token,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, app_state_json, _app_hash_hex, balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender_pubkey: 10_000},
        operations={"7": {"mint": [[sender_pubkey, token, 10_000]]}, "5": [intent]},
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
        app_state_json="",
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
        app_state_json="",
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
        app_state_json="",
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
        app_state_json="",
        chain_balances={},
        operations={
            "7": {"mint": [[sender, token, 1000]]},
            "9": [
                {
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": token,
                    "to_pubkey": recipient,
                    "amount": 250,
                    "nonce": 1,
                }
            ],
        },
        tx_sender_pubkey=sender,
        block_timestamp=100,
    )
    assert ok is True
    assert err is None

    parsed = json.loads(app_state_json)
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
                    "action": "transfer",
                    "asset": token,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
                }
            ]
        },
        tx_sender_pubkey=sender,
        block_timestamp=101,
    )
    assert ok2 is False
    assert isinstance(err2, str) and "nonce invalid" in err2


def test_apply_app_tx_token_mint_requires_operator(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    operator = "0x" + "aa" * 48
    non_operator = "0x" + "bb" * 48
    recipient = "0x" + "cc" * 48
    token = "0x" + "44" * 32

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    ok, _app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "mint",
                    "asset": token,
                    "to_pubkey": recipient,
                    "amount": 100,
                    "nonce": 1,
                }
            ]
        },
        tx_sender_pubkey=non_operator,
        block_timestamp=123,
    )
    assert ok is False
    assert err == "token mint requires operator sender"


def test_apply_app_tx_token_mint_and_burn(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    operator = "0x" + "ab" * 48
    user = "0x" + "cd" * 48
    token = "0x" + "55" * 32

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_TOKEN_OPERATOR_PUBKEY", operator)

    ok, app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "mint",
                    "asset": token,
                    "to_pubkey": user,
                    "amount": 500,
                    "nonce": 1,
                },
                {
                    "module": "TauToken",
                    "action": "mint",
                    "asset": token,
                    "to_pubkey": user,
                    "amount": 100,
                    "nonce": 2,
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
                    "action": "burn",
                    "asset": token,
                    "amount": 150,
                    "nonce": 1,
                }
            ]
        },
        tx_sender_pubkey=user,
        block_timestamp=11,
    )
    assert ok2 is True
    assert err2 is None

    parsed = json.loads(app_state_json2)
    balances = {(b["pubkey"], b["asset"]): int(b["amount"]) for b in parsed.get("balances", [])}
    assert balances.get((user, token)) == 450


def test_apply_app_tx_token_ops_reject_native_and_expired(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.state.balances import NATIVE_ASSET

    sender = "0x" + "11" * 48
    recipient = "0x" + "22" * 48

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    ok, _app_state_json, _app_hash_hex, _balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender: 1000},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "transfer",
                    "asset": NATIVE_ASSET,
                    "to_pubkey": recipient,
                    "amount": 1,
                    "nonce": 1,
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
        app_state_json="",
        chain_balances={},
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "transfer",
                    "asset": token,
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
