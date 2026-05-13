import json
import sys


def _intent_signing_dict_from_tx_intent(intent_dict: dict) -> dict:
    from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    return build_dex_intent_signing_dict_v1(intent)


def _parse_single_intent(intent_dict: dict):
    from src.integration.operations import parse_intents

    return parse_intents({"2": [intent_dict]})[0]


def _settlement_commitment_dict_from_settlement(settlement_obj: dict) -> dict:
    out = {k: v for k, v in settlement_obj.items() if k not in ("batch_ref", "events", "proof")}
    fills = out.get("fills") or []
    out["fills"] = [
        {k: v for k, v in fill.items() if v is not None and k != "reason"} for fill in fills if isinstance(fill, dict)
    ]
    return out


def _batch_commitment(*, signing_dicts: list[dict], settlement_obj: dict) -> str:
    from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes, domain_sep_bytes, sha256_hex

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


def test_apply_app_tx_proof_mining_claim_updates_reward_pool_and_wrapper_state(monkeypatch):
    from src.core.batch_clearing import compute_settlement
    from src.core.proof_mining_claims import build_proof_mining_claim
    from src.integration import tau_testnet_dex_plugin as plugin
    from src.integration.dex_engine import DexEngineConfig, apply_ops
    from src.integration.dex_snapshot import state_from_snapshot
    from src.integration.operations import create_settlement_operation
    from src.integration.proof_verifier import ProofVerifierConfig
    from src.state.lp import LPTable
    from src.state.state_root import compute_state_root

    sender = "0x" + "11" * 48
    reward_pool = "0x" + "99" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    verifier_cmd = [sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')"]
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "0")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_ALLOW_EXTERNAL_TOOLS", "1")
    monkeypatch.setenv("TAU_DEX_CONSENSUS_MODE", "0")
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(verifier_cmd))
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)

    ok0, app_state_json0, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender: 123, reward_pool: 20},
        operations={"7": {"mint": [[sender, asset0, 10_000], [sender, asset1, 10_000]]}},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert ok0 is True
    assert err0 is None

    state0 = state_from_snapshot(json.loads(app_state_json0))
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
    settlement = compute_settlement(
        intents=[parsed_intent],
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
        verifier_evidence=[
            {"verifier_id": 0, "domain_id": 0, "accepted": 1},
            {"verifier_id": 1, "domain_id": 1, "accepted": 1},
        ],
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
    assert parsed["schema"] == "zenodex/tau_app_state/v1"
    assert parsed["proof_mining"]["schema"] == "zenodex/proof_mining_runtime_state/v1"
    assert parsed["proof_mining"]["reward_pool_pubkey"] == reward_pool
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
    assert json.loads(synced_json)["schema"] == "zenodex/tau_app_state/v1"

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

    verifier_cmd = [sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')"]
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "0")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_ALLOW_EXTERNAL_TOOLS", "1")
    monkeypatch.setenv("TAU_DEX_CONSENSUS_MODE", "0")
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(verifier_cmd))
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)

    ok0, app_state_json0, _hash0, _patch0, err0 = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender: 50, reward_pool: 20},
        operations={"7": {"mint": [[sender, asset0, 10_000], [sender, asset1, 10_000]]}},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert ok0 is True
    assert err0 is None

    state0 = state_from_snapshot(json.loads(app_state_json0))
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
        verifier_evidence=[
            {"verifier_id": 0, "domain_id": 0, "accepted": 1},
            {"verifier_id": 1, "domain_id": 1, "accepted": 1},
        ],
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


def test_apply_app_tx_proof_mining_rejects_malformed_claim_without_crash(monkeypatch):
    from src.integration import tau_testnet_dex_plugin as plugin

    sender = "0x" + "33" * 48
    reward_pool = "0x" + "77" * 48

    class _ProofContext:
        proposal_hash = "proposal-hash"

    class _DexResult:
        ok = True
        error = None
        proof_mining_context = _ProofContext()

        def __init__(self, state):
            self.state = state

    def _fake_apply_ops(*, config, state, operations, block_timestamp, tx_sender_pubkey):
        return _DexResult(state)

    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    monkeypatch.setattr(plugin, "apply_ops", _fake_apply_ops)

    ok, _state, _hash, patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={sender: 123, reward_pool: 20},
        operations={
            "5": [],
            "10": {
                "module": "ZenoProofMining",
                "action": "submit_proof",
                "claim": {"schema": "zenodex/proof_mining_claim/v1", "body": "not-object"},
            },
        },
        tx_sender_pubkey=sender,
        block_timestamp=2,
    )

    assert ok is False
    assert patch is None
    assert err == "proof mining claim.body must be an object"
