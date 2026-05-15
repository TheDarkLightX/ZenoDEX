from __future__ import annotations

import json
import shutil
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_dex_intent_for_engine
from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import (
    NODE_JOIN_CONFIG_SCHEMA,
    build_node_evidence_report_v0,
    build_public_network_config_v0,
    check_peer_status_v0,
    doctor_public_node_v0,
    join_public_node_from_network_config_url_v0,
    join_public_node_from_config_v0,
    load_node_status_v0,
    make_node_http_server_v0,
    poll_live_peers_once_v0,
    pull_live_from_peer_v0,
    run_node_once_v0,
    sync_public_bundle_from_url_v0,
)
from tools.zeno_ledger_verify_two_machine_evidence import verify_two_machine_evidence_report_v0


def _read_url_json(url: str) -> dict[str, object]:
    with urlopen(url, timeout=5) as response:  # noqa: S310 - local test server
        payload = response.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


def _post_url_json(url: str, value: dict[str, object]) -> dict[str, object]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj


def _signed_intent(intent: dict[str, object], *, chain_id: str, privkey: int) -> dict[str, object]:
    return {
        **intent,
        "signature": sign_dex_intent_for_engine(intent, privkey=privkey, chain_id=chain_id),
    }


class _QuietStaticHandler(SimpleHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return


def test_zeno_ledger_node_syncs_replays_bundle_and_serves_status(tmp_path: Path) -> None:
    source_bundle_root = tmp_path / "source_bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=source_bundle_root,
        network_id="zeno-ledger-node-testnet-0",
        chain_id="zeno-ledger-node-testnet-0",
        sequencer_id="sequencer-node-testnet-0",
        time_ms=1_778_730_123_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    static_handler = partial(_QuietStaticHandler, directory=str(source_bundle_root))
    static_server = ThreadingHTTPServer(("127.0.0.1", 0), static_handler)
    static_thread = threading.Thread(target=static_server.serve_forever, daemon=True)
    static_thread.start()
    try:
        host, port = static_server.server_address
        synced_bundle_root = tmp_path / "synced_bundle"
        sync_report = sync_public_bundle_from_url_v0(
            base_url=f"http://{host}:{port}",
            out_dir=synced_bundle_root,
        )
    finally:
        static_server.shutdown()
        static_server.server_close()

    assert sync_report["ok"] is True
    assert sync_report["feature_count"] == 10
    assert sync_report["downloaded_mirror_count"] == 11

    peer_attestation = synced_bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    node_dir = tmp_path / "node-b"
    node_report = run_node_once_v0(
        bundle_root=synced_bundle_root,
        node_id="node-b",
        data_dir=node_dir,
        peer_watcher_attestation_paths=[peer_attestation],
    )
    assert node_report["ok"] is True
    assert node_report["combined_watcher_count"] == 2
    assert node_report["covered_feature_count"] == 10

    status = load_node_status_v0(node_dir)
    assert status["ok"] is True
    assert status["node_role"] == "follower_watcher"
    assert status["network_id"] == "zeno-ledger-node-testnet-0"
    assert status["latest_height"] == 5
    assert status["token_symbol"] == "tZENO"
    assert [item["symbol"] for item in status["test_token_catalog"]] == ["tZENO", "tASSET0", "tASSET1"]
    assert status["testnet_faucet_posture"]["supports_fixture_mint"] is True
    assert status["testnet_token_support"]["faucet_scope"] == "testnet-only feature lanes"

    join_config_path = tmp_path / "node-join-config.json"
    join_config_path.write_text(
        json.dumps(
            {
                "schema": NODE_JOIN_CONFIG_SCHEMA,
                "bundle_root": str(synced_bundle_root),
                "node_id": "node-join",
                "data_dir": str(tmp_path / "node-join"),
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    join_report = join_public_node_from_config_v0(config_path=join_config_path)
    assert join_report["ok"] is True
    assert join_report["run_report"]["covered_feature_count"] == 10

    peer_node_dir = tmp_path / "node-c"
    shutil.copytree(node_dir, peer_node_dir)

    server = make_node_http_server_v0(
        data_dir=node_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        asset_a = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
        asset_b = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
        user_privkey = 7
        user_pubkey = bls_pubkey_hex_from_privkey(user_privkey)
        chain_id = "zeno-ledger-node-testnet-0"
        faucet_report = _post_url_json(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": user_pubkey,
                "asset": asset_a,
                "amount": 1234,
                "time_ms": 1_778_731_122_000,
                "tx_id": "node-http-faucet-v0",
            },
        )
        assert faucet_report["ok"] is True
        assert faucet_report["height"] == 6
        spoofed_unsigned_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_122_500,
                "tx": {
                    "tx_id": "node-live-unsigned-spoof-v0",
                    "block_timestamp": 1_778_731_122,
                    "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "operations": {
                        "2": [
                            {
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "SWAP_EXACT_IN",
                                "intent_id": "0x" + "ba" * 32,
                                "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                                "deadline": 1_999_999_999,
                                "nonce": 5,
                                "pool_id": compute_pool_id(asset_a, asset_b, 30),
                                "asset_in": asset_a,
                                "asset_out": asset_b,
                                "amount_in": 100,
                                "min_amount_out": 1,
                                "recipient": DEFAULT_BOOTSTRAP_SENDER,
                            }
                        ]
                    },
                },
            },
        )
        assert spoofed_unsigned_report["ok"] is False
        assert spoofed_unsigned_report["tx_accepted"] is False
        assert spoofed_unsigned_report["height"] == 7
        assert spoofed_unsigned_report["receipt"]["accepted"] is False
        assert "missing_intent_signature" in spoofed_unsigned_report["receipt"]["error_code"]
        assert _read_url_json(f"http://{host}:{port}/live")["state"]["latest_height"] == 6
        append_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_123_000,
                "tx": {
                    "tx_id": "node-live-swap-v0",
                    "block_timestamp": 1_778_731_123,
                    "tx_sender_pubkey": user_pubkey,
                    "operations": {
                        "2": [
                            _signed_intent({
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "SWAP_EXACT_IN",
                                "intent_id": "0x" + "bb" * 32,
                                "sender_pubkey": user_pubkey,
                                "deadline": 1_999_999_999,
                                "nonce": 1,
                                "pool_id": compute_pool_id(asset_a, asset_b, 30),
                                "asset_in": asset_a,
                                "asset_out": asset_b,
                                "amount_in": 100,
                                "min_amount_out": 1,
                                "recipient": user_pubkey,
                            }, chain_id=chain_id, privkey=user_privkey)
                        ]
                    },
                },
            },
        )
        assert append_report["ok"] is True
        assert append_report["height"] == 7
        assert append_report["receipt"]["accepted"] is True

        token_create_report = _post_url_json(
            f"http://{host}:{port}/tokens",
            {
                "creator_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "decimals": 8,
                "name": "Test Mango Credit",
                "salt": "node-http-token-v0",
                "symbol": "tMANGO",
                "time_ms": 1_778_731_124_000,
                "tx_id": "node-http-create-test-token-v0",
            },
        )
        assert token_create_report["ok"] is True
        assert token_create_report["height"] == 8
        assert token_create_report["receipt"]["accepted"] is True
        new_fake_asset = token_create_report["testnet_token"]["asset"]
        fake_asset_faucet_report = _post_url_json(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": user_pubkey,
                "asset": new_fake_asset,
                "amount": 50_000,
                "time_ms": 1_778_731_125_000,
                "tx_id": "node-http-new-fake-asset-faucet-v0",
            },
        )
        assert fake_asset_faucet_report["ok"] is True
        assert fake_asset_faucet_report["height"] == 9

        asset0_for_new_pool = min(asset_a, new_fake_asset)
        asset1_for_new_pool = max(asset_a, new_fake_asset)
        create_new_pool_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_125_000,
                "tx": {
                    "tx_id": "node-live-create-fake-token-pool-v0",
                    "block_timestamp": 1_778_731_125,
                    "tx_sender_pubkey": user_pubkey,
                    "operations": {
                        "2": [
                            _signed_intent({
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "CREATE_POOL",
                                "intent_id": "0x" + "cc" * 32,
                                "sender_pubkey": user_pubkey,
                                "deadline": 1_999_999_999,
                                "nonce": 2,
                                "asset0": asset0_for_new_pool,
                                "asset1": asset1_for_new_pool,
                                "fee_bps": 30,
                                "amount0": 100,
                                "amount1": 100,
                                "created_at": 1_778_731_125,
                            }, chain_id=chain_id, privkey=user_privkey)
                        ]
                    },
                },
            },
        )
        assert create_new_pool_report["ok"] is True
        assert create_new_pool_report["height"] == 10
        assert create_new_pool_report["receipt"]["accepted"] is True
        fake_pool_id = compute_pool_id(asset0_for_new_pool, asset1_for_new_pool, 30)
        add_fake_pool_liquidity_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_126_000,
                "tx": {
                    "tx_id": "node-live-add-fake-token-liquidity-v0",
                    "block_timestamp": 1_778_731_126,
                    "tx_sender_pubkey": user_pubkey,
                    "operations": {
                        "2": [
                            _signed_intent({
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "ADD_LIQUIDITY",
                                "intent_id": "0x" + "cd" * 32,
                                "sender_pubkey": user_pubkey,
                                "deadline": 1_999_999_999,
                                "nonce": 3,
                                "pool_id": fake_pool_id,
                                "amount0_desired": 10,
                                "amount1_desired": 10,
                                "amount0_min": 0,
                                "amount1_min": 0,
                                "recipient": user_pubkey,
                            }, chain_id=chain_id, privkey=user_privkey)
                        ]
                    },
                },
            },
        )
        assert add_fake_pool_liquidity_report["ok"] is True
        assert add_fake_pool_liquidity_report["height"] == 11
        assert add_fake_pool_liquidity_report["receipt"]["accepted"] is True
        remove_fake_pool_liquidity_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_127_000,
                "tx": {
                    "tx_id": "node-live-remove-fake-token-liquidity-v0",
                    "block_timestamp": 1_778_731_127,
                    "tx_sender_pubkey": user_pubkey,
                    "operations": {
                        "2": [
                            _signed_intent({
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "REMOVE_LIQUIDITY",
                                "intent_id": "0x" + "ce" * 32,
                                "sender_pubkey": user_pubkey,
                                "deadline": 1_999_999_999,
                                "nonce": 4,
                                "pool_id": fake_pool_id,
                                "lp_amount": 1,
                                "amount0_min": 0,
                                "amount1_min": 0,
                                "recipient": user_pubkey,
                            }, chain_id=chain_id, privkey=user_privkey)
                        ]
                    },
                },
            },
        )
        assert remove_fake_pool_liquidity_report["ok"] is True
        assert remove_fake_pool_liquidity_report["height"] == 12
        assert remove_fake_pool_liquidity_report["receipt"]["accepted"] is True

        mirror_handler = partial(_QuietStaticHandler, directory=str(source_bundle_root))
        mirror_server = ThreadingHTTPServer(("127.0.0.1", 0), mirror_handler)
        mirror_thread = threading.Thread(target=mirror_server.serve_forever, daemon=True)
        mirror_thread.start()
        try:
            mirror_host, mirror_port = mirror_server.server_address
            public_network_config = build_public_network_config_v0(
                bundle_root=source_bundle_root,
                mirror_base_url=f"http://{mirror_host}:{mirror_port}",
                writer_urls=[f"http://{host}:{port}"],
                peer_urls=[],
                poll_seconds=5,
                node_port=8790,
            )
            (source_bundle_root / "public_network_config.json").write_text(
                json.dumps(public_network_config, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            doctor_report = doctor_public_node_v0(
                config_url=f"http://{mirror_host}:{mirror_port}/public_network_config.json",
                expected_network_config_hash=str(public_network_config["network_config_hash"]),
            )
            assert doctor_report["ok"] is True
            assert doctor_report["remote_network"]["network_config_hash"] == public_network_config["network_config_hash"]
            bad_doctor_report = doctor_public_node_v0(
                config_url=f"http://{mirror_host}:{mirror_port}/public_network_config.json",
                expected_network_config_hash="0x" + "00" * 32,
            )
            assert bad_doctor_report["ok"] is False
            with pytest.raises(ValueError, match="network config hash"):
                join_public_node_from_network_config_url_v0(
                    config_url=f"http://{mirror_host}:{mirror_port}/public_network_config.json",
                    node_id="node-network-join-bad-hash",
                    bundle_root=tmp_path / "network-join-bad-hash-bundle",
                    data_dir=tmp_path / "node-network-join-bad-hash",
                    host="127.0.0.1",
                    port=None,
                    poll_seconds=None,
                    serve=False,
                    expected_network_config_hash="0x" + "00" * 32,
                )
            join_network_report = join_public_node_from_network_config_url_v0(
                config_url=f"http://{mirror_host}:{mirror_port}/public_network_config.json",
                node_id="node-network-join",
                bundle_root=tmp_path / "network-join-bundle",
                data_dir=tmp_path / "node-network-join",
                host="127.0.0.1",
                port=None,
                poll_seconds=None,
                serve=False,
                expected_network_config_hash=str(public_network_config["network_config_hash"]),
            )
        finally:
            mirror_server.shutdown()
            mirror_server.server_close()

        health = _read_url_json(f"http://{host}:{port}/health")
        served_status = _read_url_json(f"http://{host}:{port}/status")
        features = _read_url_json(f"http://{host}:{port}/features")
        tokens = _read_url_json(f"http://{host}:{port}/tokens")
        live = _read_url_json(f"http://{host}:{port}/live")
        network = _read_url_json(f"http://{host}:{port}/network")
        testnet_status = _read_url_json(f"http://{host}:{port}/testnet-status")
        pre_pull_peer_check = check_peer_status_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        follow_report = poll_live_peers_once_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        pull_report = follow_report["peers"][0]["pull_report"]
        post_pull_peer_check = check_peer_status_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        forward_server = make_node_http_server_v0(
            data_dir=peer_node_dir,
            host="127.0.0.1",
            port=0,
            enable_testnet_intake=True,
            enable_testnet_faucet=True,
            submit_peer_url=f"http://{host}:{port}",
        )
        forward_thread = threading.Thread(target=forward_server.serve_forever, daemon=True)
        forward_thread.start()
        try:
            forward_host, forward_port = forward_server.server_address
            forwarded_faucet_report = _post_url_json(
                f"http://{forward_host}:{forward_port}/faucet",
                {
                    "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "asset": asset_a,
                    "amount": 55,
                    "time_ms": 1_778_731_128_000,
                    "tx_id": "node-http-forwarded-faucet-v0",
                },
            )
            forward_network = _read_url_json(f"http://{forward_host}:{forward_port}/network")
        finally:
            forward_server.shutdown()
            forward_server.server_close()
        forwarded_pull_report = pull_live_from_peer_v0(
            data_dir=peer_node_dir,
            peer_url=f"http://{host}:{port}",
        )
        final_peer_check = check_peer_status_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        evidence_report = build_node_evidence_report_v0(
            data_dir=peer_node_dir,
            peer_urls=[f"http://{host}:{port}"],
        )
        evidence_verification = verify_two_machine_evidence_report_v0(
            evidence_report=evidence_report,
            expected_created_token_symbols=["tMANGO"],
            min_height=13,
        )

        assert health["ok"] is True
        assert health["node_status_hash"] == status["node_status_hash"]
        assert served_status["node_status_hash"] == status["node_status_hash"]
        assert features["covered_feature_count"] == 10
        assert len(tokens["test_token_catalog"]) == 3
        assert tokens["created_test_token_count"] == 1
        assert tokens["created_test_tokens"][0]["symbol"] == "tMANGO"
        assert tokens["created_test_tokens"][0]["asset"] == new_fake_asset
        assert join_network_report["ok"] is True
        assert join_network_report["peer_check"]["ok"] is True
        assert join_network_report["run_report"]["covered_feature_count"] == 10
        assert network["local_tip"]["height"] == 12
        assert network["capabilities"]["submission_forwarding_enabled"] is False
        assert live["live"] is True
        assert live["state"]["latest_height"] == 12
        assert pre_pull_peer_check["ok"] is True
        assert pre_pull_peer_check["peers"][0]["height_relation"] == "peer_ahead"
        assert pre_pull_peer_check["peers"][0]["common_height"] == 5
        assert follow_report["ok"] is True
        assert follow_report["peer_count"] == 1
        assert follow_report["peers"][0]["pulled_count"] == 7
        assert (peer_node_dir / "peer_follow_state.json").is_file()
        assert pull_report["ok"] is True
        assert pull_report["pulled_count"] == 7
        assert pull_report["to_height"] == 12
        assert post_pull_peer_check["ok"] is True
        assert post_pull_peer_check["peers"][0]["height_relation"] == "same_height"
        assert post_pull_peer_check["peers"][0]["common_height"] == 12
        assert (peer_node_dir / "testnet_token_registry.json").is_file()
        peer_registry = json.loads((peer_node_dir / "testnet_token_registry.json").read_text(encoding="utf-8"))
        assert peer_registry["tokens"][0]["symbol"] == "tMANGO"
        assert peer_registry["tokens"][0]["asset"] == new_fake_asset
        assert forwarded_faucet_report["ok"] is True
        assert forwarded_faucet_report["forwarded_to"] == f"http://{host}:{port}"
        assert forwarded_faucet_report["height"] == 13
        assert forward_network["capabilities"]["submission_forwarding_enabled"] is True
        assert forward_network["submit_peer_url"] == f"http://{host}:{port}"
        assert forwarded_pull_report["ok"] is True
        assert forwarded_pull_report["pulled_count"] == 1
        assert forwarded_pull_report["to_height"] == 13
        assert final_peer_check["ok"] is True
        assert final_peer_check["peers"][0]["height_relation"] == "same_height"
        assert final_peer_check["peers"][0]["common_height"] == 13
        assert evidence_report["ok"] is True
        assert evidence_report["local_tip"]["height"] == 13
        assert evidence_report["created_test_token_count"] == 1
        assert evidence_report["created_test_tokens"][0]["symbol"] == "tMANGO"
        assert evidence_report["peer_check"]["ok"] is True
        assert evidence_verification["ok"] is True
        assert evidence_verification["same_height_peer"]["height_relation"] == "same_height"
        peer_live = _read_url_json(f"http://{host}:{port}/live/header/13")
        assert peer_live["height"] == 13
        assert load_node_status_v0(peer_node_dir)["ok"] is True
        assert json.loads((peer_node_dir / "live_state.json").read_text(encoding="utf-8"))["latest_height"] == 13
        assert testnet_status["watcher_count"] == 2
    finally:
        server.shutdown()
        server.server_close()
