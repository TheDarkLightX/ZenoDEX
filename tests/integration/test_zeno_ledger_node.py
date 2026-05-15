from __future__ import annotations

import json
import shutil
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.request import Request, urlopen

from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import (
    load_node_status_v0,
    make_node_http_server_v0,
    pull_live_from_peer_v0,
    run_node_once_v0,
    sync_public_bundle_from_url_v0,
)


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
    with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
        body = response.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj


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
        faucet_report = _post_url_json(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": asset_a,
                "amount": 1234,
                "time_ms": 1_778_731_122_000,
                "tx_id": "node-http-faucet-v0",
            },
        )
        assert faucet_report["ok"] is True
        assert faucet_report["height"] == 6
        append_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_123_000,
                "tx": {
                    "tx_id": "node-live-swap-v0",
                    "block_timestamp": 1_778_731_123,
                    "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "operations": {
                        "2": [
                            {
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "SWAP_EXACT_IN",
                                "intent_id": "0x" + "bb" * 32,
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
        assert append_report["ok"] is True
        assert append_report["height"] == 7
        assert append_report["receipt"]["accepted"] is True

        new_fake_asset = "0x" + "33" * 32
        fake_asset_faucet_report = _post_url_json(
            f"http://{host}:{port}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": new_fake_asset,
                "amount": 50_000,
                "time_ms": 1_778_731_124_000,
                "tx_id": "node-http-new-fake-asset-faucet-v0",
            },
        )
        assert fake_asset_faucet_report["ok"] is True
        assert fake_asset_faucet_report["height"] == 8

        asset0_for_new_pool = min(asset_a, new_fake_asset)
        asset1_for_new_pool = max(asset_a, new_fake_asset)
        create_new_pool_report = _post_url_json(
            f"http://{host}:{port}/tx",
            {
                "time_ms": 1_778_731_125_000,
                "tx": {
                    "tx_id": "node-live-create-fake-token-pool-v0",
                    "block_timestamp": 1_778_731_125,
                    "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "operations": {
                        "2": [
                            {
                                "module": "TauSwap",
                                "version": "0.1",
                                "kind": "CREATE_POOL",
                                "intent_id": "0x" + "cc" * 32,
                                "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                                "deadline": 1_999_999_999,
                                "nonce": 6,
                                "asset0": asset0_for_new_pool,
                                "asset1": asset1_for_new_pool,
                                "fee_bps": 30,
                                "amount0": 100,
                                "amount1": 100,
                                "created_at": 1_778_731_125,
                            }
                        ]
                    },
                },
            },
        )
        assert create_new_pool_report["ok"] is True
        assert create_new_pool_report["height"] == 9
        assert create_new_pool_report["receipt"]["accepted"] is True

        health = _read_url_json(f"http://{host}:{port}/health")
        served_status = _read_url_json(f"http://{host}:{port}/status")
        features = _read_url_json(f"http://{host}:{port}/features")
        tokens = _read_url_json(f"http://{host}:{port}/tokens")
        live = _read_url_json(f"http://{host}:{port}/live")
        testnet_status = _read_url_json(f"http://{host}:{port}/testnet-status")
        pull_report = pull_live_from_peer_v0(
            data_dir=peer_node_dir,
            peer_url=f"http://{host}:{port}",
        )

        assert health["ok"] is True
        assert health["node_status_hash"] == status["node_status_hash"]
        assert served_status["node_status_hash"] == status["node_status_hash"]
        assert features["covered_feature_count"] == 10
        assert len(tokens["test_token_catalog"]) == 3
        assert live["live"] is True
        assert live["state"]["latest_height"] == 9
        assert pull_report["ok"] is True
        assert pull_report["pulled_count"] == 4
        assert pull_report["to_height"] == 9
        peer_live = _read_url_json(f"http://{host}:{port}/live/header/9")
        assert peer_live["height"] == 9
        assert load_node_status_v0(peer_node_dir)["ok"] is True
        assert json.loads((peer_node_dir / "live_state.json").read_text(encoding="utf-8"))["latest_height"] == 9
        assert testnet_status["watcher_count"] == 2
    finally:
        server.shutdown()
        server.server_close()
