from __future__ import annotations

import json
import threading
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.request import urlopen

from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_node import (
    load_node_status_v0,
    make_node_http_server_v0,
    run_node_once_v0,
    sync_public_bundle_from_url_v0,
)


def _read_url_json(url: str) -> dict[str, object]:
    with urlopen(url, timeout=5) as response:  # noqa: S310 - local test server
        payload = response.read().decode("utf-8")
    obj = json.loads(payload)
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

    server = make_node_http_server_v0(data_dir=node_dir, host="127.0.0.1", port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        host, port = server.server_address
        health = _read_url_json(f"http://{host}:{port}/health")
        served_status = _read_url_json(f"http://{host}:{port}/status")
        features = _read_url_json(f"http://{host}:{port}/features")
        tokens = _read_url_json(f"http://{host}:{port}/tokens")
        testnet_status = _read_url_json(f"http://{host}:{port}/testnet-status")

        assert health["ok"] is True
        assert health["node_status_hash"] == status["node_status_hash"]
        assert served_status["node_status_hash"] == status["node_status_hash"]
        assert features["covered_feature_count"] == 10
        assert len(tokens["test_token_catalog"]) == 3
        assert testnet_status["watcher_count"] == 2
    finally:
        server.shutdown()
        server.server_close()
