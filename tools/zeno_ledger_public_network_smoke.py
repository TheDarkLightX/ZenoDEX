#!/usr/bin/env python3
"""Run a local two-node ZenoLedger public-network smoke test."""

from __future__ import annotations

import argparse
import json
import sys
import threading
import time
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_ASSET0,
    DEFAULT_ASSET1,
    DEFAULT_BOOTSTRAP_SENDER,
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_node import (
    append_dex_transaction_v0,
    append_testnet_faucet_v0,
    check_peer_status_v0,
    make_node_http_server_v0,
    pull_live_from_peer_v0,
    run_node_once_v0,
    sync_public_bundle_from_url_v0,
)
from tools.operator_report_output import emit_operator_json, write_public_json


REPORT_SCHEMA = "zenodex.zeno_ledger.public_network_smoke_report.v0"
EXPECTED_FEATURE_COUNT = 10
EXPECTED_WATCHER_COUNT = 2


class _QuietStaticHandler(SimpleHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return


def _start_static_server(root: Path) -> tuple[ThreadingHTTPServer, str]:
    handler = partial(_QuietStaticHandler, directory=str(root))
    server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address
    return server, f"http://{host}:{port}"


def _start_node_server(data_dir: Path, *, submit_peer_url: str | None = None) -> tuple[ThreadingHTTPServer, str]:
    server = make_node_http_server_v0(
        data_dir=data_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        submit_peer_url=submit_peer_url,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address
    return server, f"http://{host}:{port}"


def _post_json(url: str, value: dict[str, object]) -> dict[str, object]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urlopen(request, timeout=30) as response:  # noqa: S310 - local smoke server
        body = response.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj


def validate_public_network_smoke_report_v0(report: dict[str, Any]) -> list[str]:
    """Validate the exact state-machine trace expected from the smoke scenario."""

    errors: list[str] = []

    def require(condition: bool, message: str) -> None:
        if not condition:
            errors.append(message)

    def field(name: str) -> Any:
        return report.get(name)

    require(field("schema") == REPORT_SCHEMA, "schema mismatch")
    require(field("ok") is True, "ok must be true")
    require(field("status") == "accepted", "status must be accepted")
    elapsed_ms = field("elapsed_ms")
    require(isinstance(elapsed_ms, (int, float)) and elapsed_ms >= 0, "elapsed_ms must be nonnegative")
    require(isinstance(field("network_id"), str) and bool(field("network_id")), "network_id must be non-empty")
    require(isinstance(field("chain_id"), str) and bool(field("chain_id")), "chain_id must be non-empty")

    for name in ("source_feature_count", "sync_a_feature_count", "sync_b_feature_count"):
        require(field(name) == EXPECTED_FEATURE_COUNT, f"{name} must be {EXPECTED_FEATURE_COUNT}")

    for name in ("node_a_watcher_count", "node_b_watcher_count"):
        require(field(name) == EXPECTED_WATCHER_COUNT, f"{name} must be {EXPECTED_WATCHER_COUNT}")

    expected_heights = {
        "faucet_existing_height": 6,
        "swap_height": 7,
        "faucet_new_asset_height": 8,
        "create_fake_pool_height": 9,
        "add_fake_pool_liquidity_height": 10,
        "remove_fake_pool_liquidity_height": 11,
        "forwarded_faucet_height": 12,
        "node_b_latest_height": 12,
    }
    for name, expected in expected_heights.items():
        require(field(name) == expected, f"{name} must be {expected}")

    require(field("node_b_pulled_count") == 6, "node_b_pulled_count must be 6")
    require(field("node_b_total_pulled_count") == 7, "node_b_total_pulled_count must be 7")
    require(field("forwarded_pull_count") == 1, "forwarded_pull_count must be 1")
    require(field("forwarded_pull_to_height") == 12, "forwarded_pull_to_height must be 12")

    require(field("pre_pull_peer_check_ok") is True, "pre-pull peer check must pass")
    require(field("pre_pull_peer_height_relation") == "peer_ahead", "pre-pull peer must be ahead")
    require(field("pre_pull_common_height") == 5, "pre-pull common height must be 5")
    require(field("post_pull_peer_check_ok") is True, "post-pull peer check must pass")
    require(field("post_pull_peer_height_relation") == "same_height", "post-pull peer relation must be same_height")
    require(field("post_pull_common_height") == 11, "post-pull common height must be 11")
    require(field("final_peer_check_ok") is True, "final peer check must pass")
    require(field("final_peer_height_relation") == "same_height", "final peer relation must be same_height")
    require(field("final_common_height") == 12, "final common height must be 12")

    forwarded_to = field("forwarded_faucet_submit_peer")
    require(isinstance(forwarded_to, str) and forwarded_to.startswith("http://127.0.0.1:"), "forwarded faucet must target local writer peer")
    return errors


def run_public_network_smoke_v0(*, out_dir: Path, network_id: str, chain_id: str) -> dict[str, Any]:
    start = time.perf_counter()
    source_bundle = out_dir / "source_bundle"
    node_a_bundle = out_dir / "node_a_bundle"
    node_b_bundle = out_dir / "node_b_bundle"
    node_a_dir = out_dir / "node_a"
    node_b_dir = out_dir / "node_b"
    out_dir.mkdir(parents=True, exist_ok=True)

    build_report = build_public_testnet_bundle_v0(
        out_dir=source_bundle,
        network_id=network_id,
        chain_id=chain_id,
        sequencer_id=DEFAULT_SEQUENCER_ID,
        time_ms=DEFAULT_TIME_MS,
        token_symbol="tZENO",
    )
    mirror_server, mirror_url = _start_static_server(source_bundle)
    node_a_server: ThreadingHTTPServer | None = None
    node_b_forward_server: ThreadingHTTPServer | None = None
    try:
        sync_a = sync_public_bundle_from_url_v0(base_url=mirror_url, out_dir=node_a_bundle)
        sync_b = sync_public_bundle_from_url_v0(base_url=mirror_url, out_dir=node_b_bundle)
    finally:
        mirror_server.shutdown()
        mirror_server.server_close()

    peer_attestation_a = node_a_bundle / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    peer_attestation_b = node_b_bundle / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    node_a = run_node_once_v0(
        bundle_root=node_a_bundle,
        node_id="node-a",
        data_dir=node_a_dir,
        peer_watcher_attestation_paths=[peer_attestation_a],
    )
    node_b = run_node_once_v0(
        bundle_root=node_b_bundle,
        node_id="node-b",
        data_dir=node_b_dir,
        peer_watcher_attestation_paths=[peer_attestation_b],
    )

    node_a_server, node_a_url = _start_node_server(node_a_dir)
    try:
        asset_a = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
        asset_b = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
        faucet_existing = append_testnet_faucet_v0(
            data_dir=node_a_dir,
            to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
            asset=asset_a,
            amount=1234,
            time_ms=DEFAULT_TIME_MS + 1_000_000,
            tx_id="smoke-faucet-existing-asset-v0",
        )
        swap = append_dex_transaction_v0(
            data_dir=node_a_dir,
            time_ms=DEFAULT_TIME_MS + 1_001_000,
            tx={
                "tx_id": "smoke-live-swap-v0",
                "block_timestamp": (DEFAULT_TIME_MS + 1_001_000) // 1000,
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
        )
        new_asset = "0x" + "33" * 32
        faucet_new = append_testnet_faucet_v0(
            data_dir=node_a_dir,
            to_pubkey=DEFAULT_BOOTSTRAP_SENDER,
            asset=new_asset,
            amount=50_000,
            time_ms=DEFAULT_TIME_MS + 1_002_000,
            tx_id="smoke-faucet-new-asset-v0",
        )
        new_pool_asset0 = min(asset_a, new_asset)
        new_pool_asset1 = max(asset_a, new_asset)
        create_fake_pool = append_dex_transaction_v0(
            data_dir=node_a_dir,
            time_ms=DEFAULT_TIME_MS + 1_003_000,
            tx={
                "tx_id": "smoke-create-fake-token-pool-v0",
                "block_timestamp": (DEFAULT_TIME_MS + 1_003_000) // 1000,
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
                            "asset0": new_pool_asset0,
                            "asset1": new_pool_asset1,
                            "fee_bps": 30,
                            "amount0": 100,
                            "amount1": 100,
                            "created_at": (DEFAULT_TIME_MS + 1_003_000) // 1000,
                        }
                    ]
                },
            },
        )
        fake_pool_id = compute_pool_id(new_pool_asset0, new_pool_asset1, 30)
        add_fake_pool_liquidity = append_dex_transaction_v0(
            data_dir=node_a_dir,
            time_ms=DEFAULT_TIME_MS + 1_004_000,
            tx={
                "tx_id": "smoke-add-fake-token-liquidity-v0",
                "block_timestamp": (DEFAULT_TIME_MS + 1_004_000) // 1000,
                "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "operations": {
                    "2": [
                        {
                            "module": "TauSwap",
                            "version": "0.1",
                            "kind": "ADD_LIQUIDITY",
                            "intent_id": "0x" + "cd" * 32,
                            "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                            "deadline": 1_999_999_999,
                            "nonce": 7,
                            "pool_id": fake_pool_id,
                            "amount0_desired": 10,
                            "amount1_desired": 10,
                            "amount0_min": 0,
                            "amount1_min": 0,
                            "recipient": DEFAULT_BOOTSTRAP_SENDER,
                        }
                    ]
                },
            },
        )
        remove_fake_pool_liquidity = append_dex_transaction_v0(
            data_dir=node_a_dir,
            time_ms=DEFAULT_TIME_MS + 1_005_000,
            tx={
                "tx_id": "smoke-remove-fake-token-liquidity-v0",
                "block_timestamp": (DEFAULT_TIME_MS + 1_005_000) // 1000,
                "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "operations": {
                    "2": [
                        {
                            "module": "TauSwap",
                            "version": "0.1",
                            "kind": "REMOVE_LIQUIDITY",
                            "intent_id": "0x" + "ce" * 32,
                            "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                            "deadline": 1_999_999_999,
                            "nonce": 8,
                            "pool_id": fake_pool_id,
                            "lp_amount": 1,
                            "amount0_min": 0,
                            "amount1_min": 0,
                            "recipient": DEFAULT_BOOTSTRAP_SENDER,
                        }
                    ]
                },
            },
        )
        pre_pull_peer_check = check_peer_status_v0(data_dir=node_b_dir, peer_urls=[node_a_url])
        pull = pull_live_from_peer_v0(data_dir=node_b_dir, peer_url=node_a_url)
        post_pull_peer_check = check_peer_status_v0(data_dir=node_b_dir, peer_urls=[node_a_url])
        node_b_forward_server, node_b_url = _start_node_server(node_b_dir, submit_peer_url=node_a_url)
        forwarded_faucet = _post_json(
            f"{node_b_url}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": asset_a,
                "amount": 55,
                "time_ms": DEFAULT_TIME_MS + 1_006_000,
                "tx_id": "smoke-forwarded-faucet-v0",
            },
        )
        forwarded_pull = pull_live_from_peer_v0(data_dir=node_b_dir, peer_url=node_a_url)
        final_peer_check = check_peer_status_v0(data_dir=node_b_dir, peer_urls=[node_a_url])
    finally:
        if node_b_forward_server is not None:
            node_b_forward_server.shutdown()
            node_b_forward_server.server_close()
        if node_a_server is not None:
            node_a_server.shutdown()
            node_a_server.server_close()

    ok = all(
        item.get("ok") is True
        for item in (
            build_report,
            sync_a,
            sync_b,
            node_a,
            node_b,
            faucet_existing,
            swap,
            faucet_new,
            create_fake_pool,
            add_fake_pool_liquidity,
            remove_fake_pool_liquidity,
            pre_pull_peer_check,
            pull,
            post_pull_peer_check,
            forwarded_faucet,
            forwarded_pull,
            final_peer_check,
        )
    )
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "elapsed_ms": (time.perf_counter() - start) * 1000.0,
        "out_dir": str(out_dir),
        "network_id": network_id,
        "chain_id": chain_id,
        "source_feature_count": build_report["covered_feature_count"],
        "sync_a_feature_count": sync_a["feature_count"],
        "sync_b_feature_count": sync_b["feature_count"],
        "node_a_watcher_count": node_a["combined_watcher_count"],
        "node_b_watcher_count": node_b["combined_watcher_count"],
        "faucet_existing_height": faucet_existing["height"],
        "swap_height": swap["height"],
        "faucet_new_asset_height": faucet_new["height"],
        "create_fake_pool_height": create_fake_pool["height"],
        "add_fake_pool_liquidity_height": add_fake_pool_liquidity["height"],
        "remove_fake_pool_liquidity_height": remove_fake_pool_liquidity["height"],
        "node_b_pulled_count": pull["pulled_count"],
        "node_b_total_pulled_count": int(pull["pulled_count"]) + int(forwarded_pull["pulled_count"]),
        "node_b_latest_height": forwarded_pull["local_latest_height"],
        "pre_pull_peer_check_ok": pre_pull_peer_check["ok"],
        "pre_pull_peer_height_relation": pre_pull_peer_check["peers"][0]["height_relation"],
        "pre_pull_common_height": pre_pull_peer_check["peers"][0]["common_height"],
        "post_pull_peer_check_ok": post_pull_peer_check["ok"],
        "post_pull_peer_height_relation": post_pull_peer_check["peers"][0]["height_relation"],
        "post_pull_common_height": post_pull_peer_check["peers"][0]["common_height"],
        "forwarded_faucet_height": forwarded_faucet["height"],
        "forwarded_faucet_submit_peer": forwarded_faucet["forwarded_to"],
        "forwarded_pull_count": forwarded_pull["pulled_count"],
        "forwarded_pull_to_height": forwarded_pull["to_height"],
        "final_peer_check_ok": final_peer_check["ok"],
        "final_peer_height_relation": final_peer_check["peers"][0]["height_relation"],
        "final_common_height": final_peer_check["peers"][0]["common_height"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run a local two-node ZenoLedger public-network smoke test")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--report-out", type=Path)
    args = parser.parse_args(argv)

    try:
        report = run_public_network_smoke_v0(
            out_dir=args.out_dir,
            network_id=args.network_id,
            chain_id=args.chain_id,
        )
        trace_errors = validate_public_network_smoke_report_v0(report)
        if trace_errors:
            report = {
                **report,
                "ok": False,
                "status": "rejected",
                "trace_errors": trace_errors,
            }
    except Exception as exc:
        report = {"schema": REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    if args.report_out is not None:
        write_public_json(args.report_out, report)
    emit_operator_json(report)
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
