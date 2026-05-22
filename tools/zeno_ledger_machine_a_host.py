#!/usr/bin/env python3
"""Run the Machine A host flow for a ZenoLedger public testnet."""

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

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_node import (
    build_public_network_config_v0,
    make_node_http_server_v0,
    run_node_once_v0,
)
from tools.operator_report_output import emit_operator_json


MACHINE_A_HOST_SCHEMA = "zenodex.zeno_ledger.machine_a_host.v0"
LOCAL_TESTNET_WRITE_BINDINGS = frozenset({"127.0.0.1", "localhost", "::1"})


def validate_testnet_write_binding_v0(*, bind_host: str, enable_testnet_writes: bool) -> bool:
    """Return the validated writer-intake posture for the Machine A runner.

    Preconditions:
    - bind_host is the interface used by the unauthenticated writer server.
    - enable_testnet_writes means POST /tx and POST /faucet would mutate live testnet state.

    Invariant:
    - unauthenticated write endpoints are never enabled on wildcard/public bindings.

    Postcondition:
    - True is returned only for loopback-only bindings explicitly opted into writes.
    """

    normalized_bind_host = bind_host.strip().lower()
    if not enable_testnet_writes:
        return False
    if normalized_bind_host in LOCAL_TESTNET_WRITE_BINDINGS:
        return True
    raise ValueError(
        "Machine A testnet writes are unsigned and may only be enabled on a loopback bind host; "
        "use --bind-host 127.0.0.1 for local testing or keep writes disabled for public hosting"
    )


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


class _QuietStaticHandler(SimpleHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return


def _start_server(server: ThreadingHTTPServer) -> threading.Thread:
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return thread


def build_machine_b_acceptance_command_v0(
    *,
    config_url: str,
    network_config_hash: str,
    token_symbol: str,
) -> list[str]:
    return [
        "python3",
        "tools/zeno_ledger_machine_b_acceptance.py",
        "--config-url",
        config_url,
        "--expected-network-config-hash",
        network_config_hash,
        "--node-id",
        "operator-b",
        "--bundle-root",
        "/tmp/zeno-ledger-public-testnet-synced",
        "--data-dir",
        "/tmp/zeno-ledger-node-b",
        "--token-symbol",
        token_symbol,
        "--out",
        "/tmp/zeno-ledger-node-b/machine_b_acceptance_report.json",
    ]


def build_machine_a_ready_report_v0(
    *,
    out_dir: Path,
    data_dir: Path,
    public_host: str,
    mirror_port: int,
    writer_port: int,
    recommended_node_port: int,
    poll_seconds: int,
    network_config_path: Path,
    build_report: dict[str, Any],
    node_report: dict[str, Any],
    network_config: dict[str, Any],
    machine_b_token_symbol: str,
    enable_testnet_writes: bool = False,
) -> dict[str, Any]:
    mirror_base_url = f"http://{public_host}:{mirror_port}/"
    writer_url = f"http://{public_host}:{writer_port}"
    config_url = f"{mirror_base_url}public_network_config.json"
    network_config_hash = str(network_config["network_config_hash"])
    return {
        "schema": MACHINE_A_HOST_SCHEMA,
        "ok": True,
        "status": "serving",
        "network_id": network_config["network_id"],
        "chain_id": network_config["chain_id"],
        "public_host": public_host,
        "out_dir": str(out_dir),
        "data_dir": str(data_dir),
        "mirror_base_url": mirror_base_url,
        "writer_url": writer_url,
        "config_url": config_url,
        "network_config_path": str(network_config_path),
        "network_config_hash": network_config_hash,
        "recommended_node_port": recommended_node_port,
        "poll_seconds": poll_seconds,
        "build_report_ok": build_report.get("ok") is True,
        "node_report_ok": node_report.get("ok") is True,
        "covered_feature_count": build_report.get("covered_feature_count"),
        "latest_height": node_report.get("latest_height"),
        "machine_b_acceptance_command": build_machine_b_acceptance_command_v0(
            config_url=config_url,
            network_config_hash=network_config_hash,
            token_symbol=machine_b_token_symbol,
        ),
        "machine_b_acceptance_note": (
            "Run the command from a second machine using Python 3.10 or newer."
        ),
        "testnet_writes_enabled": enable_testnet_writes,
        "endpoints": {
            "health": f"{writer_url}/health",
            "status": f"{writer_url}/status",
            "network": f"{writer_url}/network",
            "tokens": f"{writer_url}/tokens",
            "live": f"{writer_url}/live",
            "follow": f"{writer_url}/follow",
            **(
                {"tx": f"{writer_url}/tx", "faucet": f"{writer_url}/faucet"}
                if enable_testnet_writes
                else {}
            ),
        },
    }


def run_machine_a_host_v0(
    *,
    out_dir: Path,
    data_dir: Path,
    bind_host: str,
    public_host: str,
    mirror_port: int,
    writer_port: int,
    network_id: str,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
    machine_b_token_symbol: str,
    poll_seconds: int,
    recommended_node_port: int,
    enable_testnet_writes: bool = False,
) -> dict[str, Any]:
    validated_testnet_writes = validate_testnet_write_binding_v0(
        bind_host=bind_host,
        enable_testnet_writes=enable_testnet_writes,
    )
    out_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    build_report = build_public_testnet_bundle_v0(
        out_dir=out_dir,
        network_id=network_id,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=time_ms,
        token_symbol=token_symbol,
    )
    attestation_path = out_dir / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    node_report = run_node_once_v0(
        bundle_root=out_dir,
        node_id="operator-a",
        data_dir=data_dir,
        peer_watcher_attestation_paths=[attestation_path],
    )

    static_handler = partial(_QuietStaticHandler, directory=str(out_dir))
    mirror_server = ThreadingHTTPServer((bind_host, mirror_port), static_handler)
    writer_server = make_node_http_server_v0(
        data_dir=data_dir,
        host=bind_host,
        port=writer_port,
        enable_testnet_intake=validated_testnet_writes,
        enable_testnet_faucet=validated_testnet_writes,
        peer_urls=[],
        poll_seconds=0,
    )
    actual_mirror_port = int(mirror_server.server_address[1])
    actual_writer_port = int(writer_server.server_address[1])
    mirror_base_url = f"http://{public_host}:{actual_mirror_port}/"
    writer_url = f"http://{public_host}:{actual_writer_port}"

    network_config = build_public_network_config_v0(
        bundle_root=out_dir,
        mirror_base_url=mirror_base_url,
        writer_urls=[writer_url],
        peer_urls=[],
        poll_seconds=poll_seconds,
        node_port=recommended_node_port,
        enable_testnet_intake=validated_testnet_writes,
        enable_testnet_faucet=validated_testnet_writes,
    )
    network_config_path = out_dir / "public_network_config.json"
    _write_json(network_config_path, network_config)

    mirror_thread = _start_server(mirror_server)
    writer_thread = _start_server(writer_server)
    ready_report = build_machine_a_ready_report_v0(
        out_dir=out_dir,
        data_dir=data_dir,
        public_host=public_host,
        mirror_port=actual_mirror_port,
        writer_port=actual_writer_port,
        recommended_node_port=recommended_node_port,
        poll_seconds=poll_seconds,
        network_config_path=network_config_path,
        build_report=build_report,
        node_report=node_report,
        network_config=network_config,
        machine_b_token_symbol=machine_b_token_symbol,
        enable_testnet_writes=validated_testnet_writes,
    )
    emit_operator_json(ready_report)
    sys.stdout.flush()

    try:
        while mirror_thread.is_alive() and writer_thread.is_alive():
            time.sleep(1)
    except KeyboardInterrupt:
        ready_report = {**ready_report, "status": "stopped"}
    finally:
        mirror_server.shutdown()
        writer_server.shutdown()
        mirror_server.server_close()
        writer_server.server_close()
    return ready_report


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/zeno-ledger-public-testnet"))
    parser.add_argument("--data-dir", type=Path, default=Path("/tmp/zeno-ledger-node-a"))
    parser.add_argument("--bind-host", default="0.0.0.0")
    parser.add_argument(
        "--public-host",
        required=True,
        help="Host or IP address that Machine B can use to reach Machine A.",
    )
    parser.add_argument("--mirror-port", type=int, default=8000)
    parser.add_argument("--writer-port", type=int, default=8787)
    parser.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default="tZENO")
    parser.add_argument("--machine-b-token-symbol", default="tMANGO")
    parser.add_argument("--poll-seconds", type=int, default=5)
    parser.add_argument("--recommended-node-port", type=int, default=8788)
    parser.add_argument(
        "--enable-local-testnet-writes",
        action="store_true",
        help=(
            "Enable unsigned POST /tx and /faucet only when --bind-host is loopback; "
            "never use on public interfaces."
        ),
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        run_machine_a_host_v0(
            out_dir=args.out_dir,
            data_dir=args.data_dir,
            bind_host=args.bind_host,
            public_host=args.public_host,
            mirror_port=args.mirror_port,
            writer_port=args.writer_port,
            network_id=args.network_id,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
            machine_b_token_symbol=args.machine_b_token_symbol,
            poll_seconds=args.poll_seconds,
            recommended_node_port=args.recommended_node_port,
            enable_testnet_writes=args.enable_local_testnet_writes,
        )
    except Exception as exc:
        print(
            json.dumps(
                {
                    "schema": MACHINE_A_HOST_SCHEMA,
                    "ok": False,
                    "status": "rejected",
                    "errors": [str(exc)],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
