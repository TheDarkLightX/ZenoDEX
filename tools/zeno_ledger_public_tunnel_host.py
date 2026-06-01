#!/usr/bin/env python3
"""Run a zero-cost outbound tunnel host for a ZenoLedger public testnet.

This runner is for operator environments that cannot accept inbound Wi-Fi or
router traffic. It binds the ledger writer and bundle mirror to loopback, then
publishes one HTTP gateway through a Cloudflare Quick Tunnel. The generated
``public_network_config.json`` uses the public tunnel URL for both the bundle
mirror and writer URL, so a clean Machine B can join from that single URL.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import secrets
import subprocess
import sys
import threading
import time
from functools import partial
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import urljoin
from urllib.request import HTTPRedirectHandler, Request, build_opener, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.operator_report_output import emit_operator_json
from tools.zeno_ledger_machine_a_host import build_machine_b_acceptance_command_v0
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


PUBLIC_TUNNEL_HOST_SCHEMA = "zenodex.zeno_ledger.public_tunnel_host.v0"
MAX_PROXY_BODY_BYTES = 16 * 1024 * 1024
TRYCLOUDFLARE_URL_RE = re.compile(r"https://[a-zA-Z0-9-]+\.trycloudflare\.com")


class _NoRedirectHandler(HTTPRedirectHandler):
    """Reject upstream redirects so bearer tokens cannot be forwarded elsewhere."""

    def redirect_request(self, req: Request, fp: Any, code: int, msg: str, headers: Any, newurl: str) -> None:
        raise HTTPError(newurl, code, "redirects disabled for tunnel gateway", headers, fp)


_NO_REDIRECT_OPENER = build_opener(_NoRedirectHandler())


def is_writer_proxy_path_v0(path: str) -> bool:
    """Return whether a public gateway request should be proxied to the writer."""

    request_path = path.split("?", 1)[0]
    if request_path in {
        "/",
        "/health",
        "/status",
        "/features",
        "/tokens",
        "/network",
        "/api/pools",
        "/api/swap",
        "/live",
        "/attestation",
        "/testnet-status",
        "/tx",
        "/faucet",
    }:
        return True
    return any(
        request_path.startswith(prefix)
        for prefix in (
            "/live/header/",
            "/live/body/",
            "/live/checkpoint/",
            "/live/snapshot/",
        )
    )


def parse_cloudflared_quick_tunnel_url_v0(text: str) -> str | None:
    """Extract the public Cloudflare Quick Tunnel URL from one log line."""

    match = TRYCLOUDFLARE_URL_RE.search(text)
    return None if match is None else match.group(0).rstrip("/")


def build_public_tunnel_ready_report_v0(
    *,
    out_dir: Path,
    data_dir: Path,
    tunnel_url: str,
    gateway_port: int,
    writer_port: int,
    network_config_path: Path,
    build_report: dict[str, Any],
    node_report: dict[str, Any],
    network_config: dict[str, Any],
    machine_b_token_symbol: str,
    write_auth_token_path: Path,
    machine_b_peer_auth_token_file: str,
    cloudflared_command: list[str],
) -> dict[str, Any]:
    """Build the operator-facing report printed after the tunnel is ready."""

    config_url = f"{tunnel_url.rstrip('/')}/public_network_config.json"
    network_config_hash = str(network_config["network_config_hash"])
    return {
        "schema": PUBLIC_TUNNEL_HOST_SCHEMA,
        "ok": True,
        "status": "serving",
        "exposure_model": "outbound_cloudflare_quick_tunnel",
        "out_dir": str(out_dir),
        "data_dir": str(data_dir),
        "gateway_url": tunnel_url.rstrip("/"),
        "config_url": config_url,
        "writer_url": tunnel_url.rstrip("/"),
        "mirror_base_url": f"{tunnel_url.rstrip('/')}/",
        "network_id": network_config["network_id"],
        "chain_id": network_config["chain_id"],
        "network_config_path": str(network_config_path),
        "network_config_hash": network_config_hash,
        "local_gateway_url": f"http://127.0.0.1:{gateway_port}",
        "local_writer_url": f"http://127.0.0.1:{writer_port}",
        "write_auth_required": True,
        "write_auth_token_file": str(write_auth_token_path),
        "write_auth_token_distribution": (
            "Copy the token file contents to the Machine B path shown in the acceptance command."
        ),
        "build_report_ok": build_report.get("ok") is True,
        "node_report_ok": node_report.get("ok") is True,
        "covered_feature_count": build_report.get("covered_feature_count"),
        "latest_height": node_report.get("latest_height"),
        "cloudflared_command": list(cloudflared_command),
        "machine_b_acceptance_command": build_machine_b_acceptance_command_v0(
            config_url=config_url,
            network_config_hash=network_config_hash,
            token_symbol=machine_b_token_symbol,
            peer_auth_token_file=machine_b_peer_auth_token_file,
        ),
        "endpoints": {
            "health": f"{tunnel_url.rstrip('/')}/health",
            "status": f"{tunnel_url.rstrip('/')}/status",
            "network": f"{tunnel_url.rstrip('/')}/network",
            "tokens": f"{tunnel_url.rstrip('/')}/tokens",
            "live": f"{tunnel_url.rstrip('/')}/live",
            "follow": f"{tunnel_url.rstrip('/')}/follow",
            "tx": f"{tunnel_url.rstrip('/')}/tx",
            "faucet": f"{tunnel_url.rstrip('/')}/faucet",
        },
    }


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_private_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    try:
        path.chmod(0o600)
    except OSError:
        pass


def _copy_proxy_headers(headers: Any) -> dict[str, str]:
    skipped = {"connection", "content-length", "host", "transfer-encoding"}
    return {
        str(key): str(value)
        for key, value in headers.items()
        if str(key).lower() not in skipped
    }


def make_public_tunnel_gateway_server_v0(
    *,
    bundle_root: Path,
    writer_url: str,
    host: str,
    port: int,
) -> ThreadingHTTPServer:
    """Create a same-origin gateway for bundle files and writer endpoints."""

    writer_base = writer_url.rstrip("/") + "/"

    class Handler(SimpleHTTPRequestHandler):
        server_version = "ZenoLedgerTunnelGateway/0"

        def _send_json(self, value: object, *, status: HTTPStatus = HTTPStatus.OK) -> None:
            payload = json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"
            self.send_response(int(status))
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def _proxy_to_writer(self) -> None:
            content_length = int(self.headers.get("Content-Length", "0") or "0")
            if content_length > MAX_PROXY_BODY_BYTES:
                self._send_json(
                    {"ok": False, "error": "request_body_too_large"},
                    status=HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
                )
                return
            body = self.rfile.read(content_length) if content_length else None
            target = urljoin(writer_base, self.path.lstrip("/"))
            request = Request(
                target,
                data=body,
                headers=_copy_proxy_headers(self.headers),
                method=self.command,
            )
            try:
                with _NO_REDIRECT_OPENER.open(request, timeout=30) as response:  # noqa: S310 - local writer URL
                    status = int(response.status)
                    payload = response.read(MAX_PROXY_BODY_BYTES + 1)
                    content_type = response.headers.get("Content-Type", "application/json")
            except HTTPError as exc:
                status = int(exc.code)
                payload = exc.read(MAX_PROXY_BODY_BYTES + 1)
                content_type = exc.headers.get("Content-Type", "application/json")
            except Exception as exc:  # noqa: BLE001 - gateway should report and keep serving.
                self._send_json(
                    {"ok": False, "error": "writer_proxy_failed", "detail": str(exc)},
                    status=HTTPStatus.BAD_GATEWAY,
                )
                return
            if len(payload) > MAX_PROXY_BODY_BYTES:
                self._send_json(
                    {"ok": False, "error": "writer_response_too_large"},
                    status=HTTPStatus.BAD_GATEWAY,
                )
                return
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def do_GET(self) -> None:  # noqa: N802
            if is_writer_proxy_path_v0(self.path):
                self._proxy_to_writer()
                return
            super().do_GET()

        def do_POST(self) -> None:  # noqa: N802
            if is_writer_proxy_path_v0(self.path):
                self._proxy_to_writer()
                return
            self._send_json({"ok": False, "error": "not_found"}, status=HTTPStatus.NOT_FOUND)

        def log_message(self, format: str, *args: object) -> None:
            return

    handler = partial(Handler, directory=str(bundle_root))
    return ThreadingHTTPServer((host, port), handler)


def build_cloudflared_command_v0(
    *,
    local_url: str,
    mode: str,
    image: str,
) -> list[str]:
    if mode == "docker-host":
        return [
            "docker",
            "run",
            "--rm",
            "--network",
            "host",
            image,
            "tunnel",
            "--no-autoupdate",
            "--url",
            local_url,
        ]
    if mode == "local-binary":
        return ["cloudflared", "tunnel", "--no-autoupdate", "--url", local_url]
    raise ValueError(f"unsupported cloudflared mode: {mode}")


def start_cloudflared_quick_tunnel_v0(
    *,
    command: list[str],
    timeout_seconds: int,
) -> tuple[subprocess.Popen[str], str, list[str]]:
    """Start cloudflared and return the first trycloudflare URL it prints."""

    proc = subprocess.Popen(  # noqa: S603 - operator-facing CLI runner.
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert proc.stdout is not None
    started = time.monotonic()
    lines: list[str] = []
    while time.monotonic() - started < timeout_seconds:
        line = proc.stdout.readline()
        if line == "":
            if proc.poll() is not None:
                raise RuntimeError(f"cloudflared exited before publishing a URL: {lines[-8:]}")
            time.sleep(0.1)
            continue
        stripped = line.rstrip()
        lines.append(stripped)
        tunnel_url = parse_cloudflared_quick_tunnel_url_v0(stripped)
        if tunnel_url is not None:
            return proc, tunnel_url, lines
    proc.terminate()
    raise TimeoutError(f"cloudflared did not publish a tunnel URL within {timeout_seconds}s")


def _start_server(server: ThreadingHTTPServer) -> threading.Thread:
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return thread


def run_public_tunnel_host_v0(
    *,
    out_dir: Path,
    data_dir: Path,
    gateway_port: int,
    writer_port: int,
    network_id: str,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
    machine_b_token_symbol: str,
    poll_seconds: int,
    recommended_node_port: int,
    write_auth_token_file: Path | None,
    machine_b_peer_auth_token_file: str,
    cloudflared_mode: str,
    cloudflared_image: str,
    tunnel_timeout_seconds: int,
) -> dict[str, Any]:
    """Run the public tunnel host until interrupted."""

    out_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    if write_auth_token_file is None:
        write_auth_token_file = out_dir / "secrets" / "public_tunnel_write.token"
    if write_auth_token_file.is_file():
        write_auth_token = write_auth_token_file.read_text(encoding="utf-8").strip()
        if write_auth_token == "":
            raise ValueError("write auth token file is empty")
    else:
        write_auth_token = secrets.token_urlsafe(32)
        _write_private_text(write_auth_token_file, write_auth_token)

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

    writer_server = make_node_http_server_v0(
        data_dir=data_dir,
        host="127.0.0.1",
        port=writer_port,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        write_auth_token=write_auth_token,
        peer_urls=[],
    )
    writer_actual_port = int(writer_server.server_address[1])
    writer_url = f"http://127.0.0.1:{writer_actual_port}"
    gateway_server = make_public_tunnel_gateway_server_v0(
        bundle_root=out_dir,
        writer_url=writer_url,
        host="127.0.0.1",
        port=gateway_port,
    )
    gateway_actual_port = int(gateway_server.server_address[1])
    gateway_url = f"http://127.0.0.1:{gateway_actual_port}"

    writer_thread = _start_server(writer_server)
    gateway_thread = _start_server(gateway_server)
    cloudflared_command = build_cloudflared_command_v0(
        local_url=gateway_url,
        mode=cloudflared_mode,
        image=cloudflared_image,
    )
    cloudflared_proc, tunnel_url, cloudflared_log = start_cloudflared_quick_tunnel_v0(
        command=cloudflared_command,
        timeout_seconds=tunnel_timeout_seconds,
    )

    network_config = build_public_network_config_v0(
        bundle_root=out_dir,
        mirror_base_url=f"{tunnel_url}/",
        writer_urls=[tunnel_url],
        peer_urls=[],
        poll_seconds=poll_seconds,
        node_port=recommended_node_port,
    )
    network_config_path = out_dir / "public_network_config.json"
    _write_json(network_config_path, network_config)
    _write_json(out_dir / "cloudflared_startup_log.json", {"lines": cloudflared_log})

    ready_report = build_public_tunnel_ready_report_v0(
        out_dir=out_dir,
        data_dir=data_dir,
        tunnel_url=tunnel_url,
        gateway_port=gateway_actual_port,
        writer_port=writer_actual_port,
        network_config_path=network_config_path,
        build_report=build_report,
        node_report=node_report,
        network_config=network_config,
        machine_b_token_symbol=machine_b_token_symbol,
        write_auth_token_path=write_auth_token_file,
        machine_b_peer_auth_token_file=machine_b_peer_auth_token_file,
        cloudflared_command=cloudflared_command,
    )
    emit_operator_json(ready_report)
    sys.stdout.flush()

    try:
        while (
            writer_thread.is_alive()
            and gateway_thread.is_alive()
            and cloudflared_proc.poll() is None
        ):
            time.sleep(1)
    except KeyboardInterrupt:
        ready_report = {**ready_report, "status": "stopped"}
    finally:
        cloudflared_proc.terminate()
        writer_server.shutdown()
        gateway_server.shutdown()
        writer_server.server_close()
        gateway_server.server_close()
    return ready_report


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/zeno-ledger-public-testnet-tunnel"))
    parser.add_argument("--data-dir", type=Path, default=Path("/tmp/zeno-ledger-node-a-tunnel"))
    parser.add_argument("--gateway-port", type=int, default=0)
    parser.add_argument("--writer-port", type=int, default=0)
    parser.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default="tZENO")
    parser.add_argument("--machine-b-token-symbol", default="tZENO")
    parser.add_argument("--poll-seconds", type=int, default=5)
    parser.add_argument("--recommended-node-port", type=int, default=8788)
    parser.add_argument("--write-auth-token-file", type=Path)
    parser.add_argument(
        "--machine-b-peer-auth-token-file",
        default="/tmp/zeno-ledger-machine-b-peer.token",
        help="Path to use in the printed Machine B acceptance command.",
    )
    parser.add_argument(
        "--cloudflared-mode",
        choices=("docker-host", "local-binary"),
        default="docker-host",
        help="Use Docker host networking on Linux, or an installed cloudflared binary.",
    )
    parser.add_argument("--cloudflared-image", default="cloudflare/cloudflared:latest")
    parser.add_argument("--tunnel-timeout-seconds", type=int, default=90)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        run_public_tunnel_host_v0(
            out_dir=args.out_dir,
            data_dir=args.data_dir,
            gateway_port=args.gateway_port,
            writer_port=args.writer_port,
            network_id=args.network_id,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
            machine_b_token_symbol=args.machine_b_token_symbol,
            poll_seconds=args.poll_seconds,
            recommended_node_port=args.recommended_node_port,
            write_auth_token_file=args.write_auth_token_file,
            machine_b_peer_auth_token_file=args.machine_b_peer_auth_token_file,
            cloudflared_mode=args.cloudflared_mode,
            cloudflared_image=args.cloudflared_image,
            tunnel_timeout_seconds=args.tunnel_timeout_seconds,
        )
    except Exception as exc:
        print(
            json.dumps(
                {
                    "schema": PUBLIC_TUNNEL_HOST_SCHEMA,
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
