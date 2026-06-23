from __future__ import annotations

import json
import threading
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen

from src.integration.zeno_ledger_v0 import hash_v0
from tools.zeno_ledger_node import NODE_STATUS_SCHEMA, _post_json_url, check_peer_status_v0, make_node_http_server_v0


AUTH_TOKEN = "test-node-auth-token-v0"


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _node_status_hash(status: dict[str, object]) -> str:
    body = {key: value for key, value in status.items() if key != "node_status_hash"}
    return hash_v0("node_status_v0", body)


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_node_status(
    *,
    data_dir: Path,
    node_id: str,
    latest_height: int,
    last_header_hash: str,
) -> dict[str, object]:
    body: dict[str, object] = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_id,
        "node_role": "follower_watcher",
        "network_id": "zeno-ledger-transport-auth-testnet-0",
        "chain_id": "zeno-ledger-transport-auth-testnet-0",
        "bundle_root": str(data_dir / "bundle"),
        "data_dir": str(data_dir),
        "latest_height": latest_height,
        "last_header_hash": last_header_hash,
        "last_app_hash": _root(f"{node_id}-app"),
        "operator_attestation_path": "",
        "operator_attestation_hash": _root(f"{node_id}-attestation"),
        "combined_testnet_status_path": "",
        "combined_testnet_status_hash": _root(f"{node_id}-testnet-status"),
        "combined_watcher_count": 1,
        "sequencer_set_hash": _root("validator-set"),
        "mirror_index_hash": _root("mirror"),
        "feature_suite_hash": _root("features"),
        "covered_feature_count": 0,
        "covered_features": [],
        "required_features": [],
        "token_symbol": "tZENO",
        "token_posture": {},
        "test_token_catalog": [],
        "testnet_faucet_posture": {},
        "testnet_token_support": {},
    }
    status = {**body, "node_status_hash": _node_status_hash(body)}
    _write_json(data_dir / "node_status.json", status)
    return status


def _request_json(url: str, *, token: str | None = None, method: str = "GET") -> tuple[dict[str, object], int]:
    headers = {"Authorization": f"Bearer {token}"} if token is not None else {}
    request = Request(url, headers=headers, method=method)
    try:
        with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
            status = int(response.status)
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
        status = int(exc.code)
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj, status


def _start_auth_node(data_dir: Path) -> tuple[object, str]:
    server = make_node_http_server_v0(
        data_dir=data_dir,
        host="127.0.0.1",
        port=0,
        node_auth_token=AUTH_TOKEN,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address
    return server, f"http://{host}:{port}"


def test_node_http_server_requires_bearer_auth_for_get_and_post(tmp_path: Path) -> None:
    data_dir = tmp_path / "node"
    status = _write_node_status(
        data_dir=data_dir,
        node_id="node-auth",
        latest_height=5,
        last_header_hash=_root("common-5"),
    )
    server, url = _start_auth_node(data_dir)
    try:
        unauth_get, unauth_get_status = _request_json(f"{url}/health")
        auth_get, auth_get_status = _request_json(f"{url}/health", token=AUTH_TOKEN)
        unauth_post, unauth_post_status = _request_json(f"{url}/tx", method="POST")
    finally:
        server.shutdown()
        server.server_close()

    assert unauth_get_status == HTTPStatus.UNAUTHORIZED
    assert unauth_get["error"] == "node_transport_auth_required"
    assert auth_get_status == HTTPStatus.OK
    assert auth_get["node_status_hash"] == status["node_status_hash"]
    assert unauth_post_status == HTTPStatus.UNAUTHORIZED
    assert unauth_post["error"] == "node_transport_auth_required"


def test_peer_status_check_uses_bearer_auth_token(tmp_path: Path) -> None:
    common_hash = _root("common-5")
    local_dir = tmp_path / "local"
    peer_dir = tmp_path / "peer"
    _write_node_status(
        data_dir=local_dir,
        node_id="local-auth-check",
        latest_height=5,
        last_header_hash=common_hash,
    )
    _write_node_status(
        data_dir=peer_dir,
        node_id="peer-auth-check",
        latest_height=5,
        last_header_hash=common_hash,
    )
    server, url = _start_auth_node(peer_dir)
    try:
        rejected = check_peer_status_v0(data_dir=local_dir, peer_urls=[url])
        accepted = check_peer_status_v0(
            data_dir=local_dir,
            peer_urls=[url],
            peer_auth_token=AUTH_TOKEN,
        )
    finally:
        server.shutdown()
        server.server_close()

    assert rejected["ok"] is False
    assert rejected["peers"][0]["status"] == "rejected"
    assert "401" in rejected["peers"][0]["error"]
    assert accepted["ok"] is True
    assert accepted["peers"][0]["status"] == "accepted"
    assert accepted["peers"][0]["height_relation"] == "same_height"


def test_post_json_url_rejects_redirect_when_bearer_token_present() -> None:
    seen_auth: list[str] = []

    class _RedirectHandler(BaseHTTPRequestHandler):
        def do_POST(self) -> None:  # noqa: N802
            if self.path == "/start":
                self.send_response(HTTPStatus.FOUND)
                self.send_header("Location", f"http://127.0.0.1:{self.server.server_address[1]}/capture")
                self.send_header("Content-Type", "application/json")
                self.end_headers()
                self.wfile.write(b'{"error":"redirect"}')
                return
            if self.path == "/capture":
                seen_auth.append(self.headers.get("Authorization", ""))
                self.send_response(HTTPStatus.OK)
                self.end_headers()
                self.wfile.write(b'{"ok": true}')
                return
            self.send_error(HTTPStatus.NOT_FOUND)

        def log_message(self, format: str, *args: object) -> None:  # noqa: A003
            return

    server = ThreadingHTTPServer(("127.0.0.1", 0), _RedirectHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        body, status = _post_json_url(
            f"http://127.0.0.1:{server.server_address[1]}/start",
            {"hello": "world"},
            bearer_token=AUTH_TOKEN,
        )
    finally:
        server.shutdown()
        server.server_close()

    assert status == HTTPStatus.FOUND
    assert body["error"] == "redirect"
    assert seen_auth == []
