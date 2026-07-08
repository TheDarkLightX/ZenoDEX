from __future__ import annotations

import json
import socket
import threading
from http.client import HTTPConnection


def _start_test_server(
    *,
    perps_enabled: bool = True,
    zusd_enabled: bool = False,
    cors_origins: set[str] | None = None,
):
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set(cors_origins or set())  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = bool(perps_enabled)  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = bool(zusd_enabled)  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def test_api_server_rejects_non_json_content_type_for_demo_post() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/perps/collateral",
            body=b"{}",
            headers={"Content-Type": "text/plain"},
        )
        resp = conn.getresponse()
        body = resp.read()
        assert resp.status == 415
        parsed = json.loads(body.decode("utf-8"))
        assert parsed["ok"] is False
        assert parsed["error"] == "unsupported_media_type"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_rejects_unsafe_cors_origin_values() -> None:
    from src.integration import api_server

    parsed = api_server._parse_cors_origins(
        "https://good.example,https://bad.example\r\nX-Injected: value"
    )

    assert parsed == {"https://good.example"}
    assert api_server._safe_cors_origin("https://bad.example\r\nX-Injected: value") is None


def test_api_server_access_log_omits_sensitive_request_target(capsys) -> None:
    secret = "secret-token-should-not-be-logged"
    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request("GET", f"/health?api_key={secret}&authorization=bearer")
        resp = conn.getresponse()
        body = resp.read()
        assert resp.status == 200
        assert json.loads(body.decode("utf-8"))["status"] == "healthy"

        captured = capsys.readouterr().out
        assert secret not in captured
        assert "api_key" not in captured
        assert "authorization" not in captured
        assert "/health" not in captured
    finally:
        _stop_test_server(httpd, t)


def test_api_server_rejects_invalid_content_length() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        with socket.create_connection((host, port), timeout=2.0) as s:
            req = (
                "POST /api/perps/collateral HTTP/1.1\r\n"
                f"Host: {host}:{port}\r\n"
                "Connection: close\r\n"
                "Content-Type: application/json\r\n"
                "Content-Length: abc\r\n"
                "\r\n"
            ).encode("ascii")
            s.sendall(req)
            chunks: list[bytes] = []
            while True:
                chunk = s.recv(4096)
                if not chunk:
                    break
                chunks.append(chunk)
            data = b"".join(chunks)
        assert b" 400 " in data
        assert b"invalid_content_length" in data
    finally:
        _stop_test_server(httpd, t)


def test_api_server_rejects_oversized_body_without_reading() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        with socket.create_connection((host, port), timeout=2.0) as s:
            req = (
                "POST /api/perps/collateral HTTP/1.1\r\n"
                f"Host: {host}:{port}\r\n"
                "Connection: close\r\n"
                "Content-Type: application/json\r\n"
                "Content-Length: 999999\r\n"
                "\r\n"
            ).encode("ascii")
            s.sendall(req)
            chunks: list[bytes] = []
            while True:
                chunk = s.recv(4096)
                if not chunk:
                    break
                chunks.append(chunk)
            data = b"".join(chunks)
        assert b" 413 " in data
        assert b"body_too_large" in data
    finally:
        _stop_test_server(httpd, t)


def _funded_perps_app_state_json() -> tuple[str, str, str, str]:
    """Build a wrapped app_state with a 2p market where account_a holds quote.

    Returns (app_state_json, account_a_pubkey, quote_asset, chain_id).
    """
    from src.core.dex import DexState
    from src.integration.dex_snapshot import snapshot_from_state
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
    from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
    from src.state import BalanceTable, LPTable

    chain_id = "tau-test-api-server-account-aware"
    account_a_privkey, account_b_privkey = 83, 84
    account_a = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:apisrv"

    op: dict = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": account_a,
        "account_b_pubkey": account_b,
        "deadline": 999_999_999,
        "nonce_a": 1,
        "nonce_b": 1,
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=account_a_privkey, chain_id=chain_id, signer_pubkey=account_a, nonce=1)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=account_b_privkey, chain_id=chain_id, signer_pubkey=account_b, nonce=1)
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=chain_id),
        state=DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
        operations={"19": [op]},
        tx_sender_pubkey=account_a,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    res.state.balances.set(account_a, quote_asset, 5_000)
    wrapped = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(res.state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }
    return json.dumps(wrapped, sort_keys=True), account_a, quote_asset, chain_id


def test_perps_wallet_status_account_query_survives_server_dispatch(monkeypatch) -> None:
    # Regression guard: do_GET strips the query string before dispatch, so the
    # wallet handlers must receive the query-bearing path. Without that, the
    # account-aware backend never sees ?account= and the community bug returns.
    import src.integration.perps_wallet_api as perps_wallet_api

    app_state_json, account_a, _quote_asset, chain_id = _funded_perps_app_state_json()

    class _FakeClient:
        def __init__(self, _cfg=None) -> None:
            self.app_hash = "sha256:" + "ab" * 32

        def rpc(self, cmd: str) -> str:
            assert cmd == "hello version=1"
            return "HELLO: ok"

        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            return json.dumps(
                {"app_hash": self.app_hash, "app_state": json.loads(app_state_json)},
                sort_keys=True,
            )

    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]
    httpd.perps_wallet_api_enabled = True  # type: ignore[attr-defined]
    thread = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    thread.start()
    host, port = httpd.server_address[:2]
    try:
        conn = HTTPConnection(host, int(port), timeout=5.0)
        conn.request("GET", f"/api/perps/wallet/status?account={account_a}")
        resp = conn.getresponse()
        payload = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200, payload
        status = payload["status"]
        assert status.get("account") == account_a, status
        view = status["account_view"]
        funded = [p for p in view["positions"] if int(p["quote_balance"]) == 5_000]
        assert funded, view

        # Malformed account still fails closed end-to-end.
        conn2 = HTTPConnection(host, int(port), timeout=5.0)
        conn2.request("GET", "/api/perps/wallet/status?account=not-a-pubkey")
        resp2 = conn2.getresponse()
        bad = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 400, bad
        assert bad["ok"] is False
    finally:
        _stop_test_server(httpd, thread)
