from __future__ import annotations

import json
import threading
from http.client import HTTPConnection
from typing import Any


def _start_test_server():
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = True  # type: ignore[attr-defined]
    httpd.api_bearer_token = ""  # type: ignore[attr-defined]
    httpd.external_auth_enforced = True  # type: ignore[attr-defined]

    thread = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    thread.start()
    host, port = httpd.server_address[:2]
    return httpd, thread, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _post_json(host: str, port: int, path: str, payload: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    conn = HTTPConnection(host, port, timeout=2.0)
    try:
        conn.request(
            "POST",
            path,
            body=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        return int(resp.status), body
    finally:
        conn.close()


def _pool_dict(*, pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> dict[str, Any]:
    asset0 = min(a0, a1)
    asset1 = max(a0, a1)
    reserve0 = r0 if a0 < a1 else r1
    reserve1 = r1 if a0 < a1 else r0
    return {
        "pool_id": pid,
        "asset0": asset0,
        "asset1": asset1,
        "reserve0": int(reserve0),
        "reserve1": int(reserve1),
        "fee_bps": int(fee_bps),
        "lp_supply": 1,
        "status": "ACTIVE",
        "created_at": 0,
        "curve_tag": "CPMM",
        "curve_params": "",
    }


def test_api_server_verify_quote_receipt_binds_expected_quote_epoch() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        pools = [_pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1000)]
        status, quote_body = _post_json(
            host,
            port,
            "/api/dex/quote",
            {
                "kind": "exact_in",
                "asset_in": "A",
                "asset_out": "B",
                "amount_in": 120,
                "quote_epoch": 7,
                "pools": pools,
            },
        )
        assert status == 200
        assert quote_body["ok"] is True

        status, verify_body = _post_json(
            host,
            port,
            "/api/dex/verify_quote_receipt",
            {
                "receipt": quote_body["receipt"],
                "expected_quote_epoch": 7,
                "pools": pools,
            },
        )
        assert status == 200
        assert verify_body == {"ok": True, "error": "ok"}

        status, verify_body = _post_json(
            host,
            port,
            "/api/dex/verify_quote_receipt",
            {
                "receipt": quote_body["receipt"],
                "expected_quote_epoch": 8,
                "pools": pools,
            },
        )
        assert status == 200
        assert verify_body == {"ok": False, "error": "quote_epoch_mismatch"}
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_verify_quote_receipt_rejects_bad_expected_quote_epoch() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/verify_quote_receipt",
            {
                "receipt": {"body": {}, "receipt_hash": "bad"},
                "expected_quote_epoch": -1,
                "pools": [],
            },
        )
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "bad_expected_quote_epoch"
    finally:
        _stop_test_server(httpd, thread)
