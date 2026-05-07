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
    httpd.demo_api_token = ""  # type: ignore[attr-defined]

    thread = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    thread.start()
    host, port = httpd.server_address[:2]
    return httpd, thread, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _post_json(host: str, port: int, path: str, body: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    conn = HTTPConnection(host, port, timeout=2.0)
    conn.request(
        "POST",
        path,
        body=json.dumps(body).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = conn.getresponse()
    return int(resp.status), json.loads(resp.read().decode("utf-8"))


def _pool(
    *,
    pid: str,
    a0: str,
    a1: str,
    r0: int,
    r1: int,
    fee_bps: int = 0,
) -> dict[str, Any]:
    return {
        "pool_id": pid,
        "asset0": a0,
        "asset1": a1,
        "reserve0": r0,
        "reserve1": r1,
        "fee_bps": fee_bps,
        "lp_supply": 1,
    }


def test_exact_out_many_pool_guarded_quote_requires_oracle_bridge_when_configured(monkeypatch) -> None:
    monkeypatch.setenv("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", "1")
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/quote_exact_out_many_pool_guarded",
            {
                "asset_in": "A",
                "asset_out": "B",
                "amount_out_total": 3,
                "max_legs": 3,
                "max_candidate_pools": 3,
                "max_candidates": 6,
                "max_iters": 512,
                "window": 8,
                "brute_force_max": 16,
                "max_enumerated_candidates": 8000,
                "pools": [
                    _pool(pid="pool_a", a0="A", a1="B", r0=40, r1=20),
                    _pool(pid="pool_b", a0="A", a1="B", r0=40, r1=63),
                    _pool(pid="pool_c", a0="A", a1="B", r0=40, r1=20),
                ],
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert body["detail"] == "guarded_quote requires oracle_adapter_bridge"
    finally:
        _stop_test_server(httpd, thread)
