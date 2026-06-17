from __future__ import annotations

import json
import threading
from http.client import HTTPConnection


def _start_test_server():
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.perps_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = True  # type: ignore[attr-defined]
    httpd.demo_api_token = "test-token"  # type: ignore[attr-defined]

    thread = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    thread.start()
    host, port = httpd.server_address[:2]
    return httpd, thread, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def test_api_server_rejects_invalid_utf8_json_body() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote",
            body=b"\xff",
            headers={
                "Authorization": "Bearer test-token",
                "Content-Type": "application/json",
            },
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))

        assert resp.status == 400
        assert body == {"ok": False, "error": "bad_json"}
    finally:
        _stop_test_server(httpd, thread)
