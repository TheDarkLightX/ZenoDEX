from __future__ import annotations

import json
import threading
from http.client import HTTPConnection


def _start_test_server():
    from src.integration import api_server
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = False  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]
    httpd.confidential_feature_status = load_confidential_feature_status_from_env().to_public_dict()  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def test_api_server_confidential_status_endpoint(monkeypatch) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", "nitro:pcr0:aa:pcr8:bb,azure-sevsnp:hostdata:cc")
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "confidential@zenodex.test")
    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request("GET", "/api/confidential/status")
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        status = body["status"]
        assert status["stage"] == "beta"
        assert status["beta_ready"] is True
        assert status["approved_measurements_count"] == 2
        assert status["operator_contact"] == "confidential@zenodex.test"
    finally:
        _stop_test_server(httpd, t)
