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
    httpd.api_bearer_token = ""  # type: ignore[attr-defined]

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


def test_api_server_cors_preflight_returns_allowed_origin_headers() -> None:
    httpd, t, host, port = _start_test_server(cors_origins={"https://app.example"})
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "OPTIONS",
            "/api/dex/quote",
            headers={
                "Origin": "https://app.example",
                "Access-Control-Request-Method": "POST",
                "Access-Control-Request-Headers": "content-type, authorization",
            },
        )
        resp = conn.getresponse()
        resp.read()

        assert resp.status == 204
        assert resp.getheader("Access-Control-Allow-Origin") == "https://app.example"
        assert resp.getheader("Access-Control-Allow-Methods") == "GET,POST,OPTIONS"
        assert resp.getheader("Access-Control-Allow-Headers") == "Content-Type, Authorization"
        assert resp.getheader("Access-Control-Max-Age") == "600"
        assert resp.getheader("Vary") == "Origin"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_cors_preflight_does_not_reflect_unconfigured_origin() -> None:
    httpd, t, host, port = _start_test_server(cors_origins={"https://app.example"})
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "OPTIONS",
            "/api/dex/quote",
            headers={
                "Origin": "https://evil.example",
                "Access-Control-Request-Method": "POST",
            },
        )
        resp = conn.getresponse()
        resp.read()

        assert resp.status == 204
        assert resp.getheader("Access-Control-Allow-Origin") is None
        assert resp.getheader("Access-Control-Allow-Methods") is None
    finally:
        _stop_test_server(httpd, t)


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
