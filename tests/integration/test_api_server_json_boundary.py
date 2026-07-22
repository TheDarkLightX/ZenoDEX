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


def _pool_dict(*, pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> dict:
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


def _post_json(host: str, port: int, path: str, payload: dict) -> tuple[int, dict]:
    conn = HTTPConnection(host, port, timeout=2.0)
    try:
        conn.request(
            "POST",
            path,
            body=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": "Bearer test-token",
                "Content-Type": "application/json",
            },
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        return int(resp.status), body
    finally:
        conn.close()


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


def test_api_server_fast_quote_domain_error_falls_back_to_exact_router() -> None:
    class FailingFastRouter:
        def quote_exact_in_2hop_fast_v1(self, **_kwargs):
            raise ValueError("simulated fast-router domain rejection")

    httpd, thread, host, port = _start_test_server()
    httpd.fast_quote_router_v1 = FailingFastRouter()  # type: ignore[attr-defined]
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/quote",
            {
                "kind": "exact_in",
                "routing_mode": "fast_v1",
                "fast_topk_max": 32,
                "asset_in": "A",
                "asset_out": "B",
                "amount_in": 100,
                "pools": [_pool_dict(pid="p1", a0="A", a1="B", r0=1_000, r1=1_000)],
            },
        )

        assert status == 200
        assert body["ok"] is True
        assert body["routing_mode"] == "exact"
        assert body["quote"]["amount_out"] > 0
        assert type(body["receipt"]) is dict
        assert type(body["receipt"]["body"]) is dict
        assert type(body["receipt"]["body"]["legs"]) is list
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_quote_rejects_bool_exact_in_amount() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/quote",
            {
                "kind": "exact_in",
                "asset_in": "A",
                "asset_out": "B",
                "amount_in": True,
                "pools": [_pool_dict(pid="p1", a0="A", a1="B", r0=1_000, r1=1_000)],
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "bad_amount_in"
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_quote_rejects_bool_exact_out_amount() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/quote",
            {
                "kind": "exact_out",
                "asset_in": "A",
                "asset_out": "B",
                "amount_out": True,
                "pools": [_pool_dict(pid="p1", a0="A", a1="B", r0=1_000, r1=1_000)],
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "bad_amount_out"
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_quote_rejects_bool_fast_topk() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/quote",
            {
                "kind": "exact_in",
                "routing_mode": "fast_v1",
                "fast_topk_max": True,
                "asset_in": "A",
                "asset_out": "B",
                "amount_in": 100,
                "pools": [_pool_dict(pid="p1", a0="A", a1="B", r0=1_000, r1=1_000)],
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "bad_fast_topk_max"
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_impact_preview_rejects_bool_reserve() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/impact_preview",
            {
                "reserve_in": True,
                "reserve_out": 1_000,
                "amount_in": 10,
                "fee_bps": 0,
            },
        )

        assert status == 400
        assert body == {"ok": False, "error": "impact_preview_error", "details": "request failed"}
    finally:
        _stop_test_server(httpd, thread)


def test_routing_oracle_adapter_bridge_domain_error_fails_closed(monkeypatch) -> None:
    from src.integration import api_server
    from tools import zenodex_oracle_aggregate_adapter

    def _raise_domain_error(_bridge: object) -> object:
        raise ValueError("unencodable bridge")

    monkeypatch.setattr(
        zenodex_oracle_aggregate_adapter,
        "verify_aggregate_adapter_bridge",
        _raise_domain_error,
    )

    err = api_server._check_routing_oracle_adapter_bridge_for_action(
        body={"oracle_adapter_bridge": {"schema": "test.bridge"}},
        expected_action_id="sha256:" + "0" * 64,
    )

    assert err == "oracle_adapter_bridge verifier error: ValueError"


def test_api_server_env_int_rejects_malformed_values(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("ZENODEX_TEST_INT", "invalid")
    assert api_server._env_int("ZENODEX_TEST_INT", 7, lo=1, hi=9) == 7

    monkeypatch.setenv("ZENODEX_TEST_INT", "1.5")
    assert api_server._env_int("ZENODEX_TEST_INT", 7, lo=1, hi=9) == 7


def test_api_server_env_int_clamps_bounds(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("ZENODEX_TEST_INT", "-10")
    assert api_server._env_int("ZENODEX_TEST_INT", 7, lo=1, hi=9) == 1

    monkeypatch.setenv("ZENODEX_TEST_INT", "99")
    assert api_server._env_int("ZENODEX_TEST_INT", 7, lo=1, hi=9) == 9
