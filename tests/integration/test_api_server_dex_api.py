from __future__ import annotations

import json
import threading
from http.client import HTTPConnection


def _start_test_server(*, dex_enabled: bool = True):
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = bool(dex_enabled)  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


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


def test_api_server_dex_quote_and_verify_receipt_roundtrip() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p1", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        req = {
            "kind": "exact_out",
            "asset_in": "A",
            "asset_out": "B",
            "amount_out": 600,
            "apply_two_hop_gate": False,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["kind"] == "exact_out"
        assert "receipt" in body
        receipt = body["receipt"]
        assert isinstance(receipt, dict)
        assert isinstance(receipt.get("receipt_hash"), str) and receipt["receipt_hash"]

        # Verify via API.
        req2 = {"receipt": receipt, "pools": pools}
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_quote_receipt",
            body=json.dumps(req2).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] == "ok"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_dex_quote_exact_out_fast_v1_roundtrip() -> None:
    import pytest

    pytest.importorskip("numpy")
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p1", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        req = {
            "kind": "exact_out",
            "routing_mode": "fast_v1",
            "fast_topk_max": 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_out": 600,
            "apply_two_hop_gate": False,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["kind"] == "exact_out"
        assert body["routing_mode"] == "fast_v1"
        assert "receipt" in body
        receipt = body["receipt"]
        assert isinstance(receipt, dict)
        assert isinstance(receipt.get("receipt_hash"), str) and receipt["receipt_hash"]

        # Verify via API.
        req2 = {"receipt": receipt, "pools": pools}
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_quote_receipt",
            body=json.dumps(req2).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] == "ok"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_dex_impact_preview() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        req = {
            "reserve_in": 1_000_000,
            "reserve_out": 1_000_000,
            "amount_in": 10_000,
            "fee_bps": 30,
            "pending_volume_same_direction": 50_000,
            "confidence_bps": 9500,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/impact_preview",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        preview = body["preview"]
        assert isinstance(preview, dict)
        assert int(preview["amount_out_best_case"]) >= int(preview["amount_out_worst_case"])
        assert int(preview["amount_out_isolated"]) == int(preview["amount_out_best_case"])
        assert int(preview["recommended_min_out"]) >= int(preview["amount_out_worst_case"])
        assert int(preview["recommended_min_out"]) <= int(preview["amount_out_best_case"])
    finally:
        _stop_test_server(httpd, t)
