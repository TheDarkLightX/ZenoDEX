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


def test_exact_out_many_pool_guarded_quote_rejects_bridge_for_reordered_pool_snapshot(
    monkeypatch,
) -> None:
    from src.integration import api_server

    pools = [
        _pool(pid="pool_a", a0="A", a1="B", r0=40, r1=20),
        _pool(pid="pool_b", a0="A", a1="B", r0=40, r1=63),
        _pool(pid="pool_c", a0="A", a1="B", r0=40, r1=20),
    ]
    params = {
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
    }
    wrong_action_id = api_server._routing_guarded_exact_out_quote_oracle_action_id(
        api_server.RoutingGuardedExactOutQuoteAction(
            path="/api/dex/quote_exact_out_many_pool_guarded",
            pools_raw=list(reversed(pools)),
            **params,
        )
    )

    def _accepted_bridge_for_reordered_snapshot(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.routing",
            "action_kind": "guarded_quote",
            "query_id": api_server.DEX_ROUTING_REFERENCE_QUERY_ID,
            "profile_id": api_server.DEX_ROUTING_GUARDED_QUOTE_PROFILE_ID,
            "action_id": wrong_action_id,
            "errors": [],
        }

    monkeypatch.setattr(
        api_server,
        "verify_aggregate_adapter_bridge",
        _accepted_bridge_for_reordered_snapshot,
    )
    monkeypatch.setenv("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", "1")
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/quote_exact_out_many_pool_guarded",
            {
                **params,
                "pools": pools,
                "oracle_adapter_bridge": {"schema": "test.accepted-reordered-pool-snapshot"},
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert body["detail"] == "oracle_adapter_bridge action_id mismatch"
    finally:
        _stop_test_server(httpd, thread)


def test_exact_out_many_pool_guard_rejects_when_projection_cover_unavailable(monkeypatch) -> None:
    from src.integration import exact_out_route_certificate as cert

    def _projection_cover_unavailable(*_args: object, **_kwargs: object) -> object:
        raise ValueError("projection cover unavailable")

    monkeypatch.setattr(
        cert,
        "_kernel_audit_exact_out_many_pool_selected_domain_projection_cover",
        _projection_cover_unavailable,
    )
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/guard_exact_out_many_pool_canonicality",
            {
                "asset_in": "A",
                "asset_out": "B",
                "amount_out_total": 3,
                "max_legs": 2,
                "max_candidate_pools": 2,
                "max_candidates": 6,
                "max_iters": 512,
                "window": 8,
                "brute_force_max": 16,
                "max_enumerated_candidates": 8000,
                "pools": [
                    _pool(pid="pool_a", a0="A", a1="B", r0=40, r1=20),
                    {
                        **_pool(pid="pool_b", a0="A", a1="B", r0=40, r1=20),
                        "curve_tag": "SUM_BOOST_V1",
                        "curve_params": {"mu_num": 200, "mu_den": 10000},
                    },
                ],
            },
        )

        assert status == 200
        assert body["ok"] is False
        assert body["contract_ok"] is False
        assert body["error"] == "many_pool_projection_cover_not_verified"
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is False
        assert body["projection_cover_holds"] is None
        assert body["contract"]["contract_ok"] is False
        assert body["contract"]["audit"]["projection_cover_audit"] is None
    finally:
        _stop_test_server(httpd, thread)
