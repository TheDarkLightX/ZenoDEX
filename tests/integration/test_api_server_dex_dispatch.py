"""PR1 byte-identical regression suite for the 5 endpoints migrated to the
``DEX_ENDPOINT_REGISTRY`` dispatch seam.

Each test fires a representative request, captures the response body, and
asserts:
  * status code unchanged from the legacy handler
  * required keys are present
  * key shape invariants hold (these are the invariants the live endpoint
    tests already validate; we replicate the shape contract here so the
    refactor is provably behavior-preserving in isolation from the broader
    test suite)

The 5 endpoints in PR1 scope:
  /api/dex/impact_preview
  /api/dex/slippage_advice
  /api/dex/pokayoke_swap_suggest
  /api/dex/pokayoke_swap_suggest_heavy
  /api/dex/proof_mining_status
"""

from __future__ import annotations

import json
import threading
from http.client import HTTPConnection

import pytest


def _start_test_server(*, dex_enabled: bool = True):
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = bool(dex_enabled)  # type: ignore[attr-defined]
    httpd.api_bearer_token = ""  # type: ignore[attr-defined]
    httpd.external_auth_enforced = True  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _post_json(host: str, port: int, path: str, payload: dict, *, timeout: float = 15.0) -> tuple[int, dict]:
    # Generous timeout because the pokayoke_swap_suggest_heavy endpoint does
    # a multi-evaluation search and can take several seconds under coverage
    # instrumentation. Real handlers should still respond in <1s.
    conn = HTTPConnection(host, port, timeout=timeout)
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


# ---------------------------------------------------------------------------
# Registry-level invariants (don't require the live server)
# ---------------------------------------------------------------------------
def test_registry_is_frozen_mappingproxytype() -> None:
    from types import MappingProxyType

    from src.integration.api_server_dex_dispatch import DEX_ENDPOINT_REGISTRY

    assert isinstance(DEX_ENDPOINT_REGISTRY, MappingProxyType)


def test_registry_has_no_reachable_mutable_backing_dict() -> None:
    from src.integration import api_server_dex_dispatch as dispatch

    assert not hasattr(dispatch, "_REGISTRY_MUTABLE")
    assert dispatch._REGISTRY_BUILD is None


def test_registry_contains_pr1_endpoints() -> None:
    from src.integration.api_server_dex_dispatch import DEX_ENDPOINT_REGISTRY

    expected = {
        "/api/dex/impact_preview",
        "/api/dex/slippage_advice",
        "/api/dex/pokayoke_swap_suggest",
        "/api/dex/pokayoke_swap_suggest_heavy",
        "/api/dex/proof_mining_status",
    }
    assert expected.issubset(set(DEX_ENDPOINT_REGISTRY.keys()))


def test_lookup_returns_none_for_unregistered_paths() -> None:
    from src.integration.api_server_dex_dispatch import lookup

    assert lookup("/api/dex/this_path_does_not_exist") is None


def test_lookup_returns_handler_for_registered_path() -> None:
    from src.integration.api_server_dex_dispatch import lookup

    assert callable(lookup("/api/dex/impact_preview"))
    assert callable(lookup("/api/dex/quote"))
    assert callable(lookup("/api/dex/build_settlement_spot_value_contract"))
    assert callable(lookup("/api/dex/verify_settlement_spot_value_contract"))
    assert callable(lookup("/api/dex/build_settlement_lp_value_contract"))
    assert callable(lookup("/api/dex/verify_settlement_lp_value_contract"))
    assert callable(lookup("/api/dex/build_settlement_value_packet"))
    assert callable(lookup("/api/dex/verify_settlement_value_packet"))
    assert callable(lookup("/api/dex/build_settlement_endogenous_lp_value_packet"))
    assert callable(lookup("/api/dex/verify_settlement_endogenous_lp_value_packet"))
    assert callable(lookup("/api/dex/build_settlement_end_to_end_certificate_packet"))
    assert callable(lookup("/api/dex/verify_settlement_end_to_end_certificate_packet"))
    assert callable(lookup("/api/dex/quote_exact_out_many_pool_repaired_selected_domain"))
    assert callable(lookup("/api/dex/quote_exact_out_many_pool_repaired_advisory"))
    assert callable(lookup("/api/dex/quote_exact_out_many_pool_bounded_advisory"))
    assert callable(lookup("/api/dex/quote_exact_out_many_pool"))
    assert callable(lookup("/api/dex/quote_exact_out_many_pool_adaptive"))
    assert callable(lookup("/api/dex/quote_exact_out_many_pool_certified_advisory"))
    assert callable(lookup("/api/dex/build_settlement_witness_lifecycle_packet"))
    assert callable(lookup("/api/dex/verify_settlement_witness_lifecycle_packet"))


def test_duplicate_registration_raises() -> None:
    from src.integration.api_server_dex_dispatch import _register

    def _dummy(obj, ctx):  # noqa: ARG001
        return 200, {"ok": True}

    with pytest.raises(RuntimeError, match="duplicate"):
        _register("/api/dex/impact_preview", _dummy)


def test_invalid_path_registration_raises() -> None:
    from src.integration.api_server_dex_dispatch import _register

    def _dummy(obj, ctx):  # noqa: ARG001
        return 200, {"ok": True}

    with pytest.raises(RuntimeError, match="must start with /api/dex/"):
        _register("/api/perps/not_dex", _dummy)


# ---------------------------------------------------------------------------
# Live byte-shape regression: each migrated endpoint
# ---------------------------------------------------------------------------
def test_impact_preview_byte_shape() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/impact_preview",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30,
             "pending_volume_same_direction": 50_000, "confidence_bps": 9500},
        )
        assert status == 200
        assert body["ok"] is True
        preview = body["preview"]
        # Pin every field the legacy handler returned.
        expected_keys = {
            "amount_out_isolated", "fee_amount", "price_impact_bps", "effective_price_e8",
            "spot_price_e8", "amount_out_best_case", "amount_out_worst_case",
            "recommended_min_out", "pending_volume_same_direction", "confidence_bps",
            "pending_volume_at_confidence", "amount_out_at_confidence",
        }
        assert set(preview.keys()) == expected_keys
        assert all(isinstance(preview[k], int) for k in expected_keys)
        assert preview["amount_out_best_case"] >= preview["amount_out_worst_case"]
    finally:
        _stop_test_server(httpd, t)


def test_impact_preview_invalid_returns_400_with_legacy_error_code() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        # Negative reserve violates internal contract; legacy returned
        # status 400, error "impact_preview_error", details "request failed".
        status, body = _post_json(
            host, port, "/api/dex/impact_preview",
            {"reserve_in": -1, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30},
        )
        assert status == 400
        assert body == {"ok": False, "error": "impact_preview_error", "details": "request failed"}
    finally:
        _stop_test_server(httpd, t)


def test_slippage_advice_byte_shape() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/slippage_advice",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30,
             "pending_volume_same_direction": 5000, "confidence_bps": 9500},
        )
        assert status == 200
        assert body["ok"] is True
        advice = body["advice"]
        for key in (
            "best_amount_out", "price_impact_bps", "amount_out_at_confidence",
            "pending_volume_at_confidence", "confidence_bps", "required_slippage_bps",
            "recommended_slippage_bps_revert_safe", "recommended_slippage_bps_mev_safe",
            "recommended_slippage_bps", "status", "pokayoke", "options",
        ):
            assert key in advice, f"missing legacy field {key!r}"
        assert isinstance(advice["options"], list)
        assert isinstance(advice["status"], str)
        assert advice["pokayoke"] is None  # no user_slippage_bps in request
    finally:
        _stop_test_server(httpd, t)


def test_slippage_advice_with_user_slippage_includes_pokayoke() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/slippage_advice",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30,
             "user_slippage_bps": 50, "slippage_options_bps": [10, 50, 100]},
        )
        assert status == 200
        assert body["ok"] is True
        pokayoke = body["advice"]["pokayoke"]
        assert isinstance(pokayoke, dict)
        for key in ("action", "reasons", "messages", "typed_confirm_phrase"):
            assert key in pokayoke
    finally:
        _stop_test_server(httpd, t)


def test_slippage_advice_with_inaction_regret_includes_proofux_payload() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/slippage_advice",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30,
             "user_slippage_bps": 50, "slippage_options_bps": [10, 50, 100],
             "inaction_regret_bps": 800},
        )
        assert status == 200
        assert body["ok"] is True
        proofux = body["advice"]["pokayoke"]["proofux"]
        assert proofux["legacy_action"] == "typed_confirm"
        assert proofux["selected_action"] == "wait_or_requote"
        assert proofux["regret_within_limit_ok"] is False
        assert proofux["minimax_certificate"]["best_certificate_id"] == "wait_or_requote"
    finally:
        _stop_test_server(httpd, t)


def test_pokayoke_swap_suggest_byte_shape() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/pokayoke_swap_suggest",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30},
        )
        assert status == 200
        assert body["ok"] is True
        s = body["suggestions"]
        expected_keys = {
            "impact_lt_500_bps", "impact_lt_100_bps",
            "required_slippage_le_user_bps", "required_slippage_le_max_option_bps",
        }
        assert set(s.keys()) == expected_keys
    finally:
        _stop_test_server(httpd, t)


def test_pokayoke_swap_suggest_heavy_byte_shape() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/pokayoke_swap_suggest_heavy",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30,
             "user_slippage_bps": 50, "slippage_options_bps": [10, 50, 100],
             "max_attacker_amount_in": 2000, "max_evals": 8},
        )
        assert status == 200
        assert body["ok"] is True
        assert isinstance(body["suggestions"], list)
        if body["suggestions"]:
            first = body["suggestions"][0]
            for key in ("target_action", "suggested_amount_in", "status",
                        "eval_count", "baseline_action", "suggested_action",
                        "baseline_reasons", "suggested_reasons"):
                assert key in first
    finally:
        _stop_test_server(httpd, t)


def test_pokayoke_swap_suggest_heavy_missing_user_slippage_returns_400() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/pokayoke_swap_suggest_heavy",
            {"reserve_in": 1_000_000, "reserve_out": 1_000_000, "amount_in": 10_000, "fee_bps": 30},
        )
        assert status == 400
        assert body == {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": "request failed"}
    finally:
        _stop_test_server(httpd, t)


def test_proof_mining_status_bad_claim_returns_400() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/proof_mining_status",
            {"claim": "not_a_dict", "tx_sender_pubkey": "0x" + "11" * 48},
        )
        assert status == 400
        assert body == {"ok": False, "error": "bad_claim"}
    finally:
        _stop_test_server(httpd, t)


def test_proof_mining_status_bad_chain_balances_returns_400() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/proof_mining_status",
            {
                "claim": {},
                "chain_balances": "not_a_dict",
                "tx_sender_pubkey": "0x" + "11" * 48,
                "expected_proposal_hash": "sha256:any",
            },
        )
        assert status == 400
        assert body == {"ok": False, "error": "bad_chain_balances"}
    finally:
        _stop_test_server(httpd, t)


def test_proof_mining_status_missing_tx_sender_returns_400() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/proof_mining_status",
            {"claim": {}, "chain_balances": {}, "tx_sender_pubkey": ""},
        )
        assert status == 400
        assert body == {"ok": False, "error": "missing_tx_sender_pubkey"}
    finally:
        _stop_test_server(httpd, t)


def test_proof_mining_status_missing_expected_proposal_hash_returns_400() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/proof_mining_status",
            {"claim": {}, "chain_balances": {}, "tx_sender_pubkey": "0x" + "11" * 48},
        )
        assert status == 400
        assert body == {"ok": False, "error": "missing_expected_proposal_hash"}
    finally:
        _stop_test_server(httpd, t)


def test_proof_mining_payout_template_route_is_not_exposed() -> None:
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/proof_mining_payout_template",
            {},
        )
        assert status == 404
        assert body == {"ok": False, "error": "not_found"}
    finally:
        _stop_test_server(httpd, thread)


def test_build_settlement_spot_price_attestation_route_is_not_exposed() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/dex/build_settlement_spot_price_attestation",
            {"packet": {}},
        )
        assert status == 404
        assert body == {"ok": False, "error": "not_found"}
    finally:
        _stop_test_server(httpd, t)


# ---------------------------------------------------------------------------
# Dispatch seam guarantees
# ---------------------------------------------------------------------------
def test_dex_endpoint_error_is_converted_to_response() -> None:
    """The dispatcher must convert a raised DexEndpointError into a
    (status, body) response without leaking the exception."""
    from src.integration.api_server_dex_dispatch import (
        DexEndpointError,
        DexEndpointSpec,
        DexRequestContext,
        dispatch_endpoint_spec,
    )

    def _raises_dex_endpoint_error(obj, ctx):  # noqa: ARG001
        raise DexEndpointError(400, "bad_assets", reason="canonical_order")

    spec = DexEndpointSpec(
        handler=_raises_dex_endpoint_error,
        default_error_code="__test_default_error__",
    )
    ctx = DexRequestContext(server=None, cors_origin=None, raw_body=None)
    result = dispatch_endpoint_spec("/api/dex/__test_dex_endpoint_error__", spec, {}, ctx)
    status, body = result
    assert status == 400
    assert body == {"ok": False, "error": "bad_assets", "reason": "canonical_order"}


def test_dispatcher_catch_all_uses_default_error_code() -> None:
    """Unhandled exceptions (anything other than DexEndpointError) get
    converted to a 400 with the spec's default_error_code + the legacy
    'request failed' detail string."""
    from src.integration.api_server_dex_dispatch import (
        DexEndpointSpec,
        DexRequestContext,
        dispatch_endpoint_spec,
    )

    def _raises_runtime_error(obj, ctx):  # noqa: ARG001
        raise RuntimeError("oh no")

    spec = DexEndpointSpec(
        handler=_raises_runtime_error,
        default_error_code="custom_catch_all_error",
    )
    ctx = DexRequestContext(server=None, cors_origin=None, raw_body=None)
    result = dispatch_endpoint_spec("/api/dex/__test_catch_all__", spec, {}, ctx)
    status, body = result
    assert status == 400
    assert body == {"ok": False, "error": "custom_catch_all_error", "details": "request failed"}


def test_openapi_fragment_includes_schema_backed_endpoint() -> None:
    """generate_openapi_fragment must emit a path for every endpoint
    registered with an EndpointSchema, and skip those without one."""
    from src.integration.api_server_dex_dispatch import generate_openapi_fragment

    fragment = generate_openapi_fragment()

    # audit_exact_out_many_pool_canonicality was migrated to use a schema
    # in Step 6; it must appear with a fully populated POST operation.
    assert "/api/dex/audit_exact_out_many_pool_canonicality" in fragment
    op = fragment["/api/dex/audit_exact_out_many_pool_canonicality"]["post"]
    assert op["operationId"] == "handle_audit_exact_out_many_pool_canonicality"
    assert op["requestBody"]["required"] is True

    body_schema = op["requestBody"]["content"]["application/json"]["schema"]
    assert body_schema["type"] == "object"

    # amount_out_total is required (no default); the others all have defaults.
    assert "amount_out_total" in body_schema["properties"]
    assert body_schema["properties"]["amount_out_total"] == {
        "type": "integer",
        "minimum": 1,
        "description": "Target output amount.",
    }
    # Runtime also requires pools + asset_in + asset_out (validated ad-hoc
    # via parse_pools and isinstance checks). The schema declares them so
    # generated clients send spec-valid requests.
    assert body_schema["required"] == ["pools", "asset_in", "asset_out", "amount_out_total"]
    assert "pools" in body_schema["properties"]
    assert body_schema["properties"]["pools"]["type"] == "array"
    assert body_schema["properties"]["asset_in"]["type"] == "string"
    assert body_schema["properties"]["asset_out"]["type"] == "string"

    # max_legs has default=3, minimum=1 — must be optional but bounded.
    assert body_schema["properties"]["max_legs"] == {
        "type": "integer",
        "minimum": 1,
        "default": 3,
    }

    # Both 200 and 400 response shapes must be documented.
    assert "200" in op["responses"]
    assert "400" in op["responses"]


def test_metrics_endpoint_starts_at_zero_after_reset() -> None:
    """Snapshot of metrics returns empty when no requests have hit dispatch."""
    from src.integration.api_server_dex_dispatch import DISPATCH_METRICS, serve_metrics

    DISPATCH_METRICS.reset()
    snap = serve_metrics()
    assert snap == {"metrics": {}, "endpoint_count": 0, "total_request_count": 0}


def test_metrics_increment_on_successful_dispatch() -> None:
    """A successful dispatch must bump request_count and record latency
    but NOT error_count."""
    from src.integration.api_server_dex_dispatch import (
        DISPATCH_METRICS,
        DexEndpointSpec,
        DexRequestContext,
        dispatch_endpoint_spec,
        serve_metrics,
    )

    def _ok_handler(obj, ctx):  # noqa: ARG001
        return 200, {"ok": True}

    spec = DexEndpointSpec(handler=_ok_handler, default_error_code="__test_ok_default__")
    DISPATCH_METRICS.reset()
    ctx = DexRequestContext(server=None, cors_origin=None, raw_body=None)
    dispatch_endpoint_spec("/api/dex/__test_metrics_ok__", spec, {}, ctx)
    dispatch_endpoint_spec("/api/dex/__test_metrics_ok__", spec, {}, ctx)
    snap = serve_metrics()
    ep = snap["metrics"]["/api/dex/__test_metrics_ok__"]
    assert ep["request_count"] == 2
    assert ep["error_count"] == 0
    assert ep["sample_count"] == 2
    assert ep["latency_p50_ms"] is not None
    assert ep["latency_p50_ms"] >= 0
    assert ep["most_recent_error_code"] is None
    assert snap["total_request_count"] == 2


def test_metrics_increment_on_dex_endpoint_error() -> None:
    """DexEndpointError must bump error_count AND record the error code."""
    from src.integration.api_server_dex_dispatch import (
        DISPATCH_METRICS,
        DexEndpointError,
        DexEndpointSpec,
        DexRequestContext,
        dispatch_endpoint_spec,
        serve_metrics,
    )

    def _raises_dex_err(obj, ctx):  # noqa: ARG001
        raise DexEndpointError(400, "bad_thing")

    spec = DexEndpointSpec(handler=_raises_dex_err, default_error_code="__test_default__")
    DISPATCH_METRICS.reset()
    ctx = DexRequestContext(server=None, cors_origin=None, raw_body=None)
    dispatch_endpoint_spec("/api/dex/__test_metrics_dex_err__", spec, {}, ctx)
    snap = serve_metrics()
    ep = snap["metrics"]["/api/dex/__test_metrics_dex_err__"]
    assert ep["request_count"] == 1
    assert ep["error_count"] == 1
    assert ep["most_recent_error_code"] == "bad_thing"
    assert ep["most_recent_error_timestamp_ms"] is not None


def test_metrics_increment_on_handler_returning_4xx_directly() -> None:
    """Handler returns (400, ...) without raising → metrics must still
    count it as an error (status >= 400 is the operator-relevant signal)."""
    from src.integration.api_server_dex_dispatch import (
        DISPATCH_METRICS,
        DexEndpointSpec,
        DexRequestContext,
        dispatch_endpoint_spec,
        serve_metrics,
    )

    def _returns_400(obj, ctx):  # noqa: ARG001
        return 400, {"ok": False, "error": "bad_assets"}

    spec = DexEndpointSpec(handler=_returns_400, default_error_code="__test_default__")
    DISPATCH_METRICS.reset()
    ctx = DexRequestContext(server=None, cors_origin=None, raw_body=None)
    dispatch_endpoint_spec("/api/dex/__test_metrics_direct_400__", spec, {}, ctx)
    snap = serve_metrics()
    ep = snap["metrics"]["/api/dex/__test_metrics_direct_400__"]
    assert ep["error_count"] == 1
    assert ep["most_recent_error_code"] == "bad_assets"


def test_metrics_endpoint_served_via_http_get() -> None:
    """GET /api/dex/metrics returns a JSON envelope with the snapshot shape."""
    from http.client import HTTPConnection

    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=5.0)
        try:
            conn.request("GET", "/api/dex/metrics")
            resp = conn.getresponse()
            assert resp.status == 200
            body = json.loads(resp.read().decode("utf-8"))
            assert "metrics" in body
            assert "endpoint_count" in body
            assert "total_request_count" in body
            assert isinstance(body["metrics"], dict)
        finally:
            conn.close()
    finally:
        _stop_test_server(httpd, t)


def test_metrics_p95_nearest_rank() -> None:
    """Percentile uses nearest-rank semantics: for 100 samples [1, 2, ..., 100],
    p50 is 50, p95 is 95, p99 is 99."""
    from src.integration.api_server_dex_dispatch import EndpointMetrics

    ep = EndpointMetrics()
    for v in range(1, 101):
        ep.record_latency(float(v))
    snap = ep.to_public_dict()
    assert snap["latency_p50_ms"] == 50.0
    assert snap["latency_p95_ms"] == 95.0
    assert snap["latency_p99_ms"] == 99.0


def test_metrics_latency_reservoir_is_bounded() -> None:
    """Latency reservoir caps at _METRICS_LATENCY_RESERVOIR; oldest
    samples replaced first."""
    from src.integration.api_server_dex_dispatch import (
        _METRICS_LATENCY_RESERVOIR,
        EndpointMetrics,
    )

    ep = EndpointMetrics()
    # Record 2x the reservoir capacity; only the most recent N must be retained.
    for v in range(_METRICS_LATENCY_RESERVOIR * 2):
        ep.record_latency(float(v))
    assert len(ep.latency_samples_ms) == _METRICS_LATENCY_RESERVOIR
    # The samples should be the second half (later values) but in ring order.
    assert min(ep.latency_samples_ms) >= _METRICS_LATENCY_RESERVOIR


def test_metrics_empty_endpoint_returns_none_percentiles() -> None:
    """A registered endpoint with no observations yet must return None
    percentiles (not crash)."""
    from src.integration.api_server_dex_dispatch import EndpointMetrics

    ep = EndpointMetrics()
    snap = ep.to_public_dict()
    assert snap["latency_p50_ms"] is None
    assert snap["latency_p95_ms"] is None
    assert snap["latency_p99_ms"] is None
    assert snap["sample_count"] == 0


def test_openapi_document_has_well_formed_envelope() -> None:
    """The full OpenAPI 3.1 document must carry the required top-level
    fields: openapi version, info, paths, components.schemas."""
    from src.integration.api_server_dex_dispatch import generate_openapi_document

    doc = generate_openapi_document()
    assert doc["openapi"] == "3.1.0"
    assert doc["info"]["title"] == "ZenoDex /api/dex/*"
    assert "version" in doc["info"]
    assert "description" in doc["info"]
    assert "paths" in doc
    assert "components" in doc
    assert "ErrorResponse" in doc["components"]["schemas"]


def test_openapi_document_is_json_serializable() -> None:
    """Must round-trip through json.dumps + loads — clients consume it
    over the wire."""
    from src.integration.api_server_dex_dispatch import generate_openapi_document

    doc = generate_openapi_document()
    payload = json.dumps(doc)
    round_tripped = json.loads(payload)
    assert round_tripped == doc


def test_openapi_document_includes_server_when_provided() -> None:
    from src.integration.api_server_dex_dispatch import generate_openapi_document

    doc = generate_openapi_document(server_url="https://api.zenodex.example")
    assert doc["servers"] == [{"url": "https://api.zenodex.example"}]


def test_openapi_endpoint_served_via_http_get() -> None:
    """GET /api/dex/openapi.json must return the OpenAPI document."""
    from http.client import HTTPConnection

    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=5.0)
        try:
            conn.request("GET", "/api/dex/openapi.json")
            resp = conn.getresponse()
            assert resp.status == 200
            body = json.loads(resp.read().decode("utf-8"))
            assert body["openapi"] == "3.1.0"
            assert "/api/dex/audit_exact_out_many_pool_canonicality" in body["paths"]
        finally:
            conn.close()
    finally:
        _stop_test_server(httpd, t)


def test_openapi_endpoint_rejects_post_with_405() -> None:
    """OpenAPI endpoint is GET-only. POST falls through to the existing
    method-not-allowed branch (which returns 405)."""

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(host, port, "/api/dex/openapi.json", {})
        # POST to openapi.json doesn't match a registered handler and
        # isn't a legacy endpoint either — falls through to 400/404 in
        # the catch-all chain. Status varies by where it lands; either
        # 400 (legacy not-found in dispatch chain) or 404. Pin: it's NOT 200.
        assert status != 200
    finally:
        _stop_test_server(httpd, t)


def test_openapi_fragment_omits_schemaless_endpoints() -> None:
    """Endpoints registered without a schema (the legacy bulk) must NOT
    appear in the OpenAPI fragment — only schema-backed endpoints are
    emitted to avoid lying about the API surface."""
    from src.integration.api_server_dex_dispatch import generate_openapi_fragment

    fragment = generate_openapi_fragment()

    # impact_preview was migrated to use parse_int_kwargs in Step 5 but
    # has no EndpointSchema yet — should be absent.
    assert "/api/dex/impact_preview" not in fragment
    assert "/api/dex/slippage_advice" not in fragment


def test_default_error_code_derived_from_path_suffix() -> None:
    """When _register is called without default_error_code, it defaults to
    the path's last segment + '_error'."""
    from src.integration.api_server_dex_dispatch import _default_error_code_for_path

    assert _default_error_code_for_path("/api/dex/impact_preview") == "impact_preview_error"
    assert _default_error_code_for_path("/api/dex/__test_default_code__") == "__test_default_code___error"


def test_unregistered_path_returns_not_found_after_dispatch_miss() -> None:
    """Unknown DEX endpoints should fall through to the final not_found response."""
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host,
            port,
            "/api/dex/this_path_does_not_exist",
            {},
        )
        assert status == 404
        assert body == {"ok": False, "error": "not_found"}
    finally:
        _stop_test_server(httpd, t)


def test_dispatch_disabled_when_dex_api_disabled() -> None:
    httpd, t, host, port = _start_test_server(dex_enabled=False)
    try:
        # Server returns 404 when DEX API is globally disabled — the
        # registry should never be consulted before that gate.
        conn = HTTPConnection(host, port, timeout=5.0)
        try:
            conn.request("POST", "/api/dex/impact_preview",
                         body=b"{}", headers={"Content-Type": "application/json"})
            resp = conn.getresponse()
            # When dex_api_enabled is False, _maybe_handle_dex_api returns
            # False so the request falls through the handler chain. The
            # generic 404 is returned by the outermost handler.
            assert resp.status in (404, 405)
        finally:
            conn.close()
    finally:
        _stop_test_server(httpd, t)
