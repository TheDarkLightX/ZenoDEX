from __future__ import annotations

import json
import threading
from http.client import HTTPConnection

import pytest

from src.integration.http_authority_ingress_v1 import (
    HttpAuthorityIngressAcceptedV1,
    HttpAuthorityIngressDeferredV1,
    HttpAuthorityIngressRejectCodeV1,
    HttpAuthorityIngressRejectedV1,
    inspect_http_authority_ingress_v1,
)


@pytest.mark.parametrize(
    "field",
    (
        "private_key",
        "privateKey",
        "account_a_privkey",
        "tx_signer_privkey",
        "buyer_privkeys",
        "secret_key_hex",
        "mnemonic",
        "seed_phrase",
    ),
)
def test_http_authority_ingress_rejects_raw_key_aliases_at_any_depth(field: str) -> None:
    raw = json.dumps({"outer": [{field: "must-never-cross-http"}]}).encode("utf-8")

    decision = inspect_http_authority_ingress_v1(raw)

    assert decision == HttpAuthorityIngressRejectedV1(
        code=HttpAuthorityIngressRejectCodeV1.RAW_AUTHORITY_MATERIAL_FORBIDDEN,
    )


def test_http_authority_ingress_accepts_public_key_and_posture_fields() -> None:
    raw = json.dumps(
        {
            "public_key": "0xpublic",
            "signer_pubkey": "0xsigner",
            "key_id": "wallet-1",
            "seed": 7,
            "no_raw_private_key_exposure": True,
        }
    ).encode("utf-8")

    decision = inspect_http_authority_ingress_v1(raw)

    assert decision == HttpAuthorityIngressAcceptedV1()


@pytest.mark.parametrize(
    ("depth", "expected_type"),
    (
        (32, HttpAuthorityIngressAcceptedV1),
        (33, HttpAuthorityIngressRejectedV1),
    ),
)
def test_http_authority_ingress_depth_bva(
    depth: int,
    expected_type: type[HttpAuthorityIngressAcceptedV1]
    | type[HttpAuthorityIngressRejectedV1],
) -> None:
    raw = (b'{"nested":' * depth) + b"null" + (b"}" * depth)

    decision = inspect_http_authority_ingress_v1(raw)

    assert type(decision) is expected_type
    if isinstance(decision, HttpAuthorityIngressRejectedV1):
        assert decision.code is HttpAuthorityIngressRejectCodeV1.SCAN_REFUSED


def test_http_authority_ingress_defers_malformed_json_to_route_error_abi() -> None:
    assert inspect_http_authority_ingress_v1(b"\xff") == HttpAuthorityIngressDeferredV1()


def test_http_authority_ingress_observes_duplicate_secret_field_before_overwrite() -> None:
    raw = b'{"private_key":"must-never-cross-http","private_key":null}'

    decision = inspect_http_authority_ingress_v1(raw)

    assert isinstance(decision, HttpAuthorityIngressRejectedV1)
    assert decision.code is HttpAuthorityIngressRejectCodeV1.RAW_AUTHORITY_MATERIAL_FORBIDDEN
    assert not hasattr(decision, "field_paths")


def test_http_authority_ingress_rejects_unscannable_shape() -> None:
    raw = (b'{"nested":' * 40) + b"null" + (b"}" * 40)

    decision = inspect_http_authority_ingress_v1(raw)

    assert decision == HttpAuthorityIngressRejectedV1(
        code=HttpAuthorityIngressRejectCodeV1.SCAN_REFUSED,
    )


@pytest.mark.parametrize(
    ("scalar_count", "expected_type"),
    (
        (131_071, HttpAuthorityIngressAcceptedV1),
        (131_072, HttpAuthorityIngressRejectedV1),
    ),
)
def test_http_authority_ingress_node_budget_bva(
    scalar_count: int,
    expected_type: type[HttpAuthorityIngressAcceptedV1]
    | type[HttpAuthorityIngressRejectedV1],
) -> None:
    raw = ("[" + ",".join("0" for _ in range(scalar_count)) + "]").encode("utf-8")

    decision = inspect_http_authority_ingress_v1(raw)

    assert type(decision) is expected_type
    if isinstance(decision, HttpAuthorityIngressRejectedV1):
        assert decision.code is HttpAuthorityIngressRejectCodeV1.SCAN_REFUSED


def _start_server(
    *,
    demo_api_token: str = "",
    external_auth_enforced: bool = True,
) -> tuple[object, threading.Thread, str, int]:
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)
    httpd.demo_api_token = demo_api_token
    httpd.external_auth_enforced = external_auth_enforced
    httpd.dex_api_enabled = True
    httpd.perps_wallet_api_enabled = True
    httpd.zusd_tau_wallet_api_enabled = True
    httpd.zusd_monetary_wallet_api_enabled = True
    httpd.autotrader_live_api_enabled = True
    httpd.confidential_sealed_bid_api_enabled = True
    thread = threading.Thread(
        target=httpd.serve_forever,
        kwargs={"poll_interval": 0.01},
        daemon=True,
    )
    thread.start()
    host, port = httpd.server_address[:2]
    return httpd, thread, str(host), int(port)


def _stop_server(httpd: object, thread: threading.Thread) -> None:
    httpd.shutdown()  # type: ignore[attr-defined]
    httpd.server_close()  # type: ignore[attr-defined]
    thread.join(timeout=2.0)


@pytest.mark.parametrize(
    "path",
    (
        "/api/dex/build_settlement_spot_price_attestation",
        "/api/perps/wallet/prepare",
        "/api/zusd/wallet/prepare",
        "/api/zusd/monetary/prepare",
        "/api/strategy/autotrader/prepare",
        "/api/confidential/sealed-bid/settle",
    ),
)
def test_mounted_post_choke_point_rejects_nested_raw_key_before_dispatch(path: str) -> None:
    httpd, thread, host, port = _start_server()
    secret = "must-never-cross-http"
    secret_field = "account_a_privkey_must-never-echo"
    try:
        connection = HTTPConnection(host, port, timeout=2.0)
        connection.request(
            "POST",
            path,
            body=json.dumps({"outer": {secret_field: secret}}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )

        response = connection.getresponse()
        raw_response = response.read()
        payload = json.loads(raw_response.decode("utf-8"))

        assert response.status == 400
        assert payload == {
            "ok": False,
            "error": "raw_authority_material_forbidden",
        }
        assert secret.encode("utf-8") not in raw_response
        assert secret_field.encode("utf-8") not in raw_response
    finally:
        _stop_server(httpd, thread)


def test_authentication_precedes_raw_authority_material_classification() -> None:
    httpd, thread, host, port = _start_server(
        demo_api_token="expected-token",
        external_auth_enforced=False,
    )
    try:
        connection = HTTPConnection(host, port, timeout=2.0)
        connection.request(
            "POST",
            "/api/dex/quote",
            body=json.dumps({"signer_privkey": "must-never-cross-http"}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )

        response = connection.getresponse()
        payload = json.loads(response.read().decode("utf-8"))

        assert response.status == 401
        assert payload == {"ok": False, "error": "unauthorized"}
    finally:
        _stop_server(httpd, thread)
