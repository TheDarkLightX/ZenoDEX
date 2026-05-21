from __future__ import annotations

import json
import sys
import threading
from http.client import HTTPConnection


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
AZURE_HOSTDATA = "c" * 64
POLICY_DIGEST = "0x" + ("d" * 64)
MEASUREMENT = f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"


def _start_test_server():
    from src.integration import api_server
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.perps_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_tau_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_monetary_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.autotrader_live_api_enabled = False  # type: ignore[attr-defined]
    httpd.confidential_attestation_api_enabled = True  # type: ignore[attr-defined]
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


def _verifier_cmd_json(*, measurement: str = MEASUREMENT, policy_digest: str = POLICY_DIGEST, epoch: int = 9) -> str:
    code = (
        "import json,sys;"
        "json.load(sys.stdin);"
        "print(json.dumps({'ok': True, 'result': "
        f"{{'measurement': {measurement!r}, 'policy_digest': {policy_digest!r}, 'attestation_epoch': {epoch}}}"
        "}))"
    )
    return json.dumps([sys.executable, "-c", code])


def _attestation_request() -> dict[str, object]:
    return {
        "attestation_payload": {"provider": "nitro", "nonce": "ui-smoke"},
        "extension_id": "route-premium-v1",
        "provider_id": "provider-1",
        "request_id": "req-api",
        "policy_version": "tee-policy-v1",
        "do_execute": 1,
        "policy_ok": 1,
        "nonce_unused": 1,
        "output_bound_ok": 1,
        "current_epoch": 10,
        "max_attestation_age": 2,
        "fee_charged": 7,
        "receipt_fee": 7,
        "credit_before": 40,
        "credit_after": 33,
        "provider_balance_before": 9,
        "provider_balance_after": 16,
    }


def _post_json(host: str, port: int, path: str, body: dict[str, object]) -> tuple[int, dict[str, object]]:
    conn = HTTPConnection(host, port, timeout=3.0)
    conn.request("POST", path, body=json.dumps(body), headers={"Content-Type": "application/json"})
    resp = conn.getresponse()
    payload = json.loads(resp.read().decode("utf-8"))
    return int(resp.status), payload


def test_api_server_confidential_status_endpoint(monkeypatch) -> None:
    monkeypatch.setenv(
        "CONFIDENTIAL_APPROVED_MEASUREMENTS",
        f"{MEASUREMENT},azure-sevsnp:hostdata:{AZURE_HOSTDATA}",
    )
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
        assert status["beta_ready"] is False
        assert status["approved_measurements_count"] == 2
        assert status["operator_contact"] == "confidential@zenodex.test"
        assert "cryptographic attestation verification remains external-only" in status["readiness_gaps"]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_accepts_allowlisted_external_verifier(monkeypatch) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(host, port, "/api/confidential/attestation/verify", _attestation_request())
        assert status == 200
        assert body["ok"] is True
        assert body["receipt_admissible"] is True
        assert body["measurement"] == MEASUREMENT
        assert body["policy_digest"] == POLICY_DIGEST
        assert body["execution_admitted"] is True
        assert str(body["receipt_hash"])
        assert body["claim_scope"] == "local_testnet_external_verifier_receipt"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_rejects_unapproved_measurement(monkeypatch) -> None:
    other_measurement = f"nitro:pcr0:{'e' * 96}:pcr8:{'f' * 96}"
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv(
        "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON",
        _verifier_cmd_json(measurement=other_measurement),
    )

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(host, port, "/api/confidential/attestation/verify", _attestation_request())
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "measurement_not_approved"
        assert body["receipt_admissible"] is False
        assert "receipt" not in body
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_fails_closed_when_verifier_disabled(monkeypatch) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "false")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(host, port, "/api/confidential/attestation/verify", _attestation_request())
        assert status == 502
        assert body["ok"] is False
        assert body["error"] == "attestation_verifier_rejected"
        assert "receipt" not in body
    finally:
        _stop_test_server(httpd, t)
