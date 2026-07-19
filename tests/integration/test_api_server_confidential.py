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
PRIVATE_ROUTE_HINT = "private-route-alpha-do-not-echo"


def _start_test_server():
    from src.integration import api_server
    from src.integration.confidential_feature_status import (
        load_confidential_feature_status_from_env,
    )
    from src.state.confidential_requests import ConfidentialRequestTable

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
    httpd.api_bearer_token = ""  # type: ignore[attr-defined]
    httpd.external_auth_enforced = True  # type: ignore[attr-defined]
    httpd.confidential_feature_status = load_confidential_feature_status_from_env().to_public_dict()  # type: ignore[attr-defined]
    httpd.confidential_request_table = ConfidentialRequestTable()  # type: ignore[attr-defined]
    httpd.confidential_request_lock = threading.Lock()  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _verifier_cmd_json(
    *, measurement: str = MEASUREMENT, policy_digest: str = POLICY_DIGEST, epoch: int = 9
) -> str:
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
        "attestation_payload": {
            "provider": "nitro",
            "nonce": "ui-smoke",
            "private_route_hint": PRIVATE_ROUTE_HINT,
        },
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


def _runtime_request(
    *, request_id: str = "req-runtime", execution_id: str = "exec-runtime"
) -> dict[str, object]:
    return {
        **_attestation_request(),
        "request_id": request_id,
        "expected_policy_digest": POLICY_DIGEST,
        "execution_id": execution_id,
        "execution_kind": "private_route_quote",
        "result_code": "bounded_route_selected",
    }


def _post_json(
    host: str, port: int, path: str, body: dict[str, object]
) -> tuple[int, dict[str, object]]:
    conn = HTTPConnection(host, port, timeout=3.0)
    conn.request("POST", path, body=json.dumps(body), headers={"Content-Type": "application/json"})
    resp = conn.getresponse()
    payload = json.loads(resp.read().decode("utf-8"))
    return int(resp.status), payload


def test_api_server_confidential_attestation_api_is_forbidden_in_production(monkeypatch, capsys) -> None:
    from src.integration import api_server

    for name in (
        "PERPS_API_ENABLED",
        "PERPS_WALLET_API_ENABLED",
        "ZUSD_API_ENABLED",
        "ZUSD_TAU_WALLET_API_ENABLED",
        "ZUSD_MONETARY_WALLET_API_ENABLED",
        "AUTOTRADER_LIVE_API_ENABLED",
        "DEX_API_ENABLED",
        "DEMO_API_TOKEN",
        "ZENODEX_EXTERNAL_AUTH_ENFORCED",
        "ALLOW_DEMO_TOKEN_AUTH",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_API_ENABLED", "true")
    monkeypatch.setenv("ZENODEX_ENV", "production")

    assert api_server.main([]) == 2
    out = capsys.readouterr().out
    assert out == (
        "Refusing to start: development/test-only settings are enabled in production: "
        "CONFIDENTIAL_ATTESTATION_API_ENABLED\n"
    )


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
        assert str(status["approved_measurements_hash"]).startswith("0x")
        assert str(status["status_hash"]).startswith("0x")
        assert status["operator_contact"] == "confidential@zenodex.test"
        assert "response redaction" in status["claim_scope"]
        assert "no in-repo proof of TEE hardware confidentiality" in status["non_claims"]
        assert (
            "cryptographic attestation verification remains external-only"
            in status["readiness_gaps"]
        )
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_status_reports_verifier_posture(monkeypatch) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request("GET", "/api/confidential/attestation/status")
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        status = body["status"]
        assert status["external_verifier_enabled"] is True
        assert status["external_verifier_configured"] is True
        assert status["approved_measurements_count"] == 1
        assert str(status["approved_measurements_hash"]).startswith("0x")
        assert str(status["status_hash"]).startswith("0x")
        assert str(status["external_verifier_binding_hash"]).startswith("0x")
        assert status["providers"] == ["nitro"]
        assert "POST /api/confidential/attestation/admit" in status["endpoints"]
        assert "POST /api/confidential/attestation/execute" in status["endpoints"]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_accepts_allowlisted_external_verifier(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/confidential/attestation/verify", _attestation_request()
        )
        assert status == 200
        assert body["ok"] is True
        assert body["receipt_admissible"] is True
        assert body["measurement"] == MEASUREMENT
        assert body["policy_digest"] == POLICY_DIGEST
        assert body["execution_admitted"] is True
        assert str(body["receipt_hash"])
        assert body["claim_scope"] == "local_testnet_external_verifier_receipt"
        response_text = json.dumps(body, sort_keys=True)
        assert "attestation_payload" not in body
        assert "attestation_payload" not in response_text
        assert "private_route_hint" not in response_text
        assert PRIVATE_ROUTE_HINT not in response_text
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_admit_consumes_request_and_rejects_replay(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    request = {**_attestation_request(), "expected_policy_digest": POLICY_DIGEST}
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(host, port, "/api/confidential/attestation/admit", request)
        assert status == 200
        assert body["ok"] is True
        assert body["admission_ok"] is True
        assert body["request_consumed"] is True
        assert body["request_key"] == {
            "extension_id": "route-premium-v1",
            "provider_id": "provider-1",
            "request_id": "req-api",
        }
        assert body["claim_scope"] == "local_testnet_external_verifier_live_admission"
        response_text = json.dumps(body, sort_keys=True)
        assert "attestation_payload" not in body
        assert "attestation_payload" not in response_text
        assert "private_route_hint" not in response_text
        assert PRIVATE_ROUTE_HINT not in response_text

        status, replay = _post_json(host, port, "/api/confidential/attestation/admit", request)
        assert status == 400
        assert replay["ok"] is False
        assert replay["error"] == "request_replay"
        assert replay["request_consumed"] is False
        assert "receipt" not in replay
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_concurrent_consume_has_one_winner(
    monkeypatch,
) -> None:
    class _CoordinatedLock:
        def __init__(self) -> None:
            self._inner = threading.Lock()
            self._attempt_guard = threading.Lock()
            self._second_attempted = threading.Event()
            self._attempts = 0

        def __enter__(self):
            with self._attempt_guard:
                self._attempts += 1
                first = self._attempts == 1
                if self._attempts == 2:
                    self._second_attempted.set()
            self._inner.acquire()
            if first and not self._second_attempted.wait(timeout=2.0):
                self._inner.release()
                raise AssertionError("second request did not reach replay-table lock")
            return self

        def __exit__(self, exc_type, exc, traceback) -> None:
            del exc_type, exc, traceback
            self._inner.release()

    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    request = {**_attestation_request(), "expected_policy_digest": POLICY_DIGEST}
    httpd, t, host, port = _start_test_server()
    httpd.confidential_request_lock = _CoordinatedLock()  # type: ignore[attr-defined]
    start = threading.Barrier(3)
    results: list[tuple[int, dict[str, object]]] = []
    errors: list[BaseException] = []

    def submit() -> None:
        try:
            start.wait(timeout=2.0)
            results.append(
                _post_json(host, port, "/api/confidential/attestation/admit", request)
            )
        except BaseException as exc:  # pragma: no cover - retained for deterministic failure reporting
            errors.append(exc)

    workers = [threading.Thread(target=submit), threading.Thread(target=submit)]
    try:
        for worker in workers:
            worker.start()
        start.wait(timeout=2.0)
        for worker in workers:
            worker.join(timeout=5.0)

        assert all(not worker.is_alive() for worker in workers)
        assert errors == []
        assert sorted(status for status, _body in results) == [200, 400]
        rejected = next(body for status, body in results if status == 400)
        assert rejected["error"] == "request_replay"
        assert len(httpd.confidential_request_table.get_all()) == 1  # type: ignore[attr-defined]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_admit_policy_mismatch_does_not_consume(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    bad_request = {**_attestation_request(), "expected_policy_digest": "0x" + ("e" * 64)}
    good_request = {**_attestation_request(), "expected_policy_digest": POLICY_DIGEST}
    httpd, t, host, port = _start_test_server()
    try:
        initial_table = httpd.confidential_request_table  # type: ignore[attr-defined]
        status, rejected = _post_json(
            host, port, "/api/confidential/attestation/admit", bad_request
        )
        assert status == 400
        assert rejected["ok"] is False
        assert rejected["error"] == "policy_digest_mismatch"
        assert rejected["request_consumed"] is False
        assert httpd.confidential_request_table is initial_table  # type: ignore[attr-defined]
        assert initial_table.get_all() == {}

        status, accepted = _post_json(
            host, port, "/api/confidential/attestation/admit", good_request
        )
        assert status == 200
        assert accepted["ok"] is True
        assert accepted["request_consumed"] is True
        committed_table = httpd.confidential_request_table  # type: ignore[attr-defined]
        assert committed_table is not initial_table
        assert initial_table.get_all() == {}
        assert len(committed_table.get_all()) == 1
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_stateful_request_fails_closed_without_lock(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    request = {**_attestation_request(), "expected_policy_digest": POLICY_DIGEST}
    httpd, t, host, port = _start_test_server()
    try:
        initial_table = httpd.confidential_request_table  # type: ignore[attr-defined]
        httpd.confidential_request_lock = None  # type: ignore[attr-defined]

        status, rejected = _post_json(
            host, port, "/api/confidential/attestation/admit", request
        )

        assert status == 503
        assert rejected == {"ok": False, "error": "confidential_request_lock_unavailable"}
        assert httpd.confidential_request_table is initial_table  # type: ignore[attr-defined]
        assert initial_table.get_all() == {}
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_execute_returns_bounded_runtime_receipt(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request("GET", "/api/confidential/attestation/status")
        status_resp = conn.getresponse()
        status_body = json.loads(status_resp.read().decode("utf-8"))
        assert status_resp.status == 200
        status_payload = status_body["status"]
        status, body = _post_json(
            host, port, "/api/confidential/attestation/execute", _runtime_request()
        )
        assert status == 200
        assert body["ok"] is True
        assert body["admission_ok"] is True
        assert body["execution_ok"] is True
        assert body["request_consumed"] is True
        assert body["result_redacted"] is True
        assert body["claim_scope"] == "local_testnet_external_verifier_bounded_runtime_receipt"
        assert body["execution_kind"] == "private_route_quote"
        assert body["result_code"] == "bounded_route_selected"
        runtime_receipt = body["runtime_receipt"]
        assert runtime_receipt["body"]["measurement_provider"] == "nitro"
        assert runtime_receipt["body"]["result_redacted"] is True
        assert runtime_receipt["body"]["operator_status_hash"] == status_payload["status_hash"]
        assert (
            runtime_receipt["body"]["approved_measurements_hash"]
            == status_payload["approved_measurements_hash"]
        )
        assert (
            runtime_receipt["body"]["external_verifier_binding_hash"]
            == status_payload["external_verifier_binding_hash"]
        )
        assert runtime_receipt["body"]["public_summary"]["execution_admitted"] is True
        assert body["runtime_receipt_hash"] == runtime_receipt["receipt_hash"]
        assert body["operator_status_hash"] == status_payload["status_hash"]
        assert body["approved_measurements_hash"] == status_payload["approved_measurements_hash"]
        assert (
            body["external_verifier_binding_hash"]
            == status_payload["external_verifier_binding_hash"]
        )
        response_text = json.dumps(body, sort_keys=True)
        assert "attestation_payload" not in body
        assert "attestation_payload" not in response_text
        assert "private_route_hint" not in response_text
        assert PRIVATE_ROUTE_HINT not in response_text
        assert POLICY_DIGEST not in response_text
        assert NITRO_PCR0 not in response_text
        assert NITRO_PCR8 not in response_text
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_execute_rejects_replay_without_second_receipt(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    request = _runtime_request()
    httpd, t, host, port = _start_test_server()
    try:
        status, first = _post_json(host, port, "/api/confidential/attestation/execute", request)
        assert status == 200
        assert first["ok"] is True
        assert first["request_consumed"] is True

        status, replay = _post_json(host, port, "/api/confidential/attestation/execute", request)
        assert status == 400
        assert replay["ok"] is False
        assert replay["error"] == "request_replay"
        assert replay["request_consumed"] is False
        assert replay["execution_ok"] is False
        assert "runtime_receipt" not in replay
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_execute_bad_runtime_request_does_not_consume(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    bad_request = _runtime_request(execution_id="exec runtime")
    good_request = _runtime_request(execution_id="exec-runtime-good")
    httpd, t, host, port = _start_test_server()
    try:
        initial_table = httpd.confidential_request_table  # type: ignore[attr-defined]
        status, rejected = _post_json(
            host, port, "/api/confidential/attestation/execute", bad_request
        )
        assert status == 400
        assert rejected["ok"] is False
        assert rejected["error"] == "bad_runtime_request"
        assert rejected["admission_ok"] is True
        assert rejected["request_consumed"] is False
        assert httpd.confidential_request_table is initial_table  # type: ignore[attr-defined]
        assert initial_table.get_all() == {}

        status, accepted = _post_json(
            host, port, "/api/confidential/attestation/execute", good_request
        )
        assert status == 200
        assert accepted["ok"] is True
        assert accepted["request_consumed"] is True
        committed_table = httpd.confidential_request_table  # type: ignore[attr-defined]
        assert committed_table is not initial_table
        assert initial_table.get_all() == {}
        assert len(committed_table.get_all()) == 1
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_rejects_bad_receipt_inputs(monkeypatch) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    cases = [
        {"current_epoch": 12},
        {"policy_ok": 0},
        {"credit_after": 34},
    ]
    httpd, t, host, port = _start_test_server()
    try:
        for overrides in cases:
            request = {**_attestation_request(), **overrides}
            status, body = _post_json(host, port, "/api/confidential/attestation/verify", request)
            assert status == 400
            assert body["ok"] is False
            assert body["error"] == "bad_request"
            assert "receipt" not in body
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_rejects_unapproved_measurement(
    monkeypatch,
) -> None:
    other_measurement = f"nitro:pcr0:{'e' * 96}:pcr8:{'f' * 96}"
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "true")
    monkeypatch.setenv(
        "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON",
        _verifier_cmd_json(measurement=other_measurement),
    )

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/confidential/attestation/verify", _attestation_request()
        )
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "measurement_not_approved"
        assert body["receipt_admissible"] is False
        assert "receipt" not in body
    finally:
        _stop_test_server(httpd, t)


def test_api_server_confidential_attestation_verify_fails_closed_when_verifier_disabled(
    monkeypatch,
) -> None:
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "false")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", _verifier_cmd_json())

    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post_json(
            host, port, "/api/confidential/attestation/verify", _attestation_request()
        )
        assert status == 502
        assert body["ok"] is False
        assert body["error"] == "attestation_verifier_rejected"
        assert "receipt" not in body
    finally:
        _stop_test_server(httpd, t)
