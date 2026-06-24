from __future__ import annotations

import json

import pytest


def _verify_body() -> bytes:
    return json.dumps(
        {
            "attestation_payload": {"provider": "nitro"},
            "extension_id": "route-premium-v1",
            "provider_id": "provider-1",
            "request_id": "req-1",
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
    ).encode("utf-8")


def test_confidential_attestation_config_rejects_malformed_boolean(monkeypatch) -> None:
    from src.integration import confidential_attestation_api

    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "maybe")

    with pytest.raises(ValueError, match="CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED"):
        confidential_attestation_api._verifier_config_from_env()


def test_confidential_attestation_config_rejects_bad_command_json(monkeypatch) -> None:
    from src.integration import confidential_attestation_api

    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "1")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", "not-json")

    with pytest.raises(ValueError, match="CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON"):
        confidential_attestation_api._verifier_config_from_env()


def test_confidential_attestation_config_rejects_malformed_limits(monkeypatch) -> None:
    from src.integration import confidential_attestation_api

    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_TIMEOUT_S", "inf")
    with pytest.raises(ValueError, match="CONFIDENTIAL_ATTESTATION_VERIFIER_TIMEOUT_S"):
        confidential_attestation_api._verifier_config_from_env()

    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_TIMEOUT_S", "10")
    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_MAX_STDOUT_BYTES", "0")
    with pytest.raises(ValueError, match="CONFIDENTIAL_ATTESTATION_VERIFIER_MAX_STDOUT_BYTES"):
        confidential_attestation_api._verifier_config_from_env()


def test_confidential_attestation_status_fails_closed_on_bad_config(monkeypatch) -> None:
    from src.integration import confidential_attestation_api

    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ALLOW_PATH_LOOKUP", "maybe")

    status_code, payload = confidential_attestation_api.handle_confidential_attestation_request(
        "GET",
        "/api/confidential/attestation/status",
        None,
    )

    assert status_code == 500
    assert payload["ok"] is False
    assert payload["error"] == "invalid_confidential_attestation_config"
    assert "CONFIDENTIAL_ATTESTATION_VERIFIER_ALLOW_PATH_LOOKUP" in str(payload["detail"])


def test_confidential_attestation_verify_fails_closed_on_bad_config(monkeypatch) -> None:
    from src.integration import confidential_attestation_api

    monkeypatch.setenv("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", "maybe")

    status_code, payload = confidential_attestation_api.handle_confidential_attestation_request(
        "POST",
        "/api/confidential/attestation/verify",
        _verify_body(),
    )

    assert status_code == 500
    assert payload["ok"] is False
    assert payload["error"] == "invalid_confidential_attestation_config"
    assert "CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED" in str(payload["detail"])


def test_confidential_attestation_verify_internal_fault_is_not_bad_request(monkeypatch) -> None:
    from src.integration import confidential_attestation_api

    def _faulting_receipt_builder(**_kwargs: object) -> object:
        raise RuntimeError("do not leak this attestation fault")

    monkeypatch.setattr(
        confidential_attestation_api,
        "verify_and_make_confidential_extension_receipt",
        _faulting_receipt_builder,
    )

    status_code, payload = confidential_attestation_api.handle_confidential_attestation_request(
        "POST",
        "/api/confidential/attestation/verify",
        _verify_body(),
    )

    assert status_code == 500
    assert payload["ok"] is False
    assert payload["error"] == "confidential_attestation_internal_error"
    assert payload["detail"] == "RuntimeError"
    assert "do not leak" not in str(payload)
