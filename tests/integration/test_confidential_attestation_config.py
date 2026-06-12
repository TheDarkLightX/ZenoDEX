from __future__ import annotations

import pytest


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
