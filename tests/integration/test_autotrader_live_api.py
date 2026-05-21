from __future__ import annotations

import json

import pytest

from src.integration.autotrader_live_api import handle_autotrader_live_request


def test_autotrader_live_status_reports_receipt_backed_prepare_surface() -> None:
    status, payload = handle_autotrader_live_request(
        "GET",
        "/api/strategy/autotrader/status",
        None,
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["status"]["surface"] == "autotrader_live_prepare"
    assert payload["status"]["mode"] == "receipt_backed_prepare"
    assert "POST /api/strategy/autotrader/prepare" in payload["status"]["endpoints"]
    assert "production_chain_submission" in payload["status"]["not_claimed"]


def test_autotrader_live_prepare_requires_risk_acknowledgement() -> None:
    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps({"signer_privkey": 7}).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "autotrader_live_requires_risk_acknowledgement"
    assert payload["risk_disclosure"]["requires_explicit_acknowledgement"] is True
    assert payload["risk_disclosure"]["user_acknowledged"] is False


def test_autotrader_live_prepare_requires_local_signing_enablement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", raising=False)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "local_signing_disabled"
    assert payload["risk_disclosure"]["user_acknowledged"] is True


def test_autotrader_live_prepare_fixture_builds_signed_receipt_backed_ops(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["status"] == "prepared"
    assert payload["surface"] == "autotrader_live_prepare"
    assert "production_chain_submission" in payload["not_claimed"]

    report = payload["report"]
    assert report["mode"] == "live_prepare"
    assert report["risk_disclosure"]["user_acknowledged"] is True
    assert report["signing"]["chain_id"] == "tau-local"
    assert report["decision"]["tag"] == "submit"
    assert report["live_admission"]["ok"] is True
    assert report["system_compose"]["ok"] is True
    assert report["submit_bundle"]["ok"] is True
    assert report["decision"]["intents"]
    assert report["operations"]["2"]
    assert report["tau_tx_payload"] is not None
    assert report["tau_tx_payload"]["sequence_number"] == 9
    assert report["tau_tx_payload"]["expiration_time"] == 999
    assert report["stage_certificate"] is not None
    assert report["live_release_certificate"] is not None
