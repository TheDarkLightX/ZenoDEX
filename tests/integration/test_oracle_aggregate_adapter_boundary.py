from __future__ import annotations

from dataclasses import FrozenInstanceError
from pathlib import Path

import pytest

from src.integration.oracle_aggregate_adapter_boundary import (
    ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE,
    ORACLE_AGGREGATE_ADAPTER_VERIFIER_AVAILABLE,
    oracle_aggregate_adapter_capability,
    verify_aggregate_adapter_bridge,
)

ROOT = Path(__file__).resolve().parents[2]


def test_production_oracle_aggregate_adapter_boundary_is_explicitly_unavailable() -> None:
    capability = oracle_aggregate_adapter_capability()

    assert ORACLE_AGGREGATE_ADAPTER_VERIFIER_AVAILABLE is False
    assert capability.to_json_obj() == {
        "schema": "zenodex.oracle.aggregate_adapter_verifier_capability.v1",
        "available": False,
        "mode": "fail_closed",
        "reason": ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE,
    }
    with pytest.raises(FrozenInstanceError):
        capability.available = True  # type: ignore[misc]


def test_production_oracle_aggregate_adapter_boundary_rejects_every_bridge() -> None:
    result = verify_aggregate_adapter_bridge(
        {"schema": "zenodex.oracle.aggregate_adapter_bridge.v1"}
    )

    assert result.status == "rejected"
    assert result.errors == (ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE,)
    assert result.to_json_obj()["ok"] is False
    assert result.to_json_obj()["consumer_module"] is None
    with pytest.raises(FrozenInstanceError):
        result.status = "accepted"  # type: ignore[misc]


def test_production_oracle_boundary_has_no_tooling_import_or_promotion_override() -> None:
    source = (
        ROOT
        / "src"
        / "integration"
        / "oracle_aggregate_adapter_boundary.py"
    ).read_text(encoding="utf-8")

    assert "from tools" not in source
    assert "import tools" not in source
    assert "os.environ" not in source
    assert "sample_" not in source
    assert "sign_" not in source

    for relative in (
        "src/integration/api_server.py",
        "src/integration/perps_wallet_api.py",
        "src/integration/zeno_oracle_trigger_authorization.py",
    ):
        consumer_source = (ROOT / relative).read_text(encoding="utf-8")
        assert "tools.zenodex_oracle_aggregate_adapter" not in consumer_source


def test_production_api_refuses_perps_surface_without_promoted_oracle_verifier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.integration import api_server

    for name in (
        "PERPS_API_ENABLED",
        "ZUSD_API_ENABLED",
        "DEX_API_ENABLED",
        "AUTOTRADER_LIVE_API_ENABLED",
        "CONFIDENTIAL_ATTESTATION_API_ENABLED",
        "CONFIDENTIAL_SEALED_BID_API_ENABLED",
        "AUTOGOV_LIVE_APPLY_API_ENABLED",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("ZENODEX_ENV", "production")
    monkeypatch.setenv("PERPS_WALLET_API_ENABLED", "true")
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "true")

    refusal = api_server._api_startup_refusal_lines(
        api_server._load_api_server_config()
    )

    assert refusal == [
        "Refusing to start: production Oracle aggregate-adapter verification "
        "is unavailable for enabled surfaces: PERPS_WALLET_API_ENABLED "
        f"({ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE})."
    ]


def test_production_api_refuses_required_dex_oracle_surface_without_verifier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.integration import api_server

    monkeypatch.setenv("ZENODEX_ENV", "production")
    monkeypatch.setenv("PERPS_WALLET_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", "true")
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "true")

    refusal = api_server._api_startup_refusal_lines(
        api_server._load_api_server_config()
    )

    assert refusal is not None
    assert "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED" in refusal[0]
    assert ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE in refusal[0]
