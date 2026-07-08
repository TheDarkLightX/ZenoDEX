from __future__ import annotations

import pytest

from src.integration.api_surface_profiles import (
    API_SURFACE_PROFILE_LOCAL_DEMO,
    API_SURFACE_PROFILE_PRODUCTION_STRICT,
    API_SURFACE_PROFILE_PUBLIC_TESTNET,
    api_surface_profile_ids,
    api_surface_profile_violations,
    validate_api_surface_profile,
)


def _clear_api_env(monkeypatch) -> None:
    for name in (
        "API_HOST",
        "API_PORT",
        "API_SURFACE_PROFILE",
        "PERPS_API_ENABLED",
        "ZUSD_API_ENABLED",
        "DEX_API_ENABLED",
        "CONFIDENTIAL_ATTESTATION_API_ENABLED",
        "CONFIDENTIAL_SEALED_BID_API_ENABLED",
        "CONFIDENTIAL_SEALED_BID_ENABLED",
        "DEMO_API_TOKEN",
        "ZENODEX_API_BEARER_TOKEN",
    ):
        monkeypatch.delenv(name, raising=False)


def test_api_surface_profile_ids_are_stable() -> None:
    assert api_surface_profile_ids() == (
        API_SURFACE_PROFILE_LOCAL_DEMO,
        API_SURFACE_PROFILE_PUBLIC_TESTNET,
        API_SURFACE_PROFILE_PRODUCTION_STRICT,
    )


def test_local_demo_allows_loopback_demo_without_token() -> None:
    assert (
        validate_api_surface_profile(
            profile_id=API_SURFACE_PROFILE_LOCAL_DEMO,
            demo_api_token="",
            perps_enabled=False,
            zusd_enabled=False,
            dex_enabled=True,
        )
        == (True, None)
    )


def test_public_testnet_requires_token_for_demo_routes() -> None:
    ok, err = validate_api_surface_profile(
        profile_id=API_SURFACE_PROFILE_PUBLIC_TESTNET,
        demo_api_token="",
        perps_enabled=False,
        zusd_enabled=True,
        dex_enabled=False,
    )
    assert ok is False
    assert err is not None
    assert "requires an API bearer token" in err

    assert (
        validate_api_surface_profile(
            profile_id=API_SURFACE_PROFILE_PUBLIC_TESTNET,
            demo_api_token="secret",
            perps_enabled=False,
            zusd_enabled=True,
            dex_enabled=False,
        )
        == (True, None)
    )


def test_production_strict_forbids_demo_value_routes() -> None:
    reasons = api_surface_profile_violations(
        profile_id=API_SURFACE_PROFILE_PRODUCTION_STRICT,
        demo_api_token="secret",
        perps_enabled=True,
        zusd_enabled=False,
        dex_enabled=False,
    )
    assert "production-strict forbids demo/value-moving API routes" in reasons


def test_production_strict_allows_health_only_surface() -> None:
    assert (
        validate_api_surface_profile(
            profile_id=API_SURFACE_PROFILE_PRODUCTION_STRICT,
            demo_api_token="",
            perps_enabled=False,
            zusd_enabled=False,
            dex_enabled=False,
        )
        == (True, None)
    )


def test_api_surface_profile_rejects_malformed_boundary_inputs() -> None:
    with pytest.raises(TypeError, match="profile id must be a string"):
        api_surface_profile_violations(
            profile_id=123,
            demo_api_token="",
            perps_enabled=False,
            zusd_enabled=False,
            dex_enabled=False,
        )
    with pytest.raises(ValueError, match="profile id must be non-empty"):
        api_surface_profile_violations(
            profile_id=" production-strict",
            demo_api_token="",
            perps_enabled=False,
            zusd_enabled=False,
            dex_enabled=False,
        )
    with pytest.raises(TypeError, match="perps_enabled must be a bool"):
        api_surface_profile_violations(
            profile_id=API_SURFACE_PROFILE_PRODUCTION_STRICT,
            demo_api_token="",
            perps_enabled="false",
            zusd_enabled=False,
            dex_enabled=False,
        )
    with pytest.raises(TypeError, match="dex_enabled must be a bool"):
        api_surface_profile_violations(
            profile_id=API_SURFACE_PROFILE_PRODUCTION_STRICT,
            demo_api_token="",
            perps_enabled=True,
            zusd_enabled=False,
            dex_enabled="false",
        )
    with pytest.raises(TypeError, match="confidential_enabled must be a bool"):
        api_surface_profile_violations(
            profile_id=API_SURFACE_PROFILE_PRODUCTION_STRICT,
            demo_api_token="",
            perps_enabled=False,
            zusd_enabled=False,
            dex_enabled=False,
            confidential_enabled="false",
        )
    with pytest.raises(TypeError, match="demo_api_token must be a string"):
        api_surface_profile_violations(
            profile_id=API_SURFACE_PROFILE_PUBLIC_TESTNET,
            demo_api_token=object(),
            perps_enabled=True,
            zusd_enabled=False,
            dex_enabled=False,
        )


def test_api_server_main_refuses_public_testnet_demo_without_token(monkeypatch) -> None:
    from src.integration import api_server

    _clear_api_env(monkeypatch)
    monkeypatch.setenv("API_SURFACE_PROFILE", API_SURFACE_PROFILE_PUBLIC_TESTNET)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("DEX_API_ENABLED", "true")

    assert api_server.main([]) == 2


def test_api_server_main_accepts_public_testnet_with_api_bearer_token(monkeypatch) -> None:
    from src.integration import api_server

    class FakeServer:
        def __init__(self, address, handler_cls):
            self.address = address
            self.handler_cls = handler_cls

        def serve_forever(self, poll_interval=0.25):  # noqa: ANN001
            return None

    _clear_api_env(monkeypatch)
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", FakeServer)
    monkeypatch.setenv("API_SURFACE_PROFILE", API_SURFACE_PROFILE_PUBLIC_TESTNET)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZENODEX_API_BEARER_TOKEN", "secret")

    assert api_server.main([]) == 0


def test_api_server_main_refuses_production_strict_demo_routes(monkeypatch) -> None:
    from src.integration import api_server

    _clear_api_env(monkeypatch)
    monkeypatch.setenv("API_SURFACE_PROFILE", API_SURFACE_PROFILE_PRODUCTION_STRICT)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("DEMO_API_TOKEN", "secret")

    assert api_server.main([]) == 2


def test_api_server_main_refuses_production_strict_confidential_routes(monkeypatch) -> None:
    from src.integration import api_server

    _clear_api_env(monkeypatch)
    monkeypatch.setenv("API_SURFACE_PROFILE", API_SURFACE_PROFILE_PRODUCTION_STRICT)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_API_ENABLED", "true")
    monkeypatch.setenv("ZENODEX_API_BEARER_TOKEN", "secret")

    assert api_server.main([]) == 2
