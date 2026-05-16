from __future__ import annotations

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
        "DEMO_API_TOKEN",
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
    assert "requires DEMO_API_TOKEN" in err

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


def test_api_server_main_refuses_public_testnet_demo_without_token(monkeypatch) -> None:
    from src.integration import api_server

    _clear_api_env(monkeypatch)
    monkeypatch.setenv("API_SURFACE_PROFILE", API_SURFACE_PROFILE_PUBLIC_TESTNET)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("DEX_API_ENABLED", "true")

    assert api_server.main([]) == 2


def test_api_server_main_refuses_production_strict_demo_routes(monkeypatch) -> None:
    from src.integration import api_server

    _clear_api_env(monkeypatch)
    monkeypatch.setenv("API_SURFACE_PROFILE", API_SURFACE_PROFILE_PRODUCTION_STRICT)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("DEMO_API_TOKEN", "secret")

    assert api_server.main([]) == 2
