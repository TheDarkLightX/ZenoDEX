"""
Regression for S5-CRIT-001 (D-CONFIG-002): the API-surface profiles defined in
api_surface_profiles.py must be ENFORCED at startup. Previously `main()` never
called `api_surface_profile_violations`, so a `production-strict` deployment
could still serve perps/zUSD/DEX value-moving routes.

`main()` now refuses to start (returns 2) before binding the socket when the
selected ZENODEX_API_SURFACE_PROFILE/API_SURFACE_PROFILE conflicts with the active
runtime flags, or when the profile id is unknown. These tests exercise the fail
paths via main() (which returns before binding) plus the pure policy function.
"""
from __future__ import annotations

import pytest

from src.integration import api_server
from src.integration.api_surface_profiles import api_surface_profile_violations

# Env vars that influence the startup posture; cleared per-test for isolation.
_RELEVANT_ENV = (
    "ZENODEX_API_SURFACE_PROFILE",
    "API_SURFACE_PROFILE",
    "PERPS_API_ENABLED",
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_API_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
    "AUTOTRADER_LIVE_API_ENABLED",
    "CONFIDENTIAL_ATTESTATION_API_ENABLED",
    "CONFIDENTIAL_SEALED_BID_API_ENABLED",
    "CONFIDENTIAL_SEALED_BID_ENABLED",
    "DEX_API_ENABLED",
    "ZENODEX_EXTERNAL_AUTH_ENFORCED",
    "ALLOW_DEMO_TOKEN_AUTH",
    "DEMO_API_TOKEN",
    "ZENODEX_API_BEARER_TOKEN",
    "ZENODEX_ENV",
    "APP_ENV",
)


@pytest.fixture
def clean_env(monkeypatch):
    for name in _RELEVANT_ENV:
        monkeypatch.delenv(name, raising=False)
    return monkeypatch


def test_production_strict_blocks_value_moving_routes_at_startup(clean_env):
    clean_env.setenv("ZENODEX_API_SURFACE_PROFILE", "production-strict")
    clean_env.setenv("PERPS_API_ENABLED", "1")
    clean_env.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")  # satisfy auth posture
    clean_env.setenv("ZENODEX_ENV", "production")
    assert api_server.main([]) == 2  # refuses to start before binding


def test_production_strict_blocks_dex_route(clean_env):
    clean_env.setenv("ZENODEX_API_SURFACE_PROFILE", "production-strict")
    clean_env.setenv("DEX_API_ENABLED", "1")
    clean_env.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")
    assert api_server.main([]) == 2


def test_production_strict_blocks_confidential_route(clean_env):
    clean_env.setenv("ZENODEX_API_SURFACE_PROFILE", "production-strict")
    clean_env.setenv("CONFIDENTIAL_SEALED_BID_API_ENABLED", "1")
    clean_env.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")
    assert api_server.main([]) == 2


def test_unknown_profile_rejected_at_startup(clean_env):
    clean_env.setenv("ZENODEX_API_SURFACE_PROFILE", "not-a-real-profile")
    # no routes enabled -> still must reject the unknown profile id
    assert api_server.main([]) == 2


def test_existing_api_surface_profile_alias_is_enforced_at_startup(clean_env):
    clean_env.setenv("API_SURFACE_PROFILE", "production-strict")
    clean_env.setenv("DEX_API_ENABLED", "1")
    clean_env.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")
    assert api_server.main([]) == 2


def test_conflicting_api_surface_profile_aliases_reject_at_startup(clean_env):
    clean_env.setenv("ZENODEX_API_SURFACE_PROFILE", "local-demo")
    clean_env.setenv("API_SURFACE_PROFILE", "production-strict")
    assert api_server.main([]) == 2


# --- pure policy function ---
def test_policy_production_strict_forbids_value_moving():
    v = api_surface_profile_violations(
        profile_id="production-strict",
        demo_api_token="",
        perps_enabled=True,
        zusd_enabled=False,
        dex_enabled=False,
    )
    assert any("forbids demo/value-moving" in r for r in v)


def test_policy_public_testnet_requires_demo_token():
    v = api_surface_profile_violations(
        profile_id="public-testnet",
        demo_api_token="",
        perps_enabled=False,
        zusd_enabled=True,
        dex_enabled=False,
    )
    assert any("requires an API bearer token" in r for r in v)
    # with a token, public-testnet permits the routes
    v2 = api_surface_profile_violations(
        profile_id="public-testnet",
        demo_api_token="tok",
        perps_enabled=False,
        zusd_enabled=True,
        dex_enabled=False,
    )
    assert v2 == ()


def test_policy_local_demo_allows_everything():
    v = api_surface_profile_violations(
        profile_id="local-demo",
        demo_api_token="",
        perps_enabled=True,
        zusd_enabled=True,
        dex_enabled=True,
        confidential_enabled=True,
    )
    assert v == ()
