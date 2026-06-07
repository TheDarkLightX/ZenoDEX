from __future__ import annotations

import pytest

from src.integration import api_server, deploy_profile
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile
from src.runtime.authority import reset_active_authority_policy

_RELEVANT_ENV = (
    "ZENODEX_DEPLOY_PROFILE",
    "PERPS_WALLET_ALLOW_LOCAL_SIGNING",
    "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD",
    "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING",
    "ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD",
    "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING",
    "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING",
    "CONFIDENTIAL_SEALED_BID_ALLOW_IN_MEMORY_STATE",
    "CONFIDENTIAL_SEALED_BID_ALLOW_FIXTURE_SETTLEMENT",
    "CONFIDENTIAL_SEALED_BID_RETURN_SIGNED_TAU_TX_PAYLOAD",
    "ALLOW_DEMO_TOKEN_AUTH",
    "DEMO_API_TOKEN",
    "ZENODEX_EXTERNAL_AUTH_ENFORCED",
    "PERPS_API_ENABLED",
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_API_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
    "AUTOTRADER_LIVE_API_ENABLED",
    "CONFIDENTIAL_ATTESTATION_API_ENABLED",
    "DEX_API_ENABLED",
    "ZENODEX_RUNTIME_BIN",
)


@pytest.fixture
def clean_env(monkeypatch):
    for name in _RELEVANT_ENV:
        monkeypatch.delenv(name, raising=False)
    yield monkeypatch
    reset_active_authority_policy()


@pytest.mark.parametrize(
    ("env_name", "expected_fragment"),
    (
        ("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "PERPS_WALLET_ALLOW_LOCAL_SIGNING is enabled"),
        ("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING is enabled"),
        ("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING is enabled"),
        ("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING is enabled"),
        (
            "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD",
            "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD is enabled",
        ),
        (
            "ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD",
            "ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD is enabled",
        ),
    ),
)
def test_production_strict_deploy_profile_rejects_raw_key_runtime_flags(env_name, expected_fragment):
    profile = load_deploy_profile("production-strict")
    conflicts = evaluate_deploy_profile_consistency(profile, {env_name.lower(): True})

    assert any(expected_fragment in conflict for conflict in conflicts)


def test_deploy_profile_loader_rejects_absolute_yaml_path(tmp_path):
    external_profile = tmp_path / "production-strict.yaml"
    external_profile.write_text(
        "\n".join(
            (
                "schema: zenodex/deployment_profile/v1",
                "profile_id: production-strict",
                "key_policy:",
                "  raw_private_key_flags_allowed: true",
                "runtime_policy:",
                "  local_only_routes_allowed: true",
            )
        ),
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="invalid deploy profile id"):
        load_deploy_profile(str(external_profile))


def test_deploy_profile_loader_rejects_path_traversal():
    with pytest.raises(ValueError, match="invalid deploy profile id"):
        load_deploy_profile("../production-strict")


def test_deploy_profile_loader_rejects_unallowlisted_profile_id(monkeypatch, tmp_path):
    deploy_dir = tmp_path / "deploy"
    deploy_dir.mkdir()
    (deploy_dir / "evil-profile.yaml").write_text(
        "\n".join(
            (
                "schema: zenodex/deployment_profile/v1",
                "profile_id: evil-profile",
            )
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(deploy_profile, "_DEPLOY_DIR", deploy_dir)

    with pytest.raises(ValueError, match="unknown deploy profile id"):
        deploy_profile.load_deploy_profile("evil-profile")


def test_deploy_profile_loader_requires_loaded_profile_id_to_match(monkeypatch, tmp_path):
    deploy_dir = tmp_path / "deploy"
    deploy_dir.mkdir()
    (deploy_dir / "production-strict.yaml").write_text(
        "\n".join(
            (
                "schema: zenodex/deployment_profile/v1",
                "profile_id: local-dev",
            )
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(deploy_profile, "_DEPLOY_DIR", deploy_dir)

    with pytest.raises(ValueError, match="deploy profile id mismatch"):
        deploy_profile.load_deploy_profile("production-strict")


def test_startup_rejects_external_deploy_profile_path(clean_env, tmp_path):
    external_profile = tmp_path / "exploit.yaml"
    external_profile.write_text(
        "\n".join(
            (
                "schema: zenodex/deployment_profile/v1",
                "profile_id: production-strict",
                "key_policy:",
                "  raw_private_key_flags_allowed: true",
                "runtime_policy:",
                "  local_only_routes_allowed: true",
            )
        ),
        encoding="utf-8",
    )
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", str(external_profile))

    assert api_server.main([]) == 2


def test_production_strict_startup_rejects_zusd_tau_local_signing(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "production-strict")
    clean_env.setenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "1")

    assert api_server.main([]) == 2


def test_public_testnet_startup_rejects_autotrader_local_signing(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "public-testnet")
    clean_env.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")

    assert api_server.main([]) == 2


def test_public_testnet_deploy_profile_rejects_half_configured_rust_authority():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["promoted_surfaces"] = []

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("half-configured Rust authority" in conflict for conflict in conflicts)


def test_public_testnet_startup_rejects_missing_rust_authority_binary(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "public-testnet")
    clean_env.setenv("ZENODEX_RUNTIME_BIN", "/tmp/zenodex-runtime-missing")

    assert api_server.main([]) == 2


def test_production_strict_startup_rejects_local_fixture_routes(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "production-strict")
    clean_env.setenv("ALLOW_DEMO_TOKEN_AUTH", "1")

    assert api_server.main([]) == 2


def test_unknown_deploy_profile_rejects_at_startup(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "not-a-real-profile")

    assert api_server.main([]) == 2


def test_local_dev_profile_allows_local_signing_facts():
    profile = load_deploy_profile("local-dev")
    conflicts = evaluate_deploy_profile_consistency(
        profile,
        {
            "perps_wallet_allow_local_signing": True,
            "zusd_tau_wallet_allow_local_signing": True,
            "zusd_monetary_wallet_allow_local_signing": True,
            "autotrader_live_allow_local_signing": True,
            "allow_demo_token_auth": True,
            "legacy_demo_token_active": True,
        },
    )

    assert conflicts == ()
