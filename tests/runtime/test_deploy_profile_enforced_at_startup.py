from __future__ import annotations

import pytest
import yaml

from src.integration import api_server
from src.integration import deploy_profile as deploy_profile_module
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
    "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED",
    "ZUSD_ORACLE_ADAPTER_REQUIRED",
    "ZUSD_ORACLE_AUTHORIZATION_REQUIRED",
    "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
    "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
    "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH",
    "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
    "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE_EPOCH",
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
    "ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED",
    "AUTOTRADER_LIVE_API_ENABLED",
    "CONFIDENTIAL_ATTESTATION_API_ENABLED",
    "DEX_API_ENABLED",
    "ZENODEX_RUNTIME_BIN",
)


def _required_oracle_runtime_facts() -> dict[str, bool]:
    return {
        "dex_routing_oracle_adapter_required": True,
        "zusd_oracle_adapter_required": True,
        "zusd_oracle_authorization_required": True,
        "zusd_monetary_wallet_oracle_authorization_required": True,
        "perps_clearinghouse_settle_oracle_adapter_required": True,
        "perps_clearinghouse_settle_oracle_authorization_required": True,
        "perps_isolated_settle_oracle_adapter_required": True,
        "perps_isolated_partial_liquidate_oracle_adapter_required": True,
        "perps_isolated_settle_oracle_authorization_required": True,
    }


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


def test_production_strict_startup_rejects_zusd_tau_local_signing(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "production-strict")
    clean_env.setenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "1")

    assert api_server.main([]) == 2


def test_public_testnet_startup_rejects_autotrader_local_signing(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "public-testnet")
    clean_env.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")

    assert api_server.main([]) == 2


def test_public_testnet_deploy_profile_rejects_enabled_local_demo_route():
    profile = load_deploy_profile("public-testnet")
    conflicts = evaluate_deploy_profile_consistency(
        profile,
        {
            "enabled_routes": ("local_demo",),
            "sensitive_api_enabled": True,
            "auth_bearer_token_set": True,
        },
    )

    assert any("allowed_routes does not permit enabled route 'local_demo'" in c for c in conflicts)


def test_deploy_profile_rejects_malformed_enabled_routes_fact():
    profile = load_deploy_profile("public-testnet")
    conflicts = evaluate_deploy_profile_consistency(profile, {"enabled_routes": "local_demo"})

    assert any("runtime fact 'enabled_routes' must be a string collection" in c for c in conflicts)


def test_public_testnet_deploy_profile_allows_signed_intents_route():
    profile = load_deploy_profile("public-testnet")
    conflicts = evaluate_deploy_profile_consistency(
        profile,
        {
            **_required_oracle_runtime_facts(),
            "enabled_routes": ("signed_intents",),
            "sensitive_api_enabled": True,
            "auth_bearer_token_set": True,
        },
    )

    assert conflicts == ()


@pytest.mark.parametrize(
    ("fact_name", "env_name"),
    (
        ("dex_routing_oracle_adapter_required", "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED"),
        ("zusd_oracle_adapter_required", "ZUSD_ORACLE_ADAPTER_REQUIRED"),
        ("zusd_oracle_authorization_required", "ZUSD_ORACLE_AUTHORIZATION_REQUIRED"),
        (
            "perps_clearinghouse_settle_oracle_adapter_required",
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
        ),
        (
            "perps_clearinghouse_settle_oracle_authorization_required",
            "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
        ),
        (
            "perps_isolated_settle_oracle_adapter_required",
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH",
        ),
        (
            "perps_isolated_partial_liquidate_oracle_adapter_required",
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
        ),
        (
            "perps_isolated_settle_oracle_authorization_required",
            "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE_EPOCH",
        ),
    ),
)
@pytest.mark.parametrize("profile_id", ("public-testnet", "production-strict"))
def test_strict_deploy_profiles_reject_missing_required_oracle_gate(profile_id, fact_name, env_name):
    profile = load_deploy_profile(profile_id)
    facts = _required_oracle_runtime_facts()
    facts[fact_name] = False

    conflicts = evaluate_deploy_profile_consistency(profile, facts)

    assert any(f"oracle_policy.{fact_name}=true but {env_name} is not enabled" in c for c in conflicts)


def test_deploy_profile_rejects_malformed_oracle_policy():
    profile = load_deploy_profile("public-testnet")
    profile["oracle_policy"]["zusd_oracle_authorization_required"] = "yes"

    conflicts = evaluate_deploy_profile_consistency(profile, _required_oracle_runtime_facts())

    assert any("oracle_policy.zusd_oracle_authorization_required must be bool" in c for c in conflicts)


def test_public_testnet_startup_rejects_missing_required_oracle_gate(clean_env):
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "public-testnet")
    clean_env.setenv("ZENODEX_RUNTIME_BIN", "/tmp/zenodex-runtime-missing")

    assert api_server.main([]) == 2


def test_production_strict_startup_rejects_perps_api_even_with_auth(clean_env, monkeypatch):
    class FakeServer:
        def __init__(self, address, handler_cls):
            self.address = address
            self.handler_cls = handler_cls

        def serve_forever(self, poll_interval=0.25):  # noqa: ANN001
            return None

    monkeypatch.setattr(api_server, "ThreadingHTTPServer", FakeServer)
    clean_env.setenv("ZENODEX_DEPLOY_PROFILE", "production-strict")
    clean_env.setenv("PERPS_API_ENABLED", "1")
    clean_env.setenv("DEMO_API_TOKEN", "token")
    clean_env.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")

    assert api_server.main([]) == 2


def test_public_testnet_deploy_profile_rejects_half_configured_rust_authority():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["promoted_surfaces"] = []

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("half-configured Rust authority" in conflict for conflict in conflicts)


def test_deploy_profile_rejects_unknown_runtime_authority_policy_key():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["promoted_surface"] = list(
        profile["runtime_authority_policy"]["promoted_surfaces"]
    )
    del profile["runtime_authority_policy"]["promoted_surfaces"]

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("runtime_authority_policy has unknown keys" in conflict for conflict in conflicts)


def test_deploy_profile_rejects_non_trusted_core_authority_surface():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["per_surface"]["debug_dashboard"] = (
        "rust_authority_with_python_shadow"
    )
    profile["runtime_authority_policy"]["promoted_surfaces"].append("debug_dashboard")

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("non-trusted-core surfaces" in conflict for conflict in conflicts)


def test_public_testnet_profile_rejects_missing_trusted_core_surface():
    profile = load_deploy_profile("public-testnet")
    del profile["runtime_authority_policy"]["per_surface"]["fee_router"]
    profile["runtime_authority_policy"]["promoted_surfaces"].remove("fee_router")

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("missing trusted-core authority surfaces" in conflict for conflict in conflicts)


def test_public_testnet_profile_rejects_trusted_core_rust_shadow():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["per_surface"]["fee_router"] = "rust_shadow"
    profile["runtime_authority_policy"]["promoted_surfaces"].remove("fee_router")

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("trusted-core surfaces must use" in conflict for conflict in conflicts)


def test_public_testnet_profile_demotes_perp_stateful_to_python_authority():
    # Stateful perps remains partial CBC, so Python retains authority and the
    # surface cannot appear in the promotion set.
    profile = load_deploy_profile("public-testnet")
    assert (
        profile["runtime_authority_policy"]["per_surface"]["perp_stateful"]
        == "python_authority"
    )
    assert "perp_stateful" not in profile["runtime_authority_policy"]["promoted_surfaces"]
    conflicts = evaluate_deploy_profile_consistency(profile, {})
    assert not any("perp_stateful" in c for c in conflicts)


def test_deploy_profile_rejects_stale_promoted_surface_entry():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["per_surface"]["fee_router"] = "rust_shadow"

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("trusted-core surfaces must use" in conflict for conflict in conflicts)


def test_deploy_profile_rejects_pure_rust_authority_in_strict_profile():
    profile = load_deploy_profile("public-testnet")
    profile["runtime_authority_policy"]["per_surface"]["fee_router"] = "rust_authority"

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any("pure rust_authority is not admitted" in conflict for conflict in conflicts)


def test_deploy_profile_rejects_non_bool_runtime_facts():
    profile = load_deploy_profile("production-strict")
    conflicts = evaluate_deploy_profile_consistency(
        profile,
        {
            "sensitive_api_enabled": True,
            "auth_bearer_token_set": "false",
            "external_auth_enforced": False,
        },
    )

    assert any("runtime fact 'auth_bearer_token_set' must be a bool" in c for c in conflicts)
    assert any("sensitive APIs are enabled without a bearer token" in c for c in conflicts)


@pytest.mark.parametrize(
    ("field", "bad_value", "expected"),
    (
        ("profile_id", " production-strict", "profile_id must be a non-empty"),
        ("key_policy", "disabled", "key_policy must be a mapping"),
        ("runtime_policy", "disabled", "runtime_policy must be a mapping"),
        ("required_auth", "disabled", "required_auth must be a mapping"),
    ),
)
def test_deploy_profile_rejects_malformed_policy_sections(field, bad_value, expected):
    profile = load_deploy_profile("production-strict")
    profile[field] = bad_value

    conflicts = evaluate_deploy_profile_consistency(profile, {})

    assert any(expected in c for c in conflicts)


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


def test_load_deploy_profile_rejects_malformed_profile_request():
    with pytest.raises(ValueError, match="profile must be a non-empty string"):
        load_deploy_profile("")
    with pytest.raises(ValueError, match="invalid deploy profile id"):
        load_deploy_profile("../etc/passwd")
    with pytest.raises(ValueError, match="unknown deploy profile id"):
        load_deploy_profile("not-a-real-profile")


def test_load_deploy_profile_rejects_mismatched_named_profile(tmp_path, monkeypatch):
    profile_dir = tmp_path / "profiles"
    profile_dir.mkdir()
    path = profile_dir / "production-strict.yaml"
    path.write_text(
        "\n".join(
            [
                "schema: zenodex/deployment_profile/v1",
                "profile_id: local-dev",
                "runtime_authority_policy:",
                "  schema: zenodex/runtime_authority_policy/v1",
                "  default: python_authority",
                "  per_surface: {}",
                "  promoted_surfaces: []",
            ]
        ),
        encoding="utf-8",
    )
    # Path hardening: arbitrary filesystem paths are rejected; only allowlisted
    # profile ids are accepted. Monkeypatch the deploy dir and allowlist to
    # admit the test profile, then verify the id mismatch is caught.
    monkeypatch.setattr(deploy_profile_module, "_DEPLOY_DIR", profile_dir)
    monkeypatch.setattr(deploy_profile_module, "_DEPLOY_PROFILE_IDS", frozenset({"production-strict"}))
    with pytest.raises(ValueError, match="deploy profile id mismatch"):
        load_deploy_profile("production-strict")


def test_load_deploy_profile_rejects_unknown_top_level_keys(tmp_path, monkeypatch):
    profile = load_deploy_profile("production-strict")
    profile["runtime_polciy"] = dict(profile["runtime_policy"])
    del profile["runtime_policy"]
    profile["profile_id"] = "test-typo"
    path = tmp_path / "test-typo.yaml"
    path.write_text(yaml.safe_dump(profile, sort_keys=True), encoding="utf-8")

    monkeypatch.setattr(deploy_profile_module, "_DEPLOY_DIR", tmp_path)
    monkeypatch.setattr(deploy_profile_module, "_DEPLOY_PROFILE_IDS", frozenset({"test-typo"}))
    with pytest.raises(ValueError, match="unknown top-level keys"):
        load_deploy_profile("test-typo")


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
