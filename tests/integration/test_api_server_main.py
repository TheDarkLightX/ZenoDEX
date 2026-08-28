from __future__ import annotations

import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import pytest
import yaml

from src.integration.local_route_quarantine import (
    QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1,
    QUARANTINED_ROUTE_ENVIRONMENT_V1,
    LocalRouteQuarantineRejectV1,
    quarantined_route_environment_rejections_v1,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
PREWARM_MODULES_V1 = (
    "src.integration.api_server_settlement_parsers",
    "src.integration.operations",
    "src.integration.validation",
    "src.integration.settlement_price_provenance",
    "src.integration.settlement_price_attestation",
    "src.integration.settlement_end_to_end_certificate_packet",
    "src.integration.settlement_witness_lifecycle",
    "src.integration.settlement_feature_extension_packet",
    "src.integration.settlement_value_contract",
    "src.integration.settlement_lp_value_contract",
    "src.integration.settlement_endogenous_lp_value_packet",
    "src.integration.settlement_value_packet",
)


@pytest.fixture(autouse=True)
def _isolate_retired_tau_route_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in QUARANTINED_ROUTE_ENVIRONMENT_V1 + QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1:
        monkeypatch.delenv(name, raising=False)


def _unexpected_server_construction(*_args, **_kwargs) -> None:
    raise AssertionError("startup refusal must precede server construction")


def test_given_direct_state_attachment_when_retired_routes_are_enabled_then_rejects_before_effects() -> None:
    # Arrange.
    from src.integration import api_server

    config = replace(
        api_server._load_api_server_config(),
        perps_wallet_enabled=True,
        zusd_tau_wallet_enabled=True,
        zusd_monetary_wallet_enabled=True,
    )
    server = type("InertServer", (), {})()

    # Act.
    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        api_server._attach_api_server_state(server, config)

    # Assert.
    assert vars(server) == {}


def test_given_api_module_import_when_admission_has_not_run_then_prewarm_targets_remain_unloaded() -> None:
    script = (
        "import sys\n"
        "import src.integration.api_server\n"
        f"targets={PREWARM_MODULES_V1!r}\n"
        "print('\\n'.join(name for name in targets if name in sys.modules))\n"
    )

    result = subprocess.run(
        [sys.executable, "-c", script],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout == "\n"


def test_given_legacy_package_export_when_explicitly_requested_then_only_its_module_loads() -> None:
    script = (
        "import sys\n"
        "import src.integration\n"
        "assert 'src.integration.operations' not in sys.modules\n"
        "from src.integration import parse_intents\n"
        "assert callable(parse_intents)\n"
        "assert 'src.integration.operations' in sys.modules\n"
    )

    result = subprocess.run(
        [sys.executable, "-c", script],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("route_name", QUARANTINED_ROUTE_ENVIRONMENT_V1)
@pytest.mark.parametrize("value", ("", "true", "TRUE", "1", "yes", " false ", "on"))
def test_given_noncanonical_retired_route_value_when_api_starts_then_preflight_rejects_without_effect(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    route_name: str,
    value: str,
) -> None:
    from src.integration import api_server

    monkeypatch.setenv(route_name, value)
    events: list[str] = []
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: events.append("config"))
    monkeypatch.setattr(api_server, "_prewarm_api_modules", lambda: events.append("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_server_construction)

    assert api_server.main([]) == 2
    assert events == []
    assert capsys.readouterr().out.splitlines() == [
        "Refusing to start: retired Tau route environment variable "
        f"{route_name!r} must be absent, exact 'false', or exact '0'."
    ]


@pytest.mark.parametrize("alias", QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1)
def test_given_retired_route_alias_when_api_starts_then_preflight_rejects_before_config(
    monkeypatch: pytest.MonkeyPatch,
    alias: str,
) -> None:
    from src.integration import api_server

    monkeypatch.setenv(alias, "false")
    events: list[str] = []
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: events.append("config"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_server_construction)

    assert api_server.main([]) == 2
    assert events == []


@pytest.mark.parametrize("value", ("false", "0"))
def test_given_exact_disabled_retired_routes_when_checked_then_preflight_accepts(
    value: str,
) -> None:
    environment = {name: value for name in QUARANTINED_ROUTE_ENVIRONMENT_V1}

    assert quarantined_route_environment_rejections_v1(environment) == ()


def test_given_hostile_retired_route_value_when_checked_then_no_dunder_executes() -> None:
    class HostileValue:
        def __eq__(self, _other: object) -> bool:
            raise AssertionError("hostile equality executed")

        def __hash__(self) -> int:
            raise AssertionError("hostile hash executed")

    environment = {QUARANTINED_ROUTE_ENVIRONMENT_V1[0]: HostileValue()}

    assert quarantined_route_environment_rejections_v1(environment) == (
        LocalRouteQuarantineRejectV1(
            code="QUARANTINED_ROUTE_ENV_VALUE",
            variable=QUARANTINED_ROUTE_ENVIRONMENT_V1[0],
        ),
    )


@pytest.mark.parametrize(
    ("field_name", "expected"),
    (
        (
            "perps_wallet_enabled",
            "Refusing to start: PERPS_WALLET_API_ENABLED depends on the retired Tau "
            "stream-8 application bridge; use a current-Tau ingress and ZenoLedger publication.",
        ),
        (
            "zusd_monetary_wallet_enabled",
            "Refusing to start: ZUSD_MONETARY_WALLET_API_ENABLED depends on the retired Tau "
            "stream-11 application bridge and lacks a verifier-owned execution clock.",
        ),
    ),
)
def test_given_parsed_retired_route_enable_when_api_starts_then_backstop_rejects_without_effect(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    field_name: str,
    expected: str,
) -> None:
    from src.integration import api_server

    base_config = api_server._load_api_server_config()
    if field_name == "perps_wallet_enabled":
        config = replace(base_config, perps_wallet_enabled=True)
    elif field_name == "zusd_monetary_wallet_enabled":
        config = replace(base_config, zusd_monetary_wallet_enabled=True)
    else:
        raise AssertionError(f"unsupported retired route field: {field_name}")
    events: list[str] = []
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: config)
    monkeypatch.setattr(api_server, "_prewarm_api_modules", lambda: events.append("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_server_construction)

    assert api_server.main([]) == 2
    assert events == []
    assert capsys.readouterr().out.splitlines() == [expected]


def test_api_server_refuses_demo_routes_without_token_on_public_host(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "0.0.0.0")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "true")
    monkeypatch.setenv("DEX_API_ENABLED", "false")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)

    rc = api_server.main([])
    assert rc == 2


def test_api_server_refuses_unsafe_perps_demo_api_in_production(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "true")
    monkeypatch.setenv("PERPS_DEMO_API_UNSAFE_ENABLED", "true")
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")
    monkeypatch.setenv("ZENODEX_ENV", "production")

    rc = api_server.main([])
    assert rc == 2


def test_api_server_refuses_sensitive_routes_without_auth_on_loopback(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)
    monkeypatch.delenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", raising=False)

    rc = api_server.main([])
    assert rc == 2


def test_api_server_refuses_demo_token_auth_in_production_without_exception(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.setenv("DEMO_API_TOKEN", "redacted-demo-token")
    monkeypatch.setenv("ZENODEX_ENV", "production")
    monkeypatch.delenv("ALLOW_DEMO_TOKEN_AUTH", raising=False)
    monkeypatch.delenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", raising=False)

    rc = api_server.main([])
    assert rc == 2


def test_api_server_allows_sensitive_routes_when_external_auth_declared(monkeypatch) -> None:
    from src.integration import api_server

    class FakeServer:
        def __init__(self, address, handler_cls):
            self.address = address
            self.handler_cls = handler_cls

        def serve_forever(self, poll_interval=0.25):  # noqa: ANN001
            return None

    monkeypatch.setattr(api_server, "ThreadingHTTPServer", FakeServer)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")

    rc = api_server.main([])
    assert rc == 0


def test_api_server_refuses_autotrader_live_mount_until_external_intent_signing_exists(
    monkeypatch,
    capsys,
) -> None:
    from src.integration import api_server

    base_config = api_server._load_api_server_config()
    config = replace(
        base_config,
        autotrader_live_enabled=True,
        confidential_sealed_bid_asset_settlement_enabled=False,
    )
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: config)
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_server_construction)

    rc = api_server.main([])

    assert rc == 2
    assert capsys.readouterr().out.splitlines() == [
        "Refusing to start: AUTOTRADER_LIVE_API_ENABLED is unavailable until "
        "client-signed DEX intent envelopes are implemented and verified."
    ]


def test_api_server_refuses_zusd_tau_wallet_mount_until_network_binding_and_reconciliation_exist(
    monkeypatch,
    capsys,
) -> None:
    from src.integration import api_server

    base_config = api_server._load_api_server_config()
    config = replace(base_config, autotrader_live_enabled=False, zusd_tau_wallet_enabled=True)
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: config)
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_server_construction)

    rc = api_server.main([])

    assert rc == 2
    assert capsys.readouterr().out.splitlines() == [
        "Refusing to start: ZUSD_TAU_WALLET_API_ENABLED requires Tau network-domain "
        "signature binding and durable submission reconciliation."
    ]


def test_api_server_refuses_mounted_sealed_bid_fixture_signer(
    monkeypatch,
    capsys,
) -> None:
    from src.integration import api_server

    base_config = api_server._load_api_server_config()
    config = replace(
        base_config,
        autotrader_live_enabled=False,
        confidential_sealed_bid_asset_settlement_enabled=True,
    )
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: config)
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_server_construction)

    rc = api_server.main([])

    assert rc == 2
    assert capsys.readouterr().out.splitlines() == [
        "Refusing to start: CONFIDENTIAL_SEALED_BID_LOCAL_LEDGER_SETTLEMENT_ENABLED "
        "uses local fixture signing authority and is not mountable."
    ]


def test_local_testnet_compose_disables_unsafe_adapters_and_reaches_server_construction(
    monkeypatch,
) -> None:
    from src.integration import api_server
    from tools.zenoctl_testnet_local import lifecycle

    compose = yaml.safe_load(
        (REPO_ROOT / "docker-compose.local-testnet.yml").read_text(encoding="utf-8")
    )
    environment = compose["services"]["zenodex-api"]["environment"]
    assert environment["AUTOTRADER_LIVE_API_ENABLED"] == "false"
    assert environment["AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING"] == "false"
    assert environment["AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION"] == "false"
    assert environment["AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED"] == "false"
    assert environment["AUTOTRADER_LIVE_SUPERVISOR_ENABLED"] == "false"
    assert environment["CONFIDENTIAL_SEALED_BID_LOCAL_LEDGER_SETTLEMENT_ENABLED"] == "false"
    assert environment["CONFIDENTIAL_SEALED_BID_AUTO_MINE"] == "false"
    assert "AUTOTRADER_LIVE_API_ENABLED" not in lifecycle.LOCAL_TESTNET_ENABLED_LANES

    lane_fields = {
        "DEX_API_ENABLED": "dex_enabled",
        "PERPS_WALLET_API_ENABLED": "perps_wallet_enabled",
        "ZUSD_TAU_WALLET_API_ENABLED": "zusd_tau_wallet_enabled",
        "ZUSD_MONETARY_WALLET_API_ENABLED": "zusd_monetary_wallet_enabled",
        "AUTOTRADER_LIVE_API_ENABLED": "autotrader_live_enabled",
        "CONFIDENTIAL_ATTESTATION_API_ENABLED": "confidential_attestation_enabled",
    }
    for env_name in lane_fields:
        monkeypatch.setenv(env_name, environment[env_name])
    monkeypatch.setenv(
        "CONFIDENTIAL_SEALED_BID_LOCAL_LEDGER_SETTLEMENT_ENABLED",
        environment["CONFIDENTIAL_SEALED_BID_LOCAL_LEDGER_SETTLEMENT_ENABLED"],
    )
    monkeypatch.setenv("PERPS_API_ENABLED", environment["PERPS_API_ENABLED"])
    monkeypatch.setenv("PERPS_DEMO_API_UNSAFE_ENABLED", "false")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_API_ENABLED", "false")
    monkeypatch.setenv("AUTOGOV_LIVE_APPLY_API_ENABLED", "false")
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "true")

    config = api_server._load_api_server_config()
    configured_enabled_lanes = {
        env_name for env_name, field_name in lane_fields.items() if getattr(config, field_name)
    }
    assert configured_enabled_lanes == set(lifecycle.LOCAL_TESTNET_ENABLED_LANES)
    assert config.confidential_sealed_bid_asset_settlement_enabled is False

    class FakeServer:
        autotrader_live_api_enabled: bool
        confidential_sealed_bid_asset_settlement_submitter: object | None

        def __init__(self, address, handler_cls):
            self.address = address
            self.handler_cls = handler_cls
            server_instances.append(self)

        def serve_forever(self, poll_interval=0.25):  # noqa: ANN001
            return None

    server_instances: list[FakeServer] = []
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", FakeServer)

    rc = api_server.main([])

    assert rc == 0
    assert len(server_instances) == 1
    assert server_instances[0].autotrader_live_api_enabled is False
    assert server_instances[0].confidential_sealed_bid_asset_settlement_submitter is None


def test_local_testnet_profile_quarantines_zusd_tau_wallet_lane() -> None:
    from tools.zenoctl_testnet_local import lifecycle

    compose = yaml.safe_load((REPO_ROOT / "docker-compose.local-testnet.yml").read_text(encoding="utf-8"))
    environment = compose["services"]["zenodex-api"]["environment"]

    assert environment["ZUSD_TAU_WALLET_API_ENABLED"] == "false"
    assert environment["ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING"] == "false"
    assert environment["ZUSD_TAU_WALLET_AUTO_MINE"] == "false"
    assert "ZUSD_TAU_WALLET_API_ENABLED" not in lifecycle.LOCAL_TESTNET_ENABLED_LANES


def test_operator_docs_state_current_retired_tau_route_quarantine() -> None:
    ui_status = (REPO_ROOT / "docs/ZENODEX_UI_SURFACE_STATUS_2026_05_20.md").read_text(
        encoding="utf-8"
    )
    perps_plan = (REPO_ROOT / "docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md").read_text(
        encoding="utf-8"
    )
    zusd_status = (REPO_ROOT / "docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md").read_text(
        encoding="utf-8"
    )
    quickstart = (REPO_ROOT / "docs/LOCAL_TESTNET_QUICKSTART.md").read_text(encoding="utf-8")
    ui_readme = (REPO_ROOT / "tools/dex-ui/README.md").read_text(encoding="utf-8")
    normalized_ui_status = " ".join(ui_status.split())
    normalized_perps_plan = " ".join(perps_plan.split())
    normalized_zusd_status = " ".join(zusd_status.split())
    normalized_quickstart = " ".join(quickstart.split())
    normalized_ui_readme = " ".join(ui_readme.split())

    prohibited_current_claims = (
        "Live Tau wallet plus monetary-vault lanes",
        "the mounted zUSD tab can submit through the Tau wallet bridge",
        "The mounted non-demo zUSD UI now exposes both the stream `9` TauToken wallet",
    )
    combined = (
        normalized_ui_status
        + normalized_perps_plan
        + normalized_zusd_status
        + normalized_quickstart
    )
    for claim in prohibited_current_claims:
        assert claim not in combined
    assert "Current authority correction (2026-08-28)" in normalized_ui_status
    assert "stream `8` perps wallet, stream `9` zUSD wallet, stream `11` zUSD monetary" in normalized_ui_status
    assert "They do not establish current route reachability, settlement authority, or production readiness." in normalized_perps_plan
    assert "Historical Donor Evidence Ledger" in normalized_perps_plan
    assert "The current profile keeps stream `11` unmounted." in normalized_zusd_status
    assert "does not establish current route reachability" in normalized_zusd_status
    assert "Compose project: zenodex-local-testnet-v2-<hash32>" in normalized_quickstart
    assert "Perps, both zUSD routes, and AutoTrader are unmounted." in normalized_quickstart
    assert "Current route posture:" in normalized_ui_readme
    assert "Normal API startup refuses the stream-8 wallet route." in normalized_ui_readme
    assert "Normal startup refuses both routes." in normalized_ui_readme
