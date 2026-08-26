from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]


def _unexpected_server_construction(*_args, **_kwargs) -> None:
    raise AssertionError("startup refusal must precede server construction")


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


def test_operator_docs_do_not_advertise_quarantined_zusd_tau_wallet_as_mounted() -> None:
    ui_status = (REPO_ROOT / "docs/ZENODEX_UI_SURFACE_STATUS_2026_05_20.md").read_text(
        encoding="utf-8"
    )
    perps_plan = (REPO_ROOT / "docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md").read_text(
        encoding="utf-8"
    )
    quickstart = (REPO_ROOT / "docs/LOCAL_TESTNET_QUICKSTART.md").read_text(encoding="utf-8")
    normalized_ui_status = " ".join(ui_status.split())
    normalized_perps_plan = " ".join(perps_plan.split())
    normalized_quickstart = " ".join(quickstart.split())

    prohibited_current_claims = (
        "Live Tau wallet plus monetary-vault lanes",
        "the mounted zUSD tab can submit through the Tau wallet bridge",
        "The mounted non-demo zUSD UI now exposes both the stream `9` TauToken wallet",
    )
    combined = normalized_ui_status + normalized_perps_plan + normalized_quickstart
    for claim in prohibited_current_claims:
        assert claim not in combined
    assert "Normal API startup refuses `/api/zusd/wallet/*`" in normalized_ui_status
    assert "The stream `11` monetary-vault path remains mounted." in normalized_ui_status
    assert (
        "The stream `9` TauToken wallet transport path is unmounted."
        in normalized_perps_plan
    )
    assert "Compose project: zenodex-local-testnet-v2-<hash32>" in normalized_quickstart
    assert "The AutoTrader route and stream `9` zUSD Tau wallet are unmounted." in normalized_quickstart
