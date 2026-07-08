from __future__ import annotations

import pytest


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


def test_api_server_refuses_sensitive_routes_without_auth_on_loopback(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)
    monkeypatch.delenv("ZENODEX_API_BEARER_TOKEN", raising=False)
    monkeypatch.delenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", raising=False)

    rc = api_server.main([])
    assert rc == 2


def test_api_server_allows_sensitive_routes_with_api_bearer_token(monkeypatch) -> None:
    from src.integration import api_server

    started: dict[str, object] = {}

    class FakeServer:
        def __init__(self, address, handler_cls):
            self.address = address
            self.handler_cls = handler_cls

        def serve_forever(self, poll_interval=0.25):  # noqa: ANN001
            started["demo_api_token"] = getattr(self, "demo_api_token", None)
            return None

    monkeypatch.setattr(api_server, "ThreadingHTTPServer", FakeServer)
    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.setenv("ZENODEX_ENV", "production")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)
    monkeypatch.setenv("ZENODEX_API_BEARER_TOKEN", "redacted-api-token")
    monkeypatch.delenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", raising=False)
    monkeypatch.delenv("ALLOW_DEMO_TOKEN_AUTH", raising=False)

    rc = api_server.main([])
    assert rc == 0
    assert started["demo_api_token"] == "redacted-api-token"


def test_api_server_refuses_demo_token_auth_in_production_without_exception(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "false")
    monkeypatch.setenv("DEX_API_ENABLED", "true")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.setenv("DEMO_API_TOKEN", "redacted-demo-token")
    monkeypatch.delenv("ZENODEX_API_BEARER_TOKEN", raising=False)
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


def test_api_server_refuses_malformed_boolean_env(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("DEX_API_ENABLED", "maybe")

    assert api_server.main([]) == 2


def test_env_int_rejects_malformed_or_out_of_range_runtime_control(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("RATE_LIMIT_RPM", "abc")
    with pytest.raises(ValueError, match="RATE_LIMIT_RPM"):
        api_server._env_int("RATE_LIMIT_RPM", 600, lo=0, hi=1_000_000)

    monkeypatch.setenv("RATE_LIMIT_RPM", "-1")
    with pytest.raises(ValueError, match="RATE_LIMIT_RPM"):
        api_server._env_int("RATE_LIMIT_RPM", 600, lo=0, hi=1_000_000)


def test_api_server_refuses_invalid_rate_limit_integer(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("RATE_LIMIT_RPM", "-1")

    assert api_server.main([]) == 2


def test_api_server_refuses_invalid_port_integer(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "70000")

    assert api_server.main([]) == 2


def test_env_bool_rejects_malformed_runtime_control(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", "maybe")

    with pytest.raises(ValueError, match="DEX_ROUTING_ORACLE_ADAPTER_REQUIRED"):
        api_server._env_bool("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", False)


def test_api_server_refuses_malformed_routing_oracle_control(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", "maybe")

    assert api_server.main([]) == 2
