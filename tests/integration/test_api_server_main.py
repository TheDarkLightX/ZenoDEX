from __future__ import annotations


def test_api_server_refuses_retired_unsigned_perps_setting(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "0.0.0.0")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "true")
    monkeypatch.setenv("DEX_API_ENABLED", "false")
    monkeypatch.setenv("ZUSD_API_ENABLED", "false")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)

    rc = api_server.main([])
    assert rc == 2


def test_api_server_refuses_retired_unsigned_zusd_setting(monkeypatch, capsys) -> None:
    from src.integration import api_server

    for name in (
        "PERPS_API_ENABLED",
        "PERPS_DEMO_API_UNSAFE_ENABLED",
        "DEMO_API_TOKEN",
        "ALLOW_DEMO_TOKEN_AUTH",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("ZUSD_API_ENABLED", "true")

    rc = api_server.main([])

    assert rc == 2
    assert "ZUSD_API_ENABLED" in capsys.readouterr().out


def test_api_server_refuses_retired_perps_demo_setting_in_every_environment(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "true")
    monkeypatch.setenv("PERPS_DEMO_API_UNSAFE_ENABLED", "true")
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")
    monkeypatch.setenv("ZENODEX_ENV", "local")

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


def test_api_server_refuses_retired_demo_token_auth(monkeypatch) -> None:
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


def test_api_server_refuses_in_memory_sealed_bid_override_in_production(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("ZENODEX_ENV", "production")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_ALLOW_IN_MEMORY_STATE", "true")
    monkeypatch.setenv("ZENODEX_EXTERNAL_AUTH_ENFORCED", "1")

    rc = api_server.main([])
    assert rc == 2


def test_api_server_refuses_local_private_key_signing_in_production(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "127.0.0.1")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("ZENODEX_ENV", "production")
    monkeypatch.setenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", "true")

    rc = api_server.main([])
    assert rc == 2


def test_legacy_unsigned_perps_routes_have_no_dispatcher() -> None:
    from src.integration.api_server import _Handler

    handler = object.__new__(_Handler)
    assert (
        handler._maybe_handle_perps_api(
            method="GET",
            path="/api/perps/markets",
            cors_origin=None,
            raw_body=None,
        )
        is False
    )
    assert (
        handler._maybe_handle_perps_api(
            method="POST",
            path="/api/perps/collateral",
            cors_origin=None,
            raw_body=b"{}",
        )
        is False
    )


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
