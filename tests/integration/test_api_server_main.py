from __future__ import annotations


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
