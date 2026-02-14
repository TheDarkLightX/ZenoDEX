from __future__ import annotations


def test_api_server_refuses_demo_routes_without_token_on_public_host(monkeypatch) -> None:
    from src.integration import api_server

    monkeypatch.setenv("API_HOST", "0.0.0.0")
    monkeypatch.setenv("API_PORT", "8000")
    monkeypatch.setenv("PERPS_API_ENABLED", "true")
    monkeypatch.delenv("DEMO_API_TOKEN", raising=False)

    rc = api_server.main([])
    assert rc == 2

