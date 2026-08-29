from __future__ import annotations

from dataclasses import replace

import pytest

from src.integration.local_route_quarantine import (
    QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1,
    QUARANTINED_ROUTE_ENVIRONMENT_V1,
)


@pytest.fixture(autouse=True)
def isolate_retired_tau_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in QUARANTINED_ROUTE_ENVIRONMENT_V1 + QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1:
        monkeypatch.delenv(name, raising=False)


def _unexpected_effect(label: str):
    def effect(*_args: object, **_kwargs: object) -> object:
        raise AssertionError(f"startup refusal must precede {label}")

    return effect


@pytest.mark.parametrize("variable", QUARANTINED_ROUTE_ENVIRONMENT_V1)
@pytest.mark.parametrize("value", ("", "true", "TRUE", "1", "yes", " false ", "on"))
def test_given_retired_route_value_when_starting_then_refuse_before_effects(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    variable: str,
    value: str,
) -> None:
    from src.integration import api_server

    # Arrange.
    monkeypatch.setenv(variable, value)
    monkeypatch.setattr(api_server, "_load_api_server_config", _unexpected_effect("config"))
    monkeypatch.setattr(api_server, "_prewarm_api_modules", _unexpected_effect("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_effect("server construction"))

    # Act and assert.
    assert api_server.main([]) == 2
    assert capsys.readouterr().out.splitlines() == [
        "Refusing to start: retired Tau route environment variable "
        f"{variable!r} must be absent, exact 'false', or exact '0'."
    ]


@pytest.mark.parametrize("alias", QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1)
def test_given_retired_route_alias_when_starting_then_refuse_before_config(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    alias: str,
) -> None:
    from src.integration import api_server

    # Arrange.
    monkeypatch.setenv(alias, "false")
    monkeypatch.setattr(api_server, "_load_api_server_config", _unexpected_effect("config"))
    monkeypatch.setattr(api_server, "_prewarm_api_modules", _unexpected_effect("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_effect("server construction"))

    # Act and assert.
    assert api_server.main([]) == 2
    assert capsys.readouterr().out.splitlines() == [
        f"Refusing to start: retired Tau route environment alias {alias!r} is forbidden."
    ]


@pytest.mark.parametrize(
    ("field_name", "variable"),
    (
        ("perps_wallet_enabled", "PERPS_WALLET_API_ENABLED"),
        ("zusd_tau_wallet_enabled", "ZUSD_TAU_WALLET_API_ENABLED"),
        ("zusd_monetary_wallet_enabled", "ZUSD_MONETARY_WALLET_API_ENABLED"),
    ),
)
def test_given_parsed_retired_mode_when_starting_then_refuse_before_server_effects(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    field_name: str,
    variable: str,
) -> None:
    from src.integration import api_server

    # Arrange.
    config = replace(api_server._load_api_server_config(), **{field_name: True})
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: config)
    monkeypatch.setattr(api_server, "_prewarm_api_modules", _unexpected_effect("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", _unexpected_effect("server construction"))

    # Act and assert.
    assert api_server.main([]) == 2
    refusal = capsys.readouterr().out
    assert refusal.startswith("Refusing to start:")
    assert variable in refusal
