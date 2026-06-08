from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_exact_in_route_quote_routes import (
    maybe_handle_exact_in_route_quote_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _parse_pools() -> dict[str, object]:
    return {"pool_a": object(), "pool_b": object()}


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
    }
    request.update(overrides)
    return request


def _accept_bridge(**_kwargs: object) -> None:
    return None


_DEFAULT_RUNTIME_QUOTE = object()


class _FakeContract:
    def __init__(self, runtime_quote: object = _DEFAULT_RUNTIME_QUOTE) -> None:
        if runtime_quote is _DEFAULT_RUNTIME_QUOTE:
            self.runtime_quote = {"amount_out": 99}
        else:
            self.runtime_quote = runtime_quote

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-exact-in-quote-contract",
            "runtime_matches_canonical": True,
            "runtime_quote": self.runtime_quote,
        }


def _fail_on_exact_in_certificate_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name == "src.integration.exact_in_route_certificate":
            raise AssertionError("exact-in certificate module imported before bridge admission")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_exact_in_quote_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/not_exact_in_quote",
        obj={},
        parse_pools=_parse_pools,
        check_oracle_bridge=_accept_bridge,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_quote_exact_in_route_parse_failure_uses_legacy_generic_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pools must be a non-empty list")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(),
        parse_pools=parse_pools,
        check_oracle_bridge=_accept_bridge,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "quote_exact_in_route_guarded_error",
                "details": "request failed",
            },
        )
    ]


def test_quote_exact_in_route_rejects_bad_assets_after_parse_before_bridge_and_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_exact_in_certificate_import(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return _parse_pools()

    def bridge_should_not_run(**_kwargs: object) -> None:
        raise AssertionError("bridge check should not run before cheap field validation")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(asset_out="A"),
        parse_pools=parse_pools,
        check_oracle_bridge=bridge_should_not_run,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is True
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_quote_exact_in_route_rejects_bad_amount_before_bridge_and_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    def bridge_should_not_run(**_kwargs: object) -> None:
        raise AssertionError("bridge check should not run before amount validation")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(amount_in=True),
        parse_pools=_parse_pools,
        check_oracle_bridge=bridge_should_not_run,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_amount_in"})]


def test_quote_exact_in_route_rejects_empty_split_profile_before_bridge_and_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    def bridge_should_not_run(**_kwargs: object) -> None:
        raise AssertionError("bridge check should not run before split profile validation")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(split_search_profile=" "),
        parse_pools=_parse_pools,
        check_oracle_bridge=bridge_should_not_run,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_split_search_profile"})]


def test_quote_exact_in_route_rejects_bad_enable_flag_before_bridge_and_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    def bridge_should_not_run(**_kwargs: object) -> None:
        raise AssertionError("bridge check should not run before enable flag validation")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(enable_mixed_direct_twohop_split=1),
        parse_pools=_parse_pools,
        check_oracle_bridge=bridge_should_not_run,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"})]


def test_quote_exact_in_route_rejects_bad_binding_ok_before_bridge_and_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    def bridge_should_not_run(**_kwargs: object) -> None:
        raise AssertionError("bridge check should not run before binding flag validation")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(binding_ok=2),
        parse_pools=_parse_pools,
        check_oracle_bridge=bridge_should_not_run,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_binding_ok"})]


def test_quote_exact_in_route_rejects_bridge_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    _fail_on_exact_in_certificate_import(monkeypatch)

    def reject_bridge(**kwargs: object) -> str:
        captured.update(kwargs)
        return "oracle_adapter_bridge action_id mismatch"

    request = _request(
        asset_in=" A ",
        asset_out=" B ",
        split_search_profile="adaptive_v7",
        enable_mixed_direct_twohop_split=True,
        binding_ok=0,
    )
    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=request,
        parse_pools=_parse_pools,
        check_oracle_bridge=reject_bridge,
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "body": request,
        "path": "/api/dex/quote_exact_in_route_guarded",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
        "split_search_profile": "adaptive_v7",
        "enable_mixed_direct_twohop_split": True,
        "binding_ok": 0,
    }
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "rejected",
                "detail": "oracle_adapter_bridge action_id mismatch",
            },
        )
    ]


def test_quote_exact_in_route_bridge_exception_uses_generic_error() -> None:
    writes, write_json = _capture()

    def bridge_raises(**_kwargs: object) -> str:
        raise RuntimeError("bridge unavailable")

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(),
        parse_pools=_parse_pools,
        check_oracle_bridge=bridge_raises,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "quote_exact_in_route_guarded_error",
                "details": "request failed",
            },
        )
    ]


def test_quote_exact_in_route_success_payload_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def quote_exact_in_route_guarded(**kwargs: object) -> tuple[object, None, _FakeContract]:
        captured.update(kwargs)
        return object(), None, _FakeContract()

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.quote_exact_in_route_guarded",
        quote_exact_in_route_guarded,
    )
    pools_by_id = _parse_pools()

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(
            asset_in=" A ",
            asset_out=" B ",
            split_search_profile="adaptive_v7",
            enable_mixed_direct_twohop_split=True,
            binding_ok=0,
        ),
        parse_pools=lambda: pools_by_id,
        check_oracle_bridge=_accept_bridge,
        write_json=write_json,
    )

    assert handled is True
    assert captured["pools_by_id"] is pools_by_id
    assert captured == {
        "pools_by_id": pools_by_id,
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
        "split_search_profile": "adaptive_v7",
        "enable_mixed_direct_twohop_split": True,
        "binding_ok": 0,
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "contract": {
                    "schema": "fake-exact-in-quote-contract",
                    "runtime_matches_canonical": True,
                    "runtime_quote": {"amount_out": 99},
                },
                "error": None,
                "quote": {"amount_out": 99},
            },
        )
    ]


def test_quote_exact_in_route_preserves_no_quote_response(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def quote_exact_in_route_guarded(**_kwargs: object) -> tuple[None, str, _FakeContract]:
        return None, "no route", _FakeContract(runtime_quote=None)

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.quote_exact_in_route_guarded",
        quote_exact_in_route_guarded,
    )

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(),
        parse_pools=_parse_pools,
        check_oracle_bridge=_accept_bridge,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            200,
            {
                "ok": False,
                "contract": {
                    "schema": "fake-exact-in-quote-contract",
                    "runtime_matches_canonical": True,
                    "runtime_quote": None,
                },
                "error": "no route",
            },
        )
    ]


def test_quote_exact_in_route_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def quote_exact_in_route_guarded(**_kwargs: object) -> tuple[None, str, _FakeContract]:
        raise RuntimeError("quote failed")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.quote_exact_in_route_guarded",
        quote_exact_in_route_guarded,
    )

    handled = maybe_handle_exact_in_route_quote_route(
        path="/api/dex/quote_exact_in_route_guarded",
        obj=_request(),
        parse_pools=_parse_pools,
        check_oracle_bridge=_accept_bridge,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "quote_exact_in_route_guarded_error",
                "details": "request failed",
            },
        )
    ]
