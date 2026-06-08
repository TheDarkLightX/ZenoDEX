from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_exact_out_certificate_routes import (
    maybe_handle_exact_out_certificate_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


class _FakeCertificate:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-exact-out-certificate",
            "winner_index": 0,
        }


def _parse_quote(payload: object) -> object:
    if not isinstance(payload, dict):
        raise ValueError("bad quote")
    return {"parsed": payload}


def _fail_on_exact_out_certificate_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name == "src.integration.exact_out_route_certificate":
            raise AssertionError("certificate verifier imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_exact_out_certificate_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/exact_out_certificate_unknown",
        obj={},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_exact_out_certificate_rejects_bad_quotes_before_parser_or_import(
    monkeypatch: Any,
) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_exact_out_certificate_import(monkeypatch)

    def parse_quote(_payload: object) -> object:
        nonlocal parse_called
        parse_called = True
        return object()

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/build_exact_out_route_certificate",
        obj={"quotes": []},
        parse_exact_out_quote=parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is False
    assert writes == [(400, {"ok": False, "error": "bad_quotes"})]


def test_build_exact_out_certificate_payload_contract(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured_quotes: tuple[object, ...] | None = None

    def build(quotes: tuple[object, ...]) -> _FakeCertificate:
        nonlocal captured_quotes
        captured_quotes = quotes
        return _FakeCertificate()

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.build_exact_out_route_canonical_certificate",
        build,
    )

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/build_exact_out_route_certificate",
        obj={"quotes": [{"q": 1}, {"q": 2}]},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert captured_quotes == ({"parsed": {"q": 1}}, {"parsed": {"q": 2}})
    assert writes == [
        (
            200,
            {
                "ok": True,
                "certificate": {
                    "schema": "fake-exact-out-certificate",
                    "winner_index": 0,
                },
            },
        )
    ]


def test_build_exact_out_certificate_parser_exception_payload() -> None:
    writes, write_json = _capture()

    def parse_quote(_payload: object) -> object:
        raise RuntimeError("internal detail must not leak")

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/build_exact_out_route_certificate",
        obj={"quotes": [{"q": 1}]},
        parse_exact_out_quote=parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "bad_exact_out_certificate_request",
                "details": "request failed",
            },
        )
    ]


def test_verify_exact_out_certificate_rejects_bad_certificate_before_import(
    monkeypatch: Any,
) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/verify_exact_out_route_certificate",
        obj={"certificate": []},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_certificate"})]


def test_verify_exact_out_certificate_success_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify(_certificate: object) -> tuple[bool, str | None]:
        return True, None

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.verify_exact_out_route_canonical_certificate_payload",
        verify,
    )

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/verify_exact_out_route_certificate",
        obj={"certificate": {"schema": "fake"}},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": True, "error": "ok"})]


def test_verify_exact_out_certificate_preserves_verifier_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify(_certificate: object) -> tuple[bool, str | None]:
        return False, "certificate payload mismatch"

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.verify_exact_out_route_canonical_certificate_payload",
        verify,
    )

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/verify_exact_out_route_certificate",
        obj={"certificate": {"schema": "fake"}},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "certificate payload mismatch"})]


def test_verify_exact_out_certificate_none_error_stringified(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify(_certificate: object) -> tuple[bool, str | None]:
        return False, None

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.verify_exact_out_route_canonical_certificate_payload",
        verify,
    )

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/verify_exact_out_route_certificate",
        obj={"certificate": {"schema": "fake"}},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "None"})]


def test_verify_exact_out_certificate_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify(_certificate: object) -> tuple[bool, str | None]:
        raise RuntimeError("internal detail must not leak")

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.verify_exact_out_route_canonical_certificate_payload",
        verify,
    )

    handled = maybe_handle_exact_out_certificate_route(
        path="/api/dex/verify_exact_out_route_certificate",
        obj={"certificate": {"schema": "fake"}},
        parse_exact_out_quote=_parse_quote,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "verify_exact_out_certificate_error",
                "details": "request failed",
            },
        )
    ]
