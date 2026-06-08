from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_exact_in_route_packet_routes import (
    maybe_handle_exact_in_route_packet_route,
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


class _FakePacket:
    def __init__(self, *, guard_ok: bool = True, error: str | None = None) -> None:
        self.guard_ok = guard_ok
        self.error = error

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-exact-in-guarded-quote-packet",
            "guard_ok": self.guard_ok,
            "quote": {"amount_out": 99} if self.guard_ok else None,
            "error": self.error,
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
            raise AssertionError("exact-in certificate module imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_exact_in_packet_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/not_exact_in_packet",
        obj={},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_guarded_quote_packet_parse_failure_uses_legacy_generic_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pools must be a non-empty list")

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "build_exact_in_route_guarded_quote_packet_error",
                "details": "request failed",
            },
        )
    ]


def test_build_guarded_quote_packet_rejects_bad_assets_after_parse_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_exact_in_certificate_import(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return _parse_pools()

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(asset_out="A"),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is True
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_build_guarded_quote_packet_rejects_bad_amount_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(amount_in=True),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_amount_in"})]


def test_build_guarded_quote_packet_rejects_empty_split_profile_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(split_search_profile=" "),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_split_search_profile"})]


def test_build_guarded_quote_packet_rejects_bad_enable_flag_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(enable_mixed_direct_twohop_split=1),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"})]


def test_build_guarded_quote_packet_rejects_bad_binding_ok_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(binding_ok=2),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_binding_ok"})]


def test_build_guarded_quote_packet_success_payload_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def build_exact_in_route_guarded_quote_packet(**kwargs: object) -> _FakePacket:
        captured.update(kwargs)
        return _FakePacket()

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.build_exact_in_route_guarded_quote_packet",
        build_exact_in_route_guarded_quote_packet,
    )
    pools_by_id = _parse_pools()

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(
            asset_in=" A ",
            asset_out=" B ",
            split_search_profile="adaptive_v7",
            enable_mixed_direct_twohop_split=True,
            binding_ok=0,
        ),
        parse_pools=lambda: pools_by_id,
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
                "packet_schema": "zenodex/exact-in-route-guarded-quote-packet/v1",
                "verify_packet_endpoint": "/api/dex/verify_exact_in_route_guarded_quote_packet",
                "packet": {
                    "schema": "fake-exact-in-guarded-quote-packet",
                    "guard_ok": True,
                    "quote": {"amount_out": 99},
                    "error": None,
                },
            },
        )
    ]


def test_build_guarded_quote_packet_preserves_guard_failure_top_level_fields(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def build_exact_in_route_guarded_quote_packet(**_kwargs: object) -> _FakePacket:
        return _FakePacket(guard_ok=False, error="runtime route not canonical")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.build_exact_in_route_guarded_quote_packet",
        build_exact_in_route_guarded_quote_packet,
    )

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            200,
            {
                "ok": True,
                "packet_schema": "zenodex/exact-in-route-guarded-quote-packet/v1",
                "verify_packet_endpoint": "/api/dex/verify_exact_in_route_guarded_quote_packet",
                "packet": {
                    "schema": "fake-exact-in-guarded-quote-packet",
                    "guard_ok": False,
                    "quote": None,
                    "error": "runtime route not canonical",
                },
                "guard_ok": False,
                "error": "runtime route not canonical",
            },
        )
    ]


def test_build_guarded_quote_packet_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def build_exact_in_route_guarded_quote_packet(**_kwargs: object) -> _FakePacket:
        raise RuntimeError("packet failed")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.build_exact_in_route_guarded_quote_packet",
        build_exact_in_route_guarded_quote_packet,
    )

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/build_exact_in_route_guarded_quote_packet",
        obj=_request(),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "build_exact_in_route_guarded_quote_packet_error",
                "details": "request failed",
            },
        )
    ]


def test_verify_guarded_quote_packet_rejects_bad_packet_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/verify_exact_in_route_guarded_quote_packet",
        obj={"packet": []},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_packet"})]


def test_verify_guarded_quote_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    packet = {"schema": "fake-packet"}
    captured: dict[str, object] = {}

    def verify_exact_in_route_guarded_quote_packet_payload(payload: object) -> tuple[bool, None]:
        captured["payload"] = payload
        return True, None

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.verify_exact_in_route_guarded_quote_packet_payload",
        verify_exact_in_route_guarded_quote_packet_payload,
    )

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/verify_exact_in_route_guarded_quote_packet",
        obj={"packet": packet},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert captured["payload"] is packet
    assert writes == [(200, {"ok": True, "error": None})]


def test_verify_guarded_quote_packet_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_exact_in_route_guarded_quote_packet_payload(_payload: object) -> tuple[bool, str]:
        return False, "guarded quote packet payload mismatch"

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.verify_exact_in_route_guarded_quote_packet_payload",
        verify_exact_in_route_guarded_quote_packet_payload,
    )

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/verify_exact_in_route_guarded_quote_packet",
        obj={"packet": {"schema": "fake-packet"}},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "guarded quote packet payload mismatch"})]


def test_verify_guarded_quote_packet_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_exact_in_route_guarded_quote_packet_payload(_payload: object) -> tuple[bool, str]:
        raise RuntimeError("verify failed")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.verify_exact_in_route_guarded_quote_packet_payload",
        verify_exact_in_route_guarded_quote_packet_payload,
    )

    handled = maybe_handle_exact_in_route_packet_route(
        path="/api/dex/verify_exact_in_route_guarded_quote_packet",
        obj={"packet": {"schema": "fake-packet"}},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "verify_exact_in_route_guarded_quote_packet_error",
                "details": "request failed",
            },
        )
    ]
