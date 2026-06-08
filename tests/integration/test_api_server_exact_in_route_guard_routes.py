from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_exact_in_route_guard_routes import (
    maybe_handle_exact_in_route_guard_route,
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


class _FakeContract:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-exact-in-guard-contract",
            "runtime_matches_canonical": True,
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


def test_unknown_exact_in_guard_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/not_exact_in_guard",
        obj={},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_guard_exact_in_route_parse_failure_uses_legacy_generic_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pools must be a non-empty list")

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
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
                "error": "guard_exact_in_route_canonicality_error",
                "details": "request failed",
            },
        )
    ]


def test_guard_exact_in_route_rejects_bad_assets_after_parse_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_exact_in_certificate_import(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return _parse_pools()

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
        obj=_request(asset_out="A"),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is True
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_guard_exact_in_route_rejects_bad_amount_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
        obj=_request(amount_in=True),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_amount_in"})]


def test_guard_exact_in_route_rejects_empty_split_profile_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
        obj=_request(split_search_profile=" "),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_split_search_profile"})]


def test_guard_exact_in_route_rejects_bad_enable_flag_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
        obj=_request(enable_mixed_direct_twohop_split=1),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"})]


def test_guard_exact_in_route_rejects_bad_binding_ok_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
        obj=_request(binding_ok=2),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_binding_ok"})]


def test_guard_exact_in_route_success_payload_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def guard_exact_in_route_runtime_canonicality(**kwargs: object) -> tuple[bool, None, _FakeContract]:
        captured.update(kwargs)
        return True, None, _FakeContract()

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.guard_exact_in_route_runtime_canonicality",
        guard_exact_in_route_runtime_canonicality,
    )
    pools_by_id = _parse_pools()

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
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
                "contract": {
                    "schema": "fake-exact-in-guard-contract",
                    "runtime_matches_canonical": True,
                },
                "error": None,
            },
        )
    ]


def test_guard_exact_in_route_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def guard_exact_in_route_runtime_canonicality(**_kwargs: object) -> tuple[bool, str, _FakeContract]:
        return False, "runtime route not canonical", _FakeContract()

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.guard_exact_in_route_runtime_canonicality",
        guard_exact_in_route_runtime_canonicality,
    )

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
        obj=_request(),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            200,
            {
                "ok": False,
                "contract": {
                    "schema": "fake-exact-in-guard-contract",
                    "runtime_matches_canonical": True,
                },
                "error": "runtime route not canonical",
            },
        )
    ]


def test_guard_exact_in_route_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def guard_exact_in_route_runtime_canonicality(**_kwargs: object) -> tuple[bool, None, _FakeContract]:
        raise RuntimeError("internal detail must not leak")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.guard_exact_in_route_runtime_canonicality",
        guard_exact_in_route_runtime_canonicality,
    )

    handled = maybe_handle_exact_in_route_guard_route(
        path="/api/dex/guard_exact_in_route_canonicality",
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
                "error": "guard_exact_in_route_canonicality_error",
                "details": "request failed",
            },
        )
    ]
