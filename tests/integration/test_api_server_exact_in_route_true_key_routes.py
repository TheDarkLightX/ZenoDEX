from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_exact_in_route_true_key_routes import (
    maybe_handle_exact_in_route_true_key_route,
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
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-exact-in-true-key-interpretation-packet",
            "packet_ok": True,
            "winner_index": 0,
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


def test_unknown_true_key_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/not_true_key",
        obj={},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_true_key_parse_failure_uses_legacy_generic_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pools must be a non-empty list")

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
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
                "error": "build_exact_in_route_true_key_interpretation_packet_error",
                "details": "request failed",
            },
        )
    ]


def test_build_true_key_rejects_bad_assets_after_parse_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_exact_in_certificate_import(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return _parse_pools()

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
        obj=_request(asset_out="A"),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is True
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_build_true_key_rejects_bad_amount_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
        obj=_request(amount_in=True),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_amount_in"})]


def test_build_true_key_rejects_empty_split_profile_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
        obj=_request(split_search_profile=" "),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_split_search_profile"})]


def test_build_true_key_rejects_bad_enable_flag_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
        obj=_request(enable_mixed_direct_twohop_split=1),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"})]


def test_build_true_key_ignores_binding_ok_and_preserves_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def build_exact_in_route_true_key_interpretation_packet_for_pools(**kwargs: object) -> _FakePacket:
        captured.update(kwargs)
        return _FakePacket()

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.build_exact_in_route_true_key_interpretation_packet_for_pools",
        build_exact_in_route_true_key_interpretation_packet_for_pools,
    )
    pools_by_id = _parse_pools()

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
        obj=_request(
            asset_in=" A ",
            asset_out=" B ",
            split_search_profile="adaptive_v7",
            enable_mixed_direct_twohop_split=True,
            binding_ok=2,
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
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "packet_schema": "zenodex/exact-in-route-true-key-interpretation-packet/v1",
                "verify_packet_endpoint": "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
                "packet": {
                    "schema": "fake-exact-in-true-key-interpretation-packet",
                    "packet_ok": True,
                    "winner_index": 0,
                },
            },
        )
    ]


def test_build_true_key_preserves_no_route_response(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def build_exact_in_route_true_key_interpretation_packet_for_pools(**_kwargs: object) -> None:
        return None

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.build_exact_in_route_true_key_interpretation_packet_for_pools",
        build_exact_in_route_true_key_interpretation_packet_for_pools,
    )

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
        obj=_request(),
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "no_route_candidates"})]


def test_build_true_key_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def build_exact_in_route_true_key_interpretation_packet_for_pools(**_kwargs: object) -> _FakePacket:
        raise RuntimeError("packet failed")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.build_exact_in_route_true_key_interpretation_packet_for_pools",
        build_exact_in_route_true_key_interpretation_packet_for_pools,
    )

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/build_exact_in_route_true_key_interpretation_packet",
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
                "error": "build_exact_in_route_true_key_interpretation_packet_error",
                "details": "request failed",
            },
        )
    ]


def test_verify_true_key_rejects_bad_packet_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_in_certificate_import(monkeypatch)

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/verify_exact_in_route_true_key_interpretation_packet",
        obj={"packet": []},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_packet"})]


def test_verify_true_key_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    packet = {"schema": "fake-packet"}
    captured: dict[str, object] = {}

    def verify_exact_in_route_true_key_interpretation_packet_payload(payload: object) -> tuple[bool, None]:
        captured["payload"] = payload
        return True, None

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.verify_exact_in_route_true_key_interpretation_packet_payload",
        verify_exact_in_route_true_key_interpretation_packet_payload,
    )

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/verify_exact_in_route_true_key_interpretation_packet",
        obj={"packet": packet},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert captured["payload"] is packet
    assert writes == [(200, {"ok": True, "error": None})]


def test_verify_true_key_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_exact_in_route_true_key_interpretation_packet_payload(_payload: object) -> tuple[bool, str]:
        return False, "true-key interpretation packet payload mismatch"

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.verify_exact_in_route_true_key_interpretation_packet_payload",
        verify_exact_in_route_true_key_interpretation_packet_payload,
    )

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/verify_exact_in_route_true_key_interpretation_packet",
        obj={"packet": {"schema": "fake-packet"}},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "true-key interpretation packet payload mismatch"})]


def test_verify_true_key_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_exact_in_route_true_key_interpretation_packet_payload(_payload: object) -> tuple[bool, str]:
        raise RuntimeError("verify failed")

    monkeypatch.setattr(
        "src.integration.exact_in_route_certificate.verify_exact_in_route_true_key_interpretation_packet_payload",
        verify_exact_in_route_true_key_interpretation_packet_payload,
    )

    handled = maybe_handle_exact_in_route_true_key_route(
        path="/api/dex/verify_exact_in_route_true_key_interpretation_packet",
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
                "error": "verify_exact_in_route_true_key_interpretation_packet_error",
                "details": "request failed",
            },
        )
    ]
