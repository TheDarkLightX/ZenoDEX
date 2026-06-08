from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_settlement_feature_extension_routes import (
    maybe_handle_settlement_feature_extension_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "feature_extension_inputs": {"trade_amount": 100},
    }
    request.update(overrides)
    return request


class _FakePacket:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "fake-settlement-feature-extension-packet",
            "packet_ok": True,
        }


def _fail_on_feature_extension_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name in {
            "src.integration.api_server_settlement_parsers",
            "src.integration.settlement_feature_extension_packet",
        }:
            raise AssertionError("feature extension modules imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_feature_extension_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/not_feature_extension",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_feature_extension_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_inputs = object()

    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_settlement_feature_extension_inputs_payload",
        lambda payload: ("feature-inputs", payload, parsed_inputs),
    )

    def build_settlement_feature_extension_packet(inputs: object) -> _FakePacket:
        captured["inputs"] = inputs
        return _FakePacket()

    monkeypatch.setattr(
        "src.integration.settlement_feature_extension_packet.build_settlement_feature_extension_packet",
        build_settlement_feature_extension_packet,
    )

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/build_settlement_feature_extension_packet",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {"inputs": ("feature-inputs", {"trade_amount": 100}, parsed_inputs)}
    assert writes == [
        (
            200,
            {
                "ok": True,
                "packet": {
                    "schema": "fake-settlement-feature-extension-packet",
                    "packet_ok": True,
                },
            },
        )
    ]


def test_build_feature_extension_packet_bad_inputs_map_to_generic_error() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/build_settlement_feature_extension_packet",
        obj={"feature_extension_inputs": []},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"},
        )
    ]


def test_build_feature_extension_packet_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    monkeypatch.setattr(
        "src.integration.api_server_settlement_parsers._parse_settlement_feature_extension_inputs_payload",
        lambda _payload: object(),
    )

    def build_settlement_feature_extension_packet(_inputs: object) -> _FakePacket:
        raise RuntimeError("build failed")

    monkeypatch.setattr(
        "src.integration.settlement_feature_extension_packet.build_settlement_feature_extension_packet",
        build_settlement_feature_extension_packet,
    )

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/build_settlement_feature_extension_packet",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"},
        )
    ]


def test_verify_feature_extension_packet_rejects_bad_packet_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_feature_extension_import(monkeypatch)

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/verify_settlement_feature_extension_packet",
        obj=_request(packet=[]),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_packet"})]


def test_verify_feature_extension_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    packet = {"schema": "fake-packet"}

    def verify_settlement_feature_extension_packet_payload(**kwargs: object) -> tuple[bool, None]:
        captured.update(kwargs)
        return True, None

    monkeypatch.setattr(
        "src.integration.settlement_feature_extension_packet.verify_settlement_feature_extension_packet_payload",
        verify_settlement_feature_extension_packet_payload,
    )

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/verify_settlement_feature_extension_packet",
        obj=_request(packet=packet),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "inputs_payload": {"trade_amount": 100},
        "packet_payload": packet,
    }
    assert writes == [(200, {"ok": True, "error": None})]


def test_verify_feature_extension_packet_preserves_rejection_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_settlement_feature_extension_packet_payload(**_kwargs: object) -> tuple[bool, str]:
        return False, "settlement feature extension packet mismatch"

    monkeypatch.setattr(
        "src.integration.settlement_feature_extension_packet.verify_settlement_feature_extension_packet_payload",
        verify_settlement_feature_extension_packet_payload,
    )

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/verify_settlement_feature_extension_packet",
        obj=_request(packet={"schema": "fake-packet"}),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "settlement feature extension packet mismatch"})]


def test_verify_feature_extension_packet_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_settlement_feature_extension_packet_payload(**_kwargs: object) -> tuple[bool, str]:
        raise RuntimeError("verify failed")

    monkeypatch.setattr(
        "src.integration.settlement_feature_extension_packet.verify_settlement_feature_extension_packet_payload",
        verify_settlement_feature_extension_packet_payload,
    )

    handled = maybe_handle_settlement_feature_extension_route(
        path="/api/dex/verify_settlement_feature_extension_packet",
        obj=_request(packet={"schema": "fake-packet"}),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "verify_settlement_feature_extension_packet_error", "details": "request failed"},
        )
    ]
