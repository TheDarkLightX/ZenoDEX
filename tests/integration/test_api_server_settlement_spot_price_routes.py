from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_settlement_spot_price_routes import (
    maybe_handle_settlement_spot_price_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _packet_request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "entries": [{"asset": "AAA", "price": 100, "observed_epoch": 10, "source_id": "oracle-a"}],
        "now_epoch": 10,
        "max_staleness_epochs": 3,
    }
    request.update(overrides)
    return request


def _attestation_request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "attestation": {"schema": "fake-attestation"},
        "consumer_now_epoch": 10,
        "max_attestation_age_epochs": 3,
    }
    request.update(overrides)
    return request


class _FakePacket:
    def to_dict(self) -> dict[str, object]:
        return {"schema": "fake-settlement-spot-price-packet", "packet_ok": True}


class _FakeAttestation:
    def to_dict(self) -> dict[str, object]:
        return {"schema": "fake-settlement-spot-price-attestation", "attestation_ok": True}


def _fail_on_price_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name in {
            "src.integration.settlement_price_attestation",
            "src.integration.settlement_price_provenance",
        }:
            raise AssertionError("price modules imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_spot_price_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/not_spot_price",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_build_spot_price_packet_rejects_bad_fields_before_import(monkeypatch: Any) -> None:
    _fail_on_price_import(monkeypatch)

    cases = [
        (_packet_request(entries={}), "bad_entries"),
        (_packet_request(entries=[]), "bad_entries"),
        (_packet_request(now_epoch=True), "bad_now_epoch"),
        (_packet_request(now_epoch=-1), "bad_now_epoch"),
        (_packet_request(max_staleness_epochs=True), "bad_max_staleness_epochs"),
        (_packet_request(max_staleness_epochs=-1), "bad_max_staleness_epochs"),
        (_packet_request(cross_module_sync_required=1), "bad_cross_module_sync_required"),
        (_packet_request(cross_module_sync_contract=[]), "bad_cross_module_sync_contract"),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_spot_price_route(
            path="/api/dex/build_settlement_spot_price_packet",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_build_spot_price_packet_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    parsed_entry = object()

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPriceEntry.from_dict",
        staticmethod(lambda payload: ("entry", payload, parsed_entry)),
    )

    def build_settlement_spot_price_packet(**kwargs: object) -> _FakePacket:
        captured.update(kwargs)
        return _FakePacket()

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.build_settlement_spot_price_packet",
        build_settlement_spot_price_packet,
    )

    sync_contract = {"sync_gate_ok": True}
    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/build_settlement_spot_price_packet",
        obj=_packet_request(cross_module_sync_required=True, cross_module_sync_contract=sync_contract),
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "entries": (("entry", _packet_request()["entries"][0], parsed_entry),),
        "now_epoch": 10,
        "max_staleness_epochs": 3,
        "cross_module_sync_required": True,
        "cross_module_sync_contract": sync_contract,
    }
    assert writes == [(200, {"ok": True, "packet": {"schema": "fake-settlement-spot-price-packet", "packet_ok": True}})]


def test_build_spot_price_packet_invalid_entry_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def from_dict(_payload: object) -> object:
        raise ValueError("entry failed")

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPriceEntry.from_dict",
        staticmethod(from_dict),
    )

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/build_settlement_spot_price_packet",
        obj=_packet_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (400, {"ok": False, "error": "build_settlement_spot_price_packet_error", "details": "request failed"})
    ]


def test_build_spot_price_packet_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPriceEntry.from_dict",
        staticmethod(lambda payload: ("entry", payload)),
    )

    def build_settlement_spot_price_packet(**_kwargs: object) -> _FakePacket:
        raise RuntimeError("build failed")

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.build_settlement_spot_price_packet",
        build_settlement_spot_price_packet,
    )

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/build_settlement_spot_price_packet",
        obj=_packet_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (400, {"ok": False, "error": "build_settlement_spot_price_packet_error", "details": "request failed"})
    ]


def test_verify_spot_price_packet_rejects_bad_packet_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_price_import(monkeypatch)

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/verify_settlement_spot_price_packet",
        obj={"packet": []},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_packet"})]


def test_verify_spot_price_packet_success_and_rejection(monkeypatch: Any) -> None:
    packet = {"schema": "fake-packet"}

    for result, expected in [
        ((True, None), (200, {"ok": True, "error": None})),
        ((False, "price packet mismatch"), (200, {"ok": False, "error": "price packet mismatch"})),
    ]:
        writes, write_json = _capture()
        captured: dict[str, object] = {}

        def verify_settlement_spot_price_packet_payload(payload: object) -> tuple[bool, str | None]:
            captured["payload"] = payload
            return result

        monkeypatch.setattr(
            "src.integration.settlement_price_provenance.verify_settlement_spot_price_packet_payload",
            verify_settlement_spot_price_packet_payload,
        )

        handled = maybe_handle_settlement_spot_price_route(
            path="/api/dex/verify_settlement_spot_price_packet",
            obj={"packet": packet},
            write_json=write_json,
        )

        assert handled is True
        assert captured == {"payload": packet}
        assert writes == [expected]


def test_verify_spot_price_packet_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_settlement_spot_price_packet_payload(_payload: object) -> tuple[bool, str | None]:
        raise RuntimeError("verify failed")

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.verify_settlement_spot_price_packet_payload",
        verify_settlement_spot_price_packet_payload,
    )

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/verify_settlement_spot_price_packet",
        obj={"packet": {"schema": "fake-packet"}},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (400, {"ok": False, "error": "verify_settlement_spot_price_packet_error", "details": "request failed"})
    ]


def test_build_spot_price_attestation_rejects_bad_fields_before_import(monkeypatch: Any) -> None:
    _fail_on_price_import(monkeypatch)

    cases = [
        ({"packet": [], "signer_privkey": 7}, "bad_packet"),
        ({"packet": {}, "signer_privkey": []}, "bad_signer_privkey"),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_spot_price_route(
            path="/api/dex/build_settlement_spot_price_attestation",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_build_spot_price_attestation_accepts_bool_privkey_like_inline_handler(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parsed_packet = object()
    captured: dict[str, object] = {}

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPricePacket.from_dict",
        staticmethod(lambda payload: ("packet", payload, parsed_packet)),
    )

    def build_settlement_spot_price_attestation(**kwargs: object) -> _FakeAttestation:
        captured.update(kwargs)
        return _FakeAttestation()

    monkeypatch.setattr(
        "src.integration.settlement_price_attestation.build_settlement_spot_price_attestation",
        build_settlement_spot_price_attestation,
    )

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/build_settlement_spot_price_attestation",
        obj={"packet": {"schema": "fake-packet"}, "signer_privkey": True},
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "packet": ("packet", {"schema": "fake-packet"}, parsed_packet),
        "signer_privkey": True,
    }
    assert writes == [
        (
            200,
            {"ok": True, "attestation": {"schema": "fake-settlement-spot-price-attestation", "attestation_ok": True}},
        )
    ]


def test_build_spot_price_attestation_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    monkeypatch.setattr(
        "src.integration.settlement_price_provenance.SettlementSpotPricePacket.from_dict",
        staticmethod(lambda payload: ("packet", payload)),
    )

    def build_settlement_spot_price_attestation(**_kwargs: object) -> _FakeAttestation:
        raise RuntimeError("attestation failed")

    monkeypatch.setattr(
        "src.integration.settlement_price_attestation.build_settlement_spot_price_attestation",
        build_settlement_spot_price_attestation,
    )

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/build_settlement_spot_price_attestation",
        obj={"packet": {"schema": "fake-packet"}, "signer_privkey": 7},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "build_settlement_spot_price_attestation_error", "details": "request failed"},
        )
    ]


def test_verify_spot_price_attestation_rejects_bad_fields_before_import(monkeypatch: Any) -> None:
    _fail_on_price_import(monkeypatch)

    cases = [
        (_attestation_request(attestation=[]), "bad_attestation"),
        (_attestation_request(consumer_now_epoch=True), "bad_consumer_now_epoch"),
        (_attestation_request(consumer_now_epoch=-1), "bad_consumer_now_epoch"),
        (_attestation_request(max_attestation_age_epochs=True), "bad_max_attestation_age_epochs"),
        (_attestation_request(max_attestation_age_epochs=-1), "bad_max_attestation_age_epochs"),
        (_attestation_request(allowed_signers=[]), "bad_allowed_signers"),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_settlement_spot_price_route(
            path="/api/dex/verify_settlement_spot_price_attestation",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_verify_spot_price_attestation_success_and_rejection(monkeypatch: Any) -> None:
    attestation = {"schema": "fake-attestation"}
    allowed_signers = {"signer-a": ["oracle-a"]}

    for result, expected in [
        ((True, None), (200, {"ok": True, "error": None})),
        ((False, "attestation mismatch"), (200, {"ok": False, "error": "attestation mismatch"})),
    ]:
        writes, write_json = _capture()
        captured: dict[str, object] = {}

        def verify_settlement_spot_price_attestation_payload(**kwargs: object) -> tuple[bool, str | None]:
            captured.update(kwargs)
            return result

        monkeypatch.setattr(
            "src.integration.settlement_price_attestation.verify_settlement_spot_price_attestation_payload",
            verify_settlement_spot_price_attestation_payload,
        )

        handled = maybe_handle_settlement_spot_price_route(
            path="/api/dex/verify_settlement_spot_price_attestation",
            obj=_attestation_request(attestation=attestation, allowed_signers=allowed_signers),
            write_json=write_json,
        )

        assert handled is True
        assert captured == {
            "payload": attestation,
            "consumer_now_epoch": 10,
            "max_attestation_age_epochs": 3,
            "allowed_signers": allowed_signers,
        }
        assert writes == [expected]


def test_verify_spot_price_attestation_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_settlement_spot_price_attestation_payload(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError("attestation verify failed")

    monkeypatch.setattr(
        "src.integration.settlement_price_attestation.verify_settlement_spot_price_attestation_payload",
        verify_settlement_spot_price_attestation_payload,
    )

    handled = maybe_handle_settlement_spot_price_route(
        path="/api/dex/verify_settlement_spot_price_attestation",
        obj=_attestation_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "verify_settlement_spot_price_attestation_error", "details": "request failed"},
        )
    ]
